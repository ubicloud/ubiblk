use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use log::error;
use serde::Serialize;

use ubiblk::{
    archive::{ArchiveCompressionAlgorithm, StripeArchiver},
    backends::{build_block_device, SECTOR_SIZE},
    block_device::UbiMetadata,
    cli::{load_config, CommonArgs},
    config::v2,
    stripe_source::StripeSourceBuilder,
    Result,
};

#[derive(Parser)]
#[command(
    name = "archive",
    version,
    author,
    about = "Archive stripes from a ubiblk device to a store.",
    long_about = r#"Archive stripes from a ubiblk device to an S3-compatible bucket or local filesystem.

Examples:
  # Archive to a local folder
  archive -f config.toml --target-config archive_target.toml

  # Archive to S3 with an optional prefix
  archive -f config.toml --target-config archive_target.toml"#
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,

    #[arg(
        long = "target-config",
        value_name = "PATH",
        help = "Path to archive target config."
    )]
    target_config_path: PathBuf,

    /// Encrypt archived stripes.
    #[arg(short = 'e', long = "encrypt", default_value_t = false)]
    encrypt: bool,

    /// Compress archived stripes.
    #[arg(long = "compression", value_enum, default_value_t = CompressionChoice::None)]
    compression: CompressionChoice,

    /// Compression level for zstd (lower is faster).
    #[arg(
        long = "zstd-level",
        default_value_t = 3,
        value_parser = clap::value_parser!(i32).range(1..=22)
    )]
    zstd_level: i32,

    #[arg(
        long = "stats",
        value_name = "PATH",
        help = "Optional path to write archive stats JSON."
    )]
    stats_path: Option<PathBuf>,
}

#[derive(Clone, Debug, ValueEnum)]
enum CompressionChoice {
    None,
    Zstd,
}

#[derive(Serialize)]
struct ArchiveStats {
    physical_size_bytes: u64,
    logical_size_bytes: u64,
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    if let Err(err) = run() {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = Args::parse();

    let config = load_config(&args.common)?;
    let metadata_path = config
        .device
        .metadata_path
        .as_ref()
        .ok_or(ubiblk::ubiblk_error!(InvalidParameter {
            description: "Metadata path is missing".to_string(),
        }))?;
    let metadata_dev = build_block_device(metadata_path, &config, true)?;
    let metadata = UbiMetadata::load_from_bdev(metadata_dev.as_ref())?;

    let disk_dev = build_block_device(&config.device.data_path, &config, true)?;

    let stripe_sector_count = 1u64 << metadata.stripe_sector_count_shift;

    let stripe_source = StripeSourceBuilder::new(
        config.clone(),
        stripe_sector_count,
        metadata.has_fetched_all_stripes(),
    )
    .build()?;

    let target_config = v2::ArchiveTargetConfig::load(&args.target_config_path)?;
    let store =
        StripeSourceBuilder::build_archive_store(&target_config.target, &target_config.secrets)?;

    let compression = match args.compression {
        CompressionChoice::None => ArchiveCompressionAlgorithm::None,
        CompressionChoice::Zstd => ArchiveCompressionAlgorithm::Zstd {
            level: args.zstd_level,
        },
    };

    let mut archiver = StripeArchiver::new(
        stripe_source,
        disk_dev.as_ref(),
        metadata,
        store,
        args.encrypt,
        compression,
        StripeSourceBuilder::build_archive_kek(&target_config.target, &target_config.secrets)?,
        4,
    )?;

    archiver.archive_all()?;

    if let Some(stats_path) = args.stats_path {
        let stats = ArchiveStats {
            physical_size_bytes: archiver.physical_size_bytes(),
            logical_size_bytes: disk_dev.sector_count().saturating_mul(SECTOR_SIZE as u64),
        };
        let bytes = serde_json::to_vec_pretty(&stats).map_err(|e| {
            ubiblk::ubiblk_error!(InvalidParameter {
                description: format!("Failed to serialize stats JSON: {e}"),
            })
        })?;
        std::fs::write(&stats_path, bytes)
            .map_err(|e| ubiblk::ubiblk_error!(IoError { source: e }))?;
    }

    Ok(())
}
