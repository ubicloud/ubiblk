use std::path::PathBuf;

use clap::Parser;

use ubiblk::{
    archive::StripeArchiver,
    block_device::UbiMetadata,
    cli::{load_options_and_kek, CommonArgs},
    config::ArchiveStripeSourceConfig,
    stripe_source::StripeSourceBuilder,
    vhost_backend::build_block_device,
    Result, UbiblkError,
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
  archive -f config.yaml --target-config archive_target.yaml

  # Archive to S3 with an optional prefix
  archive -f config.yaml --target-config archive_target.yaml"#
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
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let (options, config_kek) = load_options_and_kek(&args.common)?;
    let metadata_path = options
        .metadata_path
        .as_ref()
        .ok_or(UbiblkError::InvalidParameter {
            description: "Metadata path is missing".to_string(),
        })?;
    let metadata_dev = build_block_device(metadata_path, &options, true)?;
    let metadata = UbiMetadata::load_from_bdev(metadata_dev.as_ref())?;

    let disk_dev = build_block_device(&options.path, &options, true)?;

    let stripe_sector_count = 1u64 << metadata.stripe_sector_count_shift;

    let stripe_source = StripeSourceBuilder::new(options.clone(), stripe_sector_count).build()?;

    let target_config =
        ArchiveStripeSourceConfig::load_from_file_with_kek(&args.target_config_path, &config_kek)?;
    let store = StripeSourceBuilder::build_archive_store(&target_config)?;

    let mut archiver = StripeArchiver::new(
        stripe_source,
        disk_dev.as_ref(),
        metadata,
        store,
        args.encrypt,
        target_config.archive_kek().clone(),
        target_config.connections(),
    )?;

    archiver.archive_all()?;

    Ok(())
}
