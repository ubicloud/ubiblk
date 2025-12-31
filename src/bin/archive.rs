use std::path::PathBuf;

use clap::Parser;

use ubiblk::{
    archive::{FileSystemStore, StripeArchiver},
    block_device::UbiMetadata,
    stripe_source::StripeSourceBuilder,
    vhost_backend::*,
    KeyEncryptionCipher, Result, UbiblkError,
};

#[derive(Parser)]
#[command(
    name = "archive",
    version,
    author,
    about = "Archive stripes from a ubiblk device to a store."
)]
struct Args {
    /// Path to the configuration YAML file.
    #[arg(short = 'f', long = "config")]
    config: String,

    /// Path to the key encryption key file.
    #[arg(short = 'k', long = "kek")]
    kek: Option<String>,

    /// Unlink the key encryption key file after use.
    #[arg(short = 'u', long = "unlink-kek", default_value_t = false)]
    unlink_kek: bool,

    #[arg(short = 't', long = "target")]
    target: PathBuf,

    #[arg(short = 'e', long = "encrypt", default_value_t = false)]
    encrypt: bool,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config_path = &args.config;
    let options = Options::load_from_file(&PathBuf::from(config_path))?;

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = KeyEncryptionCipher::load(kek_path.as_ref(), args.unlink_kek)?;

    let metadata_path = options
        .metadata_path
        .as_ref()
        .ok_or(UbiblkError::InvalidParameter {
            description: "Metadata path is missing".to_string(),
        })?;
    let metadata_dev = build_block_device(metadata_path, &options, kek.clone(), true)?;
    let metadata = UbiMetadata::load_from_bdev(metadata_dev.as_ref())?;

    let disk_dev = build_block_device(&options.path, &options, kek.clone(), true)?;

    let stripe_sector_count = 1u64 << metadata.stripe_sector_count_shift;
    let stripe_source =
        StripeSourceBuilder::new(options.clone(), kek.clone(), stripe_sector_count).build()?;

    let store = FileSystemStore::new(args.target.clone())?;

    let mut archiver = StripeArchiver::new(
        stripe_source,
        disk_dev.as_ref(),
        metadata,
        Box::new(store),
        args.encrypt,
        kek.clone(),
    )?;

    archiver.archive_all()?;

    Ok(())
}
