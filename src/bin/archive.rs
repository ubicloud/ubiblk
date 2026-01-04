use std::path::PathBuf;

use clap::Parser;

use ubiblk::{
    archive::{ArchiveStore, FileSystemStore, S3Store, StripeArchiver},
    block_device::UbiMetadata,
    stripe_source::StripeSourceBuilder,
    utils::s3::{build_s3_client, create_runtime},
    vhost_backend::*,
    KeyEncryptionCipher, Result, UbiblkError,
};

#[derive(Debug, Clone)]
enum ArchiveTarget {
    FileSystem(PathBuf),
    S3 {
        bucket: String,
        prefix: Option<String>,
    },
}

#[derive(Parser)]
#[command(
    name = "archive",
    version,
    author,
    about = "Archive stripes from a ubiblk device to a store.",
    long_about = r#"Archive stripes from a ubiblk device to an S3-compatible bucket or local filesystem.

Examples:
  # Archive to a local folder
  archive -f config.yaml -t /var/ubiblk/archive

  # Archive to S3 with an optional prefix
  archive -f config.yaml -t s3://my-bucket/backups

  # Set up access key and secret key for R2. Use 'auto' region.
  aws configure --profile r2

  # Archive to Cloudflare R2
  archive -f config.yaml -t s3://my-r2-bucket/ubiblk --s3-profile r2 --s3-endpoint https://<account>.r2.cloudflarestorage.com"#
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

    #[arg(
        short = 't',
        long = "target",
        value_name = "TARGET",
        help = "Archive destination: a local path or s3://bucket[/prefix]"
    )]
    target: String,

    /// Custom S3 endpoint URL (e.g. https://<account>.r2.cloudflarestorage.com).
    #[arg(long = "s3-endpoint")]
    s3_endpoint: Option<String>,

    /// Use a specific AWS profile when creating the S3 client.
    #[arg(long = "s3-profile")]
    s3_profile: Option<String>,

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

    let store = build_store(&args)?;

    let mut archiver = StripeArchiver::new(
        stripe_source,
        disk_dev.as_ref(),
        metadata,
        store,
        args.encrypt,
        kek.clone(),
    )?;

    archiver.archive_all()?;

    Ok(())
}

fn build_store(args: &Args) -> Result<Box<dyn ArchiveStore>> {
    match parse_archive_target(&args.target)? {
        ArchiveTarget::FileSystem(path) => Ok(Box::new(FileSystemStore::new(path)?)),
        ArchiveTarget::S3 { bucket, prefix } => {
            let runtime = create_runtime()?;
            let client = build_s3_client(
                &runtime,
                args.s3_profile.as_deref(),
                args.s3_endpoint.as_deref(),
                None,
                None,
            )?;
            Ok(Box::new(S3Store::new(client, bucket, prefix, runtime)?))
        }
    }
}

fn parse_archive_target(target: &str) -> Result<ArchiveTarget> {
    if let Some(rest) = target.strip_prefix("s3://") {
        let mut parts = rest.splitn(2, '/');
        let bucket =
            parts
                .next()
                .filter(|b| !b.is_empty())
                .ok_or(UbiblkError::InvalidParameter {
                    description: "S3 target must be in the form s3://<bucket>[/prefix]".to_string(),
                })?;
        let prefix = parts.next().map(|p| p.to_string());

        Ok(ArchiveTarget::S3 {
            bucket: bucket.to_string(),
            prefix,
        })
    } else {
        Ok(ArchiveTarget::FileSystem(PathBuf::from(target)))
    }
}
