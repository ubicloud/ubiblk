use std::path::PathBuf;

use base64::{engine::general_purpose::STANDARD, Engine};
use clap::Parser;

use ubiblk::{
    archive::{ArchiveStore, FileSystemStore, S3Store, StripeArchiver},
    block_device::UbiMetadata,
    cli::{load_options, CommonArgs},
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
  archive -f config.yaml -t s3://my-r2-bucket/ubiblk --profile r2 --endpoint https://<account>.r2.cloudflarestorage.com"#
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,

    #[arg(
        short = 't',
        long = "target",
        value_name = "TARGET",
        help = "Archive destination: a local path or s3://bucket[/prefix]"
    )]
    target: String,

    /// Custom S3 endpoint URL (e.g. https://<account>.r2.cloudflarestorage.com).
    #[arg(long = "endpoint")]
    s3_endpoint: Option<String>,

    /// Base64-encoded (possibly encrypted) S3 access key ID.
    #[arg(long = "access-key-id")]
    s3_access_key_id: Option<String>,

    /// Base64-encoded (possibly encrypted) S3 secret access key.
    #[arg(long = "secret-access-key")]
    s3_secret_access_key: Option<String>,

    /// S3 region (e.g. auto).
    #[arg(long = "region")]
    s3_region: Option<String>,

    /// Use a specific AWS profile when creating the S3 client.
    #[arg(long = "profile")]
    s3_profile: Option<String>,

    /// Number of concurrent S3 connections.
    #[arg(long = "concurrency", default_value_t = 16)]
    s3_connections: usize,

    /// Encrypt archived stripes.
    #[arg(short = 'e', long = "encrypt", default_value_t = false)]
    encrypt: bool,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let options = load_options(&args.common)?;
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

    // TODO: Use proper KEK for archives instead of default (tracked in future PR)
    let archive_kek = KeyEncryptionCipher::default();
    let stripe_source =
        StripeSourceBuilder::new(options.clone(), archive_kek.clone(), stripe_sector_count)
            .build()?;

    let store = build_store(&args, &archive_kek)?;
    let mut archiver = StripeArchiver::new(
        stripe_source,
        disk_dev.as_ref(),
        metadata,
        store,
        args.encrypt,
        archive_kek.clone(),
        args.s3_connections,
    )?;

    archiver.archive_all()?;

    Ok(())
}

fn build_store(args: &Args, kek: &KeyEncryptionCipher) -> Result<Box<dyn ArchiveStore>> {
    match parse_archive_target(&args.target)? {
        ArchiveTarget::FileSystem(path) => Ok(Box::new(FileSystemStore::new(path)?)),
        ArchiveTarget::S3 { bucket, prefix } => {
            let runtime = create_runtime()?;
            let decrypted_credentials = decrypt_s3_credentials(args, kek)?;
            let client = build_s3_client(
                &runtime,
                args.s3_profile.as_deref(),
                args.s3_endpoint.as_deref(),
                args.s3_region.as_deref(),
                decrypted_credentials,
            )?;
            let worker_threads = args.s3_connections;
            Ok(Box::new(S3Store::new(
                client,
                bucket,
                prefix,
                worker_threads,
            )?))
        }
    }
}

fn decrypt_s3_credentials(
    args: &Args,
    kek: &KeyEncryptionCipher,
) -> Result<Option<aws_sdk_s3::config::Credentials>> {
    match (&args.s3_access_key_id, &args.s3_secret_access_key) {
        (Some(access_key_id), Some(secret_access_key)) => {
            let access_key_id =
                kek.decrypt_aws_credential(decode_credential("access-key-id", access_key_id)?)?;
            let secret_access_key = kek.decrypt_aws_credential(decode_credential(
                "secret-access-key",
                secret_access_key,
            )?)?;
            Ok(Some(
                aws_sdk_s3::config::Credentials::builder()
                    .access_key_id(access_key_id)
                    .secret_access_key(secret_access_key)
                    .provider_name("ubiblk_archive")
                    .build(),
            ))
        }
        (None, None) => Ok(None),
        _ => Err(UbiblkError::InvalidParameter {
            description: "access-key-id and secret-access-key must both be set or both be unset"
                .to_string(),
        }),
    }
}

fn decode_credential(field: &str, value: &str) -> Result<Vec<u8>> {
    STANDARD
        .decode(value)
        .map_err(|e| UbiblkError::InvalidParameter {
            description: format!("Failed to decode {field}: {e}"),
        })
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
