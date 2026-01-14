use clap::Parser;
use ubiblk::block_device::{self, metadata_flags, BlockDevice, UbiMetadata};
use ubiblk::cli::{load_options, CommonArgs};
use ubiblk::vhost_backend::{
    build_block_device, ArchiveStripeSourceConfig, StripeSourceConfig, SECTOR_SIZE,
};
use ubiblk::{Error, Result};

#[derive(Parser)]
#[command(
    name = "dump-metadata",
    version,
    author,
    about = "Dump metadata information"
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,
}

fn format_list(list: &[usize]) -> String {
    if list.is_empty() {
        return String::new();
    }

    let mut formatted = Vec::new();
    let mut start = list[0];
    let mut prev = list[0];

    for &value in &list[1..] {
        if value == prev + 1 {
            prev = value;
            continue;
        }

        push_range(&mut formatted, start, prev);
        start = value;
        prev = value;
    }

    push_range(&mut formatted, start, prev);

    formatted.join(", ")
}

fn push_range(output: &mut Vec<String>, start: usize, end: usize) {
    match end - start {
        0 => output.push(start.to_string()),
        1 => {
            output.push(start.to_string());
            output.push(end.to_string());
        }
        _ => output.push(format!("{start}-{end}")),
    }
}

fn format_optional(value: Option<&str>) -> &str {
    value.unwrap_or("None")
}

fn format_source_info(options: &ubiblk::vhost_backend::Options) -> Result<String> {
    #[allow(deprecated)]
    match options.resolved_stripe_source() {
        Some(StripeSourceConfig::Raw { path }) => {
            let dev = block_device::UringBlockDevice::new(
                path.clone(),
                options.queue_size,
                true,
                true,
                options.write_through,
            )?;
            let image_size = dev.sector_count() * SECTOR_SIZE as u64;
            Ok(format!(
                "raw (path: {}, size: {} bytes)",
                path.display(),
                image_size
            ))
        }
        Some(StripeSourceConfig::Remote { config }) => Ok(format!(
            "remote (address: {}, psk_identity: {})",
            config.address,
            format_optional(config.psk_identity.as_deref())
        )),
        Some(StripeSourceConfig::Archive { config }) => match config {
            ArchiveStripeSourceConfig::Filesystem { path, .. } => {
                Ok(format!("archive filesystem (path: {path})"))
            }
            ArchiveStripeSourceConfig::S3 {
                bucket,
                prefix,
                endpoint,
                region,
                profile,
                connections,
                ..
            } => Ok(format!(
                "archive s3 (bucket: {bucket}, prefix: {}, endpoint: {}, region: {}, profile: {}, connections: {connections})",
                format_optional(prefix.as_deref()),
                format_optional(endpoint.as_deref()),
                format_optional(region.as_deref()),
                format_optional(profile.as_deref()),
            )),
        },
        None => Ok(String::from("None")),
    }
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();
    let args = Args::parse();

    let options = load_options(&args.common)?;

    // base data device
    let base_dev = build_block_device(&options.path, &options, true)?;
    let data_size = base_dev.sector_count() * SECTOR_SIZE as u64;

    let source_info = format_source_info(&options)?;

    // metadata device
    let metadata_path = options
        .metadata_path
        .as_ref()
        .ok_or_else(|| Error::InvalidParameter {
            description: "metadata_path is none".to_string(),
        })?;
    let metadata_dev = build_block_device(metadata_path, &options, true)?;
    let metadata = UbiMetadata::load_from_bdev(metadata_dev.as_ref())?;

    let stripe_size = metadata.stripe_size();
    let metadata_version = format!(
        "{}.{}",
        metadata.version_major_u16(),
        metadata.version_minor_u16()
    );
    let fetched: Vec<usize> = metadata
        .stripe_headers
        .iter()
        .enumerate()
        .filter_map(|(i, h)| (h & metadata_flags::FETCHED != 0).then_some(i))
        .collect();
    let written: Vec<usize> = metadata
        .stripe_headers
        .iter()
        .enumerate()
        .filter_map(|(i, h)| (h & metadata_flags::WRITTEN != 0).then_some(i))
        .collect();
    let has_source: Vec<usize> = metadata
        .stripe_headers
        .iter()
        .enumerate()
        .filter_map(|(i, h)| (h & metadata_flags::HAS_SOURCE != 0).then_some(i))
        .collect();

    println!("data file: {} ({} bytes)", options.path, data_size);
    println!("source: {source_info}");
    println!("metadata version: {metadata_version}");
    println!("stripe size: {stripe_size} bytes");
    println!("fetched stripes: {}", format_list(&fetched));
    println!("written stripes: {}", format_list(&written));
    println!("has-source stripes: {}", format_list(&has_source));

    Ok(())
}
