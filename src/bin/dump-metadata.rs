use clap::Parser;
use log::error;
use ubiblk::backends::{build_block_device, SECTOR_SIZE};
use ubiblk::block_device::{self, metadata_flags, BlockDevice, UbiMetadata};
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::config::v2;
use ubiblk::Result;

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

fn format_source_info(config: &v2::Config) -> Result<String> {
    match config.stripe_source.as_ref() {
        Some(v2::stripe_source::StripeSourceConfig::Raw { image_path, .. }) => {
            let dev = block_device::UringBlockDevice::new(
                image_path.clone(),
                config.tuning.queue_size,
                true,
                true,
                config.tuning.write_through,
            )?;
            let image_size = dev.sector_count() * SECTOR_SIZE as u64;
            Ok(format!(
                "raw (path: {}, size: {} bytes)",
                image_path.display(),
                image_size
            ))
        }
        Some(v2::stripe_source::StripeSourceConfig::Remote(config)) => Ok(format!(
            "remote (address: {}, psk_identity: {})",
            config.address,
            config
                .psk
                .as_ref()
                .map(|psk| psk.identity.as_str())
                .unwrap_or("None")
        )),
        Some(v2::stripe_source::StripeSourceConfig::Archive(config)) => match config {
            v2::stripe_source::ArchiveStorageConfig::Filesystem { path, .. } => {
                Ok(format!("archive filesystem (path: {})", path.display()))
            }
            v2::stripe_source::ArchiveStorageConfig::S3 {
                bucket,
                prefix,
                region,
                ..
            } => Ok(format!(
                "archive s3 (bucket: {bucket}, prefix: {}, region: {})",
                prefix.as_deref().unwrap_or("None"),
                region.as_deref().unwrap_or("None")
            )),
        },
        None => Ok(String::from("None")),
    }
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

    // base data device
    let base_dev = build_block_device(&config.device.data_path, &config, true)?;
    let data_size = base_dev.sector_count() * SECTOR_SIZE as u64;

    let source_info = format_source_info(&config)?;

    // metadata device
    let metadata_path = config.device.metadata_path.as_ref().ok_or_else(|| {
        ubiblk::ubiblk_error!(InvalidParameter {
            description: "metadata_path is none".to_string(),
        })
    })?;
    let metadata_dev = build_block_device(metadata_path, &config, true)?;
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

    println!(
        "data file: {} ({} bytes)",
        config.device.data_path.display(),
        data_size
    );
    println!("source: {source_info}");
    println!("metadata version: {metadata_version}");
    println!("stripe size: {stripe_size} bytes");
    println!("fetched stripes: {}", format_list(&fetched));
    println!("written stripes: {}", format_list(&written));
    println!("has-source stripes: {}", format_list(&has_source));

    Ok(())
}
