use clap::Parser;
use std::path::PathBuf;
use ubiblk::block_device::{self, load_metadata, BlockDevice};
use ubiblk::vhost_backend::{Options, SECTOR_SIZE};
use ubiblk::{Error, KeyEncryptionCipher, Result};

#[derive(Parser)]
#[command(
    name = "dump-metadata",
    version,
    author,
    about = "Dump metadata information"
)]
struct Args {
    /// Path to the configuration YAML file
    #[arg(short = 'f', long = "config")]
    config: String,

    /// Path to the key encryption key file
    #[arg(short = 'k', long = "kek")]
    kek: Option<String>,
}

fn build_block_device(
    path: &str,
    options: &Options,
    readonly: bool,
    kek: KeyEncryptionCipher,
) -> Result<Box<dyn BlockDevice>> {
    let mut device: Box<dyn BlockDevice> = block_device::UringBlockDevice::new(
        PathBuf::from(path),
        options.queue_size,
        readonly,
        true,
        options.write_through,
    )?;

    if let Some((key1, key2)) = &options.encryption_key {
        device = block_device::CryptBlockDevice::new(device, key1.clone(), key2.clone(), kek)?;
    }

    Ok(device)
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

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();
    let args = Args::parse();

    let options = Options::load_from_file(&PathBuf::from(&args.config))?;

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = KeyEncryptionCipher::load(kek_path.as_ref(), false)?;

    // base data device
    let base_dev = build_block_device(&options.path, &options, true, kek.clone())?;
    let data_size = base_dev.sector_count() * SECTOR_SIZE as u64;

    // image device if provided
    let (image_path_display, image_size) = if let Some(ref image_path) = options.image_path {
        let dev = block_device::UringBlockDevice::new(
            PathBuf::from(image_path),
            options.queue_size,
            true,
            true,
            options.write_through,
        )?;
        (image_path.clone(), dev.sector_count() * SECTOR_SIZE as u64)
    } else {
        (String::from("None"), 0)
    };

    // metadata device
    let metadata_path = options
        .metadata_path
        .as_ref()
        .ok_or_else(|| Error::InvalidParameter {
            description: "metadata_path is none".to_string(),
        })?;
    let metadata_dev = build_block_device(metadata_path, &options, true, kek.clone())?;
    let mut ch = metadata_dev.create_channel()?;
    let metadata = load_metadata(&mut ch, metadata_dev.sector_count())?;

    let stripe_size = metadata.stripe_size() * SECTOR_SIZE as u64;
    let fetched: Vec<usize> = metadata
        .stripe_headers
        .iter()
        .enumerate()
        .filter_map(|(i, h)| if h & 1 != 0 { Some(i) } else { None })
        .collect();
    let written: Vec<usize> = metadata
        .stripe_headers
        .iter()
        .enumerate()
        .filter_map(|(i, h)| if h & 2 != 0 { Some(i) } else { None })
        .collect();
    let no_source: Vec<usize> = metadata
        .stripe_headers
        .iter()
        .enumerate()
        .filter_map(|(i, h)| if h & 4 != 0 { Some(i) } else { None })
        .collect();

    println!("data file: {} ({} bytes)", options.path, data_size);
    println!("base image file: {image_path_display} ({image_size} bytes)");
    println!("stripe size: {stripe_size} bytes");
    println!("fetched stripes: {}", format_list(&fetched));
    println!("written stripes: {}", format_list(&written));
    println!("no-source-data stripes: {}", format_list(&no_source));

    Ok(())
}
