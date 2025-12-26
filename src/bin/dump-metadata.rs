use clap::Parser;
use log::error;
use std::{fs::File, path::PathBuf, process};
use ubiblk::block_device::{self, load_metadata, BlockDevice};
use ubiblk::utils::load_kek;
use ubiblk::vhost_backend::{Options, SECTOR_SIZE};
use ubiblk::{KeyEncryptionCipher, Result};

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

fn main() {
    env_logger::builder().format_timestamp(None).init();
    let args = Args::parse();

    let config_file = match File::open(&args.config) {
        Ok(f) => f,
        Err(e) => {
            error!("Error opening config file {}: {}", args.config, e);
            process::exit(1);
        }
    };

    let options: Options = match serde_yaml::from_reader(config_file) {
        Ok(cfg) => cfg,
        Err(e) => {
            error!("Error parsing config file {}: {}", args.config, e);
            process::exit(1);
        }
    };

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = load_kek(kek_path.as_ref(), false).unwrap_or_else(|e| {
        if let Some(path) = kek_path.as_ref() {
            error!("Error loading KEK file {}: {e}", path.display());
        } else {
            error!("Error loading KEK: {e}");
        }
        process::exit(1);
    });

    // base data device
    let base_dev = match build_block_device(&options.path, &options, true, kek.clone()) {
        Ok(dev) => dev,
        Err(e) => {
            error!("Failed to open data file {}: {e}", options.path);
            process::exit(1);
        }
    };
    let data_size = base_dev.sector_count() * SECTOR_SIZE as u64;

    // image device if provided
    let (image_path_display, image_size) = if let Some(ref image_path) = options.image_path {
        match block_device::UringBlockDevice::new(
            PathBuf::from(image_path),
            options.queue_size,
            true,
            true,
            options.write_through,
        ) {
            Ok(dev) => (image_path.clone(), dev.sector_count() * SECTOR_SIZE as u64),
            Err(e) => {
                error!("Failed to open image file {image_path}: {e}");
                process::exit(1);
            }
        }
    } else {
        (String::from("None"), 0)
    };

    // metadata device
    let metadata_path = match &options.metadata_path {
        Some(p) => p,
        None => {
            error!("metadata_path is none");
            process::exit(1);
        }
    };
    let metadata_dev = match build_block_device(metadata_path, &options, true, kek.clone()) {
        Ok(dev) => dev,
        Err(e) => {
            error!("Failed to open metadata file {metadata_path}: {e}");
            process::exit(1);
        }
    };
    let mut ch = match metadata_dev.create_channel() {
        Ok(ch) => ch,
        Err(e) => {
            error!("Failed to create metadata channel: {e}");
            process::exit(1);
        }
    };
    let metadata = match load_metadata(&mut ch, metadata_dev.sector_count()) {
        Ok(md) => md,
        Err(e) => {
            error!("Failed to load metadata: {e}");
            process::exit(1);
        }
    };

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
}
