use clap::Parser;
use log::error;
use std::fs::File;
use std::process;
use ubiblk::vhost_backend::*;

const STRIPE_SECTOR_COUNT_SHIFT_MIN: u8 = 6;
const STRIPE_SECTOR_COUNT_SHIFT_MAX: u8 = 16;

#[derive(Parser)]
#[command(
    name = "vhost-user-blk metadata init",
    version,
    author,
    about = "Initialize metadata for a vhost-user-blk backend."
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

    /// Stripe sector count shift.
    #[arg(short = 's', long = "stripe-sector-count-shift", default_value_t = 11)]
    stripe_sector_count_shift: u8,
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config_path = &args.config;
    let file = match File::open(config_path) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening config file {config_path}: {e}");
            process::exit(1);
        }
    };

    let options: Options = match serde_yaml::from_reader(file) {
        Ok(cfg) => cfg,
        Err(e) => {
            error!("Error parsing config file {config_path}: {e}");
            process::exit(1);
        }
    };

    let mut kek = KeyEncryptionCipher::default();

    let stripe_sector_count_shift = args.stripe_sector_count_shift;

    if !(STRIPE_SECTOR_COUNT_SHIFT_MIN..=STRIPE_SECTOR_COUNT_SHIFT_MAX)
        .contains(&stripe_sector_count_shift)
    {
        error!(
            "stripe-sector-count-shift must be between {STRIPE_SECTOR_COUNT_SHIFT_MIN} and {STRIPE_SECTOR_COUNT_SHIFT_MAX}."
        );
        process::exit(1);
    }

    if let Some(kek_path) = &args.kek {
        let file = match File::open(kek_path) {
            Ok(file) => file,
            Err(e) => {
                error!("Error opening KEK file {kek_path}: {e}");
                process::exit(1);
            }
        };

        kek = match serde_yaml::from_reader(file) {
            Ok(kek) => kek,
            Err(e) => {
                error!("Error parsing KEK file {kek_path}: {e}");
                process::exit(1);
            }
        };

        if args.unlink_kek {
            if let Err(e) = std::fs::remove_file(kek_path) {
                error!("Error unlinking KEK file {kek_path}: {e}");
                process::exit(1);
            }
        }
    }

    if let Err(e) = init_metadata(&options, kek, stripe_sector_count_shift) {
        error!("Error initializing metadata: {e}");
        process::exit(1);
    }
}
