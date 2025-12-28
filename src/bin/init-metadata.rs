use clap::Parser;
use std::path::PathBuf;
use ubiblk::utils::load_kek;
use ubiblk::vhost_backend::*;
use ubiblk::{Error, Result};

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

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config_path = &args.config;
    let options = Options::load_from_file(&PathBuf::from(config_path))?;

    let stripe_sector_count_shift = args.stripe_sector_count_shift;

    if !(STRIPE_SECTOR_COUNT_SHIFT_MIN..=STRIPE_SECTOR_COUNT_SHIFT_MAX)
        .contains(&stripe_sector_count_shift)
    {
        return Err(Error::InvalidParameter {
            description: format!(
                "stripe-sector-count-shift must be between {STRIPE_SECTOR_COUNT_SHIFT_MIN} and {STRIPE_SECTOR_COUNT_SHIFT_MAX}."
            ),
        });
    }

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = load_kek(kek_path.as_ref(), args.unlink_kek)?;

    init_metadata(&options, kek, stripe_sector_count_shift)
}
