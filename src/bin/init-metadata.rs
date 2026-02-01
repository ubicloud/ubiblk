use clap::Parser;
use log::error;
use ubiblk::backends::init_metadata;
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::Result;

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
    #[command(flatten)]
    common: CommonArgs,

    /// Stripe sector count shift.
    #[arg(short = 's', long = "stripe-sector-count-shift", default_value_t = 11)]
    stripe_sector_count_shift: u8,
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

    let stripe_sector_count_shift = args.stripe_sector_count_shift;

    if !(STRIPE_SECTOR_COUNT_SHIFT_MIN..=STRIPE_SECTOR_COUNT_SHIFT_MAX)
        .contains(&stripe_sector_count_shift)
    {
        return Err(ubiblk::ubiblk_error!(InvalidParameter {
            description: format!(
                "stripe-sector-count-shift must be between {STRIPE_SECTOR_COUNT_SHIFT_MIN} and {STRIPE_SECTOR_COUNT_SHIFT_MAX}."
            ),
        }));
    }

    init_metadata(&config, stripe_sector_count_shift)
}
