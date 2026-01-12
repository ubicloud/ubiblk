use clap::Parser;
use ubiblk::cli::CommonArgs;
use ubiblk::{vhost_backend::*, KeyEncryptionCipher};
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
    #[command(flatten)]
    common: CommonArgs,

    /// Stripe sector count shift.
    #[arg(short = 's', long = "stripe-sector-count-shift", default_value_t = 11)]
    stripe_sector_count_shift: u8,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let options = Options::load_from_file(&args.common.config)?;

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

    let kek = KeyEncryptionCipher::load(args.common.kek.as_ref(), args.common.unlink_kek)?;

    init_metadata(&options, kek, stripe_sector_count_shift)
}
