use clap::Parser;
use log::error;
use ubiblk::backends::init_metadata;
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::Result;

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

    /// Stripe sector count shift. Defaults to device.stripe_sector_count_shift,
    /// or 11 when neither is set.
    #[arg(short = 's', long = "stripe-sector-count-shift")]
    stripe_sector_count_shift: Option<u8>,
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

    let mut device = config.device.clone();
    match (
        args.stripe_sector_count_shift,
        device.stripe_sector_count_shift,
    ) {
        (Some(given), Some(configured)) if given != configured => {
            return Err(ubiblk::ubiblk_error!(InvalidParameter {
                description: format!(
                    "stripe-sector-count-shift {given} conflicts with \
                     device.stripe_sector_count_shift {configured}"
                ),
            }));
        }
        (Some(given), _) => device.stripe_sector_count_shift = Some(given),
        _ => {}
    }
    let stripe_sector_count_shift = device.stripe_sector_count_shift()?;

    init_metadata(&config, stripe_sector_count_shift)
}
