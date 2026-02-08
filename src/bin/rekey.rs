use clap::Parser;
use log::error;
use ubiblk::cli::{load_config_and_kek, CommonArgs};
use ubiblk::Result;

#[derive(Parser)]
#[command(
    name = "ubiblk-rekey",
    version,
    author,
    about = "Rotate data encryption keys for a ubiblk device (offline, exclusive access)"
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,
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
    let (config, kek) = load_config_and_kek(&args.common)?;

    ubiblk::rekey::run(&config, &args.common.config, &kek)
}
