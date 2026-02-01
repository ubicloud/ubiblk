use clap::Parser;
use log::error;
use ubiblk::backends::ublk::ublk_backend_loop;
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::Result;

#[derive(Parser)]
#[command(
    name = "ublk backend",
    version,
    author,
    about = "Launch an ublk backend using a config file."
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

    let config = load_config(&args.common)?;
    ublk_backend_loop(&config)
}
