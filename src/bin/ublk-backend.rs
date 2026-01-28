use clap::Parser;
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

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config = load_config(&args.common)?;
    ublk_backend_loop(&config)
}
