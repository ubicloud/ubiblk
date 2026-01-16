use clap::Parser;
use ubiblk::cli::{load_options, CommonArgs};
use ubiblk::vhost_backend::*;
use ubiblk::Result;

#[derive(Parser)]
#[command(
    name = "vhost-user-blk backend",
    version,
    author,
    about = "Launch a vhost-user-blk backend using a config file."
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config = load_options(&args.common)?;
    block_backend_loop(&config)
}
