use clap::Parser;
use log::error;
use ubiblk::backends::vhost::block_backend_loop;
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::utils::security::disable_core_dumps;
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

fn main() {
    env_logger::builder().format_timestamp(None).init();
    disable_core_dumps();

    if let Err(err) = run() {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = Args::parse();

    let config = load_config(&args.common)?;
    block_backend_loop(&config)
}
