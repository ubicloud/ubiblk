use clap::Parser;
use ubiblk::cli::{load_common_args, CommonArgs};
use ubiblk::{vhost_backend::*, Result};

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
    let common = load_common_args(&args.common)?;

    block_backend_loop(&common.config, common.kek, common.archive_kek)
}
