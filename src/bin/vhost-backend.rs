use clap::Parser;
use ubiblk::cli::CommonArgs;
use ubiblk::{vhost_backend::*, KeyEncryptionCipher, Result};

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

    let options = Options::load_from_file(&args.common.config)?;

    let kek = KeyEncryptionCipher::load(args.common.kek.as_ref(), args.common.unlink_kek)?;
    block_backend_loop(&options, kek)
}
