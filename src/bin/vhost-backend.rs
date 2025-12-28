use clap::Parser;
use std::path::PathBuf;
use ubiblk::utils::load_kek;
use ubiblk::vhost_backend::*;
use ubiblk::{Error, Result};

#[derive(Parser)]
#[command(
    name = "vhost-user-blk backend",
    version,
    author,
    about = "Launch a vhost-user-blk backend using a config file."
)]
struct Args {
    /// Path to the configuration YAML file.
    #[arg(short = 'f', long = "config")]
    config: String,

    /// Path to the key encryption key file.
    #[arg(short = 'k', long = "kek")]
    kek: Option<String>,

    /// Unlink the key encryption key file after use.
    #[arg(short = 'u', long = "unlink-kek", default_value_t = false)]
    unlink_kek: bool,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config_path = &args.config;
    let options = Options::load_from_file(&PathBuf::from(config_path))?;

    if options.num_queues > 1 && options.io_debug_path.is_some() {
        return Err(Error::InvalidParameter {
            description: "I/O debug path is not supported with multiple queues.".to_string(),
        });
    }

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = load_kek(kek_path.as_ref(), args.unlink_kek)?;

    block_backend_loop(&options, kek)
}
