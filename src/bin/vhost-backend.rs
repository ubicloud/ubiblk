use clap::Parser;
use std::path::PathBuf;
use ubiblk::{vhost_backend::*, KeyEncryptionCipher, Result};

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

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = KeyEncryptionCipher::load(kek_path.as_ref(), args.unlink_kek)?;

    block_backend_loop(&options, kek)
}
