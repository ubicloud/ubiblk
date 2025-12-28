use clap::Parser;
use log::error;
use std::{path::PathBuf, process};
use ubiblk::utils::load_kek;
use ubiblk::vhost_backend::*;

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

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    let config_path = &args.config;
    let options = match Options::load_from_file(&PathBuf::from(config_path)) {
        Ok(cfg) => cfg,
        Err(e) => {
            error!("Failed to load configuration: {e}");
            process::exit(1);
        }
    };

    if options.num_queues > 1 && options.io_debug_path.is_some() {
        error!("Error: I/O debug path is not supported with multiple queues.");
        process::exit(1);
    }

    let kek_path = args.kek.as_ref().map(PathBuf::from);
    let kek = load_kek(kek_path.as_ref(), args.unlink_kek).unwrap_or_else(|e| {
        if let Some(path) = kek_path.as_ref() {
            error!("Error loading KEK file {}: {e}", path.display());
        } else {
            error!("Error loading KEK: {e}");
        }
        process::exit(1);
    });

    if let Err(e) = block_backend_loop(&options, kek) {
        error!("Backend exited with error: {e}");
        process::exit(1);
    }
}
