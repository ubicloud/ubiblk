use clap::Parser;
use log::error;
use serde_yaml;
use std::fs::File;
use std::process;
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

    let file = match File::open(config_path) {
        Ok(file) => file,
        Err(e) => {
            error!("Error opening config file {}: {}", config_path, e);
            process::exit(1);
        }
    };

    let options: Options = match serde_yaml::from_reader(file) {
        Ok(cfg) => cfg,
        Err(e) => {
            error!("Error parsing config file {}: {}", config_path, e);
            process::exit(1);
        }
    };

    if options.num_queues > 1 && options.io_debug_path.is_some() {
        error!("Error: I/O debug path is not supported with multiple queues.");
        process::exit(1);
    }

    let mut kek = KeyEncryptionCipher::default();

    if let Some(kek_path) = &args.kek {
        let file = match File::open(kek_path) {
            Ok(file) => file,
            Err(e) => {
                error!("Error opening KEK file {}: {}", kek_path, e);
                process::exit(1);
            }
        };

        kek = match serde_yaml::from_reader(file) {
            Ok(kek) => kek,
            Err(e) => {
                error!("Error parsing KEK file {}: {}", kek_path, e);
                process::exit(1);
            }
        };

        if args.unlink_kek {
            if let Err(e) = std::fs::remove_file(kek_path) {
                error!("Error unlinking KEK file {}: {}", kek_path, e);
                process::exit(1);
            }
        }
    }

    block_backend_loop(&options, kek);
}
