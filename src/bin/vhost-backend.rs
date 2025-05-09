use clap::{Arg, Command};
use log::error;
use serde_yaml;
use std::fs::File;
use std::process;
use ubiblk::vhost_backend::*;

fn main() {
    let cmd_arguments = Command::new("vhost-user-blk backend")
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .about("Launch a vhost-user-blk backend using a config file.")
        .arg(
            Arg::new("config")
                .short('f')
                .long("config")
                .required(true)
                .help("Path to the configuration YAML file."),
        )
        .arg(
            Arg::new("kek")
                .short('k')
                .long("kek")
                .help("Path to the key encryption key file."),
        )
        .get_matches();

    let config_path = cmd_arguments.get_one::<String>("config").unwrap();

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

    let mut kek = KeyEncryptionCipher {
        method: CipherMethod::None,
        key: None,
        iv: None,
    };

    if let Some(kek_path) = cmd_arguments.get_one::<String>("kek") {
        let file = match File::open(kek_path) {
            Ok(file) => file,
            Err(e) => {
                error!("Error opening config file {}: {}", config_path, e);
                process::exit(1);
            }
        };

        kek = match serde_yaml::from_reader(file) {
            Ok(kek) => kek,
            Err(e) => {
                error!("Error parsing config file {}: {}", config_path, e);
                process::exit(1);
            }
        };
    }

    block_backend_loop(&options, kek);
}
