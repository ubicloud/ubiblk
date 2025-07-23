use clap::{Arg, Command};
use log::error;
use serde_yaml;
use std::fs::File;
use std::process;
use ubiblk::vhost_backend::*;

const STRIPE_SECTOR_COUNT_SHIFT_MIN: u8 = 6;
const STRIPE_SECTOR_COUNT_SHIFT_MAX: u8 = 16;

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let cmd_arguments = Command::new("vhost-user-blk metadata init")
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .about("Initialize metadata for a vhost-user-blk backend.")
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
        .arg(
            Arg::new("unlink-kek")
                .short('u')
                .long("unlink-kek")
                .action(clap::ArgAction::SetTrue)
                .help("Unlink the key encryption key file after use."),
        )
        .arg(
            Arg::new("stripe-sector-count-shift")
                .short('s')
                .long("stripe-sector-count-shift")
                .value_parser(clap::value_parser!(u8))
                .default_value("11")
                .help("Stripe sector count shift."),
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

    let mut kek = KeyEncryptionCipher::default();

    let stripe_sector_count_shift = cmd_arguments
        .get_one::<u8>("stripe-sector-count-shift")
        .unwrap();

    if *stripe_sector_count_shift > STRIPE_SECTOR_COUNT_SHIFT_MAX
        || *stripe_sector_count_shift < STRIPE_SECTOR_COUNT_SHIFT_MIN
    {
        error!(
            "stripe-sector-count-shift must be between {} and {}.",
            STRIPE_SECTOR_COUNT_SHIFT_MIN, STRIPE_SECTOR_COUNT_SHIFT_MAX
        );
        process::exit(1);
    }

    if let Some(kek_path) = cmd_arguments.get_one::<String>("kek") {
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

        if let Some(unlink_kek) = cmd_arguments.get_one::<bool>("unlink-kek") {
            if *unlink_kek {
                if let Err(e) = std::fs::remove_file(kek_path) {
                    error!("Error unlinking KEK file {}: {}", kek_path, e);
                    process::exit(1);
                }
            }
        }
    }

    if let Err(e) = init_metadata(&options, kek, *stripe_sector_count_shift) {
        error!("Error initializing metadata: {}", e);
        process::exit(1);
    }
}
