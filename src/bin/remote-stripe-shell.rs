use clap::Parser;
use rustyline::{error::ReadlineError, DefaultEditor};
use std::{collections::HashMap, io, path::PathBuf};

use ubiblk::{
    block_device::STRIPE_WRITTEN_MASK,
    stripe_server::{connect_to_stripe_server, PskCredentials, RemoteStripeProvider},
    vhost_backend::{Options, SECTOR_SIZE},
    KeyEncryptionCipher, Result, UbiblkError,
};

#[derive(Parser)]
#[command(
    name = "remote-stripe-shell",
    about = "Interactive shell for remote-stripe-server"
)]
struct Args {
    /// Address of the remote-stripe-server, e.g. 127.0.0.1:4555
    #[arg(value_name = "IP:PORT")]
    server: String,

    /// Path to the configuration YAML file used to describe the block device.
    #[arg(short = 'f', long = "config")]
    config: Option<PathBuf>,

    /// Path to the key encryption key file.
    #[arg(short = 'k', long = "kek")]
    kek: Option<PathBuf>,

    /// Unlink the key encryption key file after use.
    #[arg(short = 'u', long = "unlink-kek", default_value_t = false)]
    unlink_kek: bool,
}

fn main() -> Result<()> {
    let Args {
        server,
        config,
        kek,
        unlink_kek,
    } = Args::parse();

    let kek = KeyEncryptionCipher::load(kek.as_ref(), unlink_kek)?;
    let psk = match config {
        Some(config) => {
            let options = Options::load_from_file(&config)?;
            PskCredentials::from_options(&options, &kek)?
        }
        None => None,
    };

    let mut client = connect_to_stripe_server(&server, psk.as_ref())?;
    let metadata = client
        .metadata
        .as_ref()
        .expect("metadata should be fetched")
        .clone();
    let stripe_len_bytes = metadata.stripe_size() as usize * SECTOR_SIZE;

    let mut rl = DefaultEditor::new().map_err(readline_err_to_io)?;
    let mut fetched_stripes: HashMap<u64, Vec<u8>> = HashMap::new();

    loop {
        let line = match rl.readline("> ") {
            Ok(line) => line,
            Err(ReadlineError::Interrupted) => {
                println!("^C");
                continue;
            }
            Err(ReadlineError::Eof) => break,
            Err(err) => {
                return Err(UbiblkError::IoError {
                    source: readline_err_to_io(err),
                })
            }
        };

        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        if let Err(err) = rl.add_history_entry(trimmed) {
            eprintln!("Failed to store command in history: {err}");
        }

        let mut parts = trimmed.split_whitespace();
        let cmd = parts.next().unwrap();

        match cmd {
            "exit" | "quit" => break,
            "help" => {
                print_help();
            }
            "stripe_header" => match parse::<usize>(parts.next()) {
                Ok(stripe_idx) => {
                    if stripe_idx >= metadata.stripe_headers.len() {
                        println!("INVALID_STRIPE");
                        continue;
                    }
                    let header = metadata.stripe_headers[stripe_idx];
                    let status = if header & STRIPE_WRITTEN_MASK != 0 {
                        "WRITTEN"
                    } else {
                        "NOT_WRITTEN"
                    };
                    println!("0x{header:02x} {status}");
                }
                Err(err) => println!("{err}"),
            },
            "fetch_stripe" => match parse::<u64>(parts.next()) {
                Ok(stripe_idx) => {
                    if stripe_idx as usize >= metadata.stripe_headers.len() {
                        println!("INVALID_STRIPE");
                        continue;
                    }

                    match client.fetch_stripe(stripe_idx) {
                        Ok(data) => {
                            fetched_stripes.insert(stripe_idx, data);
                            println!("FETCHED");
                        }
                        Err(err) => println!("{err}"),
                    }
                }
                Err(err) => println!("{err}"),
            },
            "dump_stripe" => match (
                parse::<u64>(parts.next()),
                parse::<usize>(parts.next()),
                parse::<usize>(parts.next()),
            ) {
                (Ok(stripe_idx), Ok(offset), Ok(len)) => {
                    let stripe_idx_usize = match usize::try_from(stripe_idx) {
                        Ok(value) => value,
                        Err(_) => {
                            println!("INVALID_STRIPE");
                            continue;
                        }
                    };

                    if stripe_idx_usize >= metadata.stripe_headers.len() {
                        println!("INVALID_STRIPE");
                        continue;
                    }

                    let header = metadata.stripe_headers[stripe_idx_usize];
                    if header & STRIPE_WRITTEN_MASK == 0 {
                        if offset.saturating_add(len) > stripe_len_bytes {
                            println!("INVALID_RANGE");
                            continue;
                        }
                        let zeros = vec![0u8; len];
                        let hex = hex::encode(zeros);
                        println!("{hex}");
                        continue;
                    }

                    if let Some(data) = fetched_stripes.get(&stripe_idx) {
                        if offset.saturating_add(len) > data.len() {
                            println!("INVALID_RANGE");
                            continue;
                        }
                        let end = offset + len;
                        let hex = hex::encode(&data[offset..end]);
                        println!("{hex}");
                    } else {
                        println!("NOT_FETCHED_FROM_REMOTE");
                    }
                }
                (Err(err), _, _) | (_, Err(err), _) | (_, _, Err(err)) => println!("{err}"),
            },
            other => {
                println!("UNKNOWN_COMMAND: {other}");
                println!("Type 'help' to see the list of available commands.");
            }
        }
    }

    Ok(())
}

fn print_help() {
    println!("Available commands:");
    println!("  help");
    println!("      Show this message.");
    println!("  exit | quit");
    println!("      Exit the shell.");
    println!("  stripe_header <stripe_index>");
    println!("      Print the raw header byte and status for the given stripe.");
    println!("  fetch_stripe <stripe_index>");
    println!("      Fetch the stripe from the remote server and cache it locally.");
    println!("  dump_stripe <stripe_index> <offset> <length>");
    println!("      Dump hexadecimal data from a previously fetched stripe.");
}

fn readline_err_to_io(err: ReadlineError) -> io::Error {
    match err {
        ReadlineError::Io(io_err) => io_err,
        other => io::Error::other(other),
    }
}

fn parse<T: std::str::FromStr>(input: Option<&str>) -> Result<T> {
    input
        .ok_or_else(|| UbiblkError::InvalidParameter {
            description: "MISSING_ARGUMENT".to_string(),
        })
        .and_then(|value| {
            value
                .parse::<T>()
                .map_err(|_| UbiblkError::InvalidParameter {
                    description: format!("INVALID_NUMBER: {value}"),
                })
        })
}
