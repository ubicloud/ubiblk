use std::path::PathBuf;

use clap::Parser;
use log::error;

use ubiblk::{config::v2::ExportArchiveConfig, export_archive::export_archive, Result};

#[derive(Parser)]
#[command(
    name = "export-archive",
    version,
    author,
    about = "Export an archive as a raw disk image."
)]
struct Args {
    /// Path to the export archive config TOML file.
    #[arg(long = "source", value_name = "FILE")]
    source: PathBuf,

    /// Path to the output raw disk image.
    #[arg(long = "target", value_name = "PATH")]
    target: PathBuf,
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    if let Err(err) = run() {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = Args::parse();
    let config = ExportArchiveConfig::load(&args.source)?;
    export_archive(&config, &args.target)
}
