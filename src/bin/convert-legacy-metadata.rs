use std::path::PathBuf;

use clap::Parser;
use log::error;
use ubiblk::backends::convert_legacy_metadata;
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::Result;

#[derive(Parser)]
#[command(
    name = "convert-legacy-metadata",
    version,
    author,
    about = "Convert a v0.2.x volume's metadata to the current format."
)]
struct Args {
    /// The volume's new config; its metadata_path receives the converted metadata.
    #[command(flatten)]
    common: CommonArgs,

    /// Path to the volume's v0.2.x metadata file.
    #[arg(long = "legacy-metadata")]
    legacy_metadata: PathBuf,
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
    let config = load_config(&args.common)?;
    convert_legacy_metadata(&config, &args.legacy_metadata)
}
