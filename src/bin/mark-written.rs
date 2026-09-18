use clap::Parser;
use log::error;
use ubiblk::backends::{ensure_no_backend_holds_device, mark_written_from_data};
use ubiblk::cli::{load_config, CommonArgs};
use ubiblk::Result;

#[derive(Parser)]
#[command(
    name = "mark-written",
    version,
    author,
    about = "Mark stripes containing data as written.",
    long_about = "Set the written flag for every stripe containing a nonzero byte, \
                  making a device populated with track_written disabled archivable. \
                  All-zero and source-backed stripes are left untouched. The device \
                  must not be served by a backend while this runs."
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,

    /// Acknowledge that no backend is serving the device (required when no
    /// rpc_socket is configured).
    #[arg(long = "force", default_value_t = false)]
    force: bool,
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

    ensure_no_backend_holds_device(&config, args.force)?;

    let summary = mark_written_from_data(&config)?;
    println!(
        "Marked {} of {} scanned stripes as written.",
        summary.marked, summary.scanned
    );

    Ok(())
}
