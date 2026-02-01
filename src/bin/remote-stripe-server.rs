use std::{net::TcpListener, sync::Arc, thread};

use clap::Parser;
use log::{error, info};

use ubiblk::{
    cli::{load_config_and_kek, CommonArgs},
    config::RemoteStripeSourceConfig,
    stripe_server::{prepare_stripe_server, wrap_psk_server_stream, DynStream, PskCredentials},
    Result,
};

#[derive(Parser)]
#[command(
    name = "remote-stripe-server",
    about = "Stripe server for remote block device access over TCP."
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,

    /// Config YAML file containing listening address and PSK details.
    #[arg(long = "listen-config", value_name = "CONFIG_YAML")]
    listen_config_path: std::path::PathBuf,
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    if let Err(err) = run(args) {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run(args: Args) -> Result<()> {
    let Args {
        common,
        listen_config_path,
    } = args;

    let (config, kek) = load_config_and_kek(&common)?;

    let listen_config =
        RemoteStripeSourceConfig::load_from_file_with_kek(&listen_config_path, &kek)?;
    let stripe_server = prepare_stripe_server(&config)?;
    let psk = listen_config
        .psk_identity
        .zip(listen_config.psk_secret)
        .map(|(identity, secret)| PskCredentials::new(identity, secret))
        .transpose()?;

    let listener = TcpListener::bind(&listen_config.address)?;
    info!("listening on {}", listener.local_addr()?);

    loop {
        let (stream, addr) = listener.accept()?;
        info!("accepted connection from {addr}");
        let stripe_server = Arc::clone(&stripe_server);
        let psk = psk.clone();
        thread::spawn(move || {
            let result = (|| -> Result<()> {
                let stream: DynStream = Box::new(stream);
                let stream = if let Some(ref creds) = psk {
                    wrap_psk_server_stream(stream, creds)?
                } else {
                    stream
                };
                let mut session = stripe_server.start_session(stream)?;
                session.handle_requests();
                Ok(())
            })();
            match result {
                Ok(()) => info!("client {addr} disconnected"),
                Err(err) => error!("client {addr}: {err}"),
            }
        });
    }
}
