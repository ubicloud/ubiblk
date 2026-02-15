use std::{net::TcpListener, sync::Arc, thread};

use clap::Parser;
use log::{error, info};

use ubiblk::{
    cli::{load_config, CommonArgs},
    config::v2,
    stripe_server::{prepare_stripe_server, wrap_psk_server_stream, DynStream, PskCredentials},
    utils::security::disable_core_dumps,
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

    /// Config TOML file containing listening address and PSK details.
    #[arg(long = "listen-config", value_name = "CONFIG_TOML")]
    listen_config_path: std::path::PathBuf,
}

fn main() {
    env_logger::builder().format_timestamp(None).init();
    disable_core_dumps();

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

    let config = load_config(&common)?;

    let listen_config = v2::RemoteStripeServerConfig::load(&listen_config_path)?;
    let stripe_server = prepare_stripe_server(&config)?;
    let psk = listen_config
        .server
        .psk
        .as_ref()
        .map(|psk| {
            let secret = listen_config
                .secrets
                .get(psk.secret.id())
                .ok_or_else(|| {
                    ubiblk::ubiblk_error!(InvalidParameter {
                        description: format!("PSK secret '{}' not found", psk.secret.id()),
                    })
                })?
                .as_bytes()
                .to_vec();
            PskCredentials::new(psk.identity.clone(), secret)
        })
        .transpose()?;

    let listener = TcpListener::bind(&listen_config.server.address)?;
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
