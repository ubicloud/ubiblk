use std::{net::TcpListener, sync::Arc, thread};

use clap::Parser;
use log::{error, info, warn};

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

    /// Config YAML file containing listening address and PSK details.
    #[arg(long = "listen-config", value_name = "CONFIG_YAML")]
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

    // TODO: Fix listen config loading.
    let listen_config = v2::Config::load(&listen_config_path)?;
    let remote = match listen_config.stripe_source.as_ref() {
        Some(v2::stripe_source::StripeSourceConfig::Remote { address, psk, .. }) => (address, psk),
        _ => {
            return Err(ubiblk::ubiblk_error!(InvalidParameter {
                description: "listen config must define stripe_source.type = 'remote'".to_string(),
            }))
        }
    };
    let stripe_server = prepare_stripe_server(&config)?;
    let psk = remote
        .1
        .as_ref()
        .map(|psk| {
            let secret = listen_config
                .secrets
                .get(psk.psk_secret.id())
                .ok_or_else(|| {
                    ubiblk::ubiblk_error!(InvalidParameter {
                        description: format!("PSK secret '{}' not found", psk.psk_secret.id()),
                    })
                })?
                .as_bytes()
                .to_vec();
            PskCredentials::new(psk.psk_identity.clone(), secret)
        })
        .transpose()?;

    if psk.is_none() {
        warn!("No PSK credentials configured — stripe server running WITHOUT transport encryption. All data will be transmitted in plaintext.");
    }

    let listener = TcpListener::bind(remote.0)?;
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
