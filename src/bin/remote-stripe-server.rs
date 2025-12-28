use std::{net::TcpListener, path::PathBuf, sync::Arc, thread};

use clap::Parser;
use log::{error, info};

use ubiblk::{
    stripe_server::{prepare_stripe_server, wrap_psk_server_stream, DynStream, PskCredentials},
    utils::load_kek,
    vhost_backend::Options,
    Error, Result,
};

#[derive(Parser)]
#[command(
    name = "remote-stripe-server",
    about = "Stripe server for remote block device access over TCP."
)]
struct Args {
    /// Address to listen on, e.g. 127.0.0.1:4555.
    #[arg(long, default_value = "127.0.0.1:4555")]
    bind: String,

    /// Path to the configuration YAML file used to describe the block device.
    #[arg(short = 'f', long = "config")]
    config: PathBuf,

    /// Path to the key encryption key file.
    #[arg(short = 'k', long = "kek")]
    kek: Option<PathBuf>,

    /// Unlink the key encryption key file after use.
    #[arg(short = 'u', long = "unlink-kek", default_value_t = false)]
    unlink_kek: bool,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    run(args)
}

fn run(args: Args) -> Result<()> {
    let Args {
        bind,
        config,
        kek,
        unlink_kek,
    } = args;

    let options = Options::load_from_file(&config)?;
    if options.image_path.is_some() {
        return Err(Error::InvalidParameter {
            description: "config must not specify image_path when used with remote-stripe-server"
                .to_string(),
        });
    }

    let kek = load_kek(kek.as_ref(), unlink_kek)?;
    let stripe_server = prepare_stripe_server(&options, kek.clone())?;
    let psk = PskCredentials::from_options(&options, &kek)?;

    let listener = TcpListener::bind(&bind)?;
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
