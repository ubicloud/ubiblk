use std::{net::TcpListener, sync::Arc, thread};

use clap::Parser;
use log::{error, info};

use ubiblk::{
    cli::CommonArgs,
    stripe_server::{
        parse_psk_credentials, prepare_stripe_server, wrap_psk_server_stream, DynStream,
    },
    vhost_backend::Options,
    Error, KeyEncryptionCipher, Result,
};

#[derive(Parser)]
#[command(
    name = "remote-stripe-server",
    about = "Stripe server for remote block device access over TCP."
)]
struct Args {
    #[command(flatten)]
    common: CommonArgs,

    /// Address to listen on, e.g. 127.0.0.1:4555.
    #[arg(long, default_value = "127.0.0.1:4555")]
    bind: String,

    /// PSK identity (required if --psk-secret is set).
    #[arg(long = "psk-identity")]
    psk_identity: Option<String>,

    /// Base64-encoded PSK secret encrypted with the KEK (required if --psk-identity is set).
    #[arg(long = "psk-secret")]
    psk_secret: Option<String>,
}

fn main() -> Result<()> {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    run(args)
}

fn run(args: Args) -> Result<()> {
    let Args {
        common: CommonArgs {
            config,
            kek,
            unlink_kek,
        },
        bind,
        psk_identity,
        psk_secret,
    } = args;

    let options = Options::load_from_file(&config)?;
    if options.has_stripe_source() {
        return Err(Error::InvalidParameter {
            description:
                "config must not specify a stripe source when used with remote-stripe-server"
                    .to_string(),
        });
    }

    let kek = KeyEncryptionCipher::load(kek.as_ref(), unlink_kek)?;
    let stripe_server = prepare_stripe_server(&options, kek.clone())?;
    let psk = parse_psk_credentials(psk_identity, psk_secret, &kek)?;

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
