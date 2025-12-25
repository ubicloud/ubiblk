use std::{error::Error, fs::File, io, net::TcpListener, path::PathBuf, sync::Arc, thread};

use clap::Parser;
use log::{error, info};

use ubiblk::{
    stripe_server::{prepare_stripe_server, DynStream},
    vhost_backend::Options,
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
}

fn main() {
    env_logger::builder().format_timestamp(None).init();

    let args = Args::parse();

    if let Err(err) = run(args) {
        error!("{err}");
        std::process::exit(1);
    }
}

fn run(args: Args) -> Result<(), Box<dyn Error>> {
    let Args { bind, config } = args;

    let options = load_options(&config)?;
    if options.image_path.is_some() {
        return Err(
            "config must not specify image_path when used with remote-stripe-server".into(),
        );
    }

    let stripe_server = prepare_stripe_server(&options)?;

    let listener = TcpListener::bind(&bind)?;
    info!("listening on {}", listener.local_addr()?);

    loop {
        let (stream, addr) = listener.accept()?;
        info!("accepted connection from {addr}");
        let stripe_server = Arc::clone(&stripe_server);
        thread::spawn(move || {
            let result = (|| -> Result<(), Box<dyn Error>> {
                let stream: DynStream = Box::new(stream);
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

fn load_options(config: &PathBuf) -> Result<Options, Box<dyn Error>> {
    let file = File::open(config).map_err(|err| {
        Box::<dyn Error>::from(io::Error::new(
            err.kind(),
            format!("failed to open config file {}: {err}", config.display()),
        ))
    })?;

    serde_yaml::from_reader(file).map_err(|err| {
        Box::<dyn Error>::from(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("failed to parse config file {}: {err}", config.display()),
        ))
    })
}
