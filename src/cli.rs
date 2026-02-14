use std::path::PathBuf;

use clap::Args;

use crate::{config::v2, Result};

#[derive(Args, Debug, Clone)]
/// Common command-line arguments used in most of the binaries.
pub struct CommonArgs {
    /// Path to the configuration TOML file.
    #[arg(short = 'f', long = "config")]
    pub config: PathBuf,
}

pub fn load_config(common: &CommonArgs) -> Result<v2::Config> {
    let config = v2::Config::load(&common.config)?;
    Ok(config)
}
