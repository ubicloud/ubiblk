use std::path::PathBuf;

use clap::Args;

use crate::{vhost_backend::Options, KeyEncryptionCipher, Result};

#[derive(Args, Debug, Clone)]
/// Common command-line arguments used in most of the binaries.
pub struct CommonArgs {
    /// Path to the configuration YAML file.
    #[arg(short = 'f', long = "config")]
    pub config: PathBuf,

    /// Path to the key encryption key file.
    #[arg(short = 'k', long = "kek")]
    pub kek: Option<PathBuf>,

    /// Unlink the key encryption key file after use.
    #[arg(
        short = 'u',
        long = "unlink-kek",
        default_value_t = false,
        requires = "kek"
    )]
    pub unlink_kek: bool,
}

pub fn load_options(common: &CommonArgs) -> Result<Options> {
    let (options, _kek) = load_options_and_kek(common)?;
    Ok(options)
}

pub fn load_options_and_kek(common: &CommonArgs) -> Result<(Options, KeyEncryptionCipher)> {
    let kek = KeyEncryptionCipher::load(common.kek.as_ref(), common.unlink_kek)?;
    let options = Options::load_from_file_with_kek(&common.config, &kek)?;
    Ok((options, kek))
}
