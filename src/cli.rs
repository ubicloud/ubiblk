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

    /// Path to the archive key encryption key file.
    #[arg(long = "archive-kek")]
    pub archive_kek: Option<PathBuf>,

    /// Unlink the key encryption key file after use.
    #[arg(
        short = 'u',
        long = "unlink-kek",
        default_value_t = false,
        requires = "kek"
    )]
    pub unlink_kek: bool,
}

pub struct LoadedCommonArgs {
    pub config: Options,
    pub kek: KeyEncryptionCipher,
    pub archive_kek: KeyEncryptionCipher,
}

pub fn load_common_args(args: &CommonArgs) -> Result<LoadedCommonArgs> {
    let config = Options::load_from_file(&args.config)?;
    let kek = KeyEncryptionCipher::load(args.kek.as_ref(), args.unlink_kek)?;
    let archive_kek = KeyEncryptionCipher::load(args.archive_kek.as_ref(), args.unlink_kek)?;

    Ok(LoadedCommonArgs {
        config,
        kek,
        archive_kek,
    })
}
