use std::path::PathBuf;

use clap::Args;

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
