use std::path::PathBuf;

use clap::Args;

use crate::{config::DeviceConfig, KeyEncryptionCipher, Result};

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

pub fn load_options(common: &CommonArgs) -> Result<DeviceConfig> {
    let (config, _kek) = load_options_and_kek(common)?;
    Ok(config)
}

pub fn load_options_and_kek(common: &CommonArgs) -> Result<(DeviceConfig, KeyEncryptionCipher)> {
    let kek = KeyEncryptionCipher::load(common.kek.as_ref(), common.unlink_kek)?;
    let config = DeviceConfig::load_from_file_with_kek(&common.config, &kek)?;
    Ok((config, kek))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypt::CipherMethod;
    use std::io::Write;
    use tempfile::NamedTempFile;

    fn write_temp_file(contents: &str) -> NamedTempFile {
        let mut file = NamedTempFile::new().expect("create temp file");
        file.write_all(contents.as_bytes())
            .expect("write temp file contents");
        file.flush().expect("flush temp file");
        file
    }

    #[test]
    fn load_options_reads_config() {
        let config_file = write_temp_file(
            r#"
path: /dev/null
socket: /tmp/ubiblk.sock
"#,
        );

        let args = CommonArgs {
            config: config_file.path().to_path_buf(),
            kek: None,
            unlink_kek: false,
        };

        let config = load_options(&args).expect("load options");

        assert_eq!(config.path, "/dev/null");
        assert_eq!(config.socket, "/tmp/ubiblk.sock");
    }

    #[test]
    fn load_options_and_kek_unlinks_kek() {
        let config_file = write_temp_file(
            r#"
path: /dev/null
socket: /tmp/ubiblk.sock
"#,
        );
        let kek_file = write_temp_file(
            r#"
method: none
"#,
        );
        let kek_path = kek_file.path().to_path_buf();

        let args = CommonArgs {
            config: config_file.path().to_path_buf(),
            kek: Some(kek_path.clone()),
            unlink_kek: true,
        };

        let (_config, kek) = load_options_and_kek(&args).expect("load options and kek");

        assert_eq!(kek.method, CipherMethod::None);
        assert!(
            !kek_path.exists(),
            "expected KEK file to be deleted after load"
        );
    }
}
