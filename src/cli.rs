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

    /// Allow reading the key encryption key from a regular file.
    #[arg(
        long = "allow-regular-file-as-kek",
        default_value_t = false,
        requires = "kek"
    )]
    pub allow_regular_file_as_kek: bool,
}

pub fn load_config(common: &CommonArgs) -> Result<DeviceConfig> {
    let (config, _kek) = load_config_and_kek(common)?;
    Ok(config)
}

pub fn load_config_and_kek(common: &CommonArgs) -> Result<(DeviceConfig, KeyEncryptionCipher)> {
    let kek = KeyEncryptionCipher::load(common.kek.as_ref(), common.allow_regular_file_as_kek)?;
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
    fn load_config_reads_config() {
        let config_file = write_temp_file(
            r#"
path: /dev/null
socket: /tmp/ubiblk.sock
"#,
        );

        let args = CommonArgs {
            config: config_file.path().to_path_buf(),
            kek: None,
            allow_regular_file_as_kek: false,
        };

        let config = load_config(&args).expect("load config");

        assert_eq!(config.path, "/dev/null");
        assert_eq!(config.socket.as_deref(), Some("/tmp/ubiblk.sock"));
    }

    #[test]
    fn load_config_and_kek_allows_regular_file_kek() {
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
        let args = CommonArgs {
            config: config_file.path().to_path_buf(),
            kek: Some(kek_file.path().to_path_buf()),
            allow_regular_file_as_kek: true,
        };

        let (_config, kek) = load_config_and_kek(&args).expect("load config and kek");

        assert_eq!(kek.method, CipherMethod::None);
    }
}
