use serde::{Deserialize, Serialize};
use serde_with::{base64::Base64, serde_as};

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum CipherMethod {
    None,
    Aes256Gcm,
}

#[serde_as]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KeyEncryptionCipher {
    pub method: CipherMethod,

    #[serde_as(as = "Option<Base64>")]
    pub key: Option<Vec<u8>>,

    #[serde_as(as = "Option<Base64>")]
    pub iv: Option<Vec<u8>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Options {
    pub path: String,
    pub image_path: Option<String>,
    pub io_debug_path: Option<String>,
    pub socket: String,
    pub num_queues: usize,
    pub queue_size: usize,
    pub seg_size_max: u32,
    pub seg_count_max: u32,
    pub poll_queue_timeout_us: u128,
    pub encryption_key: Option<(String, String)>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_yaml::from_str;

    #[test]
    fn test_key_encryption_cipher() {
        let yaml = r#"
        method: aes256-gcm
        key: "uCvGiJ+tlAL0635kGhUaOhmgseSkoCK1HDhxJGgujSI="
        iv: "UEt+wI+Ldq1UgQ/P"
        "#;

        let cipher: KeyEncryptionCipher = from_str(yaml).unwrap();
        assert_eq!(cipher.method, CipherMethod::Aes256Gcm);
        assert_eq!(
            cipher.key,
            Some(vec![
                0xb8, 0x2b, 0xc6, 0x88, 0x9f, 0xad, 0x94, 0x02, 0xf4, 0xeb, 0x7e, 0x64, 0x1a, 0x15,
                0x1a, 0x3a, 0x19, 0xa0, 0xb1, 0xe4, 0xa4, 0xa0, 0x22, 0xb5, 0x1c, 0x38, 0x71, 0x24,
                0x68, 0x2e, 0x8d, 0x22,
            ])
        );
        assert_eq!(
            cipher.iv,
            Some(vec![
                0x50, 0x4b, 0x7e, 0xc0, 0x8f, 0x8b, 0x76, 0xad, 0x54, 0x81, 0x0f, 0xcf,
            ])
        );
    }
}
