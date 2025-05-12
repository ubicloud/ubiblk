use base64::{engine::general_purpose::STANDARD, Engine};
use serde::{Deserialize, Deserializer, Serialize};
use serde_with::{base64::Base64, serde_as};

fn decode_encryption_keys<'de, D>(deserializer: D) -> Result<Option<(Vec<u8>, Vec<u8>)>, D::Error>
where
    D: Deserializer<'de>,
{
    let opt = Option::<(String, String)>::deserialize(deserializer)?;
    match opt {
        Some((k1, k2)) => {
            let decoded1 = STANDARD.decode(&k1).map_err(serde::de::Error::custom)?;
            let decoded2 = STANDARD.decode(&k2).map_err(serde::de::Error::custom)?;
            Ok(Some((decoded1, decoded2)))
        }
        None => Ok(None),
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(rename_all = "kebab-case")]
pub enum CipherMethod {
    None,
    Aes256Gcm,
}

#[serde_as]
#[derive(Debug, Clone, Deserialize)]
pub struct KeyEncryptionCipher {
    pub method: CipherMethod,

    #[serde_as(as = "Option<Base64>")]
    pub key: Option<Vec<u8>>,

    #[serde_as(as = "Option<Base64>")]
    pub initial_vector: Option<Vec<u8>>,

    #[serde_as(as = "Option<Base64>")]
    pub auth_data: Option<Vec<u8>>,
}

#[derive(Debug, Clone, Deserialize)]
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

    #[serde(default, deserialize_with = "decode_encryption_keys")]
    pub encryption_key: Option<(Vec<u8>, Vec<u8>)>,
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
        initial_vector: "UEt+wI+Ldq1UgQ/P"
        auth_data: "dm0zamdlejhfMA=="
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
            cipher.initial_vector,
            Some(vec![
                0x50, 0x4b, 0x7e, 0xc0, 0x8f, 0x8b, 0x76, 0xad, 0x54, 0x81, 0x0f, 0xcf,
            ])
        );
        assert_eq!(
            cipher.auth_data,
            Some(vec![
                0x76, 0x6d, 0x33, 0x6a, 0x67, 0x65, 0x7a, 56, 0x5f, 0x30
            ])
        );
    }

    #[test]
    fn test_decode_encryption_keys() {
        let yaml = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        num_queues: 4
        queue_size: 1024
        seg_size_max: 4096
        seg_count_max: 10
        poll_queue_timeout_us: 1000
        encryption_key:
          - "aISq7jbeNWO8U+VHOb09K4K5Sj1DsMGLf289oO4vOG9SI1WpGdUM7WmuWQBtGhky"
          - "5OTauknSxwWFqRGvE2Ef3Zv2s1syPdbYFXyq3FHkK69/BhI+7jF+VFQGFb1+j3sj"
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert_eq!(
            options.encryption_key,
            Some((
                vec![
                    0x68, 0x84, 0xaa, 0xee, 0x36, 0xde, 0x35, 0x63, 0xbc, 0x53, 0xe5, 0x47, 0x39,
                    0xbd, 0x3d, 0x2b, 0x82, 0xb9, 0x4a, 0x3d, 0x43, 0xb0, 0xc1, 0x8b, 0x7f, 0x6f,
                    0x3d, 0xa0, 0xee, 0x2f, 0x38, 0x6f, 0x52, 0x23, 0x55, 0xa9, 0x19, 0xd5, 0x0c,
                    0xed, 0x69, 0xae, 0x59, 0x00, 0x6d, 0x1a, 0x19, 0x32,
                ],
                vec![
                    0xe4, 0xe4, 0xda, 0xba, 0x49, 0xd2, 0xc7, 0x05, 0x85, 0xa9, 0x11, 0xaf, 0x13,
                    0x61, 0x1f, 0xdd, 0x9b, 0xf6, 0xb3, 0x5b, 0x32, 0x3d, 0xd6, 0xd8, 0x15, 0x7c,
                    0xaa, 0xdc, 0x51, 0xe4, 0x2b, 0xaf, 0x7f, 0x06, 0x12, 0x3e, 0xee, 0x31, 0x7e,
                    0x54, 0x54, 0x06, 0x15, 0xbd, 0x7e, 0x8f, 0x7b, 0x23,
                ]
            ))
        );
    }

    #[test]
    fn test_missing_encryption_key() {
        let yaml = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        num_queues: 4
        queue_size: 1024
        seg_size_max: 4096
        seg_count_max: 10
        poll_queue_timeout_us: 1000
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert!(options.encryption_key.is_none());
    }
}
