use base64::{engine::general_purpose::STANDARD, Engine};
use serde::{Deserialize, Deserializer, Serialize};
use virtio_bindings::virtio_blk::VIRTIO_BLK_ID_BYTES;

type OptKeyPair = Option<(Vec<u8>, Vec<u8>)>;

fn decode_encryption_keys<'de, D>(deserializer: D) -> Result<OptKeyPair, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<(String, String)>::deserialize(deserializer)?
        .map(|(k1, k2)| {
            let decoded1 = STANDARD.decode(k1).map_err(serde::de::Error::custom)?;
            let decoded2 = STANDARD.decode(k2).map_err(serde::de::Error::custom)?;
            Ok((decoded1, decoded2))
        })
        .transpose()
}

fn default_poll_queue_timeout_us() -> u128 {
    1000
}

fn default_num_queues() -> usize {
    1
}

fn default_queue_size() -> usize {
    64
}

fn default_seg_size_max() -> u32 {
    65536
}

fn default_seg_count_max() -> u32 {
    4
}

fn default_skip_sync() -> bool {
    false
}

fn default_copy_on_read() -> bool {
    false
}

fn default_track_written() -> bool {
    false
}

fn default_write_through() -> bool {
    false
}

fn default_autofetch() -> bool {
    false
}

fn default_device_id() -> String {
    "ubiblk".to_string()
}

fn deserialize_device_id<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: Deserializer<'de>,
{
    let s = String::deserialize(deserializer)?;
    if s.len() > VIRTIO_BLK_ID_BYTES as usize {
        return Err(serde::de::Error::custom(format!(
            "device_id exceeds maximum of {VIRTIO_BLK_ID_BYTES} bytes"
        )));
    }
    Ok(s)
}

#[derive(Debug, Clone, Deserialize)]
pub struct Options {
    pub path: String,
    pub image_path: Option<String>,
    pub metadata_path: Option<String>,
    pub io_debug_path: Option<String>,
    pub rpc_socket_path: Option<String>,
    pub socket: String,

    #[serde(default)]
    pub cpus: Option<Vec<usize>>,

    #[serde(default = "default_num_queues")]
    pub num_queues: usize,

    #[serde(default = "default_queue_size")]
    pub queue_size: usize,

    #[serde(default = "default_seg_size_max")]
    pub seg_size_max: u32,

    #[serde(default = "default_seg_count_max")]
    pub seg_count_max: u32,

    #[serde(default = "default_poll_queue_timeout_us")]
    pub poll_queue_timeout_us: u128,

    #[serde(default = "default_skip_sync")]
    pub skip_sync: bool,

    #[serde(default = "default_copy_on_read")]
    pub copy_on_read: bool,

    #[serde(default = "default_track_written")]
    pub track_written: bool,

    #[serde(default = "default_write_through")]
    pub write_through: bool,

    #[serde(default = "default_autofetch")]
    pub autofetch: bool,

    #[serde(default, deserialize_with = "decode_encryption_keys")]
    pub encryption_key: Option<(Vec<u8>, Vec<u8>)>,

    #[serde(
        default = "default_device_id",
        deserialize_with = "deserialize_device_id"
    )]
    pub device_id: String,

    #[serde(default)]
    pub io_engine: IoEngine,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Default)]
#[serde(rename_all = "snake_case")]
pub enum IoEngine {
    #[default]
    IoUring,
    Sync,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::key_encryption::{CipherMethod, KeyEncryptionCipher};
    use serde_yaml::from_str;

    #[test]
    fn test_key_encryption_cipher() {
        let yaml = r#"
        method: aes256-gcm
        key: "uCvGiJ+tlAL0635kGhUaOhmgseSkoCK1HDhxJGgujSI="
        init_vector: "UEt+wI+Ldq1UgQ/P"
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
            cipher.init_vector,
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
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert!(options.encryption_key.is_none());
    }

    #[test]
    fn test_default_values() {
        let yaml = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert!(!options.copy_on_read);
        assert!(!options.track_written);
        assert!(!options.write_through);
        assert_eq!(options.device_id, "ubiblk".to_string());
        assert!(options.rpc_socket_path.is_none());
        assert!(!options.autofetch);
        assert_eq!(options.io_engine, IoEngine::IoUring);
    }

    #[test]
    fn test_device_id_length() {
        let yaml = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        device_id: "12345678901234567890"
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert_eq!(options.device_id, "12345678901234567890".to_string());

        let yaml_too_long = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        device_id: "123456789012345678901"
        "#;
        assert!(from_str::<Options>(yaml_too_long).is_err());
    }

    #[test]
    fn test_write_through_enabled() {
        let yaml = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        write_through: true
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert!(options.write_through);
    }

    #[test]
    fn test_cpus_parsing() {
        let yaml = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        num_queues: 2
        cpus:
          - 1
          - 2
        "#;
        let options: Options = from_str(yaml).unwrap();
        assert_eq!(options.cpus, Some(vec![1, 2]));
    }

    #[test]
    fn test_io_engine_parsing() {
        let yaml_uring = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        io_engine: io_uring
        "#;
        let options_uring: Options = from_str(yaml_uring).unwrap();
        assert_eq!(options_uring.io_engine, IoEngine::IoUring);

        let yaml_sync = r#"
        path: "/path/to/image"
        socket: "/path/to/socket"
        io_engine: sync
        "#;
        let options_sync: Options = from_str(yaml_sync).unwrap();
        assert_eq!(options_sync.io_engine, IoEngine::Sync);
    }
}
