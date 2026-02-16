use base64::{engine::general_purpose::STANDARD, Engine};
use serde::{Deserialize, Deserializer, Serializer};

type OptKey = Option<Vec<u8>>;

pub fn decode_optional_key<'de, D>(deserializer: D) -> std::result::Result<OptKey, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<String>::deserialize(deserializer)?
        .map(|key| STANDARD.decode(key).map_err(serde::de::Error::custom))
        .transpose()
}

pub fn encode_optional_key<S>(key: &OptKey, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match key {
        None => serializer.serialize_none(),
        Some(key) => {
            let encoded = STANDARD.encode(key);
            serializer.serialize_some(&encoded)
        }
    }
}

pub fn decode_key<'de, D>(deserializer: D) -> std::result::Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    let key_str = String::deserialize(deserializer)?;
    STANDARD.decode(key_str).map_err(serde::de::Error::custom)
}

pub fn encode_key<S>(key: &Vec<u8>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    let encoded = STANDARD.encode(key);
    serializer.serialize_str(&encoded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct WrapOptionalKey {
        #[serde(
            default,
            deserialize_with = "decode_optional_key",
            serialize_with = "encode_optional_key"
        )]
        key: OptKey,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
    struct WrapKey {
        #[serde(deserialize_with = "decode_key", serialize_with = "encode_key")]
        key: Vec<u8>,
    }

    #[test]
    fn test_optional_key_none_when_null_or_missing() {
        let a: WrapOptionalKey = serde_json::from_str(r#"{"key":null}"#).unwrap();
        assert_eq!(a.key, None);

        let b: WrapOptionalKey = serde_json::from_str(r#"{}"#).unwrap();
        assert_eq!(b.key, None);
    }

    #[test]
    fn test_optional_key_decodes_base64() {
        let json = r#"{"key":"AQIDBAU="}"#;
        let w: WrapOptionalKey = serde_json::from_str(json).unwrap();
        assert_eq!(w.key, Some(vec![1, 2, 3, 4, 5]));
    }

    #[test]
    fn test_optional_key_invalid_base64_errors() {
        let err = serde_json::from_str::<WrapOptionalKey>(r#"{"key":"%%%"}"#).unwrap_err();
        assert!(err.to_string().contains("Invalid symbol 37, offset 0."));
    }

    #[test]
    fn test_optional_key_wrong_type_errors() {
        // number instead of string/null
        let err = serde_json::from_str::<WrapOptionalKey>(r#"{"key":123}"#).unwrap_err();
        assert!(err.to_string().contains("invalid type: integer"));
    }

    #[test]
    fn test_key_decodes_base64() {
        let json = r#"{"key":"AQIDBAU="}"#;
        let w: WrapKey = serde_json::from_str(json).unwrap();
        assert_eq!(w.key, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_key_invalid_base64_errors() {
        let err = serde_json::from_str::<WrapKey>(r#"{"key":"%%%"}"#).unwrap_err();
        assert!(err.to_string().contains("Invalid symbol 37, offset 0."));
    }

    #[test]
    fn test_encode_key() {
        let w = WrapKey {
            key: vec![10, 20, 30, 40, 50],
        };
        let json = serde_json::to_string(&w).unwrap();
        let deserialized: Result<WrapKey, _> = serde_json::from_str(&json);
        assert!(deserialized.is_ok());
        assert_eq!(deserialized.unwrap(), w);
    }
}
