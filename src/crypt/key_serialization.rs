use base64::{engine::general_purpose::STANDARD, Engine};
use serde::{Deserialize, Deserializer, Serializer};

type OptKeyPair = Option<(Vec<u8>, Vec<u8>)>;
type OptKey = Option<Vec<u8>>;

pub fn decode_optional_key_pair<'de, D>(deserializer: D) -> Result<OptKeyPair, D::Error>
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

pub fn encode_optional_key_pair<S>(keys: &OptKeyPair, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match keys {
        None => serializer.serialize_none(),
        Some((k1, k2)) => {
            let encoded1 = STANDARD.encode(k1);
            let encoded2 = STANDARD.encode(k2);
            serializer.serialize_some(&(encoded1, encoded2))
        }
    }
}

pub fn decode_optional_key<'de, D>(deserializer: D) -> std::result::Result<OptKey, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<String>::deserialize(deserializer)?
        .map(|key| STANDARD.decode(key).map_err(serde::de::Error::custom))
        .transpose()
}

pub fn decode_key<'de, D>(deserializer: D) -> std::result::Result<Vec<u8>, D::Error>
where
    D: Deserializer<'de>,
{
    let key_str = String::deserialize(deserializer)?;
    STANDARD.decode(key_str).map_err(serde::de::Error::custom)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
    struct WrapOptionalKeyPair {
        #[serde(
            default,
            deserialize_with = "decode_optional_key_pair",
            serialize_with = "encode_optional_key_pair"
        )]
        keys: OptKeyPair,
    }

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct WrapOptionalKey {
        #[serde(default, deserialize_with = "decode_optional_key")]
        key: OptKey,
    }

    #[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
    struct WrapKey {
        #[serde(deserialize_with = "decode_key")]
        key: Vec<u8>,
    }

    #[test]
    fn test_optional_key_pair_none_roundtrips_as_null() {
        let w = WrapOptionalKeyPair { keys: None };
        let yaml = serde_yaml::to_string(&w).unwrap();
        assert_eq!(yaml, "keys: null\n");

        let back: WrapOptionalKeyPair = serde_yaml::from_str(&yaml).unwrap();
        assert_eq!(back, w);
    }

    #[test]
    fn test_optional_key_pair_some_roundtrips() {
        let w = WrapOptionalKeyPair {
            keys: Some((vec![0, 1, 2, 3, 4, 5], vec![250, 251, 252, 253])),
        };

        let yaml = serde_yaml::to_string(&w).unwrap();

        // Ensure it serializes to base64 strings.
        let v: serde_yaml::Value = serde_yaml::from_str(&yaml).unwrap();
        let arr = v.get("keys").unwrap().as_sequence().unwrap();
        assert_eq!(arr.len(), 2);
        assert_eq!(
            arr[0].as_str().unwrap(),
            STANDARD.encode([0, 1, 2, 3, 4, 5])
        );
        assert_eq!(
            arr[1].as_str().unwrap(),
            STANDARD.encode([250, 251, 252, 253])
        );

        // And round-trip.
        let back: WrapOptionalKeyPair = serde_yaml::from_str(&yaml).unwrap();
        assert_eq!(back, w);
    }

    #[test]
    fn test_optional_key_pair_missing_field_defaults_to_none() {
        let back: WrapOptionalKeyPair = serde_json::from_str(r#"{}"#).unwrap();
        assert_eq!(back.keys, None);
    }

    #[test]
    fn test_optional_key_pair_invalid_base64_errors() {
        let err1 =
            serde_yaml::from_str::<WrapOptionalKeyPair>(r#"keys: ["%%%","AQID"]"#).unwrap_err();
        assert_eq!(err1.to_string(), "Invalid symbol 37, offset 0.");

        let err2 =
            serde_yaml::from_str::<WrapOptionalKeyPair>(r#"keys: ["AQID","%%%"]"#).unwrap_err();
        assert_eq!(err2.to_string(), "Invalid symbol 37, offset 0.");
    }

    #[test]
    fn test_optional_key_pair_wrong_shape_errors() {
        // object instead of array/tuple
        let result =
            serde_json::from_str::<WrapOptionalKeyPair>(r#"{"keys":{"a":"AA==","b":"AA=="}}"#);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("invalid type: map"));

        // wrong arity
        let result = serde_yaml::from_str::<WrapOptionalKeyPair>(r#"keys: ["AA=="]"#);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("invalid length 1, expected a tuple of size 2"));

        let result = serde_yaml::from_str::<WrapOptionalKeyPair>(r#"keys: ["AA==","AA==","AA=="]"#);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("invalid length 3, expected sequence of 2 elements"));
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
        let yaml = r#"key: "AQIDBAU=""#;
        let w: WrapOptionalKey = serde_yaml::from_str(yaml).unwrap();
        assert_eq!(w.key, Some(vec![1, 2, 3, 4, 5]));
    }

    #[test]
    fn test_optional_key_invalid_base64_errors() {
        let err = serde_yaml::from_str::<WrapOptionalKey>(r#"key: "%%%""#).unwrap_err();
        assert_eq!(err.to_string(), "Invalid symbol 37, offset 0.");
    }

    #[test]
    fn test_optional_key_wrong_type_errors() {
        // number instead of string/null
        let err = serde_json::from_str::<WrapOptionalKey>(r#"{"key":123}"#).unwrap_err();
        assert!(err.to_string().contains("invalid type: integer"));
    }

    #[test]
    fn test_key_decodes_base64() {
        let yaml = r#"key: "AQIDBAU=""#;
        let w: WrapKey = serde_yaml::from_str(yaml).unwrap();
        assert_eq!(w.key, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_key_invalid_base64_errors() {
        let err = serde_yaml::from_str::<WrapKey>(r#"key: "%%%""#).unwrap_err();
        assert_eq!(err.to_string(), "Invalid symbol 37, offset 0.");
    }
}
