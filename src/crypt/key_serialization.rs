use base64::{engine::general_purpose::STANDARD, Engine};
use serde::{Deserialize, Deserializer, Serializer};

pub type OptKeyPair = Option<(Vec<u8>, Vec<u8>)>;
pub type OptKey = Option<Vec<u8>>;

pub fn decode_xts_keys<'de, D>(deserializer: D) -> Result<OptKeyPair, D::Error>
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

pub fn encode_xts_keys<S>(keys: &OptKeyPair, serializer: S) -> Result<S::Ok, S::Error>
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

pub fn decode_psk_key<'de, D>(deserializer: D) -> std::result::Result<OptKey, D::Error>
where
    D: Deserializer<'de>,
{
    Option::<String>::deserialize(deserializer)?
        .map(|key| STANDARD.decode(key).map_err(serde::de::Error::custom))
        .transpose()
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde::{Deserialize, Serialize};

    #[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
    struct WrapXts {
        #[serde(
            default,
            deserialize_with = "decode_xts_keys",
            serialize_with = "encode_xts_keys"
        )]
        xts: OptKeyPair,
    }

    #[derive(Debug, Deserialize, PartialEq, Eq)]
    struct WrapPsk {
        #[serde(default, deserialize_with = "decode_psk_key")]
        psk: OptKey,
    }

    #[test]
    fn xts_none_roundtrips_as_null() {
        let w = WrapXts { xts: None };
        let yaml = serde_yaml::to_string(&w).unwrap();
        assert_eq!(yaml, "xts: null\n");

        let back: WrapXts = serde_yaml::from_str(&yaml).unwrap();
        assert_eq!(back, w);
    }

    #[test]
    fn xts_some_roundtrips() {
        let w = WrapXts {
            xts: Some((vec![0, 1, 2, 3, 4, 5], vec![250, 251, 252, 253])),
        };

        let yaml = serde_yaml::to_string(&w).unwrap();

        // Ensure it serializes to base64 strings.
        let v: serde_yaml::Value = serde_yaml::from_str(&yaml).unwrap();
        let arr = v.get("xts").unwrap().as_sequence().unwrap();
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
        let back: WrapXts = serde_yaml::from_str(&yaml).unwrap();
        assert_eq!(back, w);
    }

    #[test]
    fn xts_missing_field_defaults_to_none() {
        let back: WrapXts = serde_yaml::from_str(r#"{}"#).unwrap();
        assert_eq!(back.xts, None);
    }

    #[test]
    fn xts_invalid_base64_errors() {
        let err1 = serde_yaml::from_str::<WrapXts>(r#"xts: ["%%%","AQID"]"#).unwrap_err();
        assert_eq!(err1.to_string(), "Invalid symbol 37, offset 0.");

        let err2 = serde_yaml::from_str::<WrapXts>(r#"xts: ["AQID","%%%"]"#).unwrap_err();
        assert_eq!(err2.to_string(), "Invalid symbol 37, offset 0.");
    }

    #[test]
    fn xts_wrong_shape_errors() {
        // object instead of array/tuple
        assert!(serde_yaml::from_str::<WrapXts>(r#"{"xts":{"a":"AA==","b":"AA=="}}"#).is_err());
        // wrong arity
        assert!(serde_yaml::from_str::<WrapXts>(r#"{"xts":["AA=="]}"#).is_err());
        assert!(serde_yaml::from_str::<WrapXts>(r#"{"xts":["AA==","AA==","AA=="]}"#).is_err());
    }

    #[test]
    fn psk_none_when_null_or_missing() {
        let a: WrapPsk = serde_yaml::from_str(r#"{"psk":null}"#).unwrap();
        assert_eq!(a.psk, None);

        let b: WrapPsk = serde_yaml::from_str(r#"{}"#).unwrap();
        assert_eq!(b.psk, None);
    }

    #[test]
    fn psk_decodes_base64() {
        let yaml = r#"psk: "AQIDBAU=""#;
        let w: WrapPsk = serde_yaml::from_str(yaml).unwrap();
        assert_eq!(w.psk, Some(vec![1, 2, 3, 4, 5]));
    }

    #[test]
    fn psk_invalid_base64_errors() {
        let err = serde_yaml::from_str::<WrapPsk>(r#"psk: "%%%""#).unwrap_err();
        assert_eq!(err.to_string(), "Invalid symbol 37, offset 0.");
    }

    #[test]
    fn psk_wrong_type_errors() {
        // number instead of string/null
        assert!(serde_yaml::from_str::<WrapPsk>(r#"{"psk":123}"#).is_err());
    }
}
