use serde::de::{self, Deserializer, Visitor};
use serde::ser::Serializer;
use std::fmt;
pub fn serialize<S>(value: &[u8; 32], serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    serializer.serialize_bytes(&value[..])
}

pub fn deserialize<'de, D>(deserializer: D) -> Result<[u8; 32], D::Error>
where
    D: Deserializer<'de>,
{
    struct Bytes32Visitor;

    impl<'de> Visitor<'de> for Bytes32Visitor {
        type Value = [u8; 32];

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "a byte array of length 32")
        }

        fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
        where
            E: de::Error,
        {
            if v.len() != 32 {
                return Err(E::invalid_length(v.len(), &self));
            }
            let mut arr = [0u8; 32];
            arr.copy_from_slice(v);
            Ok(arr)
        }
    }

    deserializer.deserialize_bytes(Bytes32Visitor)
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};

    #[derive(Debug, PartialEq, Serialize, Deserialize)]
    struct Wrapper {
        #[serde(with = "super")]
        data: [u8; 32],
    }

    fn cbor_roundtrip(wrapper: &Wrapper) -> Vec<u8> {
        let mut buf = Vec::new();
        ciborium::into_writer(wrapper, &mut buf).unwrap();
        buf
    }

    #[test]
    fn serialize_deserialize_roundtrip() {
        let original = Wrapper { data: [0xAB; 32] };
        let bytes = cbor_roundtrip(&original);
        let decoded: Wrapper = ciborium::from_reader(&bytes[..]).unwrap();
        assert_eq!(original, decoded);
    }

    #[test]
    fn serialize_deserialize_zeros() {
        let original = Wrapper { data: [0; 32] };
        let bytes = cbor_roundtrip(&original);
        let decoded: Wrapper = ciborium::from_reader(&bytes[..]).unwrap();
        assert_eq!(original, decoded);
    }

    #[test]
    fn deserialize_wrong_length_too_short() {
        // Manually craft CBOR with a bytes field that's too short (16 bytes instead of 32)
        #[derive(Serialize)]
        struct FakeWrapper {
            data: ciborium::Value,
        }
        let fake = FakeWrapper {
            data: ciborium::Value::Bytes(vec![0xAA; 16]),
        };
        let mut buf = Vec::new();
        ciborium::into_writer(&fake, &mut buf).unwrap();

        let result: Result<Wrapper, _> = ciborium::from_reader(&buf[..]);
        assert!(result.is_err());
    }

    #[test]
    fn deserialize_wrong_length_too_long() {
        #[derive(Serialize)]
        struct FakeWrapper {
            data: ciborium::Value,
        }
        let fake = FakeWrapper {
            data: ciborium::Value::Bytes(vec![0xBB; 64]),
        };
        let mut buf = Vec::new();
        ciborium::into_writer(&fake, &mut buf).unwrap();

        let result: Result<Wrapper, _> = ciborium::from_reader(&buf[..]);
        assert!(result.is_err());
    }

    #[test]
    fn deserialize_wrong_length_empty() {
        #[derive(Serialize)]
        struct FakeWrapper {
            data: ciborium::Value,
        }
        let fake = FakeWrapper {
            data: ciborium::Value::Bytes(vec![]),
        };
        let mut buf = Vec::new();
        ciborium::into_writer(&fake, &mut buf).unwrap();

        let result: Result<Wrapper, _> = ciborium::from_reader(&buf[..]);
        assert!(result.is_err());
    }

    #[test]
    fn deserialize_wrong_type() {
        // Pass a string instead of bytes — triggers the `expecting` method
        #[derive(Serialize)]
        struct FakeWrapper {
            data: String,
        }
        let fake = FakeWrapper {
            data: "not bytes".to_string(),
        };
        let mut buf = Vec::new();
        ciborium::into_writer(&fake, &mut buf).unwrap();

        let result: Result<Wrapper, _> = ciborium::from_reader(&buf[..]);
        assert!(result.is_err());
    }
}
