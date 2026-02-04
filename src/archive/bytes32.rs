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
