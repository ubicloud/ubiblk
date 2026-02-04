mod key;
pub use key::{CipherMethod, KeyEncryptionCipher};

mod block;
pub use block::XtsBlockCipher;

mod key_serialization;
pub use key_serialization::{
    decode_key, decode_optional_key, decode_optional_key_pair, encode_key, encode_optional_key,
    encode_optional_key_pair,
};
