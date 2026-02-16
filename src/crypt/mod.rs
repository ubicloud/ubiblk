mod key;
pub use key::{aes256gcm_decrypt, aes256gcm_encrypt, CipherMethod, KeyEncryptionCipher};

mod block;
pub use block::XtsBlockCipher;

mod key_serialization;
pub use key_serialization::{decode_key, decode_optional_key, encode_key, encode_optional_key};
