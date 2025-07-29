use std::fmt::Write;

pub fn hexdump(data: &[u8], len: usize) -> String {
    let len = len.min(data.len());
    let mut result = String::with_capacity(len.div_ceil(16) * 60);

    for offset in (0..len).step_by(16) {
        write!(&mut result, "{offset:08x}  ").unwrap();

        let mut hex_part = String::new();
        let mut ascii_part = String::new();
        let chunk = &data[offset..len.min(offset + 16)];

        for (i, byte) in chunk.iter().enumerate() {
            write!(&mut hex_part, "{byte:02x} ").unwrap();
            ascii_part.push(if byte.is_ascii_graphic() || *byte == b' ' {
                *byte as char
            } else {
                '.'
            });
            if i == 7 {
                hex_part.push(' ');
            }
        }

        for i in chunk.len()..16 {
            hex_part.push_str("   ");
            if i == 7 {
                hex_part.push(' ');
            }
            ascii_part.push(' ');
        }

        result.push_str(&hex_part);
        result.push_str(" |");
        result.push_str(&ascii_part);
        result.push_str("|\n");
    }

    result
}

pub fn encode_hex(data: &[u8], len: usize) -> String {
    hex::encode(&data[..len.min(data.len())])
}

pub fn decode_hex(hex: &str) -> Result<Vec<u8>, String> {
    hex::decode(hex).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hexdump() {
        let data = b"Hello, world! This is a test of the hexdump function.";
        let expected =
            "00000000  48 65 6c 6c 6f 2c 20 77  6f 72 6c 64 21 20 54 68  |Hello, world! Th|\n\
00000010  69 73 20 69 73 20 61 20  74 65 73 74 20 6f 66 20  |is is a test of |\n\
00000020  74 68 65 20 68 65 78 64  75 6d 70 20 66 75 6e 63  |the hexdump func|\n\
00000030  74 69 6f 6e 2e                                    |tion.           |\n";
        assert_eq!(hexdump(data, data.len()), expected);
    }

    #[test]
    fn test_encode_hex() {
        let data = b"Hello";
        let expected = "48656c6c6f";
        assert_eq!(encode_hex(data, data.len()), expected);
    }

    #[test]
    fn test_decode_hex() {
        let hex = "48656c6c6f";
        let expected = b"Hello".to_vec();
        assert_eq!(decode_hex(hex).unwrap(), expected);
    }

    #[test]
    fn test_decode_hex_odd_len() {
        let hex = "abc";
        assert!(decode_hex(hex).is_err());
    }

    #[test]
    fn test_decode_hex_non_hex_chars() {
        let hex = "zz";
        assert!(decode_hex(hex).is_err());
    }
}
