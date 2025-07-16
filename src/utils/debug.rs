pub fn hexdump(data: &[u8], len: usize) -> String {
    let mut result = String::new();
    let mut offset = 0;

    while offset < data.len() && offset < len {
        result.push_str(&format!("{:08x}  ", offset));

        let mut hex_part = String::new();
        let mut ascii_part = String::new();

        for i in 0..16 {
            let pos = offset + i;

            if pos < data.len() && pos < len {
                hex_part.push_str(&format!("{:02x} ", data[pos]));

                if data[pos] >= 32 && data[pos] <= 126 {
                    ascii_part.push(data[pos] as char);
                } else {
                    ascii_part.push('.');
                }
            } else {
                hex_part.push_str("   ");
                ascii_part.push(' ');
            }

            if i == 7 {
                hex_part.push(' ');
            }
        }

        result.push_str(&hex_part);
        result.push_str(" |");
        result.push_str(&ascii_part);
        result.push_str("|\n");

        offset += 16;
    }

    result
}

pub fn encode_hex(data: &[u8], len: usize) -> String {
    data[..len.min(data.len())]
        .iter()
        .map(|byte| format!("{:02x}", byte))
        .collect::<String>()
}

pub fn decode_hex(hex: &str) -> Result<Vec<u8>, String> {
    if hex.len() % 2 != 0 {
        return Err("Hex string must be even length".into());
    }
    (0..hex.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&hex[i..i + 2], 16).map_err(|e| e.to_string()))
        .collect()
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
