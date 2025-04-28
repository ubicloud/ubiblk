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
