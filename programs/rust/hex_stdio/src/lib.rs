//! Hexadecimal conversion over the Talos byte stream.

use hex_dep as hex;

mod exports;

use exports::{read_all, write_all};

#[inline(never)]
fn encode_bytes(input: &[u8]) -> Vec<u8> {
    hex::encode(input).into_bytes()
}

#[inline(never)]
fn decode_bytes(input: &[u8]) -> Result<Vec<u8>, hex::FromHexError> {
    hex::decode(input)
}

/// Encode the complete input stream as lowercase hexadecimal.
#[inline]
pub fn encode() {
    let input = read_all();
    let output = encode_bytes(&input);
    write_all(&output);
}

/// Prefix decoded bytes with status 0; report odd length as 1 and invalid
/// hexadecimal as 2, without a decoded payload on either error.
#[inline]
pub fn decode() {
    let mut output = Vec::new();
    let input = read_all();
    match decode_bytes(&input) {
        Ok(bytes) => {
            output.push(0);
            output.extend_from_slice(&bytes);
        }
        Err(hex::FromHexError::OddLength) => output.push(1),
        // Vec decoding has no requested output length, so this variant is
        // unreachable; retain its distinct library error code.
        Err(hex::FromHexError::InvalidStringLength) => output.push(3),
        Err(hex::FromHexError::InvalidHexCharacter { .. }) => output.push(2),
    }
    drop(input);
    write_all(&output);
}

#[cfg(test)]
mod tests {
    use super::{decode_bytes, encode_bytes};
    use hex_dep::FromHexError;

    #[test]
    fn every_byte_encodes_in_lowercase_and_roundtrips() {
        let input: Vec<u8> = (0..=255).collect();
        let expected: String = input.iter().map(|byte| format!("{byte:02x}")).collect();
        assert_eq!(encode_bytes(&input), expected.as_bytes());
        assert_eq!(decode_bytes(expected.as_bytes()).unwrap(), input);
        assert_eq!(
            decode_bytes(expected.to_uppercase().as_bytes()).unwrap(),
            input
        );
    }

    #[test]
    fn empty_input_is_valid() {
        assert_eq!(encode_bytes(&[]), b"");
        assert_eq!(decode_bytes(&[]).unwrap(), b"");
    }

    #[test]
    fn odd_length_takes_precedence_over_invalid_characters() {
        for byte in 0..=255 {
            assert_eq!(decode_bytes(&[byte]), Err(FromHexError::OddLength));
        }
    }

    #[test]
    fn every_character_pair_has_the_expected_result() {
        fn nibble(byte: u8) -> Option<u8> {
            match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                b'A'..=b'F' => Some(byte - b'A' + 10),
                _ => None,
            }
        }
        for hi in 0..=255 {
            for lo in 0..=255 {
                match (nibble(hi), nibble(lo)) {
                    (Some(h), Some(l)) => {
                        assert_eq!(decode_bytes(&[hi, lo]).unwrap(), [h * 16 + l])
                    }
                    _ => assert!(matches!(
                        decode_bytes(&[hi, lo]),
                        Err(FromHexError::InvalidHexCharacter { .. })
                    )),
                }
            }
        }
    }
}
