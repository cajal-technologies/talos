mod exports;

/// Store a raw key/value pair in NEAR contract storage.
///
/// The wire format is deliberately tiny for the verifier fixture:
/// the first input byte is the key and the remaining bytes are the value.
pub fn set_from_input() {
    let input = near_sdk::env::input().unwrap_or_default();
    if let Some((key, value)) = input.split_first() {
        near_sdk::env::storage_write(&[*key], value);
    }
}
