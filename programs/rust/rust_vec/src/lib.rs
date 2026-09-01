//! `Vec` access patterns over the Talos stdio byte stream.
//!
//! Every export reads the whole input into a `Vec<u8>`, exercises one access
//! pattern, and writes at most one result. Nothing here indexes with `[]`: a
//! panic is a wasm trap rather than an operation of the data structure, so the
//! panic paths are kept out of the module and every read goes through `get`.
//!
//! An `Option` result is reported by output length. `None` writes nothing.

mod exports;

use talos_stdio::{read, write};

/// Read the whole input stream, one `push` per byte.
fn read_all() -> Vec<u8> {
    let mut data: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 256];
    loop {
        let count = read(&mut chunk);
        if count == 0 {
            return data;
        }
        for &byte in chunk.iter().take(count) {
            data.push(byte);
        }
    }
}

/// The little-endian `u32` in a four-byte word.
fn le_u32(word: &[u8]) -> Option<u32> {
    let bytes: [u8; 4] = word.try_into().ok()?;
    Some(u32::from_le_bytes(bytes))
}

/// Write the element count as four little-endian bytes.
pub fn vec_len() {
    let data = read_all();
    write(&(data.len() as u32).to_le_bytes());
}

/// Write the last byte, or nothing when the input is empty.
pub fn vec_pop() {
    let mut data = read_all();
    if let Some(byte) = data.pop() {
        write(&[byte]);
    }
}

/// Byte 0 selects an index into the remaining bytes. Write that element, or
/// nothing when the index is out of bounds.
pub fn vec_get() {
    let data = read_all();
    let Some((&index, rest)) = data.split_first() else {
        return;
    };
    if let Some(&byte) = rest.get(index as usize) {
        write(&[byte]);
    }
}

/// Byte 0 is the needle, the remaining bytes are the haystack. Write 1 when
/// the needle occurs, 0 when it does not, nothing on empty input.
pub fn vec_contains() {
    let data = read_all();
    let Some((&needle, rest)) = data.split_first() else {
        return;
    };
    write(&[rest.contains(&needle) as u8]);
}

/// Parse a length-prefixed list of little-endian `u32` words and write their
/// wrapping sum. Input that the wire format rejects writes nothing: a header
/// shorter than four bytes, a payload with a trailing partial word, or a word
/// count that disagrees with the header.
pub fn vec_sum32() {
    let data = read_all();
    let Some((header, payload)) = data.split_at_checked(4) else {
        return;
    };
    let Some(count) = le_u32(header) else {
        return;
    };
    let chunks = payload.chunks_exact(4);
    if !chunks.remainder().is_empty() || chunks.len() != count as usize {
        return;
    }
    // The words go into a `Vec<u32>` on purpose: the contract is stated with
    // `Vec.deserialize`, which yields the word list before it is summed.
    let Some(words) = chunks.map(le_u32).collect::<Option<Vec<u32>>>() else {
        return;
    };
    let sum = words.iter().fold(0u32, |acc, &word| acc.wrapping_add(word));
    write(&sum.to_le_bytes());
}
