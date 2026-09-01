//! `Vec` access patterns over the Talos stdio byte stream.
//!
//! Every export reads the whole input into a `Vec<u8>`, exercises one access
//! pattern, and writes the result. Nothing here indexes with `[]`: a panic is
//! a wasm trap rather than an operation of the data structure, so the panic
//! paths are kept out of the module and every read goes through `get`.
//!
//! An `Option` result is reported by output length. `None` writes nothing.

mod exports;

use talos_stdio::{read, write};

/// Read the whole input stream, one `push` per byte.
fn read_all() -> Vec<u8> {
    let mut data: Vec<u8> = Vec::new();
    let mut chunk = [0u8; 64];
    loop {
        let count = read(&mut chunk);
        if count == 0 {
            return data;
        }
        let mut i = 0usize;
        while i < count {
            match chunk.get(i) {
                Some(&byte) => data.push(byte),
                None => return data,
            }
            i += 1;
        }
    }
}

/// The little-endian `u32` starting at `base`, if four bytes are available.
fn le_u32_at(data: &[u8], base: usize) -> Option<u32> {
    let b0 = *data.get(base)?;
    let b1 = *data.get(base + 1)?;
    let b2 = *data.get(base + 2)?;
    let b3 = *data.get(base + 3)?;
    Some((b0 as u32) | ((b1 as u32) << 8) | ((b2 as u32) << 16) | ((b3 as u32) << 24))
}

/// Write the element count as four little-endian bytes.
pub fn vec_len() {
    let data = read_all();
    write(&(data.len() as u32).to_le_bytes());
}

/// Write the last byte, or nothing when the input is empty.
pub fn vec_pop() {
    let mut data = read_all();
    match data.pop() {
        Some(byte) => write(&[byte]),
        None => {}
    }
}

/// Byte 0 selects an index into the remaining bytes. Write that element, or
/// nothing when the index is out of bounds.
pub fn vec_get() {
    let data = read_all();
    let index = match data.get(0) {
        Some(&index) => index as usize,
        None => return,
    };
    match data.get(index + 1) {
        Some(&byte) => write(&[byte]),
        None => {}
    }
}

/// Byte 0 is the needle, the remaining bytes are the haystack. Write 1 when
/// the needle occurs, 0 when it does not, nothing on empty input.
pub fn vec_contains() {
    let data = read_all();
    let needle = match data.get(0) {
        Some(&needle) => needle,
        None => return,
    };
    let rest = match data.get(1..) {
        Some(rest) => rest,
        None => return,
    };
    write(&[rest.contains(&needle) as u8]);
}

/// Parse a length-prefixed list of little-endian `u32` words and write their
/// wrapping sum. A header that disagrees with the payload writes nothing.
pub fn vec_sum32() {
    let data = read_all();
    let count = match le_u32_at(&data, 0) {
        Some(count) => count as usize,
        None => return,
    };
    if data.len() < 4 || (data.len() - 4) % 4 != 0 {
        return;
    }
    let available = (data.len() - 4) / 4;
    if available != count {
        return;
    }

    let mut words: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < available {
        match le_u32_at(&data, 4 + i * 4) {
            Some(word) => words.push(word),
            None => return,
        }
        i += 1;
    }

    let mut sum = 0u32;
    let mut j = 0usize;
    while j < words.len() {
        match words.get(j) {
            Some(&word) => sum = sum.wrapping_add(word),
            None => return,
        }
        j += 1;
    }
    write(&sum.to_le_bytes());
}
