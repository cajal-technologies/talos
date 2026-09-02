//! `Vec` access patterns over the Talos stdio byte stream.
//!
//! Every export reads one [borsh](https://borsh.io/) value from standard input,
//! applies one operation, and writes one borsh value back. An export that
//! changes the vector writes the changed vector (`vec_push`). An export that
//! also produces an element writes the element beside the remaining vector
//! (`vec_pop`). An export that only observes writes the observation alone.
//! Tuple inputs carry the scalar first: a borsh tuple has no framing, and a
//! fixed-width first field lets the reader split at byte four.
//!
//! `borsh::from_slice` rejects trailing bytes, so each export accepts exactly
//! one encoded value and writes nothing otherwise. Empty input is rejected
//! too: borsh encodes an empty vector as four zero bytes. Nothing here indexes
//! with `[]`, so no index panic is compiled into the module.

mod exports;

use talos_stdio::{read, write};

/// Read the whole input stream, one `push` per byte. `take` saturates if the
/// host ever reports more than the buffer holds, and it keeps `[]` indexing
/// out of the crate.
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

/// Write one borsh value. `to_vec` cannot fail here: it writes into a
/// `Vec<u8>`, whose `Write` is infallible, and its one error path, a length
/// above `u32::MAX`, is unreachable on wasm32. The `if let` keeps a panic path
/// out of the module.
fn reply<T: borsh::BorshSerialize>(value: &T) {
    if let Ok(output) = borsh::to_vec(value) {
        write(&output);
    }
}

// Each kernel below stays out of line so that it is its own wasm function,
// separate from the stream driver, the decoder, allocation, and host I/O.
// `vec_len` has no kernel: a `len` that returns its own argument is a call
// LLVM deletes whatever the inline attribute says.

/// `Vec::push`, taking and returning the vector so the export stays functional.
#[inline(never)]
fn push(mut values: Vec<u32>, value: u32) -> Vec<u32> {
    values.push(value);
    values
}

/// `Vec::pop`, returning the removed element beside the remaining vector.
#[inline(never)]
fn pop(mut values: Vec<u32>) -> (Option<u32>, Vec<u32>) {
    let element = values.pop();
    (element, values)
}

/// `<[T]>::get`, reached through `Vec`'s slice deref.
#[inline(never)]
fn get(values: &[u32], index: u32) -> Option<u32> {
    values.get(index as usize).copied()
}

/// `<[T]>::contains`, reached through `Vec`'s slice deref.
#[inline(never)]
fn contains(values: &[u32], needle: u32) -> bool {
    values.contains(&needle)
}

/// The wrapping sum of every element.
#[inline(never)]
fn sum32(values: &[u32]) -> u32 {
    values
        .iter()
        .fold(0u32, |acc, &value| acc.wrapping_add(value))
}

/// Write the element count as a borsh `u32`. The count came from a `u32`
/// header, so the cast is exact.
pub fn vec_len() {
    let Ok(values) = borsh::from_slice::<Vec<u32>>(&read_all()) else {
        return;
    };
    reply(&(values.len() as u32));
}

/// Append the leading element to the vector and write the result.
pub fn vec_push() {
    let Ok((value, values)) = borsh::from_slice::<(u32, Vec<u32>)>(&read_all()) else {
        return;
    };
    reply(&push(values, value));
}

/// Remove the last element and write it beside the remaining vector. On an
/// empty vector the element is `None`, which still writes its tag byte.
pub fn vec_pop() {
    let Ok(values) = borsh::from_slice::<Vec<u32>>(&read_all()) else {
        return;
    };
    reply(&pop(values));
}

/// Write the element under the leading index, or `None` when it is out of
/// bounds.
pub fn vec_get() {
    let Ok((index, values)) = borsh::from_slice::<(u32, Vec<u32>)>(&read_all()) else {
        return;
    };
    reply(&get(&values, index));
}

/// Write whether the leading element occurs in the vector.
pub fn vec_contains() {
    let Ok((needle, values)) = borsh::from_slice::<(u32, Vec<u32>)>(&read_all()) else {
        return;
    };
    reply(&contains(&values, needle));
}

/// Write the wrapping sum of every element.
pub fn vec_sum32() {
    let Ok(values) = borsh::from_slice::<Vec<u32>>(&read_all()) else {
        return;
    };
    reply(&sum32(&values));
}

#[cfg(test)]
mod tests {
    #[test]
    fn push_appends_at_the_end() {
        assert_eq!(super::push(Vec::new(), 7), vec![7]);
        assert_eq!(super::push(vec![1, 2], 3), vec![1, 2, 3]);
    }

    #[test]
    fn pop_returns_the_last_element_and_the_rest() {
        assert_eq!(super::pop(Vec::new()), (None, Vec::new()));
        assert_eq!(super::pop(vec![1, 2, 3]), (Some(3), vec![1, 2]));
    }

    #[test]
    fn get_is_none_out_of_bounds() {
        assert_eq!(super::get(&[4, 5, 6], 0), Some(4));
        assert_eq!(super::get(&[4, 5, 6], 2), Some(6));
        assert_eq!(super::get(&[4, 5, 6], 3), None);
        assert_eq!(super::get(&[], 0), None);
    }

    #[test]
    fn contains_finds_a_present_element() {
        assert!(super::contains(&[1, 2, 3], 2));
        assert!(!super::contains(&[1, 2, 3], 4));
        assert!(!super::contains(&[], 0));
    }

    #[test]
    fn sum32_wraps() {
        assert_eq!(super::sum32(&[]), 0);
        assert_eq!(super::sum32(&[1, 2, 3]), 6);
        assert_eq!(super::sum32(&[u32::MAX, 1]), 0);
    }

    /// The exact bytes that `CodeLib.RustStd.Borsh` states: a `u32` is four
    /// little-endian bytes, a `bool` is one byte, an `Option` is a tag byte,
    /// a `Vec` is a `u32` count then the elements, and a tuple has no framing.
    /// The last two assertions read a value back in the two shapes the exports
    /// accept.
    #[test]
    fn borsh_layout_matches_the_lean_model() {
        assert_eq!(borsh::to_vec(&258u32).unwrap(), [2, 1, 0, 0]);
        assert_eq!(borsh::to_vec(&true).unwrap(), [1]);
        assert_eq!(borsh::to_vec(&false).unwrap(), [0]);
        assert_eq!(borsh::to_vec(&Some(7u32)).unwrap(), [1, 7, 0, 0, 0]);
        assert_eq!(borsh::to_vec(&None::<u32>).unwrap(), [0]);
        assert_eq!(borsh::to_vec(&Vec::<u32>::new()).unwrap(), [0, 0, 0, 0]);
        assert_eq!(
            borsh::to_vec(&vec![1u32, 2]).unwrap(),
            [2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0]
        );
        assert_eq!(
            borsh::to_vec(&(None::<u32>, vec![1u32])).unwrap(),
            [0, 1, 0, 0, 0, 1, 0, 0, 0]
        );
        assert_eq!(
            borsh::from_slice::<Vec<u32>>(&[1, 0, 0, 0, 5, 0, 0, 0]).unwrap(),
            vec![5u32]
        );
        assert_eq!(
            borsh::from_slice::<(u32, Vec<u32>)>(&[7, 0, 0, 0, 1, 0, 0, 0, 9, 0, 0, 0]).unwrap(),
            (7u32, vec![9u32])
        );
    }

    /// `from_slice` rejects each input the spec's reader rejects: empty input,
    /// a short header, a trailing byte, a count that disagrees with the
    /// payload, and a tuple whose vector is missing.
    #[test]
    fn borsh_rejects_what_the_spec_rejects() {
        assert!(borsh::from_slice::<Vec<u32>>(&[]).is_err());
        assert!(borsh::from_slice::<Vec<u32>>(&[1, 0, 0]).is_err());
        assert!(borsh::from_slice::<Vec<u32>>(&[0, 0, 0, 0, 9]).is_err());
        assert!(borsh::from_slice::<Vec<u32>>(&[2, 0, 0, 0, 5, 0, 0, 0]).is_err());
        assert!(borsh::from_slice::<(u32, Vec<u32>)>(&[5, 0, 0, 0]).is_err());
    }
}
