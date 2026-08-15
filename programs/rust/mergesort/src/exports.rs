//! Verification-oriented standard-I/O entry point for merge sort.

/// The public proof admits inputs containing at most this many values.
pub const MAX_VALUES: usize = 4096;

/// Packed little-endian bytes occupied by the value buffer.
pub const BUFFER_BYTES: usize = core::mem::size_of::<u64>() * MAX_VALUES;

use talos_stdio::{read_raw, write_raw};

static mut WORK: [u64; 2 * MAX_VALUES] = [0; 2 * MAX_VALUES];

/// Read packed little-endian `u64` values, sort them, and write the same byte
/// region back. The public contract supplies a whole number of words.
#[unsafe(no_mangle)]
pub extern "C" fn mergesort() {
    let work = &raw mut WORK;
    let values = unsafe { (*work).as_mut_ptr() };
    let byte_length = unsafe { read_raw(values.cast::<u8>(), BUFFER_BYTES) };
    let count = byte_length >> 3;
    let scratch = unsafe { values.add(count) };

    unsafe {
        crate::mergesort_raw(values, count, scratch);
        write_raw(values.cast::<u8>(), byte_length);
    }
}

#[cfg(test)]
mod tests {
    use super::{BUFFER_BYTES, MAX_VALUES};

    #[test]
    fn buffer_holds_every_admitted_value() {
        assert_eq!(BUFFER_BYTES, 8 * MAX_VALUES);
    }
}
