#![allow(improper_ctypes_definitions)]

mod exports;

/// Inline `len` use followed by arithmetic.
pub fn len_plus_one<T>(xs: &[T]) -> usize {
    xs.len() + 1
}

/// Inline `len` use combined with an independent argument.
pub fn len_plus_arg<T>(xs: &[T], n: usize) -> usize {
    xs.len() + n
}

/// `is_empty` use (lowered to a `call` at opt-0) followed by arithmetic.
pub fn empty_plus_three<T>(xs: &[T]) -> u32 {
    xs.is_empty() as u32 + 3
}

/// `is_empty` use (lowered to a `call` at opt-0) combined with an independent flag.
pub fn empty_xor_flag<T>(xs: &[T], flag: u32) -> u32 {
    (xs.is_empty() as u32) ^ flag
}
