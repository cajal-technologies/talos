#![allow(improper_ctypes_definitions)]

mod exports;

/// Primitive slice length operation for `&[T]`.
pub fn len<T>(xs: &[T]) -> usize {
    xs.len()
}

/// Primitive slice emptiness operation for `&[T]`.
pub fn is_empty<T>(xs: &[T]) -> bool {
    xs.is_empty()
}
