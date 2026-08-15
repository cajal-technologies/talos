//! Rust I/O adapters for the host functions provided to Talos Wasm programs.

use std::io::{BufReader, BufWriter, Read, Write};

mod sys {
    #[link(wasm_import_module = "stdio")]
    unsafe extern "C" {
        pub fn read(buf: *mut u8, count: usize) -> usize;
        pub fn write(buf: *const u8, count: usize);
    }
}

/// Invoke the canonical `stdio.read` import without constructing an
/// intermediate Rust slice.
///
/// # Safety
///
/// `buf` must be writable for `count` bytes.
pub unsafe fn read_raw(buf: *mut u8, count: usize) -> usize {
    unsafe { sys::read(buf, count) }
}

/// Invoke the canonical `stdio.write` import without constructing an
/// intermediate Rust slice.
///
/// # Safety
///
/// `buf` must be readable for `count` bytes.
pub unsafe fn write_raw(buf: *const u8, count: usize) {
    unsafe { sys::write(buf, count) }
}

fn read(buf: &mut [u8]) -> usize {
    unsafe { read_raw(buf.as_mut_ptr(), buf.len()) }
}

fn write(buf: &[u8]) {
    unsafe { write_raw(buf.as_ptr(), buf.len()) }
}

/// An unbuffered byte stream backed by Talos host imports.
pub struct ExtIO;

impl ExtIO {
    pub fn new() -> Self {
        Self
    }

    pub fn buffered() -> (BufReader<Self>, BufWriter<Self>) {
        let reader = BufReader::new(Self::new());
        let writer = BufWriter::new(Self::new());
        (reader, writer)
    }
}

impl Default for ExtIO {
    fn default() -> Self {
        Self::new()
    }
}

impl Read for ExtIO {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        Ok(read(buf))
    }
}

impl Write for ExtIO {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        write(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}
