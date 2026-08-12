//! Rust I/O adapters for the host functions provided to Talos Wasm programs.

use std::io::{BufReader, BufWriter, Read, Write};

mod sys {
    #[link(wasm_import_module = "stdio")]
    unsafe extern "C" {
        pub fn read(buf: *mut u8, count: usize) -> usize;
        pub fn write(buf: *const u8, count: usize);
    }
}

fn read(buf: &mut [u8]) -> usize {
    unsafe { sys::read(buf.as_mut_ptr(), buf.len()) }
}

fn write(buf: &[u8]) {
    unsafe { sys::write(buf.as_ptr(), buf.len()) }
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
