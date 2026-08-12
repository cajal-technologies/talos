use std::io::{BufReader, BufWriter, Read, Write};

mod sys {
    unsafe extern "C" {
        pub fn read(buf: *mut u8, count: usize) -> usize;
        pub fn write(buf: *const u8, count: usize);
    }
}

pub fn read(buf: &mut [u8], count: usize) -> usize {
    unsafe { sys::read(buf.as_mut_ptr(), count) }
}

pub fn write(buf: &[u8]) {
    unsafe { sys::write(buf.as_ptr(), buf.len()) }
}

// External interface for reading and writing using methods provided by the host
pub struct ExtIO {}

impl ExtIO {
    pub fn new() -> Self {
        ExtIO {}
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
        let count = read(buf, buf.len());
        Ok(count)
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
