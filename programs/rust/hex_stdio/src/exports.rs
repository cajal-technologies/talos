use std::io::{Read, Write};
use talos_stdio::ExtIO;

pub(super) fn read_all() -> Vec<u8> {
    let mut input = Vec::new();
    ExtIO::new().read_to_end(&mut input).unwrap();
    input
}

pub(super) fn write_all(output: &[u8]) {
    ExtIO::new().write_all(output).unwrap();
}

#[unsafe(no_mangle)]
pub extern "C" fn encode() {
    crate::encode();
}

#[unsafe(no_mangle)]
pub extern "C" fn decode() {
    crate::decode();
}
