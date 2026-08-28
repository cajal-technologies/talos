mod exports;

use talos_stdio::{read, write};

/// Read one byte and echo it. Empty input produces empty output.
pub fn byte_echo() {
    let mut byte = Box::new([0]);
    if read(byte.as_mut_slice()) == 1 {
        write(byte.as_slice());
    }
}
