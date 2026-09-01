mod exports;

use talos_stdio::{read, write};

/// Read two bytes, XOR them, and write the one-byte result.
/// Incomplete input produces no output.
pub fn xor() {
    let mut input = Box::new([0; 2]);
    let mut filled = 0;

    while filled < input.len() {
        let count = read(&mut input[filled..]);
        if count == 0 {
            return;
        }
        filled += count;
    }

    write(&[input[0] ^ input[1]]);
}
