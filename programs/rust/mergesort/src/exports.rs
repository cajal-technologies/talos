use talos_stdio::{read, write};

#[unsafe(no_mangle)]
pub extern "C" fn mergesort() {
    let mut input = Vec::new();
    let mut chunk = [0; 256];
    loop {
        let count = read(&mut chunk);
        if count == 0 {
            break;
        }
        input.extend_from_slice(&chunk[..count]);
    }

    let chunks = input.chunks_exact(4);
    if !chunks.remainder().is_empty() {
        return;
    }
    let mut values = chunks
        .map(|bytes| u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
        .collect::<Vec<_>>();

    let mut scratch = vec![0; values.len()];
    crate::mergesort(&mut values, &mut scratch);

    for value in values {
        write(&value.to_le_bytes());
    }
}
