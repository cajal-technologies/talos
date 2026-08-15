use std::io::{BufRead, Write};
use talos_stdio::ExtIO;

#[unsafe(no_mangle)]
pub extern "C" fn mergesort() {
    let (mut reader, mut writer) = ExtIO::buffered();

    let mut string = String::new();
    reader.read_line(&mut string).unwrap();
    let mut list = string
        .split(' ')
        .map(|x| x.parse::<u64>().unwrap())
        .collect::<Vec<u64>>();

    let mut sratch = vec![0; list.len()];
    crate::mergesort(&mut list, &mut sratch);

    let mut first = true;
    for item in list {
        if first {
            first = false;
        } else {
            write!(writer, " ").unwrap();
        }
        write!(writer, "{}", item).unwrap();
    }
}
