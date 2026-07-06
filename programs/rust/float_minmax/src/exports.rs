fn naive_min(arr: &[f32]) -> f32 {
    let mut m = arr[0];
    let mut i = 1;
    while i < arr.len() {
        if arr[i] < m {
            m = arr[i];
        }
        i += 1;
    }
    m
}

fn opt_min(arr: &[f32]) -> f32 {
    let mut m = arr[0];
    let mut i = 1;
    while i < arr.len() {
        m = m.min(arr[i]);
        i += 1;
    }
    m
}

fn naive_max(arr: &[f32]) -> f32 {
    let mut m = arr[0];
    let mut i = 1;
    while i < arr.len() {
        if arr[i] > m {
            m = arr[i];
        }
        i += 1;
    }
    m
}

fn opt_max(arr: &[f32]) -> f32 {
    let mut m = arr[0];
    let mut i = 1;
    while i < arr.len() {
        m = m.max(arr[i]);
        i += 1;
    }
    m
}

#[unsafe(no_mangle)]
pub extern "C" fn check_min(arr: *const f32, len: usize) -> i32 {
    let s = unsafe { core::slice::from_raw_parts(arr, len) };
    if naive_min(s) == opt_min(s) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn check_max(arr: *const f32, len: usize) -> i32 {
    let s = unsafe { core::slice::from_raw_parts(arr, len) };
    if naive_max(s) == opt_max(s) { 1 } else { 0 }
}