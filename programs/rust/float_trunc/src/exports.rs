fn naive_trunc(x: f32) -> i32 {
    if x != x {
        0
    } else if x >= 2147483648.0f32 {
        i32::MAX
    } else if x < -2147483648.0f32 {
        i32::MIN
    } else {
        x as i32
    }
}

fn sat_trunc(x: f32) -> i32 {
    x as i32
}

#[unsafe(no_mangle)]
pub extern "C" fn check(x: f32) {
    if naive_trunc(x) != sat_trunc(x) {
        unreachable!()
    }
}
