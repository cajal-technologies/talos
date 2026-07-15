/// f32.abs via the instruction
fn abs_native(x: f32) -> f32 {
    x.abs()
}

/// f32.abs via bit manipulation (reinterpret + mask + reinterpret)
fn abs_bits(x: f32) -> f32 {
    f32::from_bits(x.to_bits() & 0x7FFFFFFF)
}

/// f32.abs via promote-abs-demote
fn abs_promote(x: f32) -> f32 {
    ((x as f64).abs()) as f32
}

/// copysign via instruction
fn copysign_native(x: f32, y: f32) -> f32 {
    x.copysign(y)
}

/// copysign via bit manipulation
fn copysign_bits(x: f32, y: f32) -> f32 {
    let sign = y.to_bits() & 0x80000000;
    let mag = x.to_bits() & 0x7FFFFFFF;
    f32::from_bits(sign | mag)
}

#[unsafe(no_mangle)]
pub extern "C" fn check_abs(x: f32) -> i32 {
    if abs_native(x) == abs_bits(x) && abs_native(x) == abs_promote(x) { 1 } else { 0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn check_copysign(x: f32, y: f32) -> i32 {
    if copysign_native(x, y) == copysign_bits(x, y) { 1 } else { 0 }
}
