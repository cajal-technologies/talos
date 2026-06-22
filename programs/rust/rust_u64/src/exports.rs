//! u64 std corpus. One `#[unsafe(no_mangle)] pub extern "C"` wrapper per std
//! function (each is its own root export, never dead-code-eliminated).

// ── Other scalar arithmetic ────────────────────────────────────────────────
#[unsafe(no_mangle)]
pub extern "C" fn abs_diff(a: u64, b: u64) -> u64 {
    a.abs_diff(b)
}

// ── Operators (add .. shr) ─────────────────────────────────────────────────
#[unsafe(no_mangle)]
pub extern "C" fn add(a: u64, b: u64) -> u64 {
    a + b
}

#[unsafe(no_mangle)]
pub extern "C" fn sub(a: u64, b: u64) -> u64 {
    a - b
}

#[unsafe(no_mangle)]
pub extern "C" fn mul(a: u64, b: u64) -> u64 {
    a * b
}

#[unsafe(no_mangle)]
pub extern "C" fn div(a: u64, b: u64) -> u64 {
    a / b
}

#[unsafe(no_mangle)]
pub extern "C" fn rem(a: u64, b: u64) -> u64 {
    a % b
}

#[unsafe(no_mangle)]
pub extern "C" fn bitand(a: u64, b: u64) -> u64 {
    a & b
}

#[unsafe(no_mangle)]
pub extern "C" fn bitor(a: u64, b: u64) -> u64 {
    a | b
}

#[unsafe(no_mangle)]
pub extern "C" fn bitxor(a: u64, b: u64) -> u64 {
    a ^ b
}

#[unsafe(no_mangle)]
pub extern "C" fn not(a: u64) -> u64 {
    !a
}

#[unsafe(no_mangle)]
pub extern "C" fn shl(a: u64, b: u32) -> u64 {
    a << b
}

#[unsafe(no_mangle)]
pub extern "C" fn shr(a: u64, b: u32) -> u64 {
    a >> b
}

// ── Comparisons (eq .. ge) ─────────────────────────────────────────────────
#[unsafe(no_mangle)]
pub extern "C" fn eq(a: u64, b: u64) -> bool {
    a == b
}

#[unsafe(no_mangle)]
pub extern "C" fn ne(a: u64, b: u64) -> bool {
    a != b
}

#[unsafe(no_mangle)]
pub extern "C" fn lt(a: u64, b: u64) -> bool {
    a < b
}

#[unsafe(no_mangle)]
pub extern "C" fn le(a: u64, b: u64) -> bool {
    a <= b
}

#[unsafe(no_mangle)]
pub extern "C" fn gt(a: u64, b: u64) -> bool {
    a > b
}

#[unsafe(no_mangle)]
pub extern "C" fn ge(a: u64, b: u64) -> bool {
    a >= b
}


#[unsafe(no_mangle)]
pub extern "C" fn entrypoint(a: u64, b: u64, n: u32) {
    let _ = abs_diff(a, b);
    let _ = add(a, b);
    let _ = sub(a, b);
    let _ = mul(a, b);
    let _ = div(a, b);
    let _ = rem(a, b);
    let _ = bitand(a, b);
    let _ = bitor(a, b);
    let _ = bitxor(a, b);
    let _ = not(a);
    let _ = shl(a, n);
    let _ = shr(a, n);
}
