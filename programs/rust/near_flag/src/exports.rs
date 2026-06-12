/// Wasm-exported NEAR flag setter. The project convention reserves
/// this file for the wasm ABI surface; all unsafety lives here.
///
/// Logs [`crate::LOG_MSG`], then stores [`crate::VALUE`] under
/// [`crate::KEY`]. The output register id `u64::MAX` discards any
/// evicted previous value, per the NEAR host convention.
#[unsafe(no_mangle)]
pub extern "C" fn set_flag() {
    unsafe {
        crate::host::log_utf8(crate::LOG_MSG.len() as u64, crate::LOG_MSG.as_ptr() as u64);
        crate::host::storage_write(
            crate::KEY.len() as u64,
            crate::KEY.as_ptr() as u64,
            crate::VALUE.len() as u64,
            crate::VALUE.as_ptr() as u64,
            u64::MAX,
        );
    }
}
