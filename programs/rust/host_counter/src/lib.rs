mod exports;

#[link(wasm_import_module = "env")]
unsafe extern "C" {
    fn host_inc();
    fn host_get() -> u32;
}

/// Guarded host-counter step.
///
/// Reads the host counter via `host_get`; if it is strictly less than
/// `10`, calls `host_inc` to bump it by one. The invariant
/// `counter ≤ 10` is therefore preserved across any number of calls.
pub fn step() {
    unsafe {
        if host_get() < 10 {
            host_inc();
        }
    }
}
