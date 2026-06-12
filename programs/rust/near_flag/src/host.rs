//! Raw NEAR host-function bindings, matching the `nearcore` runtime
//! ABI. The crate deliberately avoids `near-sdk` so the compiled wasm
//! stays small enough to verify symbolically end to end.

#[link(wasm_import_module = "env")]
unsafe extern "C" {
    pub fn log_utf8(len: u64, ptr: u64);
    pub fn storage_write(
        key_len: u64,
        key_ptr: u64,
        value_len: u64,
        value_ptr: u64,
        register_id: u64,
    ) -> u64;
}
