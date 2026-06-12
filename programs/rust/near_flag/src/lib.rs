mod exports;
mod host;

/// Storage key written by `set_flag`.
pub const KEY: &[u8] = b"flag";
/// Value stored under [`KEY`].
pub const VALUE: &[u8] = &[1];
/// Log line emitted before the write.
pub const LOG_MSG: &[u8] = b"flag set";
