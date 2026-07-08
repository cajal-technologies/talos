mod exports;

/// Byte width of the little-endian `u32` length prefix of a frame.
pub const LEN_PREFIX: usize = 4;

/// Encode `src` as a length-prefixed frame in `dst`: a 4-byte little-endian
/// length followed by the payload bytes. Returns the number of bytes written
/// (`LEN_PREFIX + src.len()`). The caller guarantees `dst` has room.
pub fn encode(src: &[u8], dst: &mut [u8]) -> usize {
    let n = src.len();
    dst[..LEN_PREFIX].copy_from_slice(&(n as u32).to_le_bytes());
    dst[LEN_PREFIX..LEN_PREFIX + n].copy_from_slice(src);
    LEN_PREFIX + n
}

/// Decode a length-prefixed frame from `src`, copying the payload into `dst`.
/// Returns the payload length, or a negative status: `-1` no length prefix,
/// `-2` payload truncated, `-3` `dst` too small.
pub fn decode(src: &[u8], dst: &mut [u8]) -> i64 {
    if src.len() < LEN_PREFIX {
        return -1;
    }

    let n = u32::from_le_bytes([src[0], src[1], src[2], src[3]]) as usize;

    if LEN_PREFIX + n > src.len() {
        return -2;
    }
    if n > dst.len() {
        return -3;
    }

    dst[..n].copy_from_slice(&src[LEN_PREFIX..LEN_PREFIX + n]);
    n as i64
}
