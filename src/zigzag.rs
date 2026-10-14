/// Map a signed 64-bit integer to its unsigned ZigZag code.
/// Signed minima are handled without negating or taking their absolute value.
#[inline]
pub const fn zigzag_i64_to_u64(n: i64) -> u64 {
    ((n as u64) << 1) ^ ((n >> 63) as u64)
}

/// Invert a 64-bit ZigZag code, including `u64::MAX`.
#[inline]
pub const fn zigzag_u64_to_i64(u: u64) -> i64 {
    ((u >> 1) as i64) ^ -((u & 1) as i64)
}
/// Map a signed 32-bit integer to its unsigned ZigZag code.
#[inline]
pub const fn zigzag_i32_to_u32(n: i32) -> u32 {
    zigzag_i64_to_u64(n as i64) as u32
}

/// Invert a 32-bit ZigZag code.
#[inline]
pub const fn zigzag_u32_to_i32(u: u32) -> i32 {
    zigzag_u64_to_i64(u as u64) as i32
}
