//! Typed adapters around the unsigned codec and ZigZag bijection.
use crate::*;

/// Exact length of the ZigZag representation of an i32, including zero.
pub const fn encoded_len_i32(value: i32) -> usize {
    encoded_len_u32(zigzag_i32_to_u32(value))
}
/// Exact length of the ZigZag representation of an i64, including zero.
pub const fn encoded_len_i64(value: i64) -> usize {
    encoded_len_u64(zigzag_i64_to_u64(value))
}
/// Encode an i32 with ZigZag into initialized fixed storage.
pub fn encode_i32(value: i32) -> Encoded32 {
    encode_u32(zigzag_i32_to_u32(value))
}
/// Encode an i64 with ZigZag into initialized fixed storage.
pub fn encode_i64(value: i64) -> Encoded64 {
    encode_u64(zigzag_i64_to_u64(value))
}
/// Write an i32 ZigZag prefix; preserve the suffix and the whole buffer on insufficient capacity.
pub fn encode_i32_into(value: i32, out: &mut [u8]) -> Result<usize, EncodeError> {
    encode_u32_into(zigzag_i32_to_u32(value), out)
}
/// Write an i64 ZigZag prefix; preserve the suffix and the whole buffer on insufficient capacity.
pub fn encode_i64_into(value: i64, out: &mut [u8]) -> Result<usize, EncodeError> {
    encode_u64_into(zigzag_i64_to_u64(value), out)
}
/// Decode one ZigZag i32 prefix under the selected policy.
pub fn decode_i32(input: &[u8], policy: DecodePolicy) -> Result<Decoded<i32>, DecodeError> {
    match decode_u32(input, policy) {
        Ok(d) => Ok(Decoded {
            value: zigzag_u32_to_i32(d.value),
            consumed: d.consumed,
            canonical: d.canonical,
        }),
        Err(e) => Err(e),
    }
}
/// Decode one ZigZag i64 prefix under the selected policy.
pub fn decode_i64(input: &[u8], policy: DecodePolicy) -> Result<Decoded<i64>, DecodeError> {
    match decode_u64(input, policy) {
        Ok(d) => Ok(Decoded {
            value: zigzag_u64_to_i64(d.value),
            consumed: d.consumed,
            canonical: d.canonical,
        }),
        Err(e) => Err(e),
    }
}

fn exact<T>(
    result: Result<Decoded<T>, DecodeError>,
    length: usize,
) -> Result<Decoded<T>, DecodeError> {
    match result {
        Ok(d) => {
            if d.consumed != length {
                Err(DecodeError {
                    kind: DecodeErrorKind::TrailingBytes,
                    consumed: d.consumed,
                })
            } else {
                Ok(d)
            }
        }
        Err(e) => Err(e),
    }
}
/// Decode one unsigned u32 and reject any trailing bytes.
pub fn decode_u32_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u32>, DecodeError> {
    exact(decode_u32(input, policy), input.len())
}
/// Decode one unsigned u64 and reject any trailing bytes.
pub fn decode_u64_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u64>, DecodeError> {
    exact(decode_u64(input, policy), input.len())
}
/// Decode one ZigZag i32 and reject any trailing bytes.
pub fn decode_i32_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<i32>, DecodeError> {
    exact(decode_i32(input, policy), input.len())
}
/// Decode one ZigZag i64 and reject any trailing bytes.
pub fn decode_i64_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<i64>, DecodeError> {
    exact(decode_i64(input, policy), input.len())
}
