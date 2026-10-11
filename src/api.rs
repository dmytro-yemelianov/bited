//! Typed adapters around the unsigned codec and ZigZag bijection.
use crate::*;

pub const fn encoded_len_i32(value: i32) -> usize {
    encoded_len_u32(zigzag_i32_to_u32(value))
}
pub const fn encoded_len_i64(value: i64) -> usize {
    encoded_len_u64(zigzag_i64_to_u64(value))
}
pub fn encode_i32(value: i32) -> Encoded32 {
    encode_u32(zigzag_i32_to_u32(value))
}
pub fn encode_i64(value: i64) -> Encoded64 {
    encode_u64(zigzag_i64_to_u64(value))
}
pub fn encode_i32_into(value: i32, out: &mut [u8]) -> Result<usize, EncodeError> {
    encode_u32_into(zigzag_i32_to_u32(value), out)
}
pub fn encode_i64_into(value: i64, out: &mut [u8]) -> Result<usize, EncodeError> {
    encode_u64_into(zigzag_i64_to_u64(value), out)
}
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
pub fn decode_u32_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u32>, DecodeError> {
    exact(decode_u32(input, policy), input.len())
}
pub fn decode_u64_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u64>, DecodeError> {
    exact(decode_u64(input, policy), input.len())
}
pub fn decode_i32_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<i32>, DecodeError> {
    exact(decode_i32(input, policy), input.len())
}
pub fn decode_i64_exact(input: &[u8], policy: DecodePolicy) -> Result<Decoded<i64>, DecodeError> {
    exact(decode_i64(input, policy), input.len())
}
