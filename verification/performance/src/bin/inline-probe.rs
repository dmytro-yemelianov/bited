//! Codegen probe: the public u64 decoder fast path must inline into a downstream loop.
use bited::{decode_u64, DecodePolicy};
use std::hint::black_box;

#[inline(never)]
fn probe_decode_u64(bytes: &[u8]) -> u64 {
    let mut offset = 0;
    let mut sum = 0u64;
    while offset < bytes.len() {
        let decoded = decode_u64(black_box(&bytes[offset..]), DecodePolicy::Canonical).unwrap();
        sum = sum.wrapping_add(decoded.value);
        offset += decoded.consumed;
    }
    sum
}

fn main() {
    // One-, two- and ten-byte values so both the fast path and the scan are reachable.
    let mut bytes = vec![0x01, 0x81, 0x01];
    bytes.extend_from_slice(&[0xff; 9]);
    bytes.push(0x01);
    println!("{}", probe_decode_u64(black_box(&bytes)));
}
