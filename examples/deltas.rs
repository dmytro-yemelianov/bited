//! Encode small signed changes instead of repeatedly storing large positions.
use bited::{decode_i64, encode_i64_into, DecodePolicy};

fn main() {
    let positions = [1_000i64, 1_002, 999, 1_003];
    let mut bytes = [0u8; 40];
    let mut used = 0;
    let mut previous = 0i64;
    for value in positions {
        let delta = value.checked_sub(previous).unwrap();
        used += encode_i64_into(delta, &mut bytes[used..]).unwrap();
        previous = value;
    }
    let mut offset = 0;
    let mut restored = 0i64;
    for expected in positions {
        let decoded = decode_i64(&bytes[offset..used], DecodePolicy::Canonical).unwrap();
        restored = restored.checked_add(decoded.value).unwrap();
        assert_eq!(restored, expected);
        offset += decoded.consumed;
    }
    assert_eq!(offset, used);
    println!("{} positions in {used} bytes", positions.len());
}
