//! Independent implementation pinned in Cargo.lock. Only its unsigned LEB128
//! codec is used; signed LEB128 has a different wire format from ZigZag varints.
use verified_varint::*;
fn check(value: u64) {
    let mut external = Vec::new();
    leb128::write::unsigned(&mut external, value).unwrap();
    assert_eq!(encode_u64(value).as_bytes(), external);
    let mut input = external.as_slice();
    assert_eq!(leb128::read::unsigned(&mut input).unwrap(), value);
    assert!(input.is_empty());
    assert_eq!(
        decode_u64(&external, DecodePolicy::Canonical)
            .unwrap()
            .value,
        value
    );
    if let Ok(v) = u32::try_from(value) {
        assert_eq!(encode_u32(v).as_bytes(), external);
        assert_eq!(
            decode_u32(&external, DecodePolicy::Canonical)
                .unwrap()
                .value,
            v
        );
    }
}
#[test]
fn independent_unsigned_leb128_and_small_widths() {
    for value in 0..=u16::MAX {
        check(u64::from(value));
    }
    let mut seed = 0x1eb1_2800_0205_0001u64;
    for _ in 0..16_384 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        check(seed);
        // Independently map signed bit patterns using widened arithmetic.
        let signed = seed as i64;
        let zz = if signed < 0 {
            (-2 * i128::from(signed) - 1) as u64
        } else {
            (2 * i128::from(signed)) as u64
        };
        let mut external = Vec::new();
        leb128::write::unsigned(&mut external, zz).unwrap();
        assert_eq!(encode_i64(signed).as_bytes(), external);
        let signed32 = seed as i32;
        let zz32 = if signed32 < 0 {
            (-2 * i64::from(signed32) - 1) as u64
        } else {
            (2 * i64::from(signed32)) as u64
        };
        external.clear();
        leb128::write::unsigned(&mut external, zz32).unwrap();
        assert_eq!(encode_i32(signed32).as_bytes(), external);
    }
}
#[test]
fn external_policy_differences_do_not_change_the_contract() {
    let redundant = [0x80, 0x00];
    assert_eq!(
        leb128::read::unsigned(&mut redundant.as_slice()).unwrap(),
        0
    );
    assert_eq!(
        decode_u64(&redundant, DecodePolicy::Canonical)
            .unwrap_err()
            .kind,
        DecodeErrorKind::NonCanonical
    );
    assert_eq!(
        decode_u64(&redundant, DecodePolicy::BoundedNonCanonical)
            .unwrap()
            .value,
        0
    );
    let beyond32 = [0x80, 0x80, 0x80, 0x80, 0x10];
    assert_eq!(
        leb128::read::unsigned(&mut beyond32.as_slice()).unwrap(),
        1u64 << 32
    );
    assert_eq!(
        decode_u32(&beyond32, DecodePolicy::BoundedNonCanonical)
            .unwrap_err()
            .kind,
        DecodeErrorKind::Overflow
    );
}
