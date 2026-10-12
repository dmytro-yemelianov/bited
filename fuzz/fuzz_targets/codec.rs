#![no_main]
use libfuzzer_sys::fuzz_target;
use bited::*;

// A separate widened arithmetic oracle, never the encoder under test.
fn oracle(bytes: &[u8], width: usize, policy: DecodePolicy) -> Result<Decoded<u64>, DecodeError> {
    let limit = width.div_ceil(7);
    let last_max = if width == 32 { 15 } else { 1 };
    let mut value = 0u128;
    for (index, &byte) in bytes.iter().take(limit).enumerate() {
        let consumed = index + 1;
        let error = |kind| Err(DecodeError { kind, consumed });
        let payload = byte % 128;
        if consumed == limit && payload > last_max {
            return error(DecodeErrorKind::Overflow);
        }
        if consumed == limit && byte >= 128 {
            return error(DecodeErrorKind::TooLong);
        }
        value += u128::from(payload) * 128u128.pow(index as u32);
        if byte < 128 {
            let canonical = index == 0 || payload != 0;
            if !canonical && policy == DecodePolicy::Canonical {
                return error(DecodeErrorKind::NonCanonical);
            }
            return Ok(Decoded {
                value: value as u64,
                consumed,
                canonical,
            });
        }
    }
    Err(DecodeError {
        kind: DecodeErrorKind::Truncated,
        consumed: bytes.len().min(limit),
    })
}
fn cast32(result: Result<Decoded<u64>, DecodeError>) -> Result<Decoded<u32>, DecodeError> {
    result.map(|d| Decoded {
        value: d.value as u32,
        consumed: d.consumed,
        canonical: d.canonical,
    })
}
fuzz_target!(|input: &[u8]| {
    for policy in [DecodePolicy::Canonical, DecodePolicy::BoundedNonCanonical] {
        assert_eq!(decode_u64(input, policy), oracle(input, 64, policy));
        assert_eq!(decode_u32(input, policy), cast32(oracle(input, 32, policy)));
        // Operation grammar includes pushes, finish, reset and changed policy.
        let mut d64 = DecoderU64::new(policy);
        let mut d32 = DecoderU32::new(policy);
        let mut bytes = Vec::new();
        let mut sealed64 = None;
        let mut sealed32 = None;
        let mut selected = policy;
        for pair in input.chunks(2) {
            let value = pair.get(1).copied().unwrap_or(0);
            match pair[0] % 4 {
                0 => {
                    selected = if value & 1 == 0 {
                        DecodePolicy::Canonical
                    } else {
                        DecodePolicy::BoundedNonCanonical
                    };
                    d64.reset(selected);
                    d32.reset(selected);
                    bytes.clear();
                    sealed64 = None;
                    sealed32 = None;
                    assert_eq!((d64.bytes_seen(), d32.bytes_seen()), (0, 0));
                }
                1 => {
                    let expected64 = sealed64.unwrap_or_else(|| oracle(&bytes, 64, selected));
                    let expected32 =
                        sealed32.unwrap_or_else(|| cast32(oracle(&bytes, 32, selected)));
                    assert_eq!(d64.finish(), expected64);
                    assert_eq!(d32.finish(), expected32);
                    sealed64 = Some(expected64);
                    sealed32 = Some(expected32);
                }
                _ => {
                    bytes.push(value);
                    let actual64 = d64.push(value);
                    let actual32 = d32.push(value);
                    macro_rules! check {
                        ($actual:expr,$sealed:ident,$expected:expr) => {
                            if $sealed.is_some() {
                                assert_eq!($actual, Step::Closed);
                            } else {
                                match $expected {
                                    Ok(d) => {
                                        assert_eq!($actual, Step::Done(d));
                                        $sealed = Some(Ok(d));
                                    }
                                    Err(e) if e.kind == DecodeErrorKind::Truncated => {
                                        assert_eq!($actual, Step::NeedMore)
                                    }
                                    Err(e) => {
                                        assert_eq!($actual, Step::Error(e));
                                        $sealed = Some(Err(e));
                                    }
                                }
                            }
                        };
                    }
                    check!(actual64, sealed64, oracle(&bytes, 64, selected));
                    check!(actual32, sealed32, cast32(oracle(&bytes, 32, selected)));
                }
            }
        }
    }
    let mut bits = [0u8; 8];
    for (dst, src) in bits.iter_mut().zip(input) {
        *dst = *src;
    }
    let value = u64::from_le_bytes(bits);
    assert_eq!(
        zigzag_u64_to_i64(zigzag_i64_to_u64(value as i64)),
        value as i64
    );
    assert_eq!(
        zigzag_u32_to_i32(zigzag_i32_to_u32(value as i32)),
        value as i32
    );
    let capacity = input.last().copied().unwrap_or(0) as usize % 13;
    fn zigzag(n: i64) -> u64 {
        if n < 0 {
            (-2 * i128::from(n) - 1) as u64
        } else {
            (2 * i128::from(n)) as u64
        }
    }
    macro_rules! check_buffer {
        ($function:ident, $value:expr, $expected:expr, $width:expr) => {{
            let mut out = [0xa5; 12];
            let original = out;
            match $function($value, &mut out[..capacity]) {
                Err(e) => {
                    assert_eq!(out, original);
                    assert!(e.required > e.available);
                    assert_eq!(e.available, capacity);
                }
                Ok(len) => {
                    assert_eq!(&out[len..], &original[len..]);
                    let expected: u64 = $expected;
                    let decoded = oracle(&out[..len], $width, DecodePolicy::Canonical).unwrap();
                    assert_eq!(decoded.value, expected);
                    assert_eq!(decoded.consumed, len);
                    assert!(decoded.canonical);
                }
            }
        }};
    }
    check_buffer!(encode_u64_into, value, value, 64);
    check_buffer!(encode_u32_into, value as u32, u64::from(value as u32), 32);
    check_buffer!(encode_i64_into, value as i64, zigzag(value as i64), 64);
    check_buffer!(
        encode_i32_into,
        value as i32,
        zigzag(i64::from(value as i32)),
        32
    );
});
