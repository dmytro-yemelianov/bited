use verified_varint::*;

// Independent list/arithmetic oracle: collect the prefix, validate its shape,
// then sum in u128. It does not call the production encoder or decoder.
fn oracle_width(
    input: &[u8],
    policy: DecodePolicy,
    width: usize,
) -> Result<Decoded<u64>, DecodeError> {
    let limit = width.div_ceil(7);
    let last_max = (1u8 << (width - 7 * (limit - 1))) - 1;
    let prefix: Vec<_> = input.iter().take(limit).copied().collect();
    let terminal = prefix.iter().position(|b| *b < 128);
    let consumed = terminal.map_or(prefix.len(), |i| i + 1);
    let error = |kind| Err(DecodeError { kind, consumed });
    if consumed == limit && prefix[limit - 1] % 128 > last_max {
        return error(DecodeErrorKind::Overflow);
    }
    if consumed == limit && terminal.is_none() {
        return error(DecodeErrorKind::TooLong);
    }
    if terminal.is_none() {
        return error(DecodeErrorKind::Truncated);
    }
    let canonical = consumed == 1 || prefix[consumed - 1] % 128 != 0;
    if policy == DecodePolicy::Canonical && !canonical {
        return error(DecodeErrorKind::NonCanonical);
    }
    let value: u128 = prefix[..consumed]
        .iter()
        .enumerate()
        .map(|(i, b)| u128::from(b % 128) * 128u128.pow(i as u32))
        .sum();
    Ok(Decoded {
        value: u64::try_from(value).unwrap(),
        consumed,
        canonical,
    })
}

fn oracle(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u64>, DecodeError> {
    oracle_width(input, policy, 64)
}

fn compare(input: &[u8]) {
    for policy in [DecodePolicy::Canonical, DecodePolicy::BoundedNonCanonical] {
        let expected32 = oracle_width(input, policy, 32).map(|d| Decoded {
            value: d.value as u32,
            consumed: d.consumed,
            canonical: d.canonical,
        });
        assert_eq!(
            decode_u32(input, policy),
            expected32,
            "{input:x?}, {policy:?}"
        );
        macro_rules! check_stream {
            ($decoder:ty, $expected:expr) => {{
                let mut decoder = <$decoder>::new(policy);
                for &b in input {
                    if !matches!(decoder.push(b), Step::NeedMore) {
                        break;
                    }
                }
                assert_eq!(decoder.finish(), $expected, "stream {input:x?}, {policy:?}");
                assert_eq!(decoder.finish(), $expected);
                let seen = decoder.bytes_seen();
                assert_eq!(decoder.push(128), Step::Closed);
                assert_eq!(decoder.bytes_seen(), seen);
            }};
        }
        check_stream!(DecoderU32, expected32);
        check_stream!(DecoderU64, oracle(input, policy));
        assert_eq!(
            decode_u64(input, policy),
            oracle(input, policy),
            "{input:x?}, {policy:?}"
        );
    }
}

#[test]
fn exhaustive_zero_one_two_byte_inputs() {
    compare(&[]);
    for a in 0..=255 {
        compare(&[a]);
        for b in 0..=255 {
            compare(&[a, b]);
        }
    }
}

#[test]
fn boundaries_and_deterministic_random_inputs() {
    let mut seed = 0x2bd7_659c_4613_a805u64;
    for _ in 0..10_000 {
        // Fixed-seed generator, with wrapping used only in the test harness.
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let mut input = [0u8; 12];
        for (i, b) in input.iter_mut().enumerate() {
            *b = (seed.rotate_left((i * 7) as u32) & 255) as u8;
        }
        for len in 0..=12 {
            compare(&input[..len]);
        }
        let n32 = seed as i32;
        let math32 = if n32 >= 0 {
            2 * i64::from(n32)
        } else {
            -2 * i64::from(n32) - 1
        };
        assert_eq!(u64::from(zigzag_i32_to_u32(n32)), math32 as u64);
        assert_eq!(zigzag_u32_to_i32(zigzag_i32_to_u32(n32)), n32);
        assert_eq!(
            zigzag_i32_to_u32(zigzag_u32_to_i32(seed as u32)),
            seed as u32
        );
        let encoded32 = encode_u32(seed as u32);
        assert_eq!(
            oracle_width(encoded32.as_bytes(), DecodePolicy::Canonical, 32)
                .unwrap()
                .value,
            u64::from(seed as u32)
        );
        for capacity in 0..=12 {
            macro_rules! check_buffer {
                ($encode:expr, $expected:expr) => {{
                    let expected = $expected;
                    let mut out = [0xa5; 12];
                    let result = $encode(&mut out[..capacity]);
                    if capacity < expected.len() {
                        assert_eq!(
                            result,
                            Err(EncodeError {
                                required: expected.len(),
                                available: capacity
                            })
                        );
                        assert_eq!(out, [0xa5; 12]);
                    } else {
                        assert_eq!(result, Ok(expected.len()));
                        assert_eq!(&out[..expected.len()], expected.as_bytes());
                        assert!(out[expected.len()..].iter().all(|b| *b == 0xa5));
                    }
                }};
            }
            check_buffer!(
                |out| encode_u32_into(seed as u32, out),
                encode_u32(seed as u32)
            );
            check_buffer!(|out| encode_i32_into(n32, out), encode_i32(n32));
            check_buffer!(
                |out| encode_i64_into(seed as i64, out),
                encode_i64(seed as i64)
            );
        }
        let encoded = encode_u64(seed);
        assert_eq!(
            oracle(encoded.as_bytes(), DecodePolicy::Canonical)
                .unwrap()
                .value,
            seed
        );
        let n = seed as i64;
        let math = if n >= 0 {
            2 * i128::from(n)
        } else {
            -2 * i128::from(n) - 1
        };
        assert_eq!(u128::from(zigzag_i64_to_u64(n)), math as u128);
        assert_eq!(zigzag_u64_to_i64(zigzag_i64_to_u64(n)), n);
        assert_eq!(zigzag_i64_to_u64(zigzag_u64_to_i64(seed)), seed);
        for capacity in 0..=12 {
            let mut out = [0xa5; 12];
            let result = encode_u64_into(seed, &mut out[..capacity]);
            if capacity < encoded.len() {
                assert_eq!(
                    result,
                    Err(EncodeError {
                        required: encoded.len(),
                        available: capacity
                    })
                );
                assert_eq!(out, [0xa5; 12]);
            } else {
                assert_eq!(result, Ok(encoded.len()));
                assert_eq!(&out[..encoded.len()], encoded.as_bytes());
                assert!(out[encoded.len()..].iter().all(|b| *b == 0xa5));
            }
        }
    }
    for final_byte in 0..=255 {
        let mut input32 = [0x80; 7];
        input32[4] = final_byte;
        compare(&input32[..5]);
        compare(&input32);
        let mut input = [0x80; 12];
        input[9] = final_byte;
        compare(&input[..10]);
        compare(&input);
    }
}

#[test]
fn chunk_partitions_and_fixed_state_sizes() {
    assert!(core::mem::size_of::<DecoderU32>() <= 64);
    assert!(core::mem::size_of::<DecoderU64>() <= 64);
    for policy in [DecodePolicy::Canonical, DecodePolicy::BoundedNonCanonical] {
        for input in [
            vec![],
            vec![0],
            vec![172, 2, 127],
            vec![128; 12],
            vec![255; 12],
            vec![128, 0],
            encode_u64(u64::MAX).as_bytes().to_vec(),
        ] {
            // Every placement of chunk boundaries, including extra empty chunks.
            for mask in 0..(1usize << input.len().saturating_sub(1)) {
                let mut chunks = Vec::new();
                let mut start = 0;
                for end in 1..input.len() {
                    if mask & (1 << (end - 1)) != 0 {
                        chunks.push(&input[start..end]);
                        chunks.push(&input[end..end]);
                        start = end;
                    }
                }
                chunks.push(&input[start..]);
                macro_rules! check {
                    ($decoder:ty, $width:expr) => {{
                        let mut decoder = <$decoder>::new(policy);
                        let mut sealed = false;
                        for chunk in &chunks {
                            for &byte in *chunk {
                                if sealed {
                                    break;
                                }
                                sealed = !matches!(decoder.push(byte), Step::NeedMore);
                            }
                        }
                        let got = decoder.finish().map(|d| Decoded {
                            value: u64::from(d.value),
                            consumed: d.consumed,
                            canonical: d.canonical,
                        });
                        assert_eq!(got, oracle_width(&input, policy, $width));
                        decoder.reset(policy);
                        assert_eq!(
                            decoder.finish(),
                            Err(DecodeError {
                                kind: DecodeErrorKind::Truncated,
                                consumed: 0
                            })
                        );
                    }};
                }
                check!(DecoderU32, 32);
                check!(DecoderU64, 64);
            }
        }
    }
}

#[test]
fn exhaustive_reduced_width_models() {
    for width in 1..=16 {
        for value in 0..(1u32 << width) {
            let encoded = encode_u32(value);
            let expected = Decoded {
                value: u64::from(value),
                consumed: encoded.len(),
                canonical: true,
            };
            assert_eq!(
                oracle_width(encoded.as_bytes(), DecodePolicy::Canonical, width),
                Ok(expected)
            );
        }
        let limit = width.div_ceil(7);
        let last_max = (1u8 << (width - 7 * (limit - 1))) - 1;
        if last_max < 127 {
            let mut overflow = vec![0x80; limit];
            overflow[limit - 1] = last_max + 1;
            for policy in [DecodePolicy::Canonical, DecodePolicy::BoundedNonCanonical] {
                assert_eq!(
                    oracle_width(&overflow, policy, width),
                    Err(DecodeError {
                        kind: DecodeErrorKind::Overflow,
                        consumed: limit
                    })
                );
            }
        }
    }
}

#[test]
fn length_preflight_matches_leb128_at_every_binary_boundary() {
    const LENGTHS: [usize; 4] = [
        encoded_len_u64(0),
        encoded_len_u64(1),
        encoded_len_u64(u64::MAX),
        encoded_len_u32(u32::MAX),
    ];
    assert_eq!(LENGTHS, [1, 1, 10, 5]);
    for bit in 0..64 {
        let edge = 1u64 << bit;
        for value in [0, edge - 1, edge, edge + 1, u64::MAX] {
            let mut bytes = Vec::new();
            leb128::write::unsigned(&mut bytes, value).unwrap();
            assert_eq!(encoded_len_u64(value), bytes.len(), "{value}");
            if let Ok(value32) = u32::try_from(value) {
                assert_eq!(encoded_len_u32(value32), bytes.len(), "{value32}");
            }
        }
    }
}
