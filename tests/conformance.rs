use serde_json::Value;
use verified_varint::*;

fn bytes(hex: &str) -> Vec<u8> {
    hex.split_whitespace()
        .map(|b| u8::from_str_radix(b, 16).unwrap())
        .collect()
}

fn policy(v: &Value) -> DecodePolicy {
    match v["policy"].as_str().unwrap() {
        "canonical" => DecodePolicy::Canonical,
        "bounded_noncanonical" => DecodePolicy::BoundedNonCanonical,
        other => panic!("unknown policy {other}"),
    }
}

fn check_decode<T: core::fmt::Display>(
    actual: Result<Decoded<T>, DecodeError>,
    e: &Value,
    id: &str,
) {
    match actual {
        Ok(d) => {
            assert_eq!(e["status"], "ok", "{id}");
            assert_eq!(
                d.value.to_string(),
                e["value_decimal"].as_str().unwrap(),
                "{id}"
            );
            assert_eq!(d.consumed, e["consumed"].as_u64().unwrap() as usize, "{id}");
            assert_eq!(d.canonical, e["canonical"].as_bool().unwrap(), "{id}");
        }
        Err(d) => {
            assert_eq!(e["status"], "error", "{id}");
            assert_eq!(
                format!("{:?}", d.kind),
                e["error"].as_str().unwrap(),
                "{id}"
            );
            assert_eq!(d.consumed, e["consumed"].as_u64().unwrap() as usize, "{id}");
        }
    }
}

#[test]
fn supplied_conformance_vectors() {
    let v: Value = serde_json::from_str(include_str!("../conformance/vectors.json")).unwrap();
    let mut covered = 0;
    for c in v["unsigned_encoding"].as_array().unwrap() {
        let value = c["value_decimal"].as_str().unwrap().parse::<u64>().unwrap();
        let expected = bytes(c["hex"].as_str().unwrap());
        if c["width"] == 32 {
            let e = encode_u32(value.try_into().unwrap());
            assert_eq!(e.as_bytes(), expected);
            assert_eq!(e.len(), encoded_len_u32(value as u32));
            assert!(!e.is_empty());
        }
        let e = encode_u64(value);
        assert_eq!(
            e.as_bytes(),
            bytes(c["hex"].as_str().unwrap()),
            "{}",
            c["id"]
        );
        assert_eq!(e.len(), c["length"].as_u64().unwrap() as usize);
        assert_eq!(encoded_len_u64(value), e.len());
        assert!(!e.is_empty());
        covered += 1;
    }
    for c in v["signed_zigzag_encoding"].as_array().unwrap() {
        let n = c["value_decimal"].as_str().unwrap().parse::<i64>().unwrap();
        if c["width"] == 32 {
            let n32 = i32::try_from(n).unwrap();
            let u32 = zigzag_i32_to_u32(n32);
            assert_eq!(u32.to_string(), c["zigzag_decimal"].as_str().unwrap());
            assert_eq!(zigzag_u32_to_i32(u32), n32);
            assert_eq!(
                encode_i32(n32).as_bytes(),
                bytes(c["hex"].as_str().unwrap())
            );
            assert_eq!(encoded_len_i32(n32), encode_i32(n32).len());
            check_decode(
                decode_i32_exact(encode_i32(n32).as_bytes(), DecodePolicy::Canonical),
                &serde_json::json!({"status":"ok", "value_decimal":n32.to_string(), "consumed":encode_i32(n32).len(), "canonical":true}),
                "signed32",
            );
        }
        assert_eq!(encode_i64(n).as_bytes(), bytes(c["hex"].as_str().unwrap()));
        assert_eq!(encoded_len_i64(n), encode_i64(n).len());
        assert_eq!(
            decode_i64_exact(encode_i64(n).as_bytes(), DecodePolicy::Canonical)
                .unwrap()
                .value,
            n
        );
        let u = zigzag_i64_to_u64(n);
        assert_eq!(u.to_string(), c["zigzag_decimal"].as_str().unwrap());
        assert_eq!(zigzag_u64_to_i64(u), n);
        assert_eq!(encode_u64(u).as_bytes(), bytes(c["hex"].as_str().unwrap()));
        covered += 1;
    }
    for c in v["decoding"].as_array().unwrap() {
        let input = bytes(c["hex"].as_str().unwrap());
        let id = c["id"].as_str().unwrap();
        if c["width"] == 32 {
            let result = if c["api"] == "exact" {
                decode_u32_exact(&input, policy(c))
            } else {
                decode_u32(&input, policy(c))
            };
            check_decode(result, &c["expected"], id);
        } else {
            let result = if c["api"] == "exact" {
                decode_u64_exact(&input, policy(c))
            } else {
                decode_u64(&input, policy(c))
            };
            check_decode(result, &c["expected"], id);
        }
        covered += 1;
    }
    for c in v["encode_into"].as_array().unwrap() {
        let value = c["value_decimal"].as_str().unwrap().parse::<u64>().unwrap();
        let mut out = bytes(c["initial_buffer_hex"].as_str().unwrap());
        let e = &c["expected"];
        let result = if c["width"] == 32 {
            encode_u32_into(value.try_into().unwrap(), &mut out)
        } else {
            encode_u64_into(value, &mut out)
        };
        match result {
            Ok(written) => {
                assert_eq!(e["status"], "ok");
                assert_eq!(written, e["written"].as_u64().unwrap() as usize);
            }
            Err(err) => {
                assert_eq!(e["status"], "error");
                assert_eq!(e["error"], "OutputTooSmall");
                assert_eq!(err.required, e["required"].as_u64().unwrap() as usize);
                assert_eq!(err.available, e["available"].as_u64().unwrap() as usize);
            }
        }
        assert_eq!(out, bytes(e["buffer_hex"].as_str().unwrap()), "{}", c["id"]);
        covered += 1;
    }
    for c in v["streaming"].as_array().unwrap() {
        macro_rules! run_stream {
            ($decoder:ty) => {{
                let mut decoder = <$decoder>::new(policy(c));
                let input: Vec<u8> = c["chunks_hex"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .flat_map(|chunk| bytes(chunk.as_str().unwrap()))
                    .collect();
                let mut consumed = 0;
                for &byte in &input {
                    match decoder.push(byte) {
                        Step::NeedMore => consumed += 1,
                        Step::Done(_) | Step::Error(_) => {
                            consumed += 1;
                            break;
                        }
                        Step::Closed => panic!("unexpected closed state"),
                    }
                }
                let result = decoder.finish();
                check_decode(result, &c["expected"], c["id"].as_str().unwrap());
                assert_eq!(decoder.finish(), result);
                assert_eq!(decoder.bytes_seen(), consumed);
                assert_eq!(decoder.push(255), Step::Closed);
                assert_eq!(decoder.bytes_seen(), consumed);
                assert_eq!(
                    &input[consumed..],
                    bytes(c["unconsumed_hex"].as_str().unwrap())
                );
                decoder.reset(DecodePolicy::Canonical);
                assert_eq!(decoder.bytes_seen(), 0);
                assert!(matches!(
                    decoder.push(0),
                    Step::Done(Decoded {
                        value: 0,
                        consumed: 1,
                        canonical: true
                    })
                ));
            }};
        }
        if c["width"] == 32 {
            run_stream!(DecoderU32);
        } else {
            run_stream!(DecoderU64);
        }
        covered += 1;
    }
    eprintln!("exercised {covered} of 351 supplied cases");
    assert_eq!(covered, 351);
}
