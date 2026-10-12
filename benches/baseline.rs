//! Reproducible scalar baseline. Dataset construction stays outside measurements.
use bited::*;
use serde_json::json;
use std::hint::black_box;
use std::time::Instant;

const SEED: u64 = 0x7661_7269_6e74_3031;
const REPEATS: usize = 9;
const HOT_N: usize = 16_384;

fn random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}
fn wire(values: &[u64], signed: bool) -> Vec<u8> {
    let mut out = Vec::new();
    for &value in values {
        if signed {
            out.extend_from_slice(encode_i64(value as i64).as_bytes());
        } else {
            out.extend_from_slice(encode_u64(value).as_bytes());
        }
    }
    out
}
#[inline(never)]
fn encode_values(values: &[u64], signed: bool) {
    let mut out = [0u8; 10];
    for &value in values {
        let result = if signed {
            encode_i64_into(black_box(value) as i64, black_box(&mut out))
        } else {
            encode_u64_into(black_box(value), black_box(&mut out))
        };
        black_box(result.unwrap());
        black_box(&out);
    }
}
#[inline(never)]
fn decode_values(bytes: &[u8], signed: bool) {
    let mut offset = 0;
    while offset < bytes.len() {
        let consumed = if signed {
            let result = decode_i64(black_box(&bytes[offset..]), DecodePolicy::Canonical).unwrap();
            black_box(result.value);
            result.consumed
        } else {
            let result = decode_u64(black_box(&bytes[offset..]), DecodePolicy::Canonical).unwrap();
            black_box(result.value);
            result.consumed
        };
        offset += consumed;
    }
}
fn measurement(
    name: &str,
    operation: &str,
    cache: &str,
    values: usize,
    bytes: usize,
    rounds: usize,
    mut body: impl FnMut(),
) -> serde_json::Value {
    body();
    let mut samples = Vec::new();
    for _ in 0..REPEATS {
        let start = Instant::now();
        for _ in 0..rounds {
            body();
        }
        samples.push(start.elapsed().as_nanos() as f64 / (values * rounds) as f64);
    }
    let mean = samples.iter().sum::<f64>() / samples.len() as f64;
    let variance =
        samples.iter().map(|v| (v - mean).powi(2)).sum::<f64>() / (samples.len() - 1) as f64;
    let sem = (variance / samples.len() as f64).sqrt();
    json!({"dataset": name, "operation": operation, "cache": cache,
        "values_per_round": values, "bytes_per_round": bytes, "rounds_per_repeat": rounds,
        "ns_per_value_samples": samples, "mean_ns_per_value": mean,
        "sample_stddev_ns": variance.sqrt(), "mean_standard_error_ns": sem,
        "approx_95_percent_interval_ns": [mean-2.306*sem, mean+2.306*sem],
        "values_per_second": 1e9/mean, "encoded_bytes_per_second": 1e9/mean*bytes as f64/values as f64})
}
fn main() {
    let mut rng = SEED;
    let mut datasets: Vec<(String, Vec<u64>, bool, &str)> = Vec::new();
    // Each length gets equal representation as a separately reported dataset.
    for len in 1..=10 {
        let low = if len == 1 { 0 } else { 1u64 << (7 * (len - 1)) };
        let high = if len == 10 {
            u64::MAX
        } else {
            (1u64 << (7 * len)) - 1
        };
        let values = (0..HOT_N)
            .map(|_| low + random(&mut rng) % (high - low + 1))
            .collect();
        datasets.push((format!("uniform-length-{len}"), values, false, "hot"));
    }
    datasets.push((
        "short-weighted-80-15-5".into(),
        (0..HOT_N)
            .map(|i| {
                let r = random(&mut rng);
                match i % 100 {
                    0..=79 => r & 127,
                    80..=94 => 128 | (r & 16383),
                    _ => r,
                }
            })
            .collect(),
        false,
        "hot",
    ));
    datasets.push((
        "uniform-full-width".into(),
        (0..HOT_N).map(|_| random(&mut rng)).collect(),
        false,
        "hot",
    ));
    datasets.push((
        "signed-around-zero".into(),
        (0..HOT_N)
            .map(|i| ((i as i64 % 255) - 127) as u64)
            .collect(),
        true,
        "hot",
    ));
    datasets.push((
        "signed-extremes".into(),
        (0..HOT_N)
            .map(|i| {
                if i % 2 == 0 {
                    i64::MIN as u64
                } else {
                    i64::MAX as u64
                }
            })
            .collect(),
        true,
        "hot",
    ));
    datasets.push((
        "alternating-lengths".into(),
        (0..HOT_N)
            .map(|i| if i % 2 == 0 { 1 } else { u64::MAX })
            .collect(),
        false,
        "hot",
    ));
    let sequential: Vec<u64> = (0..HOT_N as u64).collect();
    let mut shuffled = sequential.clone();
    for i in (1..shuffled.len()).rev() {
        let j = random(&mut rng) as usize % (i + 1);
        shuffled.swap(i, j);
    }
    datasets.push(("sequential".into(), sequential, false, "hot"));
    datasets.push(("shuffled-sequential".into(), shuffled, false, "hot"));
    datasets.push((
        "large-full-width".into(),
        (0..2_097_152).map(|_| random(&mut rng)).collect(),
        false,
        "streaming traversal; cache state uncontrolled",
    ));
    let mut results = Vec::new();
    for (name, values, signed, cache) in &datasets {
        let bytes = wire(values, *signed);
        let rounds = if values.len() > HOT_N { 1 } else { 32 };
        results.push(measurement(
            name,
            "caller-buffer encode batch",
            cache,
            values.len(),
            bytes.len(),
            rounds,
            || encode_values(black_box(values), *signed),
        ));
        results.push(measurement(
            name,
            "prefix decode concatenated batch",
            cache,
            values.len(),
            bytes.len(),
            rounds,
            || decode_values(black_box(&bytes), *signed),
        ));
        if values.len() == HOT_N {
            let value = black_box(values[HOT_N / 2]);
            let single = wire(&[value], *signed);
            results.push(measurement(
                name,
                "one-value decode latency including loop and black_box",
                "hot",
                1,
                single.len(),
                200_000,
                || decode_values(black_box(&single), *signed),
            ));
            results.push(measurement(
                name,
                "one-value encode latency including loop and black_box",
                "hot",
                1,
                single.len(),
                200_000,
                || encode_values(black_box(&[value]), *signed),
            ));
        }
    }
    for width in [32, 64] {
        let limit = if width == 32 { 5 } else { 10 };
        let last_max = if width == 32 { 15 } else { 1 };
        for kind in [
            "truncated",
            "overflow",
            "too-long",
            "noncanonical",
            "trailing-bytes",
        ] {
            let mut bytes = vec![0x80; limit];
            match kind {
                "truncated" => {
                    bytes.pop();
                }
                "overflow" => bytes[limit - 1] = last_max + 1,
                "too-long" => bytes[limit - 1] = 0x80,
                "noncanonical" => bytes[limit - 1] = 0,
                _ => bytes = vec![0, 1],
            }
            for policy in [DecodePolicy::Canonical, DecodePolicy::BoundedNonCanonical] {
                results.push(measurement(
                    &format!("malformed-{width}-{kind}-{policy:?}"),
                    "exact decode",
                    "hot",
                    1,
                    bytes.len(),
                    200_000,
                    || {
                        if width == 32 {
                            let _ = black_box(decode_u32_exact(black_box(&bytes), policy));
                        } else {
                            let _ = black_box(decode_u64_exact(black_box(&bytes), policy));
                        }
                    },
                ));
            }
        }
    }
    println!(
        "{}",
        json!({"schema":"bited-benchmark/0.1", "benchmark_version":1,
        "seed":format!("{SEED:016x}"), "threads":1, "repeats":REPEATS,
        "baseline":"public scalar API; no fast paths", "uncertainty":"sample SD, SEM and t(8) approximate 95% interval; system noise uncontrolled",
        "weights":"separate equal-length datasets; short mixture 80% one byte, 15% two bytes, 5% full-width",
        "cache_note":"hot datasets warmed once; large traversal reported separately, no controlled cold-cache claim",
        "state_size_bytes":{"DecoderU32":std::mem::size_of::<DecoderU32>(),"DecoderU64":std::mem::size_of::<DecoderU64>(),"Encoded32":std::mem::size_of::<Encoded32>(),"Encoded64":std::mem::size_of::<Encoded64>()},
        "results":results})
    );
}
