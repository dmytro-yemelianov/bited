use bitet::{decode_u64, encode_u64_into, DecodePolicy};
use integer_encoding::VarInt;
use serde_json::json;
use std::{hint::black_box, time::Instant};
const N: usize = 16384;
const ROUNDS: usize = 64;
const REPEATS: usize = 15;
const SEED: u64 = 0x766172696e743031;
fn random(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}
#[derive(Clone, Copy, Debug)]
enum Implementation {
    Verified,
    Previous,
    Leb128,
    IntegerEncoding,
}
const IMPLEMENTATIONS: [Implementation; 4] = [
    Implementation::Verified,
    Implementation::Previous,
    Implementation::Leb128,
    Implementation::IntegerEncoding,
];
#[inline(always)]
fn encode(implementation: Implementation, value: u64, out: &mut [u8]) -> usize {
    match implementation {
        Implementation::Verified => encode_u64_into(value, out).unwrap(),
        Implementation::Previous => verified_varint_baseline::encode_u64_into(value, out).unwrap(),
        Implementation::Leb128 => leb128::write::unsigned(&mut &mut out[..], value).unwrap(),
        Implementation::IntegerEncoding => value.encode_var(out),
    }
}
#[inline(always)]
fn decode(implementation: Implementation, bytes: &[u8]) -> (u64, usize) {
    match implementation {
        Implementation::Verified => {
            let v = decode_u64(bytes, DecodePolicy::Canonical).unwrap();
            (v.value, v.consumed)
        }
        Implementation::Previous => {
            let v = verified_varint_baseline::decode_u64(
                bytes,
                verified_varint_baseline::DecodePolicy::Canonical,
            )
            .unwrap();
            (v.value, v.consumed)
        }
        Implementation::Leb128 => {
            let mut input = bytes;
            let v = leb128::read::unsigned(&mut input).unwrap();
            (v, bytes.len() - input.len())
        }
        Implementation::IntegerEncoding => u64::decode_var(bytes).unwrap(),
    }
}
// Dispatch is outside the value loop; inline adapters remove per-value enum dispatch.
#[inline(never)]
fn encode_batch(values: &[u64], implementation: Implementation) {
    macro_rules! batch {
        ($i:expr) => {{
            let mut out = [0; 10];
            for &v in values {
                black_box(encode($i, black_box(v), black_box(&mut out)));
                black_box(&out);
            }
        }};
    }
    match implementation {
        Implementation::Verified => batch!(Implementation::Verified),
        Implementation::Previous => batch!(Implementation::Previous),
        Implementation::Leb128 => batch!(Implementation::Leb128),
        Implementation::IntegerEncoding => batch!(Implementation::IntegerEncoding),
    }
}
#[inline(never)]
fn decode_batch(bytes: &[u8], implementation: Implementation) {
    macro_rules! batch {
        ($i:expr) => {{
            let mut offset = 0;
            while offset < bytes.len() {
                let (v, n) = decode($i, black_box(&bytes[offset..]));
                black_box(v);
                offset += n;
            }
        }};
    }
    match implementation {
        Implementation::Verified => batch!(Implementation::Verified),
        Implementation::Previous => batch!(Implementation::Previous),
        Implementation::Leb128 => batch!(Implementation::Leb128),
        Implementation::IntegerEncoding => batch!(Implementation::IntegerEncoding),
    }
}
fn thread_cpu_ns() -> u128 {
    let mut t = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: t is a valid writable timespec; libc supplies the target clock ID.
    let result = unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut t) };
    assert_eq!(result, 0, "thread CPU timer unavailable");
    t.tv_sec as u128 * 1_000_000_000 + t.tv_nsec as u128
}
fn main() {
    let mut s = SEED;
    let mut datasets = Vec::new();
    for length in 1..=10 {
        let low = if length == 1 {
            0
        } else {
            1u64 << (7 * (length - 1))
        };
        let high = if length == 10 {
            u64::MAX
        } else {
            (1u64 << (7 * length)) - 1
        };
        datasets.push((
            format!("length-{length}"),
            (0..N)
                .map(|_| low + random(&mut s) % (high - low + 1))
                .collect::<Vec<_>>(),
        ));
    }
    datasets.push((
        "short-80-15-5".into(),
        (0..N)
            .map(|i| {
                let r = random(&mut s);
                match i % 100 {
                    0..=79 => r & 127,
                    80..=94 => 128 | (r & 16383),
                    _ => r,
                }
            })
            .collect(),
    ));
    datasets.push((
        "full-width".into(),
        (0..N).map(|_| random(&mut s)).collect(),
    ));
    datasets.push((
        "alternating".into(),
        (0..N)
            .map(|i| if i % 2 == 0 { 1 } else { u64::MAX })
            .collect(),
    ));
    // Signed ZigZag wire values, mapping outside timing for ALL implementations.
    datasets.push((
        "zigzag-near-zero".into(),
        (0..N)
            .map(|i| {
                let v = (i as i64 % 255) - 127;
                ((v as u64) << 1) ^ ((v >> 63) as u64)
            })
            .collect(),
    ));
    datasets.push((
        "large-full-width".into(),
        (0..2_097_152).map(|_| random(&mut s)).collect(),
    ));
    let args: Vec<_> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("profile") {
        let implementation = match args.get(2).map(String::as_str) {
            Some("previous") => Implementation::Previous,
            Some("leb128") => Implementation::Leb128,
            Some("integer") => Implementation::IntegerEncoding,
            _ => Implementation::Verified,
        };
        let operation = args.get(3).map(String::as_str).unwrap_or("decode");
        let selected = args.get(4).map(String::as_str).unwrap_or("full-width");
        let (_, values) = datasets
            .iter()
            .find(|(n, _)| n == selected)
            .expect("dataset");
        let mut bytes = Vec::new();
        for &v in values {
            let mut b = [0; 10];
            let n = encode(Implementation::Verified, v, &mut b);
            bytes.extend_from_slice(&b[..n]);
        }
        eprintln!(
            "profile pid={} {:?} {operation} {selected}",
            std::process::id(),
            implementation
        );
        let start = Instant::now();
        while start.elapsed().as_secs() < 15 {
            if operation == "encode" {
                encode_batch(values, implementation)
            } else {
                decode_batch(&bytes, implementation)
            }
        }
        return;
    }
    let mut results = Vec::new();
    let mut checked = 0;
    for (name, values) in datasets {
        let mut bytes = Vec::new();
        for &v in &values {
            let mut expected = [0; 10];
            let n = encode(Implementation::Verified, v, &mut expected);
            for imp in IMPLEMENTATIONS {
                let mut actual = [0; 10];
                let m = encode(imp, v, &mut actual);
                assert_eq!(&actual[..m], &expected[..n]);
                assert_eq!(decode(imp, &expected[..n]), (v, n));
                checked += 1;
            }
            bytes.extend_from_slice(&expected[..n]);
        }
        let rounds = if values.len() > N { 1 } else { ROUNDS };
        for operation in ["encode", "decode"] {
            let mut samples: [Vec<f64>; 4] = std::array::from_fn(|_| Vec::new());
            let mut cpu_samples: [Vec<f64>; 4] = std::array::from_fn(|_| Vec::new());
            for imp in IMPLEMENTATIONS {
                if operation == "encode" {
                    encode_batch(&values, imp)
                } else {
                    decode_batch(&bytes, imp)
                }
            }
            for repeat in 0..REPEATS {
                // Rotate order to distribute thermal/time drift across implementations.
                for step in 0..4 {
                    let index = (step + repeat) % 4;
                    let imp = IMPLEMENTATIONS[index];
                    let cpu_start = thread_cpu_ns();
                    let start = Instant::now();
                    for _ in 0..rounds {
                        if operation == "encode" {
                            encode_batch(black_box(&values), imp)
                        } else {
                            decode_batch(black_box(&bytes), imp)
                        }
                    }
                    let wall_elapsed = start.elapsed().as_nanos();
                    let cpu_elapsed = thread_cpu_ns() - cpu_start;
                    cpu_samples[index].push(cpu_elapsed as f64 / (values.len() * rounds) as f64);
                    samples[index].push(wall_elapsed as f64 / (values.len() * rounds) as f64);
                }
            }
            for (index, imp) in IMPLEMENTATIONS.into_iter().enumerate() {
                let a = &samples[index];
                let mean = a.iter().sum::<f64>() / REPEATS as f64;
                let sd = (a.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (REPEATS - 1) as f64)
                    .sqrt();
                let sem = sd / (REPEATS as f64).sqrt();
                let cpu = &cpu_samples[index];
                let cpu_mean = cpu.iter().sum::<f64>() / REPEATS as f64;
                let cpu_sd = (cpu.iter().map(|x| (x - cpu_mean).powi(2)).sum::<f64>()
                    / (REPEATS - 1) as f64)
                    .sqrt();
                let cpu_sem = cpu_sd / (REPEATS as f64).sqrt();
                results.push(json!({"dataset":name,"operation":operation,"implementation":format!("{imp:?}"),"values":values.len(),"encoded_bytes":bytes.len(),"rounds":rounds,"samples_ns_per_value":a,"thread_cpu_ns_per_value_samples":cpu,"mean_thread_cpu_ns_per_value":cpu_mean,"thread_cpu_sd_ns":cpu_sd,"thread_cpu_approx_95_percent_interval_ns":[cpu_mean-2.145*cpu_sem,cpu_mean+2.145*cpu_sem],"mean_ns_per_value":mean,"sd_ns":sd,"approx_95_percent_interval_ns":[mean-2.145*sem,mean+2.145*sem],"values_per_second":1e9/mean}));
            }
        }
    }
    let malformed: Vec<(&str, Vec<u8>)> = vec![
        ("redundant-zero", vec![0x80, 0]),
        ("truncated", vec![0x80]),
        ("overflow", [vec![0xff; 9], vec![2]].concat()),
        ("too-long", vec![0x80; 11]),
        ("trailing", vec![0, 1]),
    ];
    let quality: Vec<_> = malformed.iter().map(|(name,b)| {let mut input=&b[..];let l=leb128::read::unsigned(&mut input);json!({"case":name,"bytes":b,"verified_canonical":format!("{:?}",decode_u64(b,DecodePolicy::Canonical)),"verified_bounded":format!("{:?}",decode_u64(b,DecodePolicy::BoundedNonCanonical)),"leb128":format!("{l:?}"),"leb128_consumed":b.len()-input.len(),"integer_encoding":format!("{:?}",u64::decode_var(b))})}).collect();
    println!(
        "{}",
        json!({"schema":"varint-comparison/0.1","seed":format!("{SEED:016x}"),"repeats":REPEATS,"checked_results":checked,"implementations":{"Verified":"repository path dependency","Previous":"original verified source snapshot","Leb128":"0.2.5","IntegerEncoding":"4.1.0"},"scope":"u64 canonical valid input; ZigZag mapped outside timing; public caller-buffer encode / prefix decode; no allocations in timed loops; large traversal cache uncontrolled","order":"rotated each repeat","results":results,"malformed_observations":quality})
    );
}
