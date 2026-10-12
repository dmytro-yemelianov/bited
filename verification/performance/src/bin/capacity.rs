//! Capacity optimization experiments only; candidates are not shipped or Lean-verified.
use bitet::{encode_u64_into, encoded_len_u64, EncodeError};
use integer_encoding::VarInt;
use serde_json::json;
use std::{hint::black_box, time::Instant};
const REPEATS: usize = 21;
const ROUNDS: usize = 64;
const N: usize = 16384;
const SEED: u64 = 0x766172696e743031;
#[derive(Copy, Clone, Debug)]
enum Codec {
    Current,
    Peer,
    PeerChecked,
    CountReturn,
    FastCapacity,
    FastRequired,
    EarlySmall,
}
const CODECS: [Codec; 7] = [
    Codec::Current,
    Codec::Peer,
    Codec::PeerChecked,
    Codec::CountReturn,
    Codec::FastCapacity,
    Codec::FastRequired,
    Codec::EarlySmall,
];
#[inline(always)]
fn peer_checked(value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    let required = encoded_len_u64(value);
    if out.len() < required {
        return Err(EncodeError {
            required,
            available: out.len(),
        });
    }
    Ok(value.encode_var(out))
}
#[inline(always)]
fn count_return(mut value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    let required = encoded_len_u64(value);
    if out.len() < required {
        return Err(EncodeError {
            required,
            available: out.len(),
        });
    }
    let mut i = 0;
    while value >= 128 {
        out[i] = (value as u8 & 127) | 128;
        value >>= 7;
        i += 1;
    }
    out[i] = value as u8;
    Ok(i + 1)
}
#[inline(always)]
fn fast_capacity(value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    if out.len() >= 10 {
        count_return(value, &mut out[..10])
    } else {
        count_return(value, out)
    }
}
#[inline(always)]
fn fast_required(value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    if out.len() >= 10 {
        encode_u64_into(value, &mut out[..10])
    } else {
        encode_u64_into(value, out)
    }
}
#[inline(always)]
fn early_small(value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    if value < 128 {
        if out.is_empty() {
            return Err(EncodeError {
                required: 1,
                available: 0,
            });
        }
        out[0] = value as u8;
        return Ok(1);
    }
    fast_capacity(value, out)
}
#[inline(always)]
fn encode(codec: Codec, value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    match codec {
        Codec::Current => encode_u64_into(value, out),
        Codec::Peer => Ok(value.encode_var(out)),
        Codec::PeerChecked => peer_checked(value, out),
        Codec::CountReturn => count_return(value, out),
        Codec::FastCapacity => fast_capacity(value, out),
        Codec::FastRequired => fast_required(value, out),
        Codec::EarlySmall => early_small(value, out),
    }
}
#[inline(always)]
fn output<const KNOWN: bool>(out: &mut [u8; 10]) -> &mut [u8] {
    if KNOWN {
        // Explicit array type keeps length 10 visible AFTER pointer black_box.
        let pointer: &mut [u8; 10] = black_box(out);
        &mut pointer[..]
    } else {
        let slice: &mut [u8] = black_box(&mut out[..]);
        slice
    }
}
#[inline(never)]
fn batch<const KNOWN: bool>(values: &[u64], codec: Codec) {
    macro_rules! body {
        ($c:expr) => {{
            let mut out = [0; 10];
            for &v in values {
                black_box(encode($c, black_box(v), output::<KNOWN>(&mut out)).unwrap());
                black_box(&out);
            }
        }};
    }
    match codec {
        Codec::Current => body!(Codec::Current),
        Codec::Peer => body!(Codec::Peer),
        Codec::PeerChecked => body!(Codec::PeerChecked),
        Codec::CountReturn => body!(Codec::CountReturn),
        Codec::FastCapacity => body!(Codec::FastCapacity),
        Codec::FastRequired => body!(Codec::FastRequired),
        Codec::EarlySmall => body!(Codec::EarlySmall),
    }
}
fn cpu_ns() -> u128 {
    let mut t = libc::timespec {
        tv_sec: 0,
        tv_nsec: 0,
    };
    // SAFETY: a writable initialized timespec and the target-provided clock ID.
    assert_eq!(
        unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, &mut t) },
        0
    );
    t.tv_sec as u128 * 1_000_000_000 + t.tv_nsec as u128
}
fn random(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}
fn validate(values: &[u64]) -> usize {
    let mut checks = 0;
    for &value in values {
        for capacity in 0..=12 {
            let mut reference = [0xa5; 12];
            let expected = encode_u64_into(value, &mut reference[..capacity]);
            for codec in [
                Codec::PeerChecked,
                Codec::CountReturn,
                Codec::FastCapacity,
                Codec::FastRequired,
                Codec::EarlySmall,
            ] {
                let mut out = [0xa5; 12];
                assert_eq!(encode(codec, value, &mut out[..capacity]), expected);
                assert_eq!(out, reference, "{codec:?} {value} cap={capacity}");
                checks += 1;
            }
            // The bare peer requires enough space, so never call it on short buffers.
            if expected.is_ok() {
                let mut out = [0xa5; 12];
                assert_eq!(encode(Codec::Peer, value, &mut out[..capacity]), expected);
                assert_eq!(out, reference);
                checks += 1;
            }
        }
    }
    checks
}
fn main() {
    let mut rng = SEED;
    let full = (0..N).map(|_| random(&mut rng)).collect::<Vec<_>>();
    let short = (0..N)
        .map(|i| {
            let r = random(&mut rng);
            match i % 140 {
                0..=79 => r & 127,
                80..=94 => 128 | (r & 16383),
                _ => r,
            }
        })
        .collect::<Vec<_>>();
    let lengths = (1..=10).map(|len| {
        let low = if len == 1 { 0 } else { 1u64 << (7 * (len - 1)) };
        let high = if len == 10 {
            u64::MAX
        } else {
            (1u64 << (7 * len)) - 1
        };
        (
            format!("length-{len}"),
            (0..N)
                .map(|_| low + random(&mut rng) % (high - low + 1))
                .collect::<Vec<_>>(),
        )
    });
    let mut datasets = vec![("full-width".into(), full), ("short-80-15-5".into(), short)];
    datasets.extend(lengths);
    let mut boundary = vec![0, u64::MAX];
    for bit in 0..64 {
        let p = 1u64 << bit;
        boundary.extend([p - 1, p, p + 1]);
    }
    let args = std::env::args().collect::<Vec<_>>();
    if args.get(1).map(String::as_str) == Some("profile") {
        let codec = match args.get(2).map(String::as_str) {
            Some("peer") => Codec::Peer,
            Some("checked") => Codec::PeerChecked,
            Some("count") => Codec::CountReturn,
            Some("fast") => Codec::FastCapacity,
            Some("required") => Codec::FastRequired,
            Some("small") => Codec::EarlySmall,
            _ => Codec::Current,
        };
        let known = args.get(3).map(String::as_str) == Some("known");
        let values = &datasets[0].1;
        eprintln!("pid={} {codec:?} known={known}", std::process::id());
        let t = Instant::now();
        while t.elapsed().as_secs() < 12 {
            if known {
                batch::<true>(values, codec)
            } else {
                batch::<false>(values, codec)
            }
        }
        return;
    }
    let mut checks = validate(&boundary);
    for (_, v) in &datasets {
        checks += validate(v);
    }
    let mut results = Vec::new();
    for (name, values) in &datasets {
        let mut cpu: [Vec<f64>; 14] = std::array::from_fn(|_| Vec::new());
        let mut wall: [Vec<f64>; 14] = std::array::from_fn(|_| Vec::new());
        for condition in 0..14 {
            let codec = CODECS[condition % 7];
            if condition >= 7 {
                batch::<true>(values, codec)
            } else {
                batch::<false>(values, codec)
            }
        }
        for repeat in 0..REPEATS {
            for step in 0..14 {
                let i = (repeat + step) % 14;
                let codec = CODECS[i % 7];
                let c = cpu_ns();
                let t = Instant::now();
                for _ in 0..ROUNDS {
                    if i >= 7 {
                        batch::<true>(black_box(values), codec)
                    } else {
                        batch::<false>(black_box(values), codec)
                    }
                }
                let w = t.elapsed().as_nanos();
                let c = cpu_ns() - c;
                cpu[i].push(c as f64 / (N * ROUNDS) as f64);
                wall[i].push(w as f64 / (N * ROUNDS) as f64);
            }
        }
        for i in 0..14 {
            let codec = CODECS[i % 7];
            let mean = cpu[i].iter().sum::<f64>() / REPEATS as f64;
            let sd = (cpu[i].iter().map(|x| (x - mean).powi(2)).sum::<f64>()
                / (REPEATS - 1) as f64)
                .sqrt();
            let half = 2.086 * sd / (REPEATS as f64).sqrt();
            results.push(json!({"dataset":name,"codec":format!("{codec:?}"),"capacity":if i >= 7 {"known-10"}else{"opaque-slice"},"cpu_ns_per_value_samples":cpu[i],"wall_ns_per_value_samples":wall[i],"mean_cpu_ns_per_value":mean,"approx_95_percent_interval_ns":[mean-half,mean+half]}));
        }
    }
    println!(
        "{}",
        json!({"schema":"varint-capacity-experiment/0.1","seed":format!("{SEED:016x}"),"repeats":REPEATS,"rounds":ROUNDS,"values":N,"checks":checks,"order":"rotate all fourteen codec/capacity conditions per repeat","results":results,"scope":"benchmark controls only; CountReturn, FastCapacity, FastRequired and EarlySmall are not shipped or Lean-verified; PeerChecked adds the current library length/capacity preflight to integer-encoding; no hardware counters; CPU time excludes descheduling"})
    );
}
