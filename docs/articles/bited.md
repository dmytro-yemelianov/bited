# bited: small integers, explicit contracts, and a faster verified encoder

*Dmytro Yemelianov · 12 October 2026 · bited 0.1.0 release candidate*

An integer codec is easy to underestimate. The happy path is a loop that emits seven bits at a time. The contract also has to answer what happens when a buffer ends halfway through a number, when the number overflows, when its representation is longer than necessary, or when a caller supplies too little output space.

**bited** is one small Rust library for 32- and 64-bit base-128 varints and signed ZigZag mappings, with a corresponding Lean 4 proof package. It is `no_std`, has zero runtime dependencies, forbids unsafe code, and performs no heap allocation. Its encoder produces the shortest representation within this format. Its runtime performance is measured separately.

The project began with an explicit specification and 351 conformance cases. All eighteen required proof obligations are now proved, including correspondence between the Rust-derived model and the mathematical contract. A capacity specialization reduces full-width `u64` encoding time by 52.5% in the matched Apple M5 experiment, with a small one-byte regression recorded alongside it.

## The format in thirty seconds

Each varint byte carries seven payload bits. The high bit means another byte follows. Payload groups appear least significant first: 300 becomes `ac 02`, because `44 + 2 × 128 = 300`.

| Unsigned value | Canonical bytes (hex) | Length |
|---:|---|---:|
| 0 | `00` | 1 |
| 127 | `7f` | 1 |
| 128 | `80 01` | 2 |
| 300 | `ac 02` | 2 |
| 16,383 | `ff 7f` | 2 |
| 16,384 | `80 80 01` | 3 |
| `u64::MAX` | `ff ff ff ff ff ff ff ff ff 01` | 10 |

The exact length is one for zero, and `ceil(bit_length(value) / 7)` otherwise. The width bound is five bytes for `u32` and ten for `u64`.

ZigZag places small signed magnitudes near zero in the unsigned domain: `0 → 0`, `−1 → 1`, `1 → 2`, `−2 → 3`, `2 → 4`. At the mathematical level, it maps nonnegative `x` to `2x` and negative `x` to `−2x−1`. The implementation handles the full fixed-width signed range, including the minimum signed integer.

## A deterministic core with thin adapters

The boundaries are logical boundaries inside one library. Callers do not assemble separate services, processes, or utility packages.

![bited architecture: integer and byte inputs flow through thin public adapters into a deterministic codec core; Rust source is extracted through Charon and Aeneas into a Lean model checked against contracts.](assets/architecture.svg)

| Surface | Caller gets |
|---|---|
| Unsigned and signed entry points | `u32`/`u64` varints and `i32`/`i64` ZigZag wrappers |
| Fixed-array encoding | Owned stack output and its used prefix |
| Caller-buffer encoding | No allocation; insufficient capacity leaves every byte unchanged |
| Prefix decoding | A value, canonicality flag, and precise consumption count |
| Exact decoding | One complete value; trailing bytes are an error |
| Incremental decoding | Bounded state carried across input chunks |
| Explicit policies | Canonical-only or bounded noncanonical acceptance |

For example, `80 00` denotes zero with a redundant byte. Canonical decoding rejects it; bounded noncanonical decoding accepts zero and marks it noncanonical. Neither policy turns into an unbounded scan. Overflow, excessive length, truncation, noncanonical representation, and trailing bytes have specified behavior and consumption counts.

```rust
use bited::{decode_u64, encode_u64, DecodePolicy};

let bytes = encode_u64(300);
assert_eq!(bytes.as_bytes(), &[0xac, 0x02]);
let number = decode_u64(bytes.as_bytes(), DecodePolicy::Canonical).unwrap();
assert_eq!((number.value, number.consumed, number.canonical), (300, 2, true));
```

## What the proofs establish

The Lean package covers all eighteen obligations in the specification. They include ZigZag bijection, encoder and decoder correctness, canonical uniqueness, minimal encoded length, streaming equivalence, bounds, buffer preservation, and Rust-to-model correspondence.

| Evidence | What it supports | Boundary |
|---|---|---|
| Lean contracts and refinement | Mathematical behavior and correspondence of extracted Rust core entry points | Pinned extraction profile: Apple ARM, 64-bit `usize` |
| Axiom audit and fresh proof replay | Stored proofs check with the pinned Lean kernel; the audit traverses 1,810 project declarations | Standard axioms `propext`, `Quot.sound`, `Classical.choice` |
| 351 original vectors | Contract examples, boundaries, malformed inputs, streaming and buffer behavior | Finite fixtures |
| 200,000 seeded ASan fuzz executions | Additional exercised behavior under instrumented execution | Finite campaign |
| Host and WASI execution; RISC-V compilation | Practical portability checks, including 32-bit targets | Not a compiler-correctness proof |
| Archive rebuilds and checksums | Released artifacts can be tied to verified source and evidence | A changed release candidate requires a new strict gate |

Source refinement does not prove the Rust compiler, machine code, CPU, or operating system correct. The separately invoked proof replay uses the same pinned Lean kernel; it is not an independent second kernel. Users of the Rust crate need Rust 1.88 or later and do not need Lean installed.

## Making a useful fact visible to the compiler

The encoder must accept arbitrary caller slices. Yet no `u64` varint needs more than ten bytes. The optimized entry point makes that bound explicit:

```rust
if out.len() >= 10 {
    encode_u64_into_checked(value, &mut out[..10])
} else {
    encode_u64_into_checked(value, out)
}
```

The checked emitter still computes the required length and checks capacity before writing. For a sufficiently large buffer, it sees a ten-byte slice. Smaller buffers keep the original checked path. The Lean correspondence proof reconstructs the whole caller buffer, including preservation of the suffix outside the ten-byte view.

This is a small source change with a distribution-dependent result. The benchmark passes an opaque caller slice to both implementations, so the comparison does not rely on one caller revealing its array size while the other hides it.

## The measurements, including the inconvenient rows

The following results were recorded on **12 October 2026**, on **Apple M5**, using **Rust 1.88.0**, one thread, optimization level 3, overflow checks enabled, and no LTO. Fifteen repetitions rotate participant order. Before timing, 9,306,112 checks compare canonical bytes, decoded values, and consumption. The previous implementation is the frozen source snapshot `0fdaadf304e6e53ad38942b2ca820c14b8ab771d`.

The values below are mean thread CPU nanoseconds per value, with approximate 95% half-widths. Lower is faster. `short-80-15-5` mixes one-byte, two-byte, and full-width values in those proportions. Full-width uses uniformly generated `u64` values; the large dataset exercises a larger traversal with uncontrolled cache state.

![Encoder comparison across four datasets with approximate 95 percent intervals. bited improves full-width encoding, while one-byte inputs remain close to the previous implementation.](assets/encode-comparison.svg)

| Dataset | bited | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---:|---:|---:|---:|
| One-byte | 1.086 ± 0.010 | 1.059 ± 0.018 | 1.790 ± 0.102 | 1.092 ± 0.011 |
| Short 80/15/5 | 1.326 ± 0.056 | 1.304 ± 0.030 | 2.918 ± 0.035 | 1.387 ± 0.052 |
| Full-width | 2.657 ± 0.041 | 5.593 ± 0.049 | 18.233 ± 0.155 | 5.320 ± 0.055 |
| Large full-width | 3.754 ± 0.099 | 6.281 ± 0.190 | 19.049 ± 0.570 | 6.036 ± 0.162 |

Paired repetitions give a **52.5% time reduction** for full-width encoding (approximately 95% interval: 51.9–53.1%) and **40.2%** for the large traversal (38.7–41.6%). One-byte encoding is **2.7% slower** (0.6–4.8%). The short mixture is 1.8% slower on the point estimate, but its interval crosses zero.

Decoding deserves its own table. The capacity change is an encoder optimization; decoder timing differences are not attributed to it.

| Decode dataset | bited | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---:|---:|---:|---:|
| One-byte | 1.041 ± 0.041 | 4.847 ± 0.029 | 5.570 ± 0.048 | 1.116 ± 0.100 |
| Short 80/15/5 | 5.011 ± 0.068 | 5.010 ± 0.048 | 5.667 ± 0.058 | 5.057 ± 0.063 |
| Full-width | 8.159 ± 0.065 | 8.208 ± 0.066 | 7.365 ± 0.076 | 8.246 ± 0.063 |
| Large full-width | 8.571 ± 0.140 | 8.537 ± 0.107 | 8.482 ± 0.110 | 8.573 ± 0.109 |

`leb128` is faster at full-width decoding in this experiment. The peer APIs also differ in malformed-input behavior: both accept redundant zero in the recorded observations, while bited exposes an explicit canonical policy. Valid-input timings compare speed, not identical feature sets or a universal quality ranking.

The shared host introduces frequency, migration, and cache uncertainty even though thread CPU time excludes descheduling. These results do not establish browser/WASM speed, other-CPU rankings, native `u32` or signed-wrapper performance, PMU counters, or cycles per value. Twelve stack profiles help locate hot functions; they do not remove those limits.

## Weight the workload, not the percentages

A 52.5% improvement on long values and a 2.7% regression on short values cannot be averaged as percentages. Weight the time per operation instead.

Let `p` be the fraction of one-byte values, and let the remaining values follow the measured full-width workload:

```text
T_previous(p) = p × 1.059 + (1 − p) × 5.593
T_bited(p)    = p × 1.086 + (1 − p) × 2.657
```

Using the unrounded recorded means, the crossover is approximately **99.08% one-byte values**: roughly **108 short values per full-width value**. Below that fraction, the capacity change improves the model's mean encoding time. This is a two-population estimate, not a threshold for every possible mixture of two- through ten-byte values.

![Weighted encoding time versus one-byte share. The full-range plot and a zoom near 100 percent show the crossover around 99.08 percent.](assets/weighted-crossover.svg)

Uniformly random `u64` values have one-byte probability `128 / 2^64`, approximately `6.94 × 10^-18`. They overwhelmingly favor the long-value path. Counters, lengths, and delta-coded identifiers can have very different distributions; measure the actual encoded lengths before applying the result.

The practical hardware ceiling also depends on workload. An encoder must write the encoded bytes and read its input. Memory traffic bounds sustained batch throughput, while branches, instruction dependencies, and stores matter for hot scalar calls. These experiments do not determine a universal theoretical maximum.

## Where bited fits

It fits inside binary protocol implementations, append-only logs, storage formats, delta-coded integer streams, embedded firmware, and WebAssembly applications that need explicit bounded behavior. ZigZag is useful when small negative and positive deltas are common. A varint codec alone does not provide message framing, compression, integrity, or application-level size limits.

The smallest base-128 representation is the encoder's proved format-level optimum. Whether that format is best for a particular dataset remains an application decision: mostly full-width random numbers consume more bytes than a fixed eight-byte integer.

## Status and reproducibility

Version 0.1.0 is a prepared release candidate. The GitHub repository and draft release are currently private; the crate has not been uploaded to crates.io. The frozen release evidence belongs to source commit `d9af05c28e0d3114423dfeeb93c31f2ff30588df`. Later CI and article changes do not silently update that evidence.

Portable Rust checks now pass on the repository-scoped `bited-ci-x64` runner on `raps-ci`. Full formal release verification remains a separate pinned local workflow.

Readers with repository access can inspect the [specification](../specification.md), [conformance vectors](../../conformance/vectors.json), [proof status](../proof-status.md), [trust boundary](../trust-boundary.md), and [raw benchmark results](../../verification/performance/results.json). Run `scripts/compare-performance` for the comparison and `scripts/verify` for the strict gate using the documented toolchain. Charts are regenerated from the recorded JSON by `scripts/article-charts.py`; raw timing metadata records the source hashes and the dirty working tree used at measurement time.

The [public article](https://yemelianov.dev/projects/bited/) also appears as a project detail inside the site's WASM portfolio.
