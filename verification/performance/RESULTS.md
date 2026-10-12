# Encoder optimization: matched before/after measurements

Measured 2026-10-12T07:48:52.454332+00:00 on Apple M5, Rust 1.88, one thread, optimization 3, overflow checks enabled, no LTO. All four implementations run in the same executable with rotating order and 15 repetitions. The host remained shared (load averages before/after timing are recorded); these are not controlled idle-host measurements.

The production change adds `#[inline]` to six unsigned length/encoder functions. It preserves the source algorithms and buffer/error contract. The source-to-Lean extraction changes only source-line doc comments; complete proof/release verification is recorded separately in the release manifest.

## CPU time per value

Mean thread CPU nanoseconds/value ± approximate 95% half-width. Wall time and every sample are in results.json. Smaller is faster.

| Dataset | Operation | Current | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---|---:|---:|---:|---:|
| length-1 | encode | 1.049 ± 0.017 | 1.439 ± 0.026 | 1.714 ± 0.041 | 1.045 ± 0.017 |
| length-1 | decode | 1.045 ± 0.075 | 4.640 ± 0.025 | 5.396 ± 0.022 | 4.640 ± 0.020 |
| short-80-15-5 | encode | 1.407 ± 0.043 | 1.822 ± 0.054 | 2.803 ± 0.029 | 1.306 ± 0.038 |
| short-80-15-5 | decode | 4.987 ± 0.062 | 4.967 ± 0.028 | 5.619 ± 0.029 | 5.077 ± 0.119 |
| full-width | encode | 7.832 ± 0.043 | 8.203 ± 0.027 | 16.308 ± 0.029 | 5.076 ± 0.050 |
| full-width | decode | 8.229 ± 0.032 | 8.343 ± 0.085 | 7.479 ± 0.241 | 8.207 ± 0.087 |
| large-full-width | encode | 7.937 ± 0.056 | 8.506 ± 0.093 | 16.552 ± 0.211 | 5.496 ± 0.034 |
| large-full-width | decode | 8.317 ± 0.125 | 8.305 ± 0.060 | 8.203 ± 0.072 | 8.344 ± 0.072 |

## Paired encoder change

Mean current/previous CPU-time reduction, pairing samples from each rotated repetition. Approximate t(14) intervals summarize ratio variation and do not eliminate shared-host systematic effects.

- length-1: 27.1% reduction (approximately 25.3%–28.9%).
- short-80-15-5: 22.6% reduction (approximately 19.2%–25.9%).
- full-width: 4.5% reduction (approximately 3.9%–5.2%).
- large-full-width: 6.6% reduction (approximately 5.3%–8.0%).

Current one-byte encoding is approximately tied with integer-encoding. On the short mixture it remains about 8% slower; full-width encoding remains about 1.4–1.5× slower. The remaining length preflight and detailed API checks are candidates for future work, not individually measured causes. A fixed-storage encoder has no caller-buffer preflight, but changing the current atomic buffer contract is not an acceptable shortcut.

## Correctness and profiles

All 9,306,112 implementation/value checks passed for 2,326,528 dataset entries (duplicates included), using all four implementations. Canonical bytes, values and consumed lengths match. Malformed-input observations retain the strict/bounded policy and error differences.

Twelve statistical stack profiles cover all participants on full-width encode, full-width decode and mixed short decode. Disassembly and binary hashes are included. These profiles identify hot functions; they do not quantify branch misses or prove which individual check accounts for the gap.

## Scope and reproduction

Run `./scripts/compare-performance`; the pre-inline source fixture is bound to commit a39937d4fcc5c13904bdfa680e921ee0ad57d446 in baseline/provenance.json. Root `./scripts/verify` separately performs conformance, target checks, fuzzing, Lean closure, stored-proof replay and fresh archive builds.

Timings compare shared u64 wire operations. ZigZag near-zero inputs are mapped outside timing for all participants. Native signed wrappers, u32 throughput and incremental throughput remain outside this comparison. Prior measurements are preserved in results-before-inline.json and RESULTS-before-inline.md.
