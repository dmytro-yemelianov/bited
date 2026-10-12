# Fixed-word encoder length preflight

Measured 2026-10-12T08:21:18.743271+00:00 on Apple M5, Rust 1.88, one thread, optimization 3, overflow checks enabled, no LTO. All four implementations run in one executable with rotating order and 15 repetitions. Host load before/after is recorded; this is a shared-host measurement.

The current encoder retains inlining and replaces the iterative length calculation with a one-byte case and `leading_zeros` arithmetic. Previous is the inlined source at b0f071d2b1d4727394020c7c43489b10f3f3a06e. Buffer preflight and atomic failure semantics remain intact.

## CPU time per value

Mean thread CPU nanoseconds/value ± approximate 95% half-width. Wall time and samples are retained in results.json. Smaller is faster.

| Dataset | Operation | Current | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---|---:|---:|---:|---:|
| length-1 | encode | 1.062 ± 0.028 | 1.116 ± 0.025 | 1.773 ± 0.028 | 1.086 ± 0.023 |
| length-1 | decode | 5.029 ± 0.126 | 1.293 ± 0.135 | 5.851 ± 0.133 | 1.373 ± 0.172 |
| short-80-15-5 | encode | 1.262 ± 0.028 | 1.397 ± 0.023 | 2.782 ± 0.034 | 1.298 ± 0.038 |
| short-80-15-5 | decode | 4.934 ± 0.053 | 4.907 ± 0.024 | 5.562 ± 0.046 | 4.966 ± 0.058 |
| full-width | encode | 5.970 ± 0.355 | 8.706 ± 0.485 | 18.691 ± 1.393 | 5.554 ± 0.566 |
| full-width | decode | 10.157 ± 0.426 | 10.276 ± 0.481 | 10.327 ± 0.813 | 10.442 ± 0.569 |
| large-full-width | encode | 6.973 ± 0.646 | 9.384 ± 0.676 | 20.674 ± 1.881 | 6.438 ± 0.516 |
| large-full-width | decode | 8.993 ± 0.362 | 9.342 ± 0.497 | 9.633 ± 0.751 | 9.368 ± 0.590 |

## Paired encoder change

Mean reduction in thread CPU time versus Previous, pairing repetitions. Approximate t(14) intervals describe observed ratio variation.

- length-1: 4.8% reduction (approximately 2.3%–7.3%).
- short-80-15-5: 9.6% reduction (approximately 7.2%–12.0%).
- full-width: 31.3% reduction (approximately 29.0%–33.7%).
- large-full-width: 25.8% reduction (approximately 22.6%–29.0%).

One-byte and mixed encoding are approximately comparable with integer-encoding in this run; full-width encoding remains about 7–8% slower. This is not a fastest-runtime or cross-platform ranking. All source algorithms for decoding remain unchanged.

## Proof and correctness

The new Lean proof establishes exact agreement of the modeled leading-zero primitive with Nat logarithms/bit size, checked arithmetic safety, and equality to the independent minimal encoder length. Dependent encoder, signed, roundtrip, canonicality and resource proofs retain their contracts. Full release validation is recorded separately in the release manifest.

All 9,306,112 implementation/value checks passed across 2,326,528 dataset entries and four implementations. Every binary boundary is additionally tested against leb128, with compile-time zero/max-length checks. Twelve profiles and disassembly are retained with hashes.

## Resource tradeoff and scope

Library object code sections: aarch64 4084 bytes (previous 4028), WASI 4880 (previous 4946), RISC-V 3956 (previous 3422). Code can also move into consumers through inlining. RISC-V hardware speed has not been measured; faster Apple M5 execution does not imply faster execution on every target. State sizes and observed static library call-path frame maxima are unchanged.

Run `./scripts/compare-performance` to reproduce. CPU time excludes descheduling, but core migration, frequency and contention remain uncontrolled. Native signed wrappers, u32 throughput and incremental throughput are outside these shared u64 timing comparisons. Root `./scripts/verify` checks all API contracts and release artifacts. Historical snapshots keep their original source identities.
