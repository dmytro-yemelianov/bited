# bited 0.1.0 performance

Measured 2026-10-12T10:52:33.935790+00:00 on Apple M5, Rust 1.88, one thread, optimization 3, overflow checks enabled, no LTO. Fifteen rotating matched repetitions compare bited with pre-specialization source `0fdaadf304e6e53ad38942b2ca820c14b8ab771d` compiled as the historical baseline. Both implementations see an opaque caller slice.

## CPU time per value

Mean thread CPU ns/value ± approximate 95% half-width. Raw CPU/wall samples and source/binary metadata are in results.json.

| Dataset | Operation | bited | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---|---:|---:|---:|---:|
| length-1 | encode | 1.086 ± 0.010 | 1.059 ± 0.018 | 1.790 ± 0.102 | 1.092 ± 0.011 |
| length-1 | decode | 1.041 ± 0.041 | 4.847 ± 0.029 | 5.570 ± 0.048 | 1.116 ± 0.100 |
| short-80-15-5 | encode | 1.326 ± 0.056 | 1.304 ± 0.030 | 2.918 ± 0.035 | 1.387 ± 0.052 |
| short-80-15-5 | decode | 5.011 ± 0.068 | 5.010 ± 0.048 | 5.667 ± 0.058 | 5.057 ± 0.063 |
| full-width | encode | 2.657 ± 0.041 | 5.593 ± 0.049 | 18.233 ± 0.155 | 5.320 ± 0.055 |
| full-width | decode | 8.159 ± 0.065 | 8.208 ± 0.066 | 7.365 ± 0.076 | 8.246 ± 0.063 |
| large-full-width | encode | 3.754 ± 0.099 | 6.281 ± 0.190 | 19.049 ± 0.570 | 6.036 ± 0.162 |
| large-full-width | decode | 8.571 ± 0.140 | 8.537 ± 0.107 | 8.482 ± 0.110 | 8.573 ± 0.109 |

## Paired encoder change

Mean reduction versus Previous, pairing fifteen repetitions; approximate t(14) intervals:

- length-1: -2.7% reduction [-4.8%, -0.6%].
- short-80-15-5: -1.8% reduction [-6.6%, +2.9%].
- full-width: +52.5% reduction [+51.9%, +53.1%].
- large-full-width: +40.2% reduction [+38.7%, +41.6%].

## Scope and tradeoff

Full-width encoding is about twice as fast in this matched executable. Large traversal improves by about 40%. The short-mixture interval crosses zero; one-byte inputs regress by about 2.7% in this run. The long-input benefit is adopted with that tradeoff explicit. The legacy JSON label Verified names bited in this run.

Canonical bytes, values and consumption agree in 9,306,112 checks before timing. Twelve statistical stack profiles locate hot functions. Shared-host CPU time excludes descheduling but not migration, frequency or cache contention. Decode source behavior is unchanged; timing shifts are not a claimed decoder optimization. No PMU, cycle, universal ranking, native signed-wrapper/u32 or other-CPU speed claim is made.

The library retains zero runtime dependencies, no_std and forbidden unsafe code. Full caller-buffer correspondence includes ten-byte subview reconstruction and preservation of every unused byte. The strict verification workflow reports compiler resources separately. Historical results retain their original source identities.
