# bitet release-candidate performance

Measured 2026-10-12T10:39:41.537083+00:00 on Apple M5, Rust 1.88, one thread, optimization 3, overflow checks enabled, no LTO. Fifteen rotating matched repetitions compare bitet with pre-specialization source `0fdaadf304e6e53ad38942b2ca820c14b8ab771d` compiled as the historical baseline. Both implementations see an opaque caller slice.

## CPU time per value

Mean thread CPU ns/value ± approximate 95% half-width. Raw CPU/wall samples and source/binary metadata are in results.json.

| Dataset | Operation | bitet | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---|---:|---:|---:|---:|
| length-1 | encode | 1.067 ± 0.024 | 1.029 ± 0.015 | 1.745 ± 0.030 | 1.056 ± 0.013 |
| length-1 | decode | 1.032 ± 0.035 | 4.641 ± 0.045 | 5.309 ± 0.092 | 1.107 ± 0.113 |
| short-80-15-5 | encode | 1.261 ± 0.031 | 1.248 ± 0.015 | 2.748 ± 0.038 | 1.302 ± 0.027 |
| short-80-15-5 | decode | 4.994 ± 0.059 | 4.920 ± 0.041 | 5.635 ± 0.053 | 5.032 ± 0.057 |
| full-width | encode | 2.608 ± 0.026 | 5.464 ± 0.068 | 17.228 ± 0.411 | 5.153 ± 0.043 |
| full-width | decode | 8.640 ± 0.273 | 8.669 ± 0.185 | 8.031 ± 0.333 | 8.861 ± 0.367 |
| large-full-width | encode | 3.835 ± 0.223 | 6.540 ± 0.476 | 18.231 ± 0.620 | 5.913 ± 0.181 |
| large-full-width | decode | 8.476 ± 0.274 | 8.410 ± 0.129 | 8.308 ± 0.068 | 8.367 ± 0.162 |

## Paired encoder change

Mean reduction versus Previous, pairing fifteen repetitions; approximate t(14) intervals:

- length-1: -3.8% reduction [-6.5%, -1.0%].
- short-80-15-5: -1.1% reduction [-3.8%, +1.6%].
- full-width: +52.2% reduction [+51.6%, +52.9%].
- large-full-width: +40.9% reduction [+37.5%, +44.3%].

## Scope and tradeoff

Full-width encoding is about twice as fast in this matched executable. Large traversal improves by about 41%. The short-input intervals cross zero. Source identity and scope distinguish this renamed release-candidate run from before-bitet-results.json and all older snapshots. The legacy JSON label Verified names bitet in this run.

Canonical bytes, values and consumption agree in 9,306,112 checks before timing. Twelve statistical stack profiles locate hot functions. Shared-host CPU time excludes descheduling but not migration, frequency or cache contention. Decode source behavior is unchanged; timing shifts are not a claimed decoder optimization. No PMU, cycle, universal ranking, native signed-wrapper/u32 or other-CPU speed claim is made.

The library retains zero runtime dependencies, no_std and forbidden unsafe code. Full caller-buffer correspondence includes ten-byte subview reconstruction and preservation of every unused byte. The recorded object resources are reported separately by the strict verification workflow.
