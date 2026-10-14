# Decoder fast-path comparison

Measured 2026-10-14T16:38:20+00:00 on Apple M5 at commit `6a6cfd9` (working tree dirty: this commit's uncommitted harness, baseline and script changes, plus unrelated untracked files), rustc 1.88.0 (LLVM 20.1.5). Settings: one thread, opt-level 3, overflow checks on, no LTO, compiler-default target CPU, debug info 1. Fifteen rotating matched repetitions compare bited with the pre-change source `5f27413dc1d7da1c7e56078a6eefd7d917894c7e`, which is compiled as `verified-varint-baseline` (hashes in `baseline/provenance.json`). Both implementations see an opaque caller slice. Host load average was 3.8–3.9 before and after timing. Raw samples are in `results.json`.

`./scripts/check-decoder-inlining` passed before timing: the probe loop calls `bited::decode::decode_u64_scan` out of line and never calls the public `decode_u64`.

## Paired Verified/Previous change (thread CPU ns per value)

Each repetition gives one Verified/Previous ratio; the approximate 95% interval is t(14) over those 15 ratios. Produced by `./scripts/summarize-comparison`.

| Dataset | Operation | Previous ns | Verified ns | Paired change | Approx. 95% interval |
|---|---|---:|---:|---:|---:|
| length-1 | encode | 1.029 | 1.036 | +0.8% | -0.8% to +2.4% |
| length-1 | decode | 1.022 | 0.459 | -54.9% | -57.4% to -52.4% |
| length-2 | encode | 1.299 | 1.301 | +0.3% | -3.8% to +4.5% |
| length-2 | decode | 1.719 | 0.638 | -60.0% | -65.2% to -54.8% |
| length-3 | encode | 1.515 | 1.557 | +2.8% | +0.2% to +5.4% |
| length-3 | decode | 2.736 | 2.515 | -3.0% | -15.4% to +9.5% |
| length-4 | encode | 1.729 | 1.736 | +0.6% | -2.2% to +3.3% |
| length-4 | decode | 3.103 | 2.919 | -2.4% | -11.5% to +6.7% |
| length-5 | encode | 2.051 | 2.063 | +0.7% | -2.6% to +4.1% |
| length-5 | decode | 5.055 | 2.871 | -42.9% | -45.9% to -39.9% |
| length-6 | encode | 2.280 | 2.236 | -1.3% | -4.7% to +2.1% |
| length-6 | decode | 5.548 | 3.331 | -40.0% | -42.0% to -37.9% |
| length-7 | encode | 2.309 | 2.302 | -0.1% | -3.4% to +3.1% |
| length-7 | decode | 6.020 | 3.506 | -41.6% | -46.6% to -36.6% |
| length-8 | encode | 2.214 | 2.283 | +3.1% | +0.1% to +6.1% |
| length-8 | decode | 6.184 | 3.985 | -35.5% | -38.6% to -32.4% |
| length-9 | encode | 2.570 | 2.498 | -2.7% | -5.1% to -0.4% |
| length-9 | decode | 6.622 | 3.986 | -39.7% | -41.9% to -37.5% |
| length-10 | encode | 2.584 | 2.566 | -0.7% | -2.5% to +1.2% |
| length-10 | decode | 6.768 | 4.202 | -37.9% | -40.3% to -35.5% |
| short-80-15-5 | encode | 1.300 | 1.285 | -0.9% | -6.6% to +4.7% |
| short-80-15-5 | decode | 4.871 | 0.920 | -81.1% | -81.7% to -80.5% |
| full-width | encode | 2.526 | 2.558 | +1.3% | -0.7% to +3.2% |
| full-width | decode | 8.005 | 6.620 | -17.3% | -18.1% to -16.4% |
| alternating | encode | 1.976 | 2.016 | +2.4% | -2.0% to +6.8% |
| alternating | decode | 2.573 | 2.462 | -3.5% | -10.9% to +4.0% |
| zigzag-near-zero | encode | 1.217 | 1.212 | +0.5% | -6.6% to +7.5% |
| zigzag-near-zero | decode | 4.865 | 0.680 | -86.0% | -87.1% to -85.0% |
| large-full-width | encode | 3.696 | 3.702 | +1.3% | -6.0% to +8.6% |
| large-full-width | decode | 8.207 | 6.921 | -15.7% | -17.8% to -13.6% |
| random-length-1-10 | encode | 1.889 | 1.849 | -1.8% | -5.6% to +1.9% |
| random-length-1-10 | decode | 6.864 | 5.916 | -13.2% | -19.8% to -6.6% |
| random-length-1-3 | encode | 1.431 | 1.309 | -6.4% | -16.8% to +4.0% |
| random-length-1-3 | decode | 5.452 | 2.411 | -55.6% | -61.0% to -50.3% |
| large-random-length | encode | 5.444 | 5.489 | +1.3% | -2.3% to +4.9% |
| large-random-length | decode | 9.116 | 8.563 | -6.0% | -7.4% to -4.7% |

## Decode next to the peers (mean thread CPU ns per value)

| Dataset | bited | Previous | leb128 0.2.5 | integer-encoding 4.1.0 |
|---|---:|---:|---:|---:|
| length-1 | 0.459 | 1.022 | 5.228 | 1.074 |
| short-80-15-5 | 0.920 | 4.871 | 5.507 | 4.953 |
| random-length-1-3 | 2.411 | 5.452 | 5.570 | 5.224 |
| random-length-1-10 | 5.916 | 6.864 | 6.354 | 6.531 |
| full-width | 6.620 | 8.005 | 7.597 | 8.217 |
| large-random-length | 8.563 | 9.116 | 10.443 | 8.625 |

## Adoption rule and outcome

The rule was fixed before measuring. Adopt only if (a) the whole short-80-15-5 decode interval lies at or below −50%, and (b) no dataset/operation pair has an interval whose lower bound is above +5%. The short-80-15-5 decode interval is −81.7% to −80.5%, and no lower bound is above +5% (the highest is length-3 encode at +0.2%). `./scripts/summarize-comparison` printed `ADOPTION RULE PASSED`, so the fast path is adopted. Encoding is unchanged code. Its intervals straddle zero or sit within a few percent of it, as expected for the same source in both builds.

Decode gains are largest for one- and two-byte values (length-1 −54.9%, length-2 −60.0%) and for mixes dominated by them. Lengths 3 and 4 show no clear change (intervals include zero). Lengths 5–10 improve by 36–43%. That is consistent with the audit finding that the out-of-line call and its stack-returned `Result`, not the loop itself, dominated the old cost.

## Limits

- Apple M5 only. x86-64 and RISC-V are compiled and tested but not timed here.
- Thread CPU time on a shared, non-idle host (load average about 4); there was no cold-cache control.
- The harness times u64 decoding and maps ZigZag outside timing, so `zigzag-near-zero` measures the u64 path on small values. The signed wrappers, whose `zigzag_u64_to_i64` is now also `#[inline]`, are not re-measured here. The audit measured −84% for `decode_i64` on short-80-15-5 in a separate prototype harness.
- Peer numbers describe these crates through this harness's call pattern only. In the audit's prototype harness `integer-encoding` decoded short values much faster than it does here, so no cross-crate ranking is claimed.
