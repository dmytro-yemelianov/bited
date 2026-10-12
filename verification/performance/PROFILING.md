# Encoder profiling: assembly and controlled comparisons

Run: 2026-10-12T09:02:37.300502+00:00; Apple M5; rustc 1.88.0 (6b00bc388 2025-06-23).

## Findings

The opaque-capacity emission loops in the previously collected comparison binary are instruction-for-instruction equivalent modulo registers: `cmp`, conditional bound branch, `orr`, `strb`, `add`, shift by 7, shift by 14, register move, `cbnz`. That is nine static instructions per continuing-byte iteration, not nine cycles. Current adds leading-zero length calculation, capacity preflight, and another initial value comparison. The live precomputed result length also changes register allocation. These are assembly observations, not per-instruction time attribution.

The strongest controlled effect is making capacity 10 visible to the compiler. In this run, the current full-width encoder falls from 5.778 to 2.216 CPU ns/value (61.5% paired reduction; approximate 95% interval 59.5%–63.5%). LLVM removes dynamic capacity/bounds checks and unrolls the write loop into constant-offset stores and value-threshold branches. Current still computes the returned length; the checked-peer and count-return controls lose their now-unneeded preflight. Thus exposing capacity changes several optimizations together.

## Full-width measurements

Mean thread CPU ns/value ± approximate 95% half-width; 21 repeats. All eight codec/capacity conditions rotate together within each repetition.

| Capacity visibility | Current verified API | Bare integer-encoding | Peer + atomic preflight | Count-return prototype |
|---|---:|---:|---:|---:|
| opaque-slice | 5.778 ± 0.236 | 5.562 ± 0.220 | 5.428 ± 0.235 | 5.430 ± 0.167 |
| known-10 | 2.216 ± 0.118 | 2.254 ± 0.200 | 2.288 ± 0.178 | 2.185 ± 0.126 |

Current versus bare peer: paired relative difference about +4.2% for opaque capacity (approximate interval +0.3% to +8.1%). With known capacity the paired interval is approximately −6.2% to +6.0%, so this run does not establish a speed winner. The previously observed 7–8% gap is not a stable universal constant.

Adding the same length/capacity preflight to the peer did not cause a statistically clear slowdown: its paired reduction relative to bare peer is 2.2%, with an interval spanning −1.2% to +5.5%. Therefore preflight instruction presence alone does not quantitatively explain the gap; scheduling, register liveness and code layout matter. These controls are not additive cost accounting.

The benchmark-only CountReturn clone returns its emission counter plus one instead of retaining precomputed required length. It is about 5.5% faster than Current for opaque full-width input in this run (paired interval 1.6%–9.4%), but its mixed-short result is inconclusive and may regress. It is local/always-inline while Current is imported/inline; both inline in the emitted code, but optimizer staging and layout remain confounders. It has finite execution checks, not Lean correspondence. It has not been adopted into the production library.

## Practical usage

A normal fixed caller buffer exposes its capacity without weakening the library contract:

```rust
let mut out = [0u8; 10];
let used = verified_varint::encode_u64_into(value, &mut out)?;
// consume &out[..used]
```

The control keeps the array pointer opaque before converting to a slice, so LLVM still sees length 10. The opaque control black-boxes the complete slice pointer/length pair. Values stay opaque in both. This models a relevant caller distinction rather than precomputing the encoded output. Opaque capacity is still representative of generic dynamic-buffer callers. The larger unrolled consumer code is a code-size tradeoff.

## Validation and evidence

6,591,872 comparisons passed before timing, checking complete output arrays, returned lengths and exact short-buffer errors across capacities 0–12, boundary values and all datasets. Bare peer is only tested when space is sufficient. The checked controls reproduce atomic failure and suffix preservation on these finite inputs.

Eight additional three-second, one-millisecond stack profiles, optimized disassembly, binary digest, source digests and all CPU/wall samples are bound in profile-controls.json. Known batch symbol `h25edeb1f1f558923` has one CLZ (Current) and 349 instructions over all four codec branches; opaque symbol `h2a83a2ea0ea08be5` has three CLZ sites and 263 instructions. These are whole harness-function sizes, not isolated library code-size measurements. Sample offsets locate hot functions but do not give exact instruction stall costs.

The standalone comparison binary and archive retain reproducibility. Run `./scripts/profile-encoder`; dependencies are pinned in the separate harness Cargo.lock. No production Rust, Lean or conformance source was changed; their hashes match release commit `0fdaadf304e6e53ad38942b2ca820c14b8ab771d`. The existing release manifest belongs to that frozen source snapshot; the profiling harness is supplementary evidence.

## Limits and next experiment

Shared-host CPU time excludes descheduling but not migration, frequency or cache contention. Approximate t(20) intervals summarize repetitions, not systematic errors. Neither branch-miss nor hardware-counter measurements were obtained. Static instruction counts cannot be converted into cycle estimates. This study covers u64 encoding on Apple M5, not native signed wrappers, u32 throughput, streaming, or other CPUs.

The strongest follow-up candidate is a production fast path that exposes a bounded ten-byte subview when a dynamic caller provides at least ten bytes, retaining the current short-buffer path. This requires measured dynamic-caller benefit, new source/model correspondence and suffix/atomicity proofs before adoption. Count-return is a secondary candidate, with mixed-input performance requiring further validation.
