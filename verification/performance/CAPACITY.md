# Dynamic-capacity specialization experiment

This supplements the frozen verified release; it does not change production Rust or Lean. The candidates are benchmark-only and have finite differential validation, not new Rust-to-Lean correspondence proofs.

## Candidates

All retain exact capacity errors, complete buffer preservation on failure, canonical bytes and untouched suffixes on the tested inputs.

- `FastCapacity`: when capacity is at least ten, pass a ten-byte subview to the count-return emitter; otherwise use its checked dynamic path.
- `FastRequired`: the same capacity branch, delegating both paths to the existing verified encoder. This retains its precomputed returned length and isolates capacity specialization from the count-return change.
- `EarlySmall`: handle one-byte values first, then use FastCapacity.

Current, bare integer-encoding, checked integer-encoding and the previous count-return control remain in the experiment. Fourteen codec/capacity conditions rotate together per repetition. Both values and the complete pointer/length pair are opaque in the dynamic case; the fixed case retains an opaque array pointer with visible length ten. Timing uses a ten-byte buffer; correctness checks cover capacities zero through twelve.

## Measurements

Host: Apple M5; rustc 1.88.0 (6b00bc388 2025-06-23); recorded 2026-10-12T09:45:25.102105+00:00.

Three runs, each with 21 repetitions and twelve datasets. **42,690,168 whole-buffer/return/error comparisons passed** across boundary values and capacities 0–12. Eight stack profiles completed successfully. Production inputs match release commit `0fdaadf304e6e53ad38942b2ca820c14b8ab771d`.

Each cell gives Current → candidate mean thread CPU ns/value, followed by paired time reduction and its approximate 95% interval. Negative reduction means a slowdown. These are batch throughput measurements, not isolated-call latency.

| Run / opaque-capacity workload | FastCapacity | FastRequired | EarlySmall |
|---|---|---|---|
| 1 / full-width | 5.499 → 2.621; +52.3% [+51.5, +53.2] | 5.499 → 2.622; +52.3% [+51.3, +53.3] | 5.499 → 2.610; +52.5% [+51.7, +53.3] |
| 1 / short-80-15-5 | 2.361 → 1.935; +18.0% [+17.0, +19.0] | 2.361 → 1.842; +21.9% [+20.7, +23.1] | 2.361 → 1.945; +17.6% [+16.0, +19.2] |
| 1 / length-1 | 0.990 → 1.012; -2.2% [-3.5, -1.0] | 0.990 → 1.029; -3.9% [-5.3, -2.4] | 0.990 → 1.022; -3.2% [-4.2, -2.2] |
| 1 / length-10 | 3.447 → 2.579; +25.1% [+23.3, +26.8] | 3.447 → 2.585; +24.8% [+23.0, +26.7] | 3.447 → 2.949; +14.3% [+5.3, +23.3] |
| 2 / full-width | 5.454 → 2.586; +52.5% [+51.6, +53.5] | 5.454 → 2.562; +53.0% [+52.0, +54.0] | 5.454 → 2.584; +52.6% [+51.5, +53.6] |
| 2 / short-80-15-5 | 2.395 → 1.930; +19.3% [+17.4, +21.3] | 2.395 → 1.834; +23.3% [+21.4, +25.3] | 2.395 → 1.909; +20.2% [+18.5, +21.9] |
| 2 / length-1 | 1.073 → 1.072; -0.2% [-3.3, +2.8] | 1.073 → 1.086; -1.4% [-5.7, +2.8] | 1.073 → 1.077; -1.4% [-7.2, +4.5] |
| 2 / length-10 | 3.400 → 2.595; +23.5% [+21.4, +25.6] | 3.400 → 2.621; +22.8% [+20.9, +24.6] | 3.400 → 2.600; +23.4% [+21.2, +25.6] |
| 3 / full-width | 5.449 → 2.596; +52.3% [+51.8, +52.9] | 5.449 → 2.569; +52.8% [+52.2, +53.5] | 5.449 → 2.600; +52.3% [+51.5, +53.0] |
| 3 / short-80-15-5 | 2.346 → 1.931; +17.6% [+16.7, +18.6] | 2.346 → 1.838; +21.6% [+20.3, +22.9] | 2.346 → 1.909; +18.6% [+17.6, +19.6] |
| 3 / length-1 | 0.991 → 1.039; -4.9% [-6.1, -3.8] | 0.991 → 1.028; -3.8% [-5.0, -2.5] | 0.991 → 1.025; -3.5% [-4.8, -2.2] |
| 3 / length-10 | 3.399 → 2.553; +24.9% [+23.8, +25.9] | 3.399 → 2.577; +24.1% [+23.0, +25.3] | 3.399 → 2.586; +23.9% [+22.0, +25.8] |

Fixed-capacity controls and all length-specific datasets are available in the companion JSON; the table selects workloads that expose the main tradeoff.

Optimized batch-function excerpts are preserved in `capacity-assembly.txt`. The two generic batch instances contain 617 and 669 static instructions across all seven codec branches, with two and seven CLZ sites respectively. These are whole harness function counts, not isolated encoder costs or CPU cycles. The extra constant-offset store sequences make the code-layout tradeoff visible.

## Interpretation and decision

Making a bounded subview visible inside the encoder recovers much of the fixed-capacity throughput for dynamic callers. It adds a capacity dispatch and changes generated code and layout. The count-return change is not necessary to obtain the long-input benefit: FastRequired also benefits.

The one-byte workload regresses in the matched experiment. An early one-byte branch does not consistently eliminate this cost. Short mixtures are particularly sensitive to generated code layout: exploratory runs with a different set of control branches produced substantially different absolute timings and even a different sign for the mixed-input change. Consequently these measurements establish a useful specialization opportunity, not a universal speed improvement or the theoretical hardware ceiling.

No candidate is adopted into the default library in this study. It would trade a short-input cost for long-input throughput, and changing the public implementation also requires correspondence proofs for mutable subview reconstruction and suffix preservation. The verified release and its eighteen obligations retain their existing source snapshot. Finite differential checks are not a substitute for those proofs.

## Reproduction and evidence

Run `./scripts/profile-capacity` on the macOS host with the pinned Rust toolchain. It executes three matched runs, captures eight one-millisecond stack profiles, and writes optimized disassembly, source/binary digests, CPU/wall samples and host metadata under `verification/reports/`. The script checks production Rust, Lean, tests and root toolchain/build inputs against the frozen release manifest and aborts if they differ. Versioned `capacity-study.json` records this study's completed run.

The host is shared. Thread CPU time excludes descheduling but still reflects frequency, migration and cache contention. Approximate paired t(20) intervals describe within-run repetitions; they do not quantify those systematic effects. Runs are reported separately rather than pooled as independent measurements. There are no PMU, branch-miss or per-instruction stall measurements. Sampling locates hot functions and cannot establish cycle costs. Local candidates use always-inline adapters while the imported production function uses inline; optimizer staging and layout remain part of the measured effect. Other CPUs, native u32 and signed wrappers are outside this experiment.
