# Scalar baseline benchmarks

Run `./scripts/benchmark` or the complete `./scripts/verify` workflow. The complete raw samples and metadata are recorded in `verification/reports/benchmark.json`; release sidecars bind that report by digest. Measurements characterize the checked scalar API, with no optimized alternative or speed-optimality claim.

The baseline was measured on Apple M5, rustc 1.88.0 (6b00bc388 2025-06-23), one thread, opt-level 3, overflow checks enabled, no LTO/features and the compiler default target CPU. Source and benchmark hashes are recorded. Dataset generation and allocation are outside timed regions; `black_box` protects inputs/results. Public buffer/prefix/exact checks remain in the measured path.

Each workload has nine repeats, raw ns/value samples, sample standard deviation, standard error and an approximate t(8) 95% interval. Shared-host noise is uncontrolled; the interval describes these samples rather than guaranteeing future performance. Latency includes loop and black-box overhead. Batch decoding uses concatenated ordinary varints.

Workloads separately cover every encoded length, full-width values, an 80% one-byte / 15% two-byte / 5% full-width mixture, signed values around zero and at extremes, alternating lengths, sequential/shuffled values, and boundary errors under both policies. The seed is `766172696e743031`; distributions and input sizes are recorded. Hot inputs are warmed once. A large full-width traversal is reported separately, with uncontrolled cache state; no controlled cold-cache claim is made.

| Target | Object code section bytes | Decoder state bytes | Largest observed library static call path |
|---|---:|---:|---:|
| aarch64-apple-darwin | 5196 | 48 | 64 bytes |
| wasm32-wasip1 | 5406 | 32 | 32 bytes |
| riscv32imac-unknown-none-elf | 3830 | 32 | 48 bytes |

These resource figures come from the pinned compiler: `llvm-size`, an LLVM-IR layout probe and emitted assembly. Archive size includes metadata and is reported separately. Static call paths exclude caller/OS/runtime, panic paths, Wasm operand stack and final-link changes. They are observations, not formal compiler stack bounds. The calling-thread allocator test must observe zero allocations on host and WASI.

The report also provides values/second and encoded bytes/second for every dataset. Abstract transition/access/operation charges are defined in [resources.md](resources.md). Minimal encoded length is a Lean theorem; neither that theorem nor these timings establish fastest runtime.
