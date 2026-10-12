# Public API performance comparison

Run `./scripts/compare-performance` from the repository root on macOS with the
pinned Rust 1.88 toolchain, Command Line Tools and cached dependencies. For the
first dependency download, use `cargo fetch --manifest-path verification/performance/Cargo.toml --locked`.
The comparison is an isolated executable: production dependencies and the
runtime dependencies stay unchanged. Raw output is written to
`verification/reports/comparison.json`; statistical stack samples and disassembly
are stored beside it. The root `scripts/verify` command separately rebuilds release evidence for the
current source snapshot. Prior measurement snapshots are kept as
`results-before-inline.json` and `RESULTS-before-inline.md`.

Compare `verified-varint` (proposed name `bited`), `leb128 = 0.2.5` and
`integer-encoding = 4.1.0`, plus the prior verified source compiled as
`verified-varint-baseline`. Its exact source hashes and commit are recorded in
`baseline/provenance.json`; its buffers, checks and algorithms match the original
library. All use the same preallocated ten-byte caller buffer
and identical canonical u64 datasets, public prefix decoding of concatenated
values, opt-level 3, overflow checks enabled, no LTO, default CPU target and one
thread. Wrapper adapters inline so implementation dispatch remains outside the
value loop; competitor internals keep their own normal inlining annotations.
Dataset generation, correctness checks and allocation stay outside timing.
Outputs and input slices are black-boxed. Loop/harness costs remain included.

Fifteen repetitions rotate participant order to reduce time/thermal bias.
Reports retain samples, sample SD and approximate t(14) 95% intervals, not a
promise about other machines. Hot datasets are warmed; large traversal cache
state is uncontrolled. No hardware performance counters, branch-miss attribution,
controlled cold-cache test or cross-platform ranking is claimed.

The timed comparison covers the shared u64 wire format, each length 1–10,
full-width, alternating lengths, 80/15/5 short-biased values, ZigZag values near
zero and a large sequential full-width traversal. ZigZag mapping happens outside
timing for all participants: this is not a native signed-wrapper timing.
The benchmark asserts byte equality and value/consumption equality for every
participant and value before timing. Existing full API conformance and Lean
proofs remain separate; comparison checks do not confer proofs on competitors.

Contracts differ. Our timed decoder enforces canonical-only input and reports
structured failure/consumption/canonicality; competitors' decoders accept some
redundant representations. `integer-encoding` requires enough output capacity;
ours promises unchanged buffers on insufficient capacity. Consequently these are
natural public API costs on shared valid inputs, not equal validation work.
Malformed observations show redundancy, truncation, overflow, excessive length
and prefix handling of trailing bytes. These are behavior differences, not a
security ranking or evidence that an accepted noncanonical value is a bug.

Profiling uses macOS `sample`, one millisecond sampling for four seconds, after
all timed measurements. All four participants are sampled on full-width encoding,
full-width decoding and mixed short decoding. Sampling locates hot functions,
not exact instruction or branch costs. The optimized binary retains line-table
information; its digest and disassembly digest are recorded.

Each repeat also records `CLOCK_THREAD_CPUTIME_ID` around the batch. CPU time
excludes time the thread is descheduled; wall time measures user-observed elapsed
time. Timer calls occur once per batch repeat, not once per value. CPU time still
reflects CPU frequency, cache behavior, core migration and contention. Heavy
concurrent tasks can therefore distort both metrics. Interpret wide intervals
as inconclusive and rerun on an idle machine before setting performance targets.
The small unsafe FFI timer call exists only in this executable; the production
library continues to forbid unsafe code.

## Encoder optimization

The library now marks unsigned length/encoder entry points with `#[inline]`,
allowing cross-crate optimization in normal non-LTO builds. Algorithms, error
precedence, buffer atomicity and initialization are unchanged. The caller-buffer
path already writes directly; no temporary-array removal was needed. Regenerated
Lean definitions differ only in source-line doc comments; the normal release
workflow still rechecks extraction, proofs, stored-proof replay and archives.

Comparative improvement is measured against the original source in the same
executable and repetition order. This controls more host drift than comparing
absolute times from separate runs, but concurrent system load remains recorded.
