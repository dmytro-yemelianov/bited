# Encoder inlining and measured comparison

Unsigned encoder/length entry points now carry `#[inline]`, letting ordinary
non-LTO consumers optimize across the crate boundary. The caller-buffer encoder
already writes directly to the supplied buffer; no temporary array was removed.
Length preflight, atomic short-buffer failure, preserved suffix, fixed-storage
initialization and all encoding algorithms are unchanged.

Pinned Rust-to-Lean extraction differs only in source-line doc comments. The
actual generated definitions and proof statements are unchanged. The full
release workflow rechecks correspondence, all 18 obligations, axiom closure,
stored-proof replay and fresh Rust/Lean archives for the modified Rust source.
Compiler optimization remains outside the formal source-refinement boundary.

The separate repository command `./scripts/compare-performance` compares current
and previous source in the same executable, along with leb128 0.2.5 and
integer-encoding 4.1.0. The old source is bound to Git commit
`a39937d4fcc5c13904bdfa680e921ee0ad57d446`. All participants use identical canonical
u64 datasets and preallocated caller buffers, one thread, Rust 1.88, optimization
3, overflow checks enabled, default CPU target and no LTO. Fifteen repetitions
rotate order. CPU and wall time, samples, approximate intervals, source/binary
hashes and twelve stack profiles are recorded. Byte/value/consumption agreement
passes before timing. These observations do not prove competitor APIs.

On Apple M5, paired thread CPU-time reductions versus the previous source were:

| Dataset | Mean reduction | Approximate 95% interval |
|---|---:|---:|
| One-byte values | 27.1% | 25.3%–28.9% |
| 80/15/5 short-biased mixture | 22.6% | 19.2%–25.9% |
| Full-width values | 4.5% | 3.9%–5.2% |
| Large full-width traversal | 6.6% | 5.3%–8.0% |

One-byte encoding was approximately tied with integer-encoding. The short mixture
remained about 8% slower and full-width encoding about 1.4–1.5 times slower. Our
full-width encoding used about half leb128's CPU time. Decoder source is unchanged.
This is a shared-host run, with load averages near 4–5; it is not a controlled
idle-host ranking. Thread CPU time removes descheduling, but frequency, cache
contention and core migration remain uncontrolled. Ratio intervals describe the
observed repetitions, not universal performance guarantees.

The timed comparison covers shared u64 wire operations, with ZigZag near-zero
values mapped outside timing for all participants. Native signed wrappers, u32
and incremental throughput remain outside this comparison. Canonical validation,
structured errors and buffer atomicity differ across APIs. This measures their
natural costs on shared valid inputs rather than identical validation work.
The comparison executable's tiny unsafe CPU-timer FFI is separate from the
production library, which continues to forbid unsafe code.
