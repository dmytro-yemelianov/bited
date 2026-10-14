# Inline u64 decoder fast path

`decode_u64` now inlines one- and two-byte successes into callers and delegates
every other input, including every error, to the unchanged verified scan, kept
out of line as a cold function. The fast path computes exactly the scan's first
one or two iterations; Lean proves `decode_u64_eq_scan`, so every existing
refinement, totality, value and resource theorem carries over unchanged.
Decode wrappers and ZigZag mappings are now `#[inline]`.

The audit found the per-value call boundary, not the loop, dominating short
decodes: a byte-for-byte copy of the loop was 50–82% faster when inlined and no
faster when LLVM declined to inline it. `scripts/check-decoder-inlining` therefore
inspects downstream machine code and fails if the public decoder is called out
of line. Hardware intrinsics were rejected: on Rust 1.88 `core::arch` calls need
`unsafe` even with the feature statically enabled. Word-at-a-time decoding was
rejected as the main path because it regresses lengths 1–8.

Matched comparison against the pre-change source `5f27413` on Apple M5 (paired
Verified/Previous thread CPU change, approximate 95% interval over 15 repeats):

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

The adoption rule, fixed before measuring, required the whole short-80-15-5 decode
interval at or below −50% and no interval with a lower bound above +5%; it passed.
See [comparison](../verification/performance/RESULTS.md) for peers, provenance and
limits. Encoding code is unchanged. The plain `#[inline]` hint was sufficient: the
codegen gate passed without `#[inline(always)]`.

# Bounded-capacity encoder specialization

The public caller-buffer encoder checks whether capacity is at least ten bytes.
If so it delegates to the same checked emitter through `&mut out[..10]`; otherwise
it delegates with the original slice. This exposes the maximum wire length to LLVM
without changing the API, returned length, exact short-buffer errors, atomic failure
or suffix preservation. The emitter still returns its precomputed required length.
Unsigned u32 and signed caller-buffer adapters retain the shared implementation.

The extracted Rust model now includes this dispatch and mutable-subview back function.
Lean proves that the ten-byte path always has sufficient capacity, emitted bytes equal
the independent canonical encoder, and reconstruction preserves every caller byte
beyond the emitted prefix, including bytes beyond the ten-byte view. Existing checked
emitter proofs apply to the shorter path. All public correspondence claims retain
their original contract.

Matched production-library measurements versus release source `0fdaadf` show a
52.5% reduction for full-width u64 encoding (approximate interval 51.9%–53.1%) and
40.2% for large traversal (38.7%–41.6%). The short-mixture result is inconclusive
(−1.8%, interval −6.6% to +2.9%). See [bounded-capacity comparison](../verification/performance/RESULTS-bounded-capacity.md)
for CPU/wall samples, peers, provenance and limitations.

The historical capacity study's weighted model placed the one-byte/full-width
break-even point around 99% one-byte inputs: an approximately 2.883 ns saving on a
full-width value compensated roughly 99 one-byte penalties of 0.029 ns each.
That model depends on the measured paths and input distribution; actual mixture
measurements remain authoritative because branch prediction and code layout vary.
The substantial long-input gain is adopted with the short-input tradeoff explicit.

Library object code grows by 512 bytes on aarch64, 661 on WASI and 688 on RISC-V.
Static library call-path observations remain unchanged; hardware speed on WASI and
RISC-V has not been measured. Compiler correctness and hardware timing remain
outside the source-level Lean correspondence boundary.

# Earlier fixed-word length preflight measurements

The inlined unsigned length function now returns one byte immediately for values
below 128. Otherwise it computes `(70 - value.leading_zeros()) / 7`: the bit length
is `64 - leading_zeros`, and adding six rounds up division by seven. This removes
the iterative preflight scan while preserving minimal length, exact required
capacity, atomic short-buffer failure and the output suffix.

The Aeneas primitive has an existing pure BitVec model. New kernel-checked Lean
lemmas connect it to Nat logarithms and bit size; the length correspondence proves
checked arithmetic safety and agreement with the independent shortest encoder.
The normal release gate audits all dependent obligations and freshly rebuilds
and replays proofs from the archived package. Compiler correctness remains outside
the source-refinement boundary.

Matched Apple M5 measurements versus the immediately preceding inlined source
at `b0f071d2b1d4727394020c7c43489b10f3f3a06e` gave:

| Dataset | Mean CPU-time reduction | Approximate 95% interval |
|---|---:|---:|
| length-1 | 4.8% | 2.3%–7.3% |
| short-80-15-5 | 9.6% | 7.2%–12.0% |
| full-width | 31.3% | 29.0%–33.7% |
| large-full-width | 25.8% | 22.6%–29.0% |

The same executable compares current/previous code, leb128 0.2.5 and
integer-encoding 4.1.0 with rotating order, fifteen repeats, identical u64 values
and caller buffers, Rust 1.88, optimization 3, overflow checks enabled and no LTO.
CPU/wall samples, intervals, source/binary hashes, disassembly and twelve profiles
are in the separate repository harness `verification/performance`. All canonical
bytes, values and consumption counts agree before timing.

Full-width encoding remains about 7–8% slower than integer-encoding in this run.
The host is shared; CPU time removes descheduling but not frequency, migration or
cache contention. Ratio intervals are not performance guarantees on other hosts.
ZigZag input mapping occurs outside timing. Native signed wrappers, u32 and
incremental throughput remain outside this comparison; their correctness remains
covered by the full suite and Lean proofs.

Object code sections changed from 4028 to 4084 bytes on aarch64, 4946 to 4880 on
WASI and 3422 to 3956 on RISC-V. RISC-V hardware timing has not been measured, and
the larger RISC-V object is an explicit tradeoff. These library-only observations
do not predict total consumer code size or formally bound compiler stack usage.

A focused test compares every binary boundary and neighbors to pinned leb128 and
checks compile-time zero/max lengths. The production library still forbids unsafe
code and has no runtime dependencies; timer FFI is confined to the comparison executable.
