# Fixed-word length preflight and encoder optimization

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
