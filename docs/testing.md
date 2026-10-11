# Execution evidence

The test suite preserves all 351 supplied JSON cases. It checks both widths and
policies, signed adapters, prefix/exact semantics, fixed arrays, caller-buffer
atomicity, and incremental consumption/terminal/reset behavior. It exhausts every
0–2 byte input, every fifth/tenth final-byte payload and continuation combination,
and all values of reduced abstract widths 1–16. Deterministic random inputs use a
separate widened arithmetic oracle. Partition tests include empty chunks and
retain the unconsumed suffix after a terminal result.

An independent implementation is pinned to
[leb128 0.2.5](https://docs.rs/leb128/0.2.5/leb128/). Tests compare unsigned canonical
emission/decoding and signed ZigZag output using independent widened arithmetic.
Its unsigned decoder accepts redundant forms that canonical mode rejects; its
64-bit reader also accepts values that the u32 boundary rejects. Those differences
are tested explicitly rather than weakening the contract. Signed LEB128 is a
different wire format and is not used as a ZigZag oracle.

Coverage-guided fuzzing uses pinned cargo-fuzz/libfuzzer-sys with AddressSanitizer,
200000 runs, seed 1234567 and maximum input length 128. The target covers arbitrary
byte slices, all four buffer encoders/capacities, signed bit patterns, and stream
push/finish/reset sequences with policy changes. It checks decoding against a
separate arithmetic oracle. Boundary seeds are versioned; temporary learned corpora
are excluded from source. The report records exact configurations, source/seed
hashes, successful run count, and any minimized regressions. Finite fuzzing remains
execution evidence rather than a proof.

The single verification command runs host debug/release tests, WASI execution,
RISC-V no_std compilation, allocation instrumentation, fuzzing and benchmarks.
Calling-thread allocation tracking avoids unrelated test-thread activity; its
recorded count must remain zero. The kernel's unsafe-code prohibition is separate
from the test harness's safe delegation to the system allocator.
