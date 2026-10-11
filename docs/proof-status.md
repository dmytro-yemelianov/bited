# Proof status and release gates

All P01–P18 have kernel-checkable proof families in the public import closure.
[coverage.json](../verification/coverage.json) records exact theorem names and maps
all 40 explicit public functions/methods to refinement theorems. The release workflow
independently verifies those names, their statements, and their transitive axioms.

| Obligations | Proof coverage |
|---|---|
| P01–P03 | Both widths: mathematical ZigZag bounds, actual Rust correspondence, both inverse compositions |
| P04–P07 | Both encoders and buffers: representation, bounded canonical bytes, exact bit-length formula and shortest length |
| P08–P10 | Canonical uniqueness; both policy decoders sound and complete for every valid prefix and arbitrary suffix |
| P11–P12 | Unsigned/signed actual encode/decode round trips; bounded decoding normalizes to the unique canonical form and preserves canonical input |
| P13 | Both widths/policies: complete result, error precedence, consumption and canonical-flag correspondence; signed/exact adapters composed from these results |
| P14 | Both unsigned/signed buffers: exact capacity errors, whole-buffer atomicity and successful suffix preservation |
| P15 | Actual public incremental APIs agree with slice semantics for every chunk partition, including malformed/truncated input and empty chunks |
| P16 | Reachable-state invariant, finish idempotence, sealed push returns Closed without changing state, reset clears state and changes policy |
| P17 | Bounded byte transitions, trace reads, emissions and abstract cost charges; checked access and fixed storage. Compiler stack/layout and allocation observations are separate evidence |
| P18 | Complete core entrypoint refinement under the pinned extraction configuration; no unproved implementation-correctness assumptions |
| Exact wrappers | All four signed/unsigned exact decoders refine the independent trailing-input contract |

Streaming preconditions concern private state validity. New/reset establish the
invariant, push/finish preserve it, and the reachable-state theorem discharges it
for arbitrary finite public lifecycles. Users do not need to supply an invariant.
Standalone fixed-array accessors assume the private length bound established by
the encoders; combined encoder/accessor contracts have no caller validity premise.

The configured logical allowlist contains only `propext`, `Quot.sound`, and
`Classical.choice`. No `sorryAx`, custom correctness axioms, native evaluation or
manually patched generated functions are admitted. The checker replays stored
terms in a separate process using the same pinned Lean kernel; it is not a second
kernel implementation. `lake build` is one check, not the whole release gate.

Formal coverage is the portable scalar implementation extracted for
`aarch64-apple-darwin`, 64-bit `usize`, no features. Host and 32-bit WASI execute all
351 cases and independent-oracle tests; 32-bit RISC-V verifies `no_std` compilation.
Cross-target formal refinement, compiler correctness, optional protocol adapters,
SIMD, and compiler stack bounds are excluded.

M0 pins the contract; M1 proves the vertical slice; M2 implements every scalar API;
M3 requires this proof closure; M4 checks the packaged source, fresh package build,
and release sidecar. The workflow records actual acceptance in
`verification/reports/verification.json`. M5 has a measured scalar baseline with no
additional fast path. Historical partial M1 evidence is retained under
`verification/history/` and does not describe the completed source.
