# Trust boundary

The Rust core is safe scalar code, `no_std`, with no runtime dependencies, heap
allocation or recursion. Checked slice/array access, final-payload validation and
capacity preflight are part of the extracted functions and their totality proofs.
The independent Lean specification uses Int/Nat arithmetic and byte lists.
Generated Lean is produced by pinned Charon/Aeneas without manual edits; refinements
connect every explicit core entry point to the reference semantics.

Proofs trust Lean's kernel and the inventoried allowed logical axioms, Rust's chosen
extraction semantics, Charon/Aeneas, and the pinned Aeneas primitive Rust models.
No project-specific correctness axioms or additional external primitive models are
introduced. Abstract resource charges are a declared accounting model described in
[resources.md](resources.md). They are separate from measured processor performance.
The axiom audit inventories every project declaration imported by the public package.
Fresh stored-proof replay uses the same pinned kernel in a separate process.

Source-level refinement does not prove the compiler, linker, operating system,
processor or execution runner correct. Hashes bind source, models, tools and artifacts;
they establish identity rather than compiler correctness. Tests, fuzzing, allocation
instrumentation, layout/assembly observations and benchmarks are execution evidence.

The formal profile is `aarch64-apple-darwin`, 64-bit `usize`, scalar code, no features.
Both widths and policies are formally covered in that profile. Host and 32-bit WASI
provide execution evidence; RISC-V bare metal provides a `no_std` compile check.
Neither 32-bit check is described as a cross-target formal proof.

The Cargo archive is compiled, compared with source and re-extracted. The Lean archive
is rebuilt and replayed with fresh project outputs. That reproduction shares checked,
pristine dependency build caches and the host tool installation; it is not an isolated
second-machine experiment. The manifest records this distinction and the dependency
commits. Cargo consumers do not need proof tooling. Standard formatting/derived trait
machinery is outside the explicit codec-entrypoint theorem inventory.

No machine-code correctness, constant-time execution, confidentiality, corruption
repair, complete message canonicalization or external protocol acceptance is claimed.
Encoded length and early termination are value-dependent. Callers enforce application
limits before using decoded values as lengths and preserve trailing bytes when parsing
multiple payloads.
