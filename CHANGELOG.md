# Changelog

## 0.1.0 — first release candidate

- Allocation-free unsigned 32/64-bit base-128 encoding and signed ZigZag mappings.
- Exact encoded lengths, initialized fixed storage and caller-provided buffers.
- Canonical and explicitly selected bounded noncanonical decoding, prefix/exact APIs,
  and fixed-state incremental decoders with precise errors and consumption counts.
- Atomic short-buffer failure and preservation of the unused output suffix.
- Eighteen Lean 4 proof obligations, including source-level Rust correspondence,
  canonical uniqueness, shortest encoded length and streaming equivalence.
- Bounded-capacity encoder specialization; the recorded Apple M5 comparison reduces
  full-width u64 encoding time by about 53% and large traversal time by about 40%.
  Short-input results and other-CPU performance are separate measured questions.
- Rust 1.88 MSRV, no runtime dependencies, no_std and forbidden unsafe library code.

The working package name was verified-varint. The first public name is bited;
historical specifications and measurement records retain their original identities.

Publication date and registry status are recorded when the release is published.
