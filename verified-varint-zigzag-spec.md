# Verified Varint + ZigZag
## Implementation and verification specification

**Document ID:** VVZ-SPEC-0.1.0  
**Status:** Proposed design; implementation and proof obligations are not yet fulfilled  
**Date:** 2026-10-11  
**Implementation:** Rust  
**Specification and proofs:** Lean 4  
**Working package name:** `verified-varint` — availability has not been checked  
**Primary deliverable:** One reusable library and one corresponding proof package

> Build a small, deterministic integer-encoding kernel whose behavior, failure modes,
> resource limits, and correspondence to the published Rust source can be checked.
> Prove minimal encoded length within the specified base-128 format; measure speed
> on actual machines. Do not conflate those two claims.

The words **MUST**, **MUST NOT**, **SHOULD**, and **MAY** express requirements of this
project specification. They do not assert additional requirements of Protobuf,
WebAssembly, or another external format. Source references `[S1]`–`[S7]` appear at
the end. Uncited architectural choices below are proposed project decisions.

---

## 1. Purpose and scope

The library provides unsigned base-128 variable-length integer encoding and a
separate, reversible ZigZag mapping for signed integers. It is a reusable primitive,
not a message format, container, schema language, compression framework, or runtime.

The wire representation is the ordinary least-significant-group-first, seven-payload-
bits-per-byte representation used for unsigned Protobuf varints. Protobuf `sint32`
and `sint64` apply ZigZag before this representation. `[S1]`

### 1.1 Required scope for the first complete release

| Area | Required behavior |
|---|---|
| Integer widths | `u32`, `u64`, `i32`, `i64`; no platform-sized wire types |
| Encoding | Deterministic, shortest-form unsigned encoding; signed encoding through ZigZag |
| Decoding | Canonical policy and explicitly selected bounded noncanonical policy |
| Input styles | Prefix slice, exact slice, and incremental byte-at-a-time decoding |
| Output styles | Fixed-capacity value object and caller-provided mutable slice |
| Failure handling | Typed errors, deterministic precedence, exact consumption counts |
| Runtime | `no_std`, no heap allocation, no I/O, no global mutable state |
| Baseline implementation | Safe, portable, scalar Rust with zero third-party runtime dependencies |
| Formal verification | Wire semantics, ZigZag bijection, round trips, error behavior, streaming equivalence, resource bounds, Rust-model refinement |
| Distribution | Cargo package, Lake proof package, conformance fixtures, verification manifest |

### 1.2 Non-goals

Do not implement signed LEB128, Protobuf `int32`/`int64` signed-field compatibility,
Protobuf messages or tags, QUIC variable-length integers, arbitrary-precision
integers, `u128`, SIMD batch formats, compression dictionaries, or a new wire format
in the first release. ZigZag is **not** signed LEB128. QUIC varints are a different
encoding and must not be advertised as supported.

No claim is made that varints beat fixed-width integers for every distribution,
that ZigZag is globally optimal for signed data, or that the implementation is the
fastest possible executable. No constant-time or cryptographic guarantee is offered.

A CLI, C ABI, WASM binding, or protocol adapter may be added later, outside the core.
They must not delay a useful library release or expand the scope of its guarantees
without their own contracts.

## 2. Architecture: one product, a small deterministic kernel

Use logical microkernel-style boundaries: a minimal pure mechanism with adapters
around it. This is a library architecture, not an operating system. It requires no
process isolation, message broker, plugin loader, scheduler, or IPC per integer.

```text
Caller / protocol adapter / optional diagnostic CLI
                      |
            Typed public Rust API
                      |
        +-------------+--------------+
        |                            |
  ZigZag mapping              Unsigned codec
        |                     /             \
        +-----------------> encoder      decoder transition
                                            |
                                    incremental state
                      |
            No I/O or allocation below

Lean: mathematical semantics -> executable reference -> Rust-derived model
                                      \___________________________/
                                             refinement proofs
```

### 2.1 Responsibilities

| Module | Sole responsibility |
|---|---|
| `zigzag` | Bijection between a fixed-width signed and unsigned domain |
| `encode` | Canonical bytes and exact encoded length |
| `decode` | One bounded unsigned value and its error semantics |
| `stream` | Carry decoder state across input boundaries |
| `api` | Typed wrappers and caller-buffer contracts |

The slice decoder and incremental decoder SHOULD share the same scalar transition
logic. A specialized fast path is allowed only after equivalence to that transition
system is established. Keep all modules in one Rust crate unless a concrete
consumer requires a split. Callers must not have to orchestrate several utilities.

### 2.2 Engineering constraints

The default library MUST use `#![no_std]` and `#![forbid(unsafe_code)]`. It MUST NOT
require `alloc`, a C compiler, network access during compilation, a runtime allocator,
or platform-specific CPU instructions. Tests and benchmarks may use `std` and dev
dependencies. The library must work without Lean installed on the consumer's machine.

Avoid elaborate macros, generic arithmetic frameworks, and hidden code generation
until the Rust-to-Lean translation route is proven on the actual API. Public
32-bit and 64-bit entry points are sufficient; a generic Lean model may cover both.

## 3. Mathematical domains and notation

For a width `W`:

```text
U_W = {x in Nat | 0 <= x < 2^W}
I_W = {n in Int | -2^(W-1) <= n < 2^(W-1)}
N_W = ceil(W / 7)
R_W = W - 7 * (N_W - 1)
LAST_MAX_W = 2^R_W - 1
```

The public Rust widths are `W = 32` and `W = 64`.

| Width | Maximum bytes `N_W` | Bits available in last byte `R_W` | Maximum last payload |
|---|---:|---:|---:|
| 32 | 5 | 4 | `0x0f` |
| 64 | 10 | 1 | `0x01` |

For a byte `b`, `payload(b) = b & 0x7f` and `continues(b) = (b & 0x80) != 0`.
Lists use zero-based indexing. `a ++ b` denotes concatenation. Bit operations in
mathematical definitions are not permission to use unchecked machine arithmetic.

## 4. Unsigned wire semantics

A nonempty byte sequence `b[0..k)` represents `x` when:

1. Every byte except the final one has its continuation bit set.
2. The final byte has its continuation bit clear.
3. `x = sum(payload(b[i]) * 2^(7*i), i = 0..k-1)`.

A **bounded representation** additionally satisfies `k <= N_W` and `x < 2^W`.
Equivalently, if `k == N_W`, its final payload must not exceed `LAST_MAX_W`.

A bounded representation is **canonical** when `k == 1` or the final payload is
nonzero. Zero is encoded as exactly `00`. No encoder in this release emits padding.

Examples below are integer payloads only, with no Protobuf field tag:

| Unsigned value | Canonical bytes, hexadecimal | Length |
|---:|---|---:|
| 0 | `00` | 1 |
| 1 | `01` | 1 |
| 127 | `7f` | 1 |
| 128 | `80 01` | 2 |
| 150 | `96 01` | 2 |
| 300 | `ac 02` | 2 |
| 16,383 | `ff 7f` | 2 |
| 16,384 | `80 80 01` | 3 |
| `u32::MAX` | `ff ff ff ff 0f` | 5 |
| `u64::MAX` | `ff ff ff ff ff ff ff ff ff 01` | 10 |

### 4.1 Exact length and the permitted optimality claim

```text
L(0) = 1
L(x) = ceil(bit_length(x) / 7), for x > 0
```

The canonical encoder MUST emit exactly `L(x)` bytes. The proof must show that no
shorter nonempty representation under Section 4's seven-bit grouping rules encodes
the same value. This does **not** compare against another coding family, external
schema information, block compression, or an assumed probability distribution.

Proof outline to formalize: a representation of `k` bytes has value below `2^(7*k)`;
canonical encoding chooses exactly the necessary groups. Zero needs one byte because
empty representations are disallowed. Canonical encoding is unique.

## 5. ZigZag semantics and implementation requirements

Define the mapping over mathematical integers, avoiding fixed-width overflow:

```text
ZZ_W(n) = 2*n       when n >= 0
ZZ_W(n) = -2*n - 1  when n < 0

UNZZ_W(u) = u/2             when u is even
UNZZ_W(u) = -(u+1)/2        when u is odd
```

Division in this definition is exact on the indicated branch. The definition is
mathematical: computing `u + 1` at `u64::MAX` in a `u64` is not a valid implementation.
Similarly, `abs(i64::MIN)` is not a safe way to implement the forward mapping.

| Signed input | ZigZag value | Encoded bytes |
|---:|---:|---|
| 0 | 0 | `00` |
| -1 | 1 | `01` |
| 1 | 2 | `02` |
| -2 | 3 | `03` |
| 63 | 126 | `7e` |
| -64 | 127 | `7f` |
| 64 | 128 | `80 01` |
| -65 | 129 | `81 01` |
| `i32::MAX` | `2^32 - 2` | `fe ff ff ff 0f` |
| `i32::MIN` | `2^32 - 1` | `ff ff ff ff 0f` |
| `i64::MAX` | `2^64 - 2` | `fe ff ff ff ff ff ff ff ff 01` |
| `i64::MIN` | `2^64 - 1` | `ff ff ff ff ff ff ff ff ff 01` |

The following are candidate scalar implementations, not delivered verified code:

```rust
pub const fn zigzag_i32_to_u32(n: i32) -> u32 {
    ((n as u32) << 1) ^ ((n >> 31) as u32)
}

pub const fn zigzag_u32_to_i32(u: u32) -> i32 {
    ((u >> 1) as i32) ^ -((u & 1) as i32)
}

pub const fn zigzag_i64_to_u64(n: i64) -> u64 {
    ((n as u64) << 1) ^ ((n >> 63) as u64)
}

pub const fn zigzag_u64_to_i64(u: u64) -> i64 {
    ((u >> 1) as i64) ^ -((u & 1) as i64)
}
```

Rust defines signed right shifts as arithmetic and same-width signed/unsigned casts
as preserving the bit pattern. The refinement proof must connect those semantics
and the unsigned left shift to the mathematical mapping. `[S3]` Do not copy a C
expression and assume identical language semantics. All fixed shift amounts must be
strictly smaller than the operand width.

Signed encoding is precisely `encode_unsigned(ZZ_W(n))`. Signed decoding first
performs the corresponding unsigned decode with the selected policy, then applies
`UNZZ_W`. It inherits all byte errors and consumption counts unchanged.

## 6. Decode policies and compatibility boundaries

```rust
pub enum DecodePolicy {
    Canonical,
    BoundedNonCanonical,
}
```

**Canonical** accepts only the bounded canonical language. **BoundedNonCanonical**
also accepts redundant zero groups, but never more than `N_W` bytes and never a
value outside `U_W`. Both policies check unused high bits. Neither truncates an
out-of-range integer to the requested width.

For example, `80 00` represents zero: canonical decoding rejects it;
bounded-noncanonical decoding returns zero and `canonical: false`.

There MUST NOT be a global configuration switch. Callers choose the policy explicitly.
Any later convenience entry point that omits a policy MUST use `Canonical` and state
that default in its documentation. All encoders remain canonical regardless of a
decoder's policy.

### 6.1 External format claims

| External use | Permitted statement | Important exclusion |
|---|---|---|
| Protobuf `uint32` / `uint64` | Canonical integer payloads use the same base-128 representation | No blanket claim of matching every runtime's malformed-input acceptance |
| Protobuf `sint32` / `sint64` | Canonical integer payloads use unsigned encoding after ZigZag | Not Protobuf `int32` / `int64` |
| WebAssembly unsigned LEB128 | Candidate primitive for `u32`/`u64` fields when using bounded-noncanonical decoding | Not a complete WASM parser or signed LEB128 implementation |

Protobuf negative `int32` and `int64` values use a different signed interpretation
and require ten-byte wire values, rather than ZigZag. `[S1]` Such adapters are out of
scope. Do not parse a ten-byte sign-extended `int32` with the five-byte `u32` core.

WebAssembly permits certain non-shortest encodings within its width and unused-bit
constraints. `[S2]` A canonical-only decoder must not be advertised as a drop-in
validator for all valid WASM integers. Any compatibility adapter must pin its target
specification and test corpus, then state its acceptance policy independently.

## 7. Decode algorithm and error semantics

### 7.1 Scalar reference algorithm

The following pseudocode defines decisions and their order. `W`, `N`, and `last_max`
are fixed for an entry point, not supplied by an untrusted caller.

```text
acc = 0
for i in 0 .. N:
    if i == input.length:
        return Truncated(consumed = i)

    byte = input[i]
    p = byte & 0x7f
    continuation = (byte & 0x80) != 0

    if i == N - 1 and p > last_max:
        return Overflow(consumed = i + 1)

    if i == N - 1 and continuation:
        return TooLong(consumed = i + 1)

    # Only now incorporate p; its shift is known to fit.
    acc = acc OR (p << (7*i))

    if not continuation:
        canonical = (i == 0) OR (p != 0)
        if policy == Canonical and not canonical:
            return NonCanonical(consumed = i + 1)
        return Decoded(value = acc, consumed = i + 1, canonical = canonical)

# No path reaches this point.
```

An implementation MUST validate the last payload before shifting it. A masking
operation that silently discards invalid high bits is not an acceptable overflow check.

### 7.2 Errors

```rust
pub enum DecodeErrorKind {
    Truncated,
    Overflow,
    TooLong,
    NonCanonical,
    TrailingBytes,
}

pub struct DecodeError {
    pub kind: DecodeErrorKind,
    pub consumed: usize,
}
```

| Error | Meaning | `consumed` |
|---|---|---|
| `Truncated` | Finalized input ended before a terminator or width-limit failure | Number of provided bytes already processed, possibly zero |
| `Overflow` | Payload bits exceed the target width at the last permitted byte | `N_W` |
| `TooLong` | The last permitted byte still requests continuation, with an otherwise admissible payload | `N_W` |
| `NonCanonical` | A terminated bounded representation is longer than the shortest form, under canonical policy | Full representation length |
| `TrailingBytes` | Exact API decoded one value successfully but input contains additional bytes | Length of the first value, not the full input |

At the last permitted byte, `Overflow` takes precedence over `TooLong`. Thus the
last byte `82` at position ten for `u64` yields `Overflow`, not `TooLong`.
`NonCanonical` is considered only after width checks and termination. `TrailingBytes`
is considered only after prefix decoding succeeds under the selected policy.

A single slice call that contains exactly `N_W` continuation bytes returns `TooLong`
(or `Overflow`), **not** `Truncated`. No eleventh byte is required to reject a `u64`.
Errors must be identical in debug and optimized builds.

### 7.3 Prefix versus exact decoding

Prefix decoding handles exactly one integer and ignores later values for semantic
purposes. For `00 80`, it succeeds with zero and `consumed = 1`. Exact decoding of
the same input returns `TrailingBytes` with `consumed = 1`.

The input is immutable. The core never advances a caller-owned cursor automatically.
On failure, the reported count describes this attempt, including the decisive byte
when there is one. It is diagnostic information, not an instruction to resynchronize.
A surrounding format must decide whether to abort, roll back, or skip a framed field.

An optimized decoder may perform an in-bounds wide load within the first
`min(input.len(), N_W)` bytes. It must not make its result depend on bytes after the
first terminator, report an error from that suffix, or read beyond the supplied
slice. Logical consumption and physical load width are distinct proof obligations.
The scalar reference loads only the bytes it processes.

## 8. Rust API contract

Names below define the proposed API. A change is allowed before implementation only
when this specification and its conformance fixtures are updated together.

```rust
pub struct Decoded<T> {
    pub value: T,
    pub consumed: usize,
    pub canonical: bool,
}

pub struct EncodeError {
    pub required: usize,
    pub available: usize,
}

pub struct Encoded32 { /* private [u8; 5] and length */ }
pub struct Encoded64 { /* private [u8; 10] and length */ }

pub fn encoded_len_u32(value: u32) -> usize;
pub fn encoded_len_u64(value: u64) -> usize;
pub fn encoded_len_i32(value: i32) -> usize;
pub fn encoded_len_i64(value: i64) -> usize;

pub fn encode_u32(value: u32) -> Encoded32;
pub fn encode_u64(value: u64) -> Encoded64;
pub fn encode_i32(value: i32) -> Encoded32;
pub fn encode_i64(value: i64) -> Encoded64;

pub fn encode_u32_into(value: u32, out: &mut [u8]) -> Result<usize, EncodeError>;
pub fn encode_u64_into(value: u64, out: &mut [u8]) -> Result<usize, EncodeError>;
pub fn encode_i32_into(value: i32, out: &mut [u8]) -> Result<usize, EncodeError>;
pub fn encode_i64_into(value: i64, out: &mut [u8]) -> Result<usize, EncodeError>;

pub fn decode_u32(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<u32>, DecodeError>;
pub fn decode_u64(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<u64>, DecodeError>;
pub fn decode_i32(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<i32>, DecodeError>;
pub fn decode_i64(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<i64>, DecodeError>;

pub fn decode_u32_exact(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<u32>, DecodeError>;
pub fn decode_u64_exact(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<u64>, DecodeError>;
pub fn decode_i32_exact(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<i32>, DecodeError>;
pub fn decode_i64_exact(input: &[u8], policy: DecodePolicy)
    -> Result<Decoded<i64>, DecodeError>;
```

`Encoded32` and `Encoded64` expose `as_bytes() -> &[u8]` and `len() -> usize`.
Only the valid prefix is exposed; unused bytes are initialized to zero. Length is
always nonzero. These small value objects and result types SHOULD implement useful
standard traits such as `Copy`, `Clone`, `Debug`, `Eq`, and `PartialEq` where applicable.
Do not promise a stable binary layout or C ABI in this release.

### 8.1 Caller-buffer atomicity

For `encode_*_into`:

* Compute or otherwise establish the required length before modifying the output.
* If capacity is insufficient, return `EncodeError` and leave the **entire** output
  slice unchanged. The error corresponds to `OutputTooSmall` in the JSON fixtures.
* On success, write exactly the canonical representation into `out[..written]` and
  leave `out[written..]` unchanged.
* Do not require callers to reserve the maximum length if the actual value is shorter.

Fixed-array staging or a verified length preflight are both allowed. The resource
model must include that work; do not benchmark a preflight-free internal primitive
as though it were the public atomic API.

A valid API call with arbitrary bytes must not panic. Panicking on a malformed
integer, a short output buffer, or end of input violates the contract.

## 9. Incremental decoder state machine

Provide `DecoderU32` and `DecoderU64`. A signed stream consumer can apply ZigZag
inverse to a completed unsigned value; separate signed machines are unnecessary.

```rust
pub enum Step<T> {
    NeedMore,
    Done(Decoded<T>),
    Error(DecodeError),
    Closed,
}

// Corresponding DecoderU32 methods return u32 results.
impl DecoderU64 {
    pub fn new(policy: DecodePolicy) -> Self;
    pub fn push(&mut self, byte: u8) -> Step<u64>;
    pub fn finish(&mut self) -> Result<Decoded<u64>, DecodeError>;
    pub fn reset(&mut self, policy: DecodePolicy);
    pub fn bytes_seen(&self) -> usize;
}
```

Internal state is private. It stores the policy, accumulator, accepted-byte count,
and a status sufficient to preserve the final result. It does not retain the input
buffer, allocate, borrow a caller's chunk, or keep a history of bytes.

### 9.1 Transition contract

| Current state | Input/action | Result and next state |
|---|---|---|
| Ready | `push(b)` | Perform byte zero of Section 7 |
| Running | `push(b)` | Perform the next byte transition |
| Ready/Running | Valid nonfinal byte | `NeedMore`; incorporate exactly one byte |
| Ready/Running | Valid final byte | `Done`; incorporate one byte and seal success |
| Ready/Running | Invalid byte | `Error`; include the decisive byte and seal failure |
| Ready/Running | `finish()` | Store and return `Truncated`, including zero-byte input |
| Done | `finish()` | Return the stored successful result unchanged |
| Failed | `finish()` | Return the stored error unchanged |
| Done/Failed | `push(b)` | Return `Closed`; do not incorporate the supplied byte |
| Any | `reset(policy)` | Return to Ready with count and accumulator zero |

`push` consumes one byte on `NeedMore`, `Done`, or `Error`, and zero on `Closed`.
All counts in `Decoded` or `DecodeError` are cumulative since the last reset.
`finish` consumes no bytes. Repeated `finish` calls are idempotent.

Empty chunks require no calls to `push`; they are not end-of-input signals. A
chunk adapter MUST stop at `Done` or `Error` and retain the remainder. The adapter
must not continue advancing a cursor over bytes for which `push` would return
`Closed`.

### 9.2 Invariants

While awaiting more data after `c` accepted bytes:

```text
0 <= c < N_W
all accepted bytes have continuation = 1
acc = sum(payload(b[i]) * 2^(7*i), i = 0..c-1)
acc < 2^(7*c)  (with acc = 0 when c = 0)
```

The next shift is `7*c < W`. Width checks precede incorporation of the final
allowed payload. Terminal states cannot silently accept a second value. A reset is
explicit, including the next policy.

### 9.3 Streaming equivalence

For every byte sequence and every partition into chunks, including empty chunks,
feeding bytes until the first terminal outcome and then finalizing if necessary
must match prefix slice decoding in:

* returned value or error kind;
* cumulative consumed-byte count;
* canonicality flag;
* remaining, unconsumed suffix.

Do not call `finish` between ordinary chunks. The proof includes malformed inputs,
not merely successful encodings. Exact-input validation remains a wrapper that
checks the enclosing input boundary after a successful value.

## 10. Formalization and proof obligations

Organize proofs in three layers. Keep the public contract layer independent of the
chosen optimization and of generated internal function names.

**Semantic layer:** arithmetic over `Nat`/`Int`, byte lists, representation relations,
canonicality, and bounded languages. Use a width parameter with an explicit `W > 0`
assumption; instantiate it at 32 and 64.

**Executable reference layer:** a terminating encoder, parser, and transition system.
Connect executable functions to the relations, including failure classification.
Do not define the specification to be whatever the optimized Rust function returns.

**Implementation layer:** a model extracted from the actual Rust source, connected
to the executable reference and then to the semantic contract. Use bit-vector or
fixed-width arithmetic models as appropriate. Prove array/slice wrapper behavior,
not just the inner arithmetic loop.

### 10.1 Required public theorem inventory

Names are proposed stable theorem names, not claims that those theorems exist yet.

| ID | Proposed theorem | Required statement |
|---|---|---|
| P01 | `zigzag_bounds` | Mapping stays inside the corresponding signed/unsigned domains |
| P02 | `zigzag_left_inverse` | `UNZZ_W(ZZ_W(n)) = n` for every `n` in `I_W` |
| P03 | `zigzag_right_inverse` | `ZZ_W(UNZZ_W(u)) = u` for every `u` in `U_W` |
| P04 | `encode_represents` | Emitted bytes represent the input according to Section 4 |
| P05 | `encode_canonical` | Encoder emits a bounded canonical representation |
| P06 | `encode_length_exact` | Returned length equals `L(x)` and is within `1..N_W` |
| P07 | `encode_length_minimal` | No shorter representation in the specified format represents the same value |
| P08 | `canonical_unique` | Two canonical representations of the same value are byte-identical |
| P09 | `decode_sound` | Every successful prefix decode has the declared value and a valid prefix for its policy |
| P10 | `decode_complete` | Every prefix valid under a policy is accepted, independent of its suffix |
| P11 | `decode_encode` | Canonical decode of encoded unsigned/signed values recovers the value and length |
| P12 | `reencode_normalizes` | Successful bounded decoding followed by encoding yields the unique canonical form; canonical input is unchanged |
| P13 | `decode_errors_exact` | Each rejection matches the prescribed failure and precedence, including at byte limits |
| P14 | `encode_into_frame` | Successful writes affect only the output prefix; short buffers remain wholly unchanged |
| P15 | `stream_partition_invariant` | Incremental and slice results agree for every chunk partition and failure case |
| P16 | `stream_terminal_stable` | Closed/finished states and reset behavior satisfy Section 9 |
| P17 | `cost_bounds` | Transition counts, checked access ranges, and fixed-memory behavior satisfy Section 11 |
| P18 | `rust_refines_reference` | Every shipped core entry point's Rust-derived model meets the reference contract and cannot panic on valid API calls |

P18 is a family of theorems, indexed by functions and covered configurations. A
single theorem about `decode_u64` does not automatically cover `u32`, signed wrappers,
streaming, output writes, or an optional fast implementation.

Add an exact-decoding theorem that combines the prefix contract with the total-input
length test. Prove signed wrappers by composition with P02/P03 instead of duplicating
an unrelated signed decoder.

### 10.2 Proof integrity

The release proof closure MUST NOT depend on `sorryAx`, project-specific unproved
correctness axioms, or assumptions asserting that the candidate implementation
already meets the desired contract. Scan transitive dependencies, not only local
source text.

Maintain a reviewed axiom allowlist. Standard Lean logical axioms such as `propext`,
`Quot.sound`, and `Classical.choice` may appear if recorded. Any additional axiom or
native-evaluation trust mechanism requires explicit approval and disclosure; it
cannot silently enter the default proof profile. Lean documents both axiom inspection
and rechecking stored proofs. `[S5]`

`lake build` success alone is not the complete acceptance criterion. Build all
exported contract modules, inspect their axiom dependencies, and recheck them with
the pinned checker where supported. Keep experimental or admitted work outside the
release module closure and label it clearly.

## 11. Resource and security contracts

### 11.1 Machine-independent bounds

| Operation | Required bound |
|---|---|
| ZigZag map/inverse | Fixed number of word operations for a fixed width |
| Canonical emission | Exactly `L(x)` emitted bytes, at most 5 or 10 loop iterations in the scalar emitter |
| Length computation | Bounded work; a scalar division/shift model takes at most `N_W` group steps |
| Atomic `encode_into` | At most one bounded length pass plus one bounded emission pass, or an equivalent fixed-array staging strategy |
| Prefix decode | At most `N_W` byte transitions, independent of total supplied slice length |
| Exact decode | Prefix work plus a length comparison; do not scan the trailing suffix |
| Incremental `push` | One bounded transition, or a terminal-state check |
| Incremental session | At most `N_W` incorporated bytes before success/failure; total call cost also depends on the number of caller invocations |
| Auxiliary storage | Fixed-size state and fixed arrays; zero heap allocations; no recursion |

The Lean cost model MUST say what it counts: byte transitions, emitted bytes,
word operations, and memory accesses as separate measures. These are not CPU cycles,
energy measurements, or a worst-case wall-clock guarantee under an operating system.

The core MUST NOT read outside its input slice, write outside its output slice, shift
by the word width, wrap an accumulated value accidentally, or rely on a particular
host endianness. Width checks must precede narrowing conversions. Wire values must
not depend on `usize` width.

State layout and stack use must be measured for supported targets. A small-state
budget of at most 64 bytes per incremental decoder is an engineering target, not an
ABI promise or a proved compiler stack bound. Record actual values before release.

### 11.2 Security boundaries

Canonical decoding removes redundant encodings at this primitive boundary, but does
not make an entire containing message canonical. Bounded-noncanonical mode deliberately
permits multiple byte strings for a value. Applications signing or hashing messages
must define which byte representation is authoritative.

A decoded integer used as a length is not automatically safe to allocate. Callers
must enforce application limits and use checked conversion to platform-sized lengths.
Do not add allocation to the primitive merely because a decoded length is available.

Encoded length reveals information about the value. Early termination and branches
are value-dependent. The library must not be marketed as constant-time, confidential,
self-authenticating, or resistant to intentional data modification.

The decoder does not repair corrupted bytes or resynchronize a damaged stream. It
also does not limit the total work of a caller that repeatedly creates/reset decoders
or supplies infinitely many empty chunks.

## 12. Rust-to-Lean verification route and trust boundary

The preferred initial route is:

```text
Pinned Rust source + features + extraction target
                    |
               Charon output
                    |
          Aeneas Lean translation
                    |
     Rust-derived functions and support models
                    |
       Refinement to the reference semantics
                    |
          Public reusable contract theorems
```

Aeneas supports a subset of safe Rust and provides a Lean backend; unsupported
operations may require additional models. Its documented limitations and translation
interface must be checked against the pinned revision. `[S4]` Do not assume that
`forbid(unsafe_code)` alone guarantees extractability.

### 12.1 Mandatory feasibility gate

Before expanding the implementation, translate and prove a vertical slice containing:
ZigZag at the signed minimum, one complete `u64` decoder, the last-byte overflow
check, and one caller-buffer encoder. This tests casts, shifts, loops, mutable slices,
results, and error paths on the real public boundary.

If a construct is unsupported, first simplify the Rust or add a justified reusable
model. A manually written Lean counterpart may still be useful, but it must be
reported as a model—not as proof that the unlinked Rust implementation is correct.

### 12.2 Trusted components that must be disclosed

The claim rests on the chosen Rust semantics and extraction/translation path,
reviewed external primitive models, Lean's kernel and allowed axioms, build tools,
and the source-to-artifact mapping. Compiling and running Rust additionally relies
on the compiler, linker where relevant, target machine, and execution environment.

A source-level refinement theorem is **not** a machine-code correctness proof.
Reproducible builds and artifact hashes bind identities; they do not prove compiler
correctness. The manifest must distinguish these facts.

Do not manually patch generated Lean functions to make the proof pass. Regenerate
them from the published Rust source. Missing external definitions may be modeled in
separate, versioned files, with the relationship to Rust reviewed and documented.

### 12.3 Configuration coverage

For the initial release, use one portable scalar implementation with no runtime
backend dispatch. Pin the extraction target and integer-width assumptions. Test at
least a 64-bit host, a 32-bit target, and a `no_std` target. Distinguish test coverage
from formal coverage unless target-independent refinement is actually established.

Later optimizations or conditional compilation paths require their own correspondence
proofs, or explicit unverified status outside the default verified profile.

## 13. Conformance tests

The companion file `verified-varint-zigzag-vectors.json` contains proposed fixtures
for this contract. It is a test artifact, not a proof and not a replacement for an
external format's conformance suite. Decimal integer values are strings so a JSON
consumer cannot silently round 64-bit values.

### 13.1 Mandatory edge cases

| Width/input | Policy | Expected result |
|---|---|---|
| Either: empty | Either | `Truncated`, consumed 0 |
| Either: `80` | Either | `Truncated`, consumed 1 |
| Either: `80 00` | Canonical | `NonCanonical`, consumed 2 |
| Either: `80 00` | BoundedNonCanonical | Zero, consumed 2, canonical false |
| Either: `00 80` | Either, prefix API | Zero, consumed 1, canonical true |
| Either: `00 80` | Either, exact API | `TrailingBytes`, consumed 1 |
| 32: `ff ff ff ff 0f` | Either | `u32::MAX`, consumed 5 |
| 32: `80 80 80 80 10` | Either | `Overflow`, consumed 5 |
| 32: `80 80 80 80 80` | Either | `TooLong`, consumed 5 |
| 32: `80 80 80 80 90` | Either | `Overflow`, consumed 5 |
| 64: nine `ff`, then `01` | Either | `u64::MAX`, consumed 10 |
| 64: nine `80`, then `02` | Either | `Overflow`, consumed 10 |
| 64: ten `80` | Either | `TooLong`, consumed 10 |
| 64: nine `80`, then `82` | Either | `Overflow`, consumed 10 |
| 64: nine `80`, then `00` | Canonical | `NonCanonical`, consumed 10 |
| 64: nine `80`, then `00` | BoundedNonCanonical | Zero, consumed 10, canonical false |

Also test every `2^(7*k)-1`, `2^(7*k)`, and `2^(7*k)+1` that fits the width; signed
minima/maxima; and the signed one-byte boundary `[-64, 63]`.

### 13.2 Test categories

**Exhaustive reduced models:** check every value for small abstract widths and all
byte strings of length zero, one, and two. This exercises the generic semantics; it
does not substitute for universal proofs at 32 and 64 bits.

**Property tests:** unsigned and signed round trips; exact lengths; canonical
uniqueness; bounded decode followed by canonical re-encoding; suffix independence;
error precedence; immutable input; short-output atomicity; reset and finish behavior.

**Streaming tests:** all partitions of each selected short representation, empty
chunks inserted at arbitrary boundaries, every truncation point, and identical tests
for malformed inputs. Ensure adapters preserve the suffix after a terminal result.

**Differential tests:** compare canonical output and valid-input results with pinned
independent implementations. Record policy differences. If another decoder truncates
out-of-range values or accepts longer encodings, do not weaken this contract simply
to make the test green.

**Fuzzing:** arbitrary byte slices, output capacities, operation sequences on the
incremental state machine, and signed bit patterns. Use minimized regression cases.
The Rust implementation must not share its encoder as the sole oracle for decoding.

**Memory and portability:** debug/release configurations, overflow checks, applicable
memory-checking tooling, 32-/64-bit targets, and a `no_std` compile check. Test any
optimized load at short slice lengths and at allocation/page boundaries.

## 14. Performance methodology

Optimization starts after the scalar implementation and its reference relationship
are stable. Candidate improvements include a one-byte fast path, unrolled scalar
paths, branch layout, efficient length calculation, and safe bounded word loads.
No speed claim is accepted without equivalent semantics and boundary checks.

### 14.1 Workloads

Benchmark uniform distributions **by encoded length**, mixtures dominated by one-
and two-byte values, uniform full-width values, signed values around zero, signed
extremes, alternating lengths, sequential and shuffled inputs, and malformed inputs
near each decisive boundary. Disclose distribution weights and seeds.

Measure both one-value latency and large-array throughput. In batch experiments,
keep the wire format unchanged: concatenated ordinary varints. A SIMD format with a
separate control stream is another project, not a faster interchangeable backend.

### 14.2 Measurements and acceptance

Report nanoseconds per value, values per second, encoded bytes per second, code size,
state size, and allocation count. Where reliable, add cycles, instruction counts,
and branch/cache events. Distinguish hot-cache and cold/streaming data.

Pin CPU model, architecture, compiler, optimization flags, target CPU flags, features,
thread count, input size, and benchmark version. Protect results from constant
folding and dead-code elimination. Include the actual public API's checks and
dispatch costs. Report repeated measurements and uncertainty.

The baseline's performance is evidence to establish, not an invented percentage
target. An optimization is accepted only if it preserves all observable contracts,
has coverage for its code path, and demonstrates a measured tradeoff on named
workloads. A regression elsewhere must be reported rather than hidden in a single
aggregate score.

Theoretical minimum **encoded length**, abstract operation bounds, and measured CPU
performance must appear as separate result categories.

## 15. Repository and developer workflow

Recommended single-repository layout:

```text
verified-varint/
  Cargo.toml
  Cargo.lock
  rust-toolchain.toml
  lean-toolchain
  lakefile.toml
  lake-manifest.json
  src/
    lib.rs
    zigzag.rs
    encode.rs
    decode.rs
    stream.rs
  lean/
    VerifiedVarint/
      Spec/Bytes.lean
      Spec/Unsigned.lean
      Spec/ZigZag.lean
      Reference/Encode.lean
      Reference/Decode.lean
      Reference/Stream.lean
      Proofs/Canonical.lean
      Proofs/Length.lean
      Proofs/Roundtrip.lean
      Proofs/Errors.lean
      Proofs/Streaming.lean
      Proofs/Resources.lean
      Generated/
      Refinement/
      Public.lean
  tests/
  fuzz/
  benches/
  conformance/vectors.json
  verification/
    coverage.json
    axioms-allowlist.json
    toolchain-lock.json
    manifest.schema.json
  scripts/
    verify
    regenerate-model
    check-proof-closure
    check-package
  docs/
    specification.md
    proof-status.md
    trust-boundary.md
    benchmarks.md
```

Configure Lake's source directory explicitly for `lean/`; do not assume the proposed
layout works with default module paths. Cargo distributes Rust packages, while Lake
manages Lean modules and dependencies. `[S6][S7]`

Expose **one verification command**, `./scripts/verify`, that performs locked build,
model regeneration, proof checking, axiom audit, tests, and artifact consistency
checks. Supporting scripts are implementation details, not a pipeline that users
must reconstruct manually. Provide a documented clean-environment invocation.

Pin exact versions/commits during the feasibility gate. Do not place invented
"latest" version numbers in this specification. The proof toolchain may require a
different Rust build from the consumer MSRV; record both and test compatibility.

## 16. Release evidence and reuse

Publish a normal Cargo crate and a corresponding Lake package. Verification is a
release/development activity, not a mandatory Cargo build dependency for users.
Publish stable theorem names so downstream Lean projects can reuse them without
re-proving byte parsing or ZigZag algebra.

### 16.1 Verification manifest

The project-defined manifest MUST record:

| Field group | Required content |
|---|---|
| Identity | Spec version, crate name/version, source commit, source/package digests |
| Tools | Rust extraction toolchain, consumer MSRV, Lean, Charon, Aeneas, checker revisions |
| Configuration | Features, target assumptions, covered modules and entry points |
| Claims | P01–P18 coverage, theorem names, exact statement/module digests, proof status |
| Trust | Axiom inventory, external primitive models, translation/compiler assumptions |
| Reproduction | Verification command, dependency locks, generated-model digests |
| Evidence | Test and benchmark report locations/digests; not mislabeled as proofs |
| Exclusions | Optional adapters or optimizations outside the claimed proof scope |

The manifest is not an established industry standard and does not require a custom
registry. Its schema belongs to this project until an external schema is deliberately
adopted. A signature proves provenance, not mathematical correctness.

A manifest containing the hash of the final `.crate` archive must be a sidecar, not
embedded inside the archive whose final hash it names. Verify the published package
contents against the source and generated-model inputs. Re-run extraction/proofs
from unpacked publication inputs, or provide a checked mapping that rules out local
unpublished changes.

### 16.2 Claim levels

Use separate labels: **specified**, **reference proved**, **Rust-model refinement
proved**, **publication linkage checked**, and **target tested**. Do not collapse
these into an ambiguous green "verified" badge. The initial deliverable is currently
only **specified**.

An optimization update must refresh code correspondence, not only reuse an old
algorithm theorem. Strengthening preconditions, changing accepted bytes, changing
error precedence, or changing consumption semantics is a public contract change.
Public theorem signatures are versioned API as well.

## 17. Delivery milestones and acceptance gates

No calendar estimate or fixed lines-of-code target is part of acceptance. Keep the
codec compact, but do not remove validation or hide dependencies to reduce a count.

| Milestone | Deliverable | Exit gate |
|---|---|---|
| M0 — Contract | Pinned wire semantics, error table, vectors, threat/trust boundary | Review resolves every width, policy, final-byte and consumption case |
| M1 — Vertical slice | Rust ZigZag, `u64` decode, atomic encode; working extraction | Endpoints and malformed inputs modeled; actual Rust functions refine the reference |
| M2 — Complete scalar API | 32/64-bit, signed wrappers, exact/prefix APIs, state machine | All API tests pass; no allocation/panic paths; no unmodeled public wrapper |
| M3 — Proof closure | P01–P18 plus exact-wrapper and configuration coverage | Clean proof build; axiom audit; no unproved implementation assumptions |
| M4 — Publication | Cargo/Lake artifacts, manifest, documentation, reports | Clean-environment reproduction and packaged-source linkage checks pass |
| M5 — Optimization | Measured fast paths or optional later adapters | Each new path has an explicit proof and compatibility status |

Do not start with SIMD, a registry service, a plugin framework, or a broad Protobuf
implementation. Ship M4 before widening the domain. M5 is not a prerequisite for a
useful, honestly characterized scalar library.

### Definition of done for the first complete release

A consumer can encode and decode every supported integer; select canonical or
bounded-noncanonical decoding deliberately; stream bytes without losing boundaries;
handle malformed inputs and short output buffers deterministically; and import the
matching Lean contracts. An independent reviewer can reproduce the checks for the
published Rust source and inspect every remaining assumption.

## 18. Agent execution instructions

Begin with the mathematical specification and fixed fixtures. Implement the smallest
scalar vertical slice that demonstrates Rust-to-Lean correspondence. Extend the same
transition semantics to the remaining API rather than writing unrelated decoders.

When a proof fails, classify the cause as an implementation bug, specification bug,
missing lemma, or tool limitation. Do not weaken an error condition, add an axiom,
switch to silent truncation, or edit generated code just to obtain a successful build.
Document unresolved obligations in the coverage file without calling them proved.

Keep source-independent test oracles. Do not regenerate expected test output from
the implementation under test. For benchmark work, retain both the proof-linked
baseline and the candidate until equivalence and measurements are reviewed.

The handoff must contain runnable build/test/verification instructions and actual
status, not placeholder checks or a claim of optimality based only on benchmarks.

## 19. Companion fixture manifest

**Filename:** `verified-varint-zigzag-vectors.json`  
**Schema:** `verified-varint-conformance/0.1`  
**SHA-256:** `b4b8310ba4a8da63780d86e8f6734b7d91ef75bf09e0e45a551783541618d662`

The fixture file includes canonical unsigned examples, signed ZigZag examples,
policy-specific prefix/exact failures, streaming sessions, and output-buffer
atomicity cases. Expected values follow this proposed contract. Preparation checks
compare a mathematical list-based oracle with a separate transition algorithm;
these checks are not Lean proofs or execution tests of a delivered Rust crate.

## 20. Primary references

References establish external format and tooling facts. This specification's APIs,
error names/precedence, milestones, cost contracts, and verification manifest are
project decisions, not quotations or requirements of those external projects.

**[S1] Protocol Buffers — Encoding.** Base-128 varints and the distinction between
signed `intN` and ZigZag `sintN` fields.  
https://protobuf.dev/programming-guides/encoding/

**[S2] WebAssembly Core Specification — Binary Values / Integers.** Unsigned and
signed LEB128 width restrictions and permitted non-shortest encodings. Pin a revision
before making a protocol-adapter compatibility claim.  
https://webassembly.github.io/spec/core/binary/values.html

**[S3] The Rust Reference — Operator expressions.** Fixed-width casts, shifts, and
integer operator semantics used by the proposed bit-level implementation.  
https://doc.rust-lang.org/reference/expressions/operator-expr.html

**[S4] Aeneas — official repository and usage documentation.** Rust functional
translation, Lean backend, Charon integration, and supported-subset limitations.  
https://github.com/AeneasVerif/aeneas

**[S5] Lean Reference — Validating a Lean Proof.** Axiom inspection, proof-closure
considerations, and stored-proof rechecking.  
https://lean-lang.org/doc/reference/latest/ValidatingProofs/

**[S6] The Cargo Book — Publishing on crates.io.** Rust package publication.  
https://doc.rust-lang.org/cargo/reference/publishing.html

**[S7] Lean Reference — Lake.** Lean package/build management.  
https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/

External references were checked on 2026-10-11. Their development branches and
"latest" documentation may change; implementation/release evidence must use pinned
versions rather than relying on this retrieval date.
