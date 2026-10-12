# Resource model

The formal model counts byte transitions, emitted bytes, word-operation charges,
input byte reads, output byte writes and state accesses separately. A word primitive
is a fixed-width arithmetic, bitwise, Boolean or comparison operation. Charges are
conservative allowances for scalar source paths, not a count of CPU instructions.
`Reference.Cost` and its profiles are exported by `Bited.Public`.

`Reference.decodeTrace` follows the same independent fuel/list transition structure
as the decoder. Its erased outcome is proved equal to `decodeAux`; its input reads
are exactly the incorporated-byte count. The actual Rust decoder-body refinements
prove one checked input-byte access and count increment per byte transition; whole
outcome correspondence connects those counts to the trace. They are bounded by 5 or
10 regardless of the supplied suffix length. Prefix charges are `64*reads+16` word
operations and `12*reads+8` state accesses; exact adds one length comparison.

Canonical emission writes exactly L payload bytes. Fixed-array storage initialization
is charged separately: u64 initializes ten bytes; u32 uses that core and copies five
initialized bytes, so its storage-write allowance is `L+15`, with five copy reads.
The fixed-array profiles bound payload transitions by 5/10 and storage writes by 20.
Caller-buffer emission has a fixed-word leading-zero/arithmetic length preflight
and a bounded emission pass. A fixed capacity dispatch exposes a ten-byte subview
when available; the borrow and its reconstruction add no byte-buffer reads/writes
in Rust. Existing conservative fixed header/word allowances cover this dispatch. It writes only
L bytes on success and zero bytes on insufficient capacity. Signed wrappers add fixed
ZigZag/cast work. The internal u32 widening reuses the u64 core without changing wire
values. ZigZag performs a fixed number of scalar operations for each width.

An open `push` invokes at most one transition; sealed push checks terminal state and
incorporates zero bytes. The invariant ensures at most 5/10 incorporated bytes per
session. Finish/reset have fixed work. Total caller work also depends on the number
of invocations, including repeated resets or empty chunks.

Aeneas totality proofs establish checked access and defined arithmetic; transition
lemmas prove width bounds before narrowing and show shift counts stay below 64.
The library uses fixed structs/arrays and no allocator or runtime recursion. Calling-
thread allocator instrumentation exercises every public family and must report zero
allocations. The 64-byte decoder target is checked on the host and 32-bit targets.

State layout and static assembly frames are compiler observations recorded by the
benchmark script, not formal stack/ABI guarantees. Library call-path frame estimates
exclude panic paths, caller/runtime/OS stack and Wasm's operand stack. Abstract costs,
shortest encoded length and measured runtime speed remain separate claims.

The leading-zero intrinsic is modeled as a fixed-word bit operation. Existing
caller-buffer charges remain conservative allowances rather than exact hardware
instruction counts; target lowering and object-code size are measured separately.
