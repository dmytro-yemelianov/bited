# Using bitet

Use bitet for bounded base-128 integers in binary protocols, records and telemetry.
Small unsigned values and small ZigZag signed values encode compactly. Arbitrary
full-width u64 values can occupy ten bytes; use fixed-width storage when that better
fits the format. Varint's shortest representation is relative to its own format.

## Caller buffers

```rust
use bitet::{decode_i64_exact, encode_i64_into, DecodePolicy};

let mut output = [0xa5; 16];
let used = encode_i64_into(-150, &mut output).unwrap();
let value = decode_i64_exact(&output[..used], DecodePolicy::Canonical).unwrap();
assert_eq!(value.value, -150);
assert!(output[used..].iter().all(|byte| *byte == 0xa5));
```

On insufficient capacity the entire output buffer remains unchanged and the error
reports required/available capacity. On success only the encoded prefix is written.
Fixed-storage `encode_u32`, `encode_u64`, `encode_i32` and `encode_i64` are alternatives
when no existing buffer is available. All core operations avoid heap allocation.

## Prefix versus exact decoding

Use `decode_u64` or its typed siblings when another value may follow the first.
Advance by `Decoded.consumed`. Use `decode_u64_exact` when the complete slice must
contain exactly one integer; it rejects a trailing suffix.

`DecodePolicy::Canonical` rejects redundant encodings. Select
`BoundedNonCanonical` explicitly when a protocol accepts them; width and overflow
checks still apply. `Decoded.canonical` records whether the accepted encoding was
minimal. Both policies process at most five bytes for u32 or ten for u64.

Signed APIs mean ZigZag, rather than two's-complement or signed LEB128. A complete
message format still needs its own field/frame handling around the numeric codec.

## Incremental input

Create `DecoderU32` or `DecoderU64`, then feed each incoming byte to `push`.
`NeedMore` continues the same value. `Done` and `Error` seal the decoder. Reset before
feeding a new value; `Closed` consumes no byte. At the end of an open frame, `finish`
reports truncation or returns the stored terminal result. Empty input is truncated.

`examples/stream.rs` demonstrates fragments, an empty chunk and two adjacent values.
`examples/deltas.rs` demonstrates signed differences with checked application-level
arithmetic; the codec does not decide how positions or counters should be updated.

## Verification scope

The packaged source is connected to the Lean model by pinned extraction and
correspondence proofs. See `docs/trust-boundary.md` for primitive/compiler
assumptions and target scope. Performance measurements have their own host and
distribution limits; they do not establish a universal fastest implementation.
