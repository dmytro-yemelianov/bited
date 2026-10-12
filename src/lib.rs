//! Allocation-free base-128 varints and ZigZag with explicit decoding policy.
//!
//! Prefix decoders report the consumed byte count; exact decoders also reject a
//! trailing suffix. Caller-buffer encoders leave the complete buffer unchanged
//! when capacity is insufficient. The library is `no_std` and forbids unsafe code.
//!
//! ```
//! use bitet::{decode_i64_exact, encode_i64_into, DecodePolicy};
//!
//! let mut buffer = [0u8; 10];
//! let used = encode_i64_into(-150, &mut buffer).unwrap();
//! let decoded = decode_i64_exact(&buffer[..used], DecodePolicy::Canonical).unwrap();
//! assert_eq!(decoded.value, -150);
//! ```
//!
//! This implements the scalar API of VVZ-SPEC-0.1.0. Source-level proofs
//! and the covered extraction configuration are inventoried separately in
//! `verification/coverage.json`.
#![no_std]
#![forbid(unsafe_code)]
#![warn(missing_docs)]

mod api;
mod decode;
mod encode;
mod stream;
mod zigzag;

pub use api::*;
pub use decode::{decode_u32, decode_u64, DecodeError, DecodeErrorKind, DecodePolicy, Decoded};
pub use encode::{
    encode_u32, encode_u32_into, encode_u64, encode_u64_into, encoded_len_u32, encoded_len_u64,
    EncodeError, Encoded32, Encoded64,
};
pub use stream::{DecoderU32, DecoderU64, Step};
pub use zigzag::{zigzag_i32_to_u32, zigzag_i64_to_u64, zigzag_u32_to_i32, zigzag_u64_to_i64};
