//! Deterministic base-128 varints with explicit decoding policy.
//!
//! This implements the scalar API of VVZ-SPEC-0.1.0. Source-level proofs
//! and the covered extraction configuration are inventoried separately in
//! `verification/coverage.json`.
#![no_std]
#![forbid(unsafe_code)]

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
