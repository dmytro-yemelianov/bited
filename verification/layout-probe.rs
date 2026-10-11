//! Compiler layout probe, outside the consumer library and formal claim.
#![no_std]
use verified_varint::{DecoderU32, DecoderU64, Encoded32, Encoded64};
#[no_mangle]
pub extern "C" fn vvz_decoder_u32_size() -> usize { core::mem::size_of::<DecoderU32>() }
#[no_mangle]
pub extern "C" fn vvz_decoder_u64_size() -> usize { core::mem::size_of::<DecoderU64>() }
#[no_mangle]
pub extern "C" fn vvz_encoded32_size() -> usize { core::mem::size_of::<Encoded32>() }
#[no_mangle]
pub extern "C" fn vvz_encoded64_size() -> usize { core::mem::size_of::<Encoded64>() }
