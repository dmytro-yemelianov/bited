//! Feed fragmented input byte by byte and retain the next frame's suffix.
use bitet::{DecodePolicy, DecoderU64, Step};

fn main() {
    let chunks: &[&[u8]] = &[&[0xac], &[], &[0x02, 0x7f]];
    let mut decoder = DecoderU64::new(DecodePolicy::Canonical);
    for chunk in chunks {
        for &byte in *chunk {
            match decoder.push(byte) {
                Step::NeedMore => {}
                Step::Done(decoded) => {
                    println!("value={} bytes={}", decoded.value, decoded.consumed);
                    decoder.reset(DecodePolicy::Canonical);
                }
                Step::Error(error) => panic!("malformed frame: {error:?}"),
                Step::Closed => unreachable!("reset immediately after a terminal result"),
            }
        }
    }
    assert_eq!(decoder.bytes_seen(), 0);
    // At EOF, call finish only if a frame is open; an empty frame is truncated.
}
