//! Write one signed value without allocating, preserving the caller's suffix.
use bited::{decode_i64_exact, encode_i64_into, DecodePolicy};

fn main() {
    let mut output = [0xa5; 16];
    let used = encode_i64_into(-150, &mut output).unwrap();
    let decoded = decode_i64_exact(&output[..used], DecodePolicy::Canonical).unwrap();
    assert_eq!(decoded.value, -150);
    assert!(output[used..].iter().all(|byte| *byte == 0xa5));
    println!("-150 -> {:?}", &output[..used]);
}
