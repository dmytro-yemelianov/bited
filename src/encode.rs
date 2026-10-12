/// Short-output error. The entire caller buffer remains unchanged.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct EncodeError {
    /// Minimum capacity needed to encode the value.
    pub required: usize,
    /// Actual capacity of the caller-provided buffer.
    pub available: usize,
}

/// One canonical representation in initialized fixed-capacity storage.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Encoded64 {
    bytes: [u8; 10],
    len: usize,
}

/// One canonical 32-bit representation in initialized fixed storage.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Encoded32 {
    bytes: [u8; 5],
    len: usize,
}

impl Encoded32 {
    /// The initialized canonical prefix.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }

    /// Encoded prefix length, always in 1..=5.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Always false: zero also requires one byte.
    pub const fn is_empty(&self) -> bool {
        false
    }
}

#[inline]
/// Exact shortest base-128 length for a u32.
pub const fn encoded_len_u32(value: u32) -> usize {
    encoded_len_u64(value as u64)
}

#[inline]
/// Encode a u32 into initialized fixed storage without allocation.
pub fn encode_u32(value: u32) -> Encoded32 {
    let encoded = encode_u64(value as u64);
    let bytes = [
        encoded.bytes[0],
        encoded.bytes[1],
        encoded.bytes[2],
        encoded.bytes[3],
        encoded.bytes[4],
    ];
    Encoded32 {
        bytes,
        len: encoded.len,
    }
}

#[inline]
/// Write a canonical u32 prefix with atomic short-buffer failure and preserved suffix.
pub fn encode_u32_into(value: u32, out: &mut [u8]) -> Result<usize, EncodeError> {
    encode_u64_into(value as u64, out)
}

impl Encoded64 {
    /// The initialized canonical prefix; unused storage is private.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }

    /// Always in `1..=10`.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Encodings are always nonempty.
    pub const fn is_empty(&self) -> bool {
        false
    }
}

/// Exact shortest length in the base-128 format, including one byte for zero.
#[inline]
pub const fn encoded_len_u64(value: u64) -> usize {
    if value < 128 {
        1
    } else {
        ((70 - value.leading_zeros()) / 7) as usize // 64-bit length, rounded up by six.
    }
}

/// Encode into fixed storage without allocation.
#[inline]
pub fn encode_u64(mut value: u64) -> Encoded64 {
    let mut bytes = [0u8; 10];
    let mut i = 0;
    while value >= 128 {
        bytes[i] = (value as u8 & 0x7f) | 0x80;
        value >>= 7;
        i += 1;
    }
    bytes[i] = value as u8;
    Encoded64 { bytes, len: i + 1 }
}

/// Write exactly the canonical prefix, preserving the output suffix.
/// Insufficient capacity preserves every byte of `out`.
#[inline]
pub fn encode_u64_into(value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    if out.len() >= 10 {
        encode_u64_into_checked(value, &mut out[..10])
    } else {
        encode_u64_into_checked(value, out)
    }
}

// A bounded subview lets the compiler specialize emission for full-capacity buffers.
// Both branches retain the same checked, atomic output contract.
#[inline]
fn encode_u64_into_checked(mut value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
    let required = encoded_len_u64(value);
    let available = out.len();
    if available < required {
        return Err(EncodeError {
            required,
            available,
        });
    }
    let mut i = 0;
    while value >= 128 {
        out[i] = (value as u8 & 0x7f) | 0x80;
        value >>= 7;
        i += 1;
    }
    out[i] = value as u8;
    Ok(required)
}
