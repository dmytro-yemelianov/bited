/// Short-output error. The entire caller buffer remains unchanged.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct EncodeError {
    pub required: usize,
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
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes[..self.len]
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        false
    }
}

#[inline]
pub const fn encoded_len_u32(value: u32) -> usize {
    encoded_len_u64(value as u64)
}

#[inline]
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
pub fn encode_u64_into(mut value: u64, out: &mut [u8]) -> Result<usize, EncodeError> {
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
