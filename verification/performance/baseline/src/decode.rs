/// Acceptance policy for one bounded unsigned representation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DecodePolicy {
    /// Reject redundant high zero groups.
    Canonical,
    /// Accept redundant zero groups within the five-byte u32 or ten-byte u64 limit.
    BoundedNonCanonical,
}

/// A successful decode and its logical input consumption.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Decoded<T> {
    /// Decoded integer value.
    pub value: T,
    /// Bytes incorporated, including the decisive byte on malformed input.
    pub consumed: usize,
    /// Whether the input used the shortest representation.
    pub canonical: bool,
}

/// Failure classification, with overflow preceding excessive length.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DecodeErrorKind {
    /// Input ended before a terminating byte.
    Truncated,
    /// Payload cannot fit the selected integer width.
    Overflow,
    /// A continuation bit exceeds the selected width limit.
    TooLong,
    /// A redundant representation was rejected by canonical policy.
    NonCanonical,
    /// Exact decoding found bytes after the first complete value.
    TrailingBytes,
}

/// Consumption includes the decisive byte on malformed input.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DecodeError {
    /// Failure classification.
    pub kind: DecodeErrorKind,
    /// Bytes incorporated, including the decisive byte on malformed input.
    pub consumed: usize,
}

/// Decode one `u64` prefix. Bytes after its terminator are ignored.
///
/// Processes at most ten bytes. An invalid tenth payload is rejected before
/// shifting it; no eleventh byte is needed to detect overflow or excessive length.
pub fn decode_u64(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u64>, DecodeError> {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < 10 {
        if i == input.len() {
            return Err(DecodeError {
                kind: DecodeErrorKind::Truncated,
                consumed: i,
            });
        }
        let byte = input[i];
        let p = byte & 0x7f;
        let continuation = byte & 0x80 != 0;
        if i == 9 {
            if p > 1 {
                return Err(DecodeError {
                    kind: DecodeErrorKind::Overflow,
                    consumed: i + 1,
                });
            }
            if continuation {
                return Err(DecodeError {
                    kind: DecodeErrorKind::TooLong,
                    consumed: i + 1,
                });
            }
        }
        acc |= (p as u64) << (7 * i);
        if !continuation {
            let canonical = i == 0 || p != 0;
            if policy == DecodePolicy::Canonical && !canonical {
                return Err(DecodeError {
                    kind: DecodeErrorKind::NonCanonical,
                    consumed: i + 1,
                });
            }
            return Ok(Decoded {
                value: acc,
                consumed: i + 1,
                canonical,
            });
        }
        i += 1;
    }
    // The tenth byte always terminates or returns an error above.
    Err(DecodeError {
        kind: DecodeErrorKind::TooLong,
        consumed: i,
    })
}

/// One scalar transition. Callers establish `count < limit` and `limit` is 5 or 10.
/// The accumulator contains only the already accepted lower payload groups.
pub(crate) fn transition(
    acc: u64,
    count: usize,
    byte: u8,
    policy: DecodePolicy,
    limit: usize,
    last_max: u8,
) -> Result<(u64, bool, bool), DecodeError> {
    let payload = byte & 0x7f;
    let continuation = byte & 0x80 != 0;
    if count == limit - 1 {
        if payload > last_max {
            return Err(DecodeError {
                kind: DecodeErrorKind::Overflow,
                consumed: count + 1,
            });
        }
        if continuation {
            return Err(DecodeError {
                kind: DecodeErrorKind::TooLong,
                consumed: count + 1,
            });
        }
    }
    let next = acc | ((payload as u64) << (7 * count));
    let canonical = count == 0 || payload != 0;
    if !continuation && policy == DecodePolicy::Canonical && !canonical {
        return Err(DecodeError {
            kind: DecodeErrorKind::NonCanonical,
            consumed: count + 1,
        });
    }
    Ok((next, !continuation, canonical))
}

/// Decode one bounded 32-bit prefix, examining at most five bytes.
pub fn decode_u32(input: &[u8], policy: DecodePolicy) -> Result<Decoded<u32>, DecodeError> {
    let mut acc = 0;
    let mut i = 0;
    while i < 5 {
        if i == input.len() {
            return Err(DecodeError {
                kind: DecodeErrorKind::Truncated,
                consumed: i,
            });
        }
        match transition(acc, i, input[i], policy, 5, 15) {
            Err(e) => return Err(e),
            Ok((next, done, canonical)) => {
                acc = next;
                i += 1;
                if done {
                    return Ok(Decoded {
                        value: acc as u32,
                        consumed: i,
                        canonical,
                    });
                }
            }
        }
    }
    Err(DecodeError {
        kind: DecodeErrorKind::TooLong,
        consumed: i,
    })
}
