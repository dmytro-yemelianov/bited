//! Fixed-size incremental state; terminal results remain sealed until reset.
use crate::decode::transition;
use crate::{DecodeError, DecodeErrorKind, DecodePolicy, Decoded};

/// Result of feeding a byte to an incremental decoder.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Step<T> {
    /// The byte was consumed; another byte is required.
    NeedMore,
    /// The byte completed a value; reset before starting another.
    Done(Decoded<T>),
    /// The byte produced a terminal error; reset before reuse.
    Error(DecodeError),
    /// The decoder is already terminal; this byte was not consumed.
    Closed,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct State {
    policy: DecodePolicy,
    acc: u64,
    count: usize,
    terminal: Option<Result<Decoded<u64>, DecodeError>>,
}

impl State {
    fn new(policy: DecodePolicy) -> Self {
        Self {
            policy,
            acc: 0,
            count: 0,
            terminal: None,
        }
    }

    fn push(&mut self, byte: u8, limit: usize, last_max: u8) -> Step<u64> {
        if self.terminal.is_some() {
            return Step::Closed;
        }
        let result = transition(self.acc, self.count, byte, self.policy, limit, last_max);
        self.count += 1;
        match result {
            Err(e) => {
                self.terminal = Some(Err(e));
                Step::Error(e)
            }
            Ok((next, done, canonical)) => {
                self.acc = next;
                if done {
                    let decoded = Decoded {
                        value: next,
                        consumed: self.count,
                        canonical,
                    };
                    self.terminal = Some(Ok(decoded));
                    Step::Done(decoded)
                } else {
                    Step::NeedMore
                }
            }
        }
    }

    fn finish(&mut self) -> Result<Decoded<u64>, DecodeError> {
        match self.terminal {
            Some(result) => result,
            None => {
                let result = Err(DecodeError {
                    kind: DecodeErrorKind::Truncated,
                    consumed: self.count,
                });
                self.terminal = Some(result);
                result
            }
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
/// Fixed-size incremental u64 decoder, sealed after completion or error.
pub struct DecoderU64 {
    state: State,
}
impl DecoderU64 {
    /// Start an empty decoder under the selected policy.
    pub fn new(policy: DecodePolicy) -> Self {
        Self {
            state: State::new(policy),
        }
    }
    /// Consume one byte unless already sealed; report progress or a terminal result.
    pub fn push(&mut self, byte: u8) -> Step<u64> {
        self.state.push(byte, 10, 1)
    }
    /// Seal an incomplete session as truncated, or return the stored terminal result.
    pub fn finish(&mut self) -> Result<Decoded<u64>, DecodeError> {
        self.state.finish()
    }
    /// Start a fresh session under the selected policy.
    pub fn reset(&mut self, policy: DecodePolicy) {
        self.state = State::new(policy);
    }
    /// Number of bytes incorporated in the current session.
    pub fn bytes_seen(&self) -> usize {
        self.state.count
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
/// Fixed-size incremental u32 decoder, sealed after completion or error.
pub struct DecoderU32 {
    state: State,
}
impl DecoderU32 {
    /// Start an empty decoder under the selected policy.
    pub fn new(policy: DecodePolicy) -> Self {
        Self {
            state: State::new(policy),
        }
    }
    /// Consume one byte unless already sealed; report progress or a terminal result.
    pub fn push(&mut self, byte: u8) -> Step<u32> {
        match self.state.push(byte, 5, 15) {
            Step::NeedMore => Step::NeedMore,
            Step::Closed => Step::Closed,
            Step::Error(e) => Step::Error(e),
            Step::Done(d) => Step::Done(Decoded {
                value: d.value as u32,
                consumed: d.consumed,
                canonical: d.canonical,
            }),
        }
    }
    /// Seal an incomplete session as truncated, or return the stored terminal result.
    pub fn finish(&mut self) -> Result<Decoded<u32>, DecodeError> {
        match self.state.finish() {
            Err(e) => Err(e),
            Ok(d) => Ok(Decoded {
                value: d.value as u32,
                consumed: d.consumed,
                canonical: d.canonical,
            }),
        }
    }
    /// Start a fresh session under the selected policy.
    pub fn reset(&mut self, policy: DecodePolicy) {
        self.state = State::new(policy);
    }
    /// Number of bytes incorporated in the current session.
    pub fn bytes_seen(&self) -> usize {
        self.state.count
    }
}
