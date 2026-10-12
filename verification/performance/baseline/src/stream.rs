//! Fixed-size incremental state; terminal results remain sealed until reset.
use crate::decode::transition;
use crate::{DecodeError, DecodeErrorKind, DecodePolicy, Decoded};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Step<T> {
    NeedMore,
    Done(Decoded<T>),
    Error(DecodeError),
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
pub struct DecoderU64 {
    state: State,
}
impl DecoderU64 {
    pub fn new(policy: DecodePolicy) -> Self {
        Self {
            state: State::new(policy),
        }
    }
    pub fn push(&mut self, byte: u8) -> Step<u64> {
        self.state.push(byte, 10, 1)
    }
    pub fn finish(&mut self) -> Result<Decoded<u64>, DecodeError> {
        self.state.finish()
    }
    pub fn reset(&mut self, policy: DecodePolicy) {
        self.state = State::new(policy);
    }
    pub fn bytes_seen(&self) -> usize {
        self.state.count
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct DecoderU32 {
    state: State,
}
impl DecoderU32 {
    pub fn new(policy: DecodePolicy) -> Self {
        Self {
            state: State::new(policy),
        }
    }
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
    pub fn reset(&mut self, policy: DecodePolicy) {
        self.state = State::new(policy);
    }
    pub fn bytes_seen(&self) -> usize {
        self.state.count
    }
}
