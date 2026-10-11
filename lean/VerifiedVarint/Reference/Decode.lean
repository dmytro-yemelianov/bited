import VerifiedVarint.Spec.Bytes

namespace VerifiedVarint.Reference
open Spec

inductive Policy where
  | canonical
  | boundedNoncanonical
  deriving DecidableEq

inductive DecodeErrorKind where
  | truncated
  | overflow
  | tooLong
  | nonCanonical
  | trailingBytes
  deriving DecidableEq

structure Decoded where
  value : Nat
  consumed : Nat
  canonical : Bool
  deriving DecidableEq

structure DecodeError where
  kind : DecodeErrorKind
  consumed : Nat
  deriving DecidableEq

abbrev Outcome := Except DecodeError Decoded

/-- Arithmetic/list reference with the prescribed decision order.
    Only the remaining allowed byte count drives recursion. -/
def decodeAux (lastMax : Nat) (policy : Policy) :
    Nat → Nat → Nat → List Byte → Outcome
  | 0, count, _, _ => .error ⟨.tooLong, count⟩
  | _ + 1, count, _, [] => .error ⟨.truncated, count⟩
  | remaining + 1, count, acc, b :: bs =>
      if remaining = 0 ∧ payload b > lastMax then .error ⟨.overflow, count + 1⟩
      else if remaining = 0 ∧ continues b then .error ⟨.tooLong, count + 1⟩
      else
        let next := acc + payload b * 2 ^ (7 * count)
        if continues b then decodeAux lastMax policy remaining (count + 1) next bs
        else
          let canonical := count = 0 || payload b != 0
          if policy = .canonical ∧ !canonical then .error ⟨.nonCanonical, count + 1⟩
          else .ok ⟨next, count + 1, canonical⟩

def decode (width : Nat) (policy : Policy) (bs : List Byte) : Outcome :=
  let count := maxBytes width
  let lastMax := 2 ^ (width - 7 * (count - 1)) - 1
  decodeAux lastMax policy count 0 0 bs

/-- Exact decoding adds a trailing-input check only after prefix success. -/
def exact (length : Nat) (result : Outcome) : Outcome :=
  match result with
  | .error e => .error e
  | .ok d => if d.consumed = length then .ok d
      else .error ⟨.trailingBytes, d.consumed⟩

end VerifiedVarint.Reference
