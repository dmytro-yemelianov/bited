import Mathlib.Data.List.Basic

namespace VerifiedVarint.Spec

abbrev Byte := Fin 256

def payload (b : Byte) : Nat := b.val % 128
def continues (b : Byte) : Bool := b.val ≥ 128

/-- List-based base-128 value, independent of the Rust transition algorithm. -/
def wireValue : List Byte → Nat
  | [] => 0
  | b :: bs => payload b + 128 * wireValue bs

/-- Nonempty, continuation bytes followed by exactly one terminator. -/
def wireShape : List Byte → Prop
  | [] => False
  | [b] => continues b = false
  | b :: c :: bs => continues b = true ∧ wireShape (c :: bs)

def represents (bs : List Byte) (x : Nat) : Prop :=
  wireShape bs ∧ wireValue bs = x

def maxBytes (width : Nat) : Nat := (width + 6) / 7

def bounded (width : Nat) (bs : List Byte) (x : Nat) : Prop :=
  represents bs x ∧ bs.length ≤ maxBytes width ∧ x < 2 ^ width

def canonical (bs : List Byte) : Prop :=
  bs.length = 1 ∨ ∃ last, bs.getLast? = some last ∧ payload last ≠ 0

end VerifiedVarint.Spec
