import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

namespace Bitet.Spec

/-- Section 5, over mathematical integers rather than machine arithmetic. -/
def zigzag (n : Int) : Nat :=
  if n ≥ 0 then (2 * n).toNat else (-2 * n - 1).toNat

/-- Odd codes use `u / 2 + 1`; no machine-width `u + 1` is needed. -/
def unzigzag (u : Nat) : Int :=
  if u % 2 = 0 then (u / 2 : Nat) else -(u / 2 : Nat) - 1

def unsignedDomain (width x : Nat) : Prop := x < 2 ^ width

def signedDomain (width : Nat) (n : Int) : Prop :=
  -(2 ^ (width - 1) : Nat) ≤ n ∧ n < (2 ^ (width - 1) : Nat)

theorem zigzag_left_inverse (n : Int) : unzigzag (zigzag n) = n := by
  unfold zigzag unzigzag
  split_ifs <;> omega

theorem zigzag_right_inverse (u : Nat) : zigzag (unzigzag u) = u := by
  unfold zigzag unzigzag
  split_ifs <;> omega

theorem zigzag_bounds (width : Nat) (hw : width > 0) :
    (∀ n, signedDomain width n → unsignedDomain width (zigzag n)) ∧
    (∀ u, unsignedDomain width u → signedDomain width (unzigzag u)) := by
  have hp : 2 ^ width = 2 * 2 ^ (width - 1) := by
    calc
      2 ^ width = 2 ^ ((width - 1) + 1) := by rw [Nat.sub_add_cancel hw]
      _ = 2 * 2 ^ (width - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  constructor
  · intro n hn
    unfold signedDomain at hn
    unfold unsignedDomain zigzag
    rw [hp]
    split_ifs <;> omega
  · intro u hu
    unfold unsignedDomain at hu
    rw [hp] at hu
    unfold signedDomain unzigzag
    split_ifs <;> omega

end Bitet.Spec
