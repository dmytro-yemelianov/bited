import Bited.Reference.Decode
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

namespace Bited.Reference
open Spec

def consumed (result : Outcome) : Nat :=
  match result with
  | .error e => e.consumed
  | .ok d => d.consumed

/-- Incorporated byte count bounds every path, including empty/truncated input. -/
theorem decodeAux_consumption_bounds (lastMax : Nat) (policy : Policy) (fuel count acc : Nat)
    (bs : List Byte) :
    count ≤ consumed (decodeAux lastMax policy fuel count acc bs) ∧
    consumed (decodeAux lastMax policy fuel count acc bs) ≤ count + fuel ∧
    consumed (decodeAux lastMax policy fuel count acc bs) ≤ count + bs.length := by
  induction fuel generalizing count acc bs with
  | zero => simp [decodeAux, consumed]
  | succ fuel ih =>
    cases bs with
    | nil => simp [decodeAux, consumed]
    | cons b bs =>
      simp only [decodeAux]
      split_ifs
      all_goals try simp [consumed]
      all_goals have h := ih (count + 1) (acc + payload b * 2 ^ (7 * count)) bs
      all_goals simp only [consumed] at h
      all_goals try simp only [List.length_cons]
      all_goals cases heq : decodeAux lastMax policy fuel (count + 1) (acc + payload b * 2 ^ (7 * count)) bs
      all_goals simp_all [consumed]
      all_goals omega

theorem decode_consumption_bounds (width : Nat) (policy : Policy) (bs : List Byte) :
    consumed (decode width policy bs) ≤ maxBytes width ∧
    consumed (decode width policy bs) ≤ bs.length := by
  have h := decodeAux_consumption_bounds
    (2 ^ (width - 7 * (maxBytes width - 1)) - 1) policy (maxBytes width) 0 0 bs
  simpa only [decode, Nat.zero_add] using h.2

end Bited.Reference
