import Bited.Reference.Stream
import Bited.Proofs.Decode

namespace Bited.Reference
open Spec

set_option maxHeartbeats 2000000 in
theorem runBytes_decodeAux (width fuel : Nat) (state : State) (bs : List Byte)
    (ht : state.terminal = none) (hc : state.count + (fuel + 1) = maxBytes width) :
    (finish (runBytes width state bs)).1 =
      decodeAux (2 ^ (width - 7 * (maxBytes width - 1)) - 1)
        state.policy (fuel + 1) state.count state.acc bs := by
  induction fuel generalizing state bs with
  | zero =>
    have heq : state.count = maxBytes width - 1 := by omega
    cases bs with
    | nil => simp [runBytes, finish, ht, decodeAux]
    | cons byte rest =>
      simp only [runBytes, push, ht, advance, heq, decodeAux]
      split_ifs <;> simp_all [finish, Spec.continues] <;> omega
  | succ fuel ih =>
    have hne : state.count ≠ maxBytes width - 1 := by omega
    cases bs with
    | nil => simp [runBytes, finish, ht, decodeAux]
    | cons byte rest =>
      simp only [runBytes, push, ht, advance, hne, false_and, ↓reduceIte, decodeAux]
      by_cases hb : continues byte
      · simp only [hb, Bool.not_true, Bool.false_eq_true, false_and, ↓reduceIte]
        apply ih
        · rfl
        · simp only
          omega
      · simp only [hb, Bool.not_false, Bool.true_eq, true_and, ↓reduceIte]
        split_ifs <;> simp_all [finish]

theorem stream_slice_equivalence (width : Nat) (policy : Policy) (bs : List Byte)
    (hwidth : 0 < maxBytes width) :
    (finish (runBytes width (initial policy) bs)).1 = decode width policy bs := by
  have h := runBytes_decodeAux width (maxBytes width - 1) (initial policy) bs rfl (by
    simp [initial]
    omega)
  simpa [decode, initial, Nat.sub_add_cancel hwidth] using h

theorem streaming_chunks_equivalence (width : Nat) (policy : Policy) (chunks : List (List Byte))
    (hwidth : 0 < maxBytes width) :
    (finish (runChunks width (initial policy) chunks)).1 = decode width policy chunks.flatten := by
  rw [stream_partition_invariant]
  exact stream_slice_equivalence width policy _ hwidth

end Bited.Reference
