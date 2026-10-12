import Bited.Refinement.DecodeArithmetic
import Bited.Refinement.EncodeContent
import Mathlib.Tactic.Ring

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

theorem wireValue_append (xs ys : List Spec.Byte) :
    Spec.wireValue (xs ++ ys) = Spec.wireValue xs + 128 ^ xs.length * Spec.wireValue ys := by
  induction xs with
  | nil => simp [Spec.wireValue]
  | cons b bs ih =>
    simp only [List.cons_append, Spec.wireValue, ih, List.length_cons, pow_succ]
    ring

/-- Meaning of the consumed prefix, using the independent specification's value. -/
def wirePrefix (input : Slice U8) (count : Nat) : Nat :=
  Spec.wireValue ((input.val.take count).map specByte)

theorem wirePrefix_succ (input : Slice U8) (count : Nat) (h : count < input.length) :
    wirePrefix input (count + 1) =
      wirePrefix input count + input.val[count]!.val % 128 * 2 ^ (7 * count) := by
  unfold wirePrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [Slice.length] using h)]
  rw [List.map_append, wireValue_append]
  simp only [List.map_cons, List.map_nil, Spec.wireValue, Spec.payload, specByte,
    Nat.mul_zero, Nat.add_zero, List.length_map, List.length_take]
  rw [Nat.min_eq_left (by simp only [Slice.length] at h; omega)]
  rw [getElem!_pos input.val count (by simpa only [Slice.length] using h)]
  have hp : 128 ^ count = 2 ^ (7 * count) := by
    exact (Nat.pow_mul 2 7 count).symm
  rw [hp, Nat.mul_comm]

/-- For every input and either policy, a successful actual Rust decode returns
    exactly the specification's value of its consumed prefix. Errors are not
    classified by this theorem. -/
theorem decode_u64_value (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy ⦃ r =>
      match r with
      | .Ok d => d.value.val = wirePrefix input d.consumed.val
      | .Err _ => True ⦄ := by
  unfold Generated.decode.decode_u64 Generated.decode.decode_u64_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Usize) => 10 - state.2.val)
    (fun state => state.2.val ≤ 10 ∧ state.2.val ≤ input.length ∧
      state.1.val < 2 ^ (7 * state.2.val) ∧ state.1.val = wirePrefix input state.2.val)
  · rintro ⟨acc, i⟩ ⟨hi, hlen, ha, hv⟩
    dsimp at hi hlen ha hv
    apply WP.spec_mono (WP.spec_and (decode_u64_body_total input policy acc i hi hlen)
      (decode_u64_body_value input policy acc i hi hlen ha))
    intro r hr
    cases r with
    | cont state =>
      rcases state with ⟨next, j⟩
      dsimp at hr ⊢
      have hstrict : i.val < input.length := by
          simp only [Slice.length]
          omega
      refine ⟨⟨hr.1.1, hr.1.2.1, hr.2.2.2, ?_⟩, by omega⟩
      rw [hr.2.1, wirePrefix_succ input i.val hstrict, hr.2.2.1, hv]
    | done result =>
      cases result with
      | Err e => trivial
      | Ok d =>
        dsimp [consumed] at hr ⊢
        have hstrict : i.val < input.length := by
          simp only [Slice.length]
          omega
        rw [hr.2.1, wirePrefix_succ input i.val hstrict, hr.2.2.1, hv]
  · simp [wirePrefix, Spec.wireValue]

end Bited.Refinement
