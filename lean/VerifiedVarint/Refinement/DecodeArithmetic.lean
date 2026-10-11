import VerifiedVarint.Refinement.Decode
import VerifiedVarint.Reference.Decode
import Mathlib.Tactic.IntervalCases

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

theorem decode_payload_value (byte : U8) :
    (byte &&& 127#u8).val = byte.val % 128 := by
  rw [UScalar.val_and]
  exact Nat.and_two_pow_sub_one_eq_mod byte.val 7

/-- Disjoint base-128 digits turn the actual bitwise OR into arithmetic addition. -/
theorem decode_or_eq_add (acc payload count : Nat) (hacc : acc < 2 ^ (7 * count)) :
    acc ||| (payload * 2 ^ (7 * count)) = acc + payload * 2 ^ (7 * count) := by
  have h := Nat.two_pow_add_eq_or_of_lt hacc payload
  rw [Nat.or_comm]
  simpa only [Nat.mul_comm, Nat.add_comm] using h.symm

/-- The tenth digit has one value bit; all earlier digits have seven. -/
theorem decode_digit_bounds (acc payload count : Nat) (hi : count < 10)
    (hp : payload < 128) (hlast : count = 9 → payload ≤ 1)
    (ha : acc < 2 ^ (7 * count)) :
    payload * 2 ^ (7 * count) < 2 ^ 64 ∧
    acc + payload * 2 ^ (7 * count) < 2 ^ 64 ∧
    acc + payload * 2 ^ (7 * count) < 2 ^ (7 * (count + 1)) := by
  interval_cases count <;> norm_num at * <;> omega

/-- Correspondence of the exact cast/multiply/shift/OR operations used by Rust.
    The bounds also establish the invariant for the following byte. -/
theorem decode_accumulate_refines (acc : U64) (payload : U8) (i : Usize)
    (hi : i.val < 10) (hp : payload.val < 128)
    (hlast : i.val = 9 → payload.val ≤ 1) (ha : acc.val < 2 ^ (7 * i.val)) :
    (do
      let p ← lift (UScalar.cast .U64 payload)
      let shift ← 7#usize * i
      let digit ← p <<< shift
      lift (acc ||| digit)) ⦃ next =>
        next.val = acc.val + payload.val * 2 ^ (7 * i.val) ∧
        next.val < 2 ^ (7 * (i.val + 1)) ⦄ := by
  have hb := decode_digit_bounds acc.val payload.val i.val hi hp hlast ha
  step*
  have hp' : p.val = payload.val := by
    rw [p_post, UScalar.cast_val_eq]
    change payload.val % (2 ^ 64) = payload.val
    exact Nat.mod_eq_of_lt (by omega)
  have hd : digit.val = payload.val * 2 ^ (7 * i.val) := by
    rw [digit_post, hp', shift_post, Nat.shiftLeft_eq]
    simp only [U64.size, U64.numBits]
    exact Nat.mod_eq_of_lt hb.1
  rw [next_post, UScalar.val_or, hd, decode_or_eq_add acc.val payload.val i.val ha]
  exact ⟨rfl, hb.2.2⟩

set_option maxHeartbeats 1500000 in
/-- The complete extracted byte transition preserves the arithmetic accumulator
    invariant, including both successful termination and continuation. -/
theorem decode_u64_body_value (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (acc : U64) (i : Usize) (hi : i.val ≤ 10) (hlen : i.val ≤ input.length)
    (ha : acc.val < 2 ^ (7 * i.val)) :
    Generated.decode.decode_u64_loop.body input policy acc i ⦃ r =>
      match r with
      | .cont (next, j) =>
        j.val = i.val + 1 ∧
        next.val = acc.val + input.val[i.val]!.val % 128 * 2 ^ (7 * i.val) ∧
        next.val < 2 ^ (7 * j.val)
      | .done (.Ok d) =>
        d.consumed.val = i.val + 1 ∧
        d.value.val = acc.val + input.val[i.val]!.val % 128 * 2 ^ (7 * i.val) ∧
        d.value.val < 2 ^ (7 * d.consumed.val)
      | .done (.Err _) => True ⦄ := by
  unfold Generated.decode.decode_u64_loop.body
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals try
    have hstrict : i.val < input.length := by
      have hnot : i ≠ input.len := by assumption
      have hne := UScalar.neq_to_neq_val.mp hnot
      simp only [Slice.len_val] at hne
      omega
  all_goals
    have hp' : p.val = byte.val % 128 := by
      rw [p_post, UScalar.val_and]
      exact Nat.and_two_pow_sub_one_eq_mod byte.val 7
    have hpbound : p.val < 128 := by rw [hp']; omega
    have hlast : i.val = 9 → p.val ≤ 1 := by scalar_tac
    have hb := decode_digit_bounds acc.val p.val i.val (by scalar_tac) hpbound hlast ha
    have hcast : i3.val = p.val := by
      rw [i3_post, UScalar.cast_val_eq]
      change p.val % (2 ^ 64) = p.val
      exact Nat.mod_eq_of_lt (by omega)
    have hd : i5.val = p.val * 2 ^ (7 * i.val) := by
      have hshift : i4.val = 7 * i.val := by scalar_tac
      rw [i5_post, hcast, hshift, Nat.shiftLeft_eq]
      simp only [U64.size, U64.numBits]
      exact Nat.mod_eq_of_lt hb.1
    have hv : acc1.val = acc.val + p.val * 2 ^ (7 * i.val) := by
      rw [acc1_post, UScalar.val_or, hd, decode_or_eq_add acc.val p.val i.val ha]
    have hbyte : byte = input.val[i.val]! := by
      rw [byte_post]
      rw [getElem!_pos input.val i.val (by simpa only [Slice.length] using hstrict)]
    have hresult : acc1.val = acc.val + input.val[i.val]!.val % 128 * 2 ^ (7 * i.val) := by
      rw [hv, hp', hbyte]
    have hnext : acc1.val < 2 ^ (7 * (i.val + 1)) := by rw [hv]; exact hb.2.2
    try simp only [Generated.decode.DecodePolicy.read_discriminant]
    step*
    all_goals by_cases hz : i = 0#usize
    all_goals try simp only [hz, ↓reduceIte]
    all_goals step*
    all_goals try subst i
    all_goals try simp_all
    all_goals step*
    all_goals have hb64 : acc1.val < 2 ^ 64 := acc1.bv.isLt
    all_goals simp only [i6_post, hresult] at hb64 ⊢
    all_goals norm_num at hb64 ⊢
    all_goals omega


end VerifiedVarint.Refinement
