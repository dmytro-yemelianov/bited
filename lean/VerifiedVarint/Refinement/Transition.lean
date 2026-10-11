import VerifiedVarint.Refinement.DecodeDecision
import VerifiedVarint.Refinement.DecodeBounds

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

set_option maxHeartbeats 2000000 in
theorem transition_u32_value (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 5)
    (ha : acc.val < 2 ^ (7 * count.val)) :
    Generated.decode.transition acc count byte policy 5#usize 15#u8 ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (next, _, _) =>
        next.val = acc.val + byte.val % 128 * 2 ^ (7 * count.val) ∧
        next.val < 2 ^ (7 * (count.val + 1)) ∧ next.val < 2^32 ⦄ := by
  unfold Generated.decode.transition
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals try (have hci : count = i1 := by assumption; subst i1)
  all_goals
    have hp : payload.val = byte.val % 128 := by
      rw [payload_post, UScalar.val_and]
      exact Nat.and_two_pow_sub_one_eq_mod byte.val 7
    have hb := decode_digit_bounds acc.val payload.val count.val (by omega)
      (by rw [hp]; omega) (by omega) ha
    have hlast : count.val = 4 → payload.val ≤ 15 := by scalar_tac
    have hb32 := decode_digit_bounds32 acc.val payload.val count.val hc (by rw [hp]; omega) hlast ha
    have hcast : i2.val = payload.val := by
      rw [i2_post, UScalar.cast_val_eq]
      change payload.val % (2^64) = payload.val
      apply Nat.mod_eq_of_lt
      rw [hp]
      omega
    have hshift : i3.val = 7 * count.val := by scalar_tac
    have hd : i4.val = payload.val * 2 ^ (7 * count.val) := by
      rw [i4_post, hcast, hshift, Nat.shiftLeft_eq]
      simp only [U64.size, U64.numBits]
      exact Nat.mod_eq_of_lt hb.1
    have hv : next.val = acc.val + payload.val * 2 ^ (7 * count.val) := by
      rw [next_post, UScalar.val_or, hd, decode_or_eq_add acc.val payload.val count.val ha]
    have hresult : next.val = acc.val + byte.val % 128 * 2 ^ (7 * count.val) := by rw [hv, hp]
    have hnext : next.val < 2 ^ (7 * (count.val + 1)) := by rw [hv]; exact hb.2.2
    have hbound : next.val < 2^32 := by rw [hv]; exact hb32
    try simp only [Generated.decode.DecodePolicy.read_discriminant]
    step*
    all_goals by_cases hz : count = 0#usize
    all_goals try simp only [hz, ↓reduceIte]
    all_goals step*
    all_goals try subst count
    all_goals try simp [hz, Generated.decode.DecodePolicy.read_discriminant,
      show (1#isize : Isize) ≠ 0#isize by decide]
    all_goals step*
    all_goals try simpa only [hz] using And.intro hresult (And.intro hnext hbound)
    all_goals have hnz : i1 ≠ 0#usize := by scalar_tac
    all_goals simp [hnz]
    all_goals step*
    all_goals exact And.intro hresult (And.intro hnext hbound)

set_option maxHeartbeats 2000000 in
theorem transition_u64_value (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 10)
    (ha : acc.val < 2 ^ (7 * count.val)) :
    Generated.decode.transition acc count byte policy 10#usize 1#u8 ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (next, _, _) =>
        next.val = acc.val + byte.val % 128 * 2 ^ (7 * count.val) ∧
        next.val < 2 ^ (7 * (count.val + 1)) ∧ next.val < 2^64 ⦄ := by
  unfold Generated.decode.transition
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals try (have hci : count = i1 := by assumption; subst i1)
  all_goals
    have hp : payload.val = byte.val % 128 := by
      rw [payload_post, UScalar.val_and]
      exact Nat.and_two_pow_sub_one_eq_mod byte.val 7
    have hlast : count.val = 9 → payload.val ≤ 1 := by scalar_tac
    have hb := decode_digit_bounds acc.val payload.val count.val hc
      (by rw [hp]; omega) hlast ha
    have hcast : i2.val = payload.val := by
      rw [i2_post, UScalar.cast_val_eq]
      change payload.val % (2^64) = payload.val
      apply Nat.mod_eq_of_lt
      rw [hp]
      omega
    have hshift : i3.val = 7 * count.val := by scalar_tac
    have hd : i4.val = payload.val * 2 ^ (7 * count.val) := by
      rw [i4_post, hcast, hshift, Nat.shiftLeft_eq]
      simp only [U64.size, U64.numBits]
      exact Nat.mod_eq_of_lt hb.1
    have hv : next.val = acc.val + payload.val * 2 ^ (7 * count.val) := by
      rw [next_post, UScalar.val_or, hd, decode_or_eq_add acc.val payload.val count.val ha]
    have hresult : next.val = acc.val + byte.val % 128 * 2 ^ (7 * count.val) := by rw [hv, hp]
    have hnext : next.val < 2 ^ (7 * (count.val + 1)) := by rw [hv]; exact hb.2.2
    have hbound : next.val < 2^64 := next.bv.isLt
    try simp only [Generated.decode.DecodePolicy.read_discriminant]
    step*
    all_goals by_cases hz : count = 0#usize
    all_goals try simp only [hz, ↓reduceIte]
    all_goals step*
    all_goals try subst count
    all_goals try simp [hz, Generated.decode.DecodePolicy.read_discriminant,
      show (1#isize : Isize) ≠ 0#isize by decide]
    all_goals step*
    all_goals try simpa only [hz] using And.intro hresult (And.intro hnext hbound)
    all_goals have hnz : i1 ≠ 0#usize := by scalar_tac
    all_goals simp [hnz]
    all_goals step*
    all_goals exact And.intro hresult (And.intro hnext hbound)

end VerifiedVarint.Refinement
