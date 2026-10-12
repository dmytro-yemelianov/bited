import Bited.Proofs.Canonical
import Mathlib.Tactic.Ring

namespace Bited.Spec

/-- The final payload alone contributes its high-order base-128 place value. -/
theorem wireValue_last_lower (bs : List Byte) (last : Byte)
    (hlast : bs.getLast? = some last) :
    payload last * 128 ^ (bs.length - 1) ≤ wireValue bs := by
  induction bs with
  | nil => simp at hlast
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb : b = last := by simpa using hlast
      simp [wireValue, hb]
    | cons c cs =>
      have htlast : (c :: cs).getLast? = some last := by simpa using hlast
      have ht := ih htlast
      have hp : 0 < (c :: cs).length := by simp
      have he : (c :: cs).length = ((c :: cs).length - 1) + 1 := by omega
      change payload last * 128 ^ ((c :: cs).length + 1 - 1) ≤ payload b + 128 * wireValue (c :: cs)
      rw [Nat.add_sub_cancel, he, Nat.pow_succ]
      calc
        payload last * (128 ^ ((c :: cs).length - 1) * 128) =
            128 * (payload last * 128 ^ ((c :: cs).length - 1)) := by ring
        _ ≤ 128 * wireValue (c :: cs) := Nat.mul_le_mul_left 128 ht
        _ ≤ payload b + 128 * wireValue (c :: cs) := by omega

theorem bounded_last_payload (width : Nat) (hw : width = 32 ∨ width = 64)
    (bs : List Byte) (value : Nat) (last : Byte) (hb : bounded width bs value)
    (hlast : bs.getLast? = some last) (hlen : bs.length = maxBytes width) :
    payload last ≤ 2 ^ (width - 7 * (maxBytes width - 1)) - 1 := by
  have hl := wireValue_last_lower bs last hlast
  rw [hlen, hb.1.2] at hl
  rcases hw with rfl | rfl
  all_goals norm_num [maxBytes] at hl ⊢
  all_goals rcases hb with ⟨hr, hcount, hvalue⟩
  all_goals norm_num at hvalue
  all_goals omega

end Bited.Spec
