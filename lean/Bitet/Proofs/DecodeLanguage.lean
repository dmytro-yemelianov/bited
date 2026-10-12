import Bitet.Proofs.DecodeComplete
import Bitet.Proofs.WireBounds

attribute [local instance] Classical.propDecidable

namespace Bitet.Spec

theorem canonical_last_flag (bs : List Byte) (last : Byte) (hlast : bs.getLast? = some last) :
    (bs.length - 1 = 0 || payload last != 0) = decide (canonical bs) := by
  have hp : 0 < bs.length := by
    cases bs with
    | nil => simp at hlast
    | cons b tail => simp
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne]
  unfold canonical
  constructor
  · rintro (hl | hv)
    · left; omega
    · exact Or.inr ⟨last, hlast, hv⟩
  · rintro (hl | ⟨last', hl', hv⟩)
    · left; omega
    · right
      have he : last = last' := Option.some.inj (hlast.symm.trans hl')
      simpa only [he] using hv

theorem encode_bounded (width : Nat) (hw : 0 < width) (value : Nat) (hv : value < 2^width) :
    bounded width (Reference.encode value) value := by
  refine ⟨encode_represents value, ?_, hv⟩
  have hn : 0 < maxBytes width := by unfold maxBytes; omega
  have he : width ≤ 7 * maxBytes width := by unfold maxBytes; omega
  apply encode_length_le (maxBytes width) value hn
  have hp : 128 ^ maxBytes width = 2 ^ (7 * maxBytes width) := by rw [Nat.pow_mul]
  rw [hp]
  exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) he)

end Bitet.Spec

namespace Bitet.Reference
open Spec

theorem decode_complete (width : Nat) (hw : width = 32 ∨ width = 64) (policy : Policy)
    (emitted rest : List Byte) (value : Nat) (hb : bounded width emitted value)
    (hpolicy : policy = .canonical → canonical emitted) :
    decode width policy (emitted ++ rest) = .ok ⟨value, emitted.length, decide (canonical emitted)⟩ := by
  have hne : emitted ≠ [] := by intro he; simp [he, bounded, represents, wireShape] at hb
  let last := emitted.getLast hne
  have hlast : emitted.getLast? = some last := List.getLast?_eq_some_getLast hne
  have hlimit := bounded_last_payload width hw emitted value last hb hlast
  have hp : policy = .canonical →
      (0 + emitted.length - 1 = 0 || payload last != 0) = true := by
    intro hc
    rw [Nat.zero_add, canonical_last_flag emitted last hlast]
    simpa using hpolicy hc
  have h := decodeAux_complete (2 ^ (width - 7 * (maxBytes width - 1)) - 1)
    policy emitted rest (maxBytes width) 0 0 last hb.1.1 hb.2.1 hlast hlimit hp
  simpa only [decode, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
    canonical_last_flag emitted last hlast, hb.1.2] using h

theorem decode_encode (width : Nat) (hw : width = 32 ∨ width = 64) (value : Nat)
    (hv : value < 2^width) (rest : List Byte) :
    decode width .canonical (encode value ++ rest) =
      .ok ⟨value, (encode value).length, true⟩ := by
  have hw' : 0 < width := by rcases hw with rfl | rfl <;> decide
  have h := decode_complete width hw .canonical (encode value) rest value
    (encode_bounded width hw' value hv) (fun _ => encode_canonical value)
  simpa only [encode_canonical, decide_true] using h

end Bitet.Reference
