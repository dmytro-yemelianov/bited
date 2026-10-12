import Bited.Reference.Decode
import Bited.Proofs.Canonical
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Bited.Reference
open Spec

/-- Every accepted reference emitted has the prescribed shape and arithmetic value.
    The remainder is untouched and the flag describes the final high payload. -/
theorem decodeAux_success (lastMax : Nat) (policy : Policy) (fuel count acc : Nat)
    (bs : List Byte) (d : Decoded)
    (h : decodeAux lastMax policy fuel count acc bs = .ok d) :
    ∃ emitted rest last,
      bs = emitted ++ rest ∧ wireShape emitted ∧ emitted.length ≤ fuel ∧
      d.consumed = count + emitted.length ∧
      d.value = acc + wireValue emitted * 2 ^ (7 * count) ∧
      emitted.getLast? = some last ∧
      d.canonical = (count + emitted.length - 1 = 0 || payload last != 0) ∧
      (policy = .canonical → d.canonical = true) := by
  induction fuel generalizing count acc bs d with
  | zero => simp [decodeAux] at h
  | succ fuel ih =>
    cases bs with
    | nil => simp [decodeAux] at h
    | cons b bs =>
      simp only [decodeAux] at h
      split_ifs at h with hov hlong hcont hstrict
      all_goals try cases h
      · obtain ⟨emitted, rest, last, hbs, hs, hlen, hcons, hval, hlast, hflag, hpolicy⟩ :=
          ih (count + 1) (acc + payload b * 2 ^ (7 * count)) bs d h
        have hp : emitted ≠ [] := by intro he; simp [he, wireShape] at hs
        refine ⟨b :: emitted, rest, last, ?_, ?_, by simp; omega,
          by simp; omega, ?_, ?_, ?_, hpolicy⟩
        · simp [hbs]
        · cases emitted with
          | nil => contradiction
          | cons c cs => exact ⟨by simpa using hcont, hs⟩
        · rw [hval]
          simp only [wireValue]
          have he : 7 * (count + 1) = 7 * count + 7 := by omega
          rw [he, Nat.pow_add]
          norm_num
          ring
        · simpa only [List.getLast?_cons_of_ne_nil hp] using hlast
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hflag
      · refine ⟨[b], bs, b, rfl, ?_, by simp, by simp, ?_, by simp, ?_, ?_⟩
        · simpa [wireShape] using hcont
        · simp [wireValue]
        · simp
        · intro hp
          simp_all
          omega

theorem decode_success_shape (width : Nat) (policy : Policy) (bs : List Byte) (d : Decoded)
    (h : decode width policy bs = .ok d) :
    ∃ emitted rest, bs = emitted ++ rest ∧ represents emitted d.value ∧
      emitted.length ≤ maxBytes width ∧ d.consumed = emitted.length ∧
      (d.canonical = true ↔ canonical emitted) ∧
      (policy = .canonical → canonical emitted) := by
  obtain ⟨emitted, rest, last, hbs, hs, hlen, hcons, hval, hlast, hflag, hpolicy⟩ :=
    decodeAux_success _ policy (maxBytes width) 0 0 bs d h
  have hp : 0 < emitted.length := by
    cases emitted with
    | nil => simp [wireShape] at hs
    | cons b tail => simp
  have hf : d.canonical = true ↔ canonical emitted := by
    rw [hflag]
    simp only [Nat.zero_add, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne]
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
  refine ⟨emitted, rest, hbs, ⟨hs, ?_⟩, hlen, by simpa using hcons, hf, ?_⟩
  · simpa using hval.symm
  · intro hc
    exact hf.mp (hpolicy hc)

theorem reencode_preserves_canonical (width : Nat) (policy : Policy) (bs : List Byte)
    (d : Decoded) (h : decode width policy bs = .ok d) (hc : d.canonical = true) :
    bs.take d.consumed = encode d.value := by
  obtain ⟨emitted, rest, hbs, hr, hlen, hcons, hflag, hpolicy⟩ :=
    decode_success_shape width policy bs d h
  rw [hbs, hcons, List.take_append_of_le_length (by rfl), List.take_length]
  rw [canonical_eq_encode emitted hr.1 (hflag.mp hc), hr.2]

end Bited.Reference
