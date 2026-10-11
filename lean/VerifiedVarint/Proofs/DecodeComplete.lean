import VerifiedVarint.Proofs.Decode

namespace VerifiedVarint.Reference
open Spec

/-- Acceptance of every shaped prefix satisfying the byte limit and policy.
    The arbitrary suffix never affects the successful result. -/
theorem decodeAux_complete (lastMax : Nat) (policy : Policy) (emitted rest : List Byte)
    (fuel count acc : Nat) (last : Byte) (hs : wireShape emitted)
    (hlen : emitted.length ≤ fuel) (hlast : emitted.getLast? = some last)
    (hlimit : emitted.length = fuel → payload last ≤ lastMax)
    (hpolicy : policy = .canonical →
      (count + emitted.length - 1 = 0 || payload last != 0) = true) :
    decodeAux lastMax policy fuel count acc (emitted ++ rest) =
      .ok ⟨acc + wireValue emitted * 2 ^ (7 * count), count + emitted.length,
        count + emitted.length - 1 = 0 || payload last != 0⟩ := by
  induction emitted generalizing fuel count acc with
  | nil => simp [wireShape] at hs
  | cons b tail ih =>
    cases fuel with
    | zero => simp at hlen
    | succ fuel =>
      cases tail with
      | nil =>
        have hb : last = b := by simpa using hlast.symm
        subst last
        have hc : continues b = false := hs
        have hov : ¬(fuel = 0 ∧ payload b > lastMax) := by
          rintro ⟨hf, hv⟩
          have hp := hlimit (by simp [hf])
          omega
        have hp : ¬(policy = .canonical ∧ (!(count = 0 || payload b != 0)) = true) := by
          rintro ⟨hpol, hbad⟩
          have hh := hpolicy hpol
          simp only [List.length_singleton, Nat.add_sub_cancel] at hh
          simp [hh] at hbad
        simp_all [decodeAux, wireValue]
        split_ifs <;> simp_all <;> omega
      | cons c cs =>
        have hs' : continues b = true ∧ wireShape (c :: cs) := hs
        have hf : fuel ≠ 0 := by simp at hlen; omega
        have htlast : (c :: cs).getLast? = some last := by simpa using hlast
        have htlen : (c :: cs).length ≤ fuel := by simpa using hlen
        have htlimit : (c :: cs).length = fuel → payload last ≤ lastMax := by
          intro he
          apply hlimit
          simp [he]
        have htpolicy : policy = .canonical →
            (count + 1 + (c :: cs).length - 1 = 0 || payload last != 0) = true := by
          intro hp
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpolicy hp
        simp only [List.cons_append, decodeAux, hf, false_and, ↓reduceIte, hs'.1,
          Bool.true_eq, ↓reduceIte]
        have hi := ih fuel (count + 1) (acc + payload b * 2 ^ (7 * count)) hs'.2 htlen htlast htlimit htpolicy
        simp only [List.cons_append] at hi
        rw [hi]
        have hv : acc + payload b * 2 ^ (7 * count) + wireValue (c :: cs) * 2 ^ (7 * (count + 1)) =
            acc + wireValue (b :: c :: cs) * 2 ^ (7 * count) := by
          simp only [wireValue]
          have he : 7 * (count + 1) = 7 * count + 7 := by omega
          rw [he, Nat.pow_add]
          norm_num
          ring
        simp [hv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end VerifiedVarint.Reference
