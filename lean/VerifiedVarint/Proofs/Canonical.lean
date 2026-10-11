import VerifiedVarint.Proofs.Encode

namespace VerifiedVarint.Spec

theorem wireValue_positive_of_last (bs : List Byte) (last : Byte)
    (hlast : bs.getLast? = some last) (hp : payload last ≠ 0) : 0 < wireValue bs := by
  induction bs with
  | nil => simp at hlast
  | cons b bs ih =>
    cases bs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst last
      simp only [wireValue, Nat.mul_zero, Nat.add_zero]
      omega
    | cons c cs =>
      have htail : (c :: cs).getLast? = some last := by simpa using hlast
      have ht := ih htail
      change 0 < payload b + 128 * wireValue (c :: cs)
      omega

theorem canonical_tail (b c : Byte) (bs : List Byte) (h : canonical (b :: c :: bs)) :
    canonical (c :: bs) := by
  rcases h with hlen | ⟨last, hlast, hp⟩
  · simp at hlen
  · exact Or.inr ⟨last, by simpa using hlast, hp⟩

/-- A canonical multi-byte representation has a positive high-order tail. -/
theorem canonical_tail_value_pos (b c : Byte) (bs : List Byte)
    (h : canonical (b :: c :: bs)) : 0 < wireValue (c :: bs) := by
  rcases h with hlen | ⟨last, hlast, hp⟩
  · simp at hlen
  · exact wireValue_positive_of_last (c :: bs) last (by simpa using hlast) hp

/-- Every canonical wire representation equals the independent encoder's output. -/
theorem canonical_eq_encode (bs : List Byte) (hs : wireShape bs) (hc : canonical bs) :
    bs = Reference.encode (wireValue bs) := by
  induction bs with
  | nil => simp [wireShape] at hs
  | cons b bs ih =>
    cases bs with
    | nil =>
      have hb : b.val < 128 := by
        simp [wireShape, continues] at hs
        omega
      rw [Reference.encode]
      simp only [wireValue, payload, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hb]
      simp only [hb, ↓reduceDIte]
    | cons c cs =>
      have hs' : continues b = true ∧ wireShape (c :: cs) := hs
      have hb : 128 ≤ b.val := by simpa [continues] using hs'.1
      have ht := canonical_tail_value_pos b c cs hc
      have ih' := ih hs'.2 (canonical_tail b c cs hc)
      have hx : 128 ≤ wireValue (b :: c :: cs) := by
        change 128 ≤ payload b + 128 * wireValue (c :: cs)
        omega
      rw [Reference.encode]
      simp only [show ¬wireValue (b :: c :: cs) < 128 by omega, ↓reduceDIte]
      have hpbound : payload b < 128 := by simp only [payload]; omega
      have hmod : wireValue (b :: c :: cs) % 128 = payload b := by
        change (payload b + 128 * wireValue (c :: cs)) % 128 = payload b
        omega
      have hdiv : wireValue (b :: c :: cs) / 128 = wireValue (c :: cs) := by
        change (payload b + 128 * wireValue (c :: cs)) / 128 = wireValue (c :: cs)
        omega
      congr 1
      · apply Fin.ext
        change b.val = wireValue (b :: c :: cs) % 128 + 128
        rw [hmod]
        simp only [payload]
        have hbyte := b.isLt
        omega
      · rw [hdiv]
        exact ih'

theorem canonical_unique (xs ys : List Byte) (hx : wireShape xs) (hy : wireShape ys)
    (hcx : canonical xs) (hcy : canonical ys) (hv : wireValue xs = wireValue ys) : xs = ys := by
  rw [canonical_eq_encode xs hx hcx, canonical_eq_encode ys hy hcy, hv]

end VerifiedVarint.Spec
