import VerifiedVarint.Reference.Encode

namespace VerifiedVarint.Spec

theorem encode_nonempty (x : Nat) : Reference.encode x ≠ [] := by
  rw [Reference.encode]
  split <;> simp

theorem encode_value (x : Nat) : wireValue (Reference.encode x) = x := by
  rw [Reference.encode]
  split
  · rename_i hx
    simp [wireValue, payload, Nat.mod_eq_of_lt hx]
  · simp only [wireValue, payload]
    rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod, encode_value]
    omega
termination_by x
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem encode_shape (x : Nat) : wireShape (Reference.encode x) := by
  rw [Reference.encode]
  split
  · simp [wireShape, continues]; omega
  · have hn := encode_nonempty (x / 128)
    have hs := encode_shape (x / 128)
    cases he : Reference.encode (x / 128) with
    | nil => simp_all
    | cons b bs =>
      simp_all [wireShape, continues]
termination_by x
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

theorem encode_represents (x : Nat) : represents (Reference.encode x) x :=
  ⟨encode_shape x, encode_value x⟩

theorem encode_length_pos (x : Nat) : 0 < (Reference.encode x).length := by
  have h := encode_nonempty x
  cases he : Reference.encode x <;> simp_all

theorem encode_length_small (x : Nat) (hx : x < 128) :
    (Reference.encode x).length = 1 := by
  rw [Reference.encode]
  simp [hx]

theorem encode_length_step (x : Nat) (hx : 128 ≤ x) :
    (Reference.encode x).length = 1 + (Reference.encode (x / 128)).length := by
  rw [Reference.encode]
  simp [show ¬x < 128 by omega, Nat.add_comm]

theorem encode_length_le (k x : Nat) (hk : 0 < k) (hx : x < 128 ^ k) :
    (Reference.encode x).length ≤ k := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
    by_cases hs : x < 128
    · rw [encode_length_small x hs]
      omega
    · have hk' : 0 < k := by
        by_contra hn
        have he : k = 0 := by omega
        simp [he] at hx
        omega
      have hd : x / 128 < 128 ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by decide)]
        simpa [Nat.pow_succ, Nat.mul_comm] using hx
      have hi := ih (x / 128) hk' hd
      rw [encode_length_step x (by omega)]
      omega

/-- Every k-byte base-128 payload is below 128^k, irrespective of shape. -/
theorem wireValue_lt_pow (bs : List Byte) : wireValue bs < 128 ^ bs.length := by
  induction bs with
  | nil => simp [wireValue]
  | cons b bs ih =>
    have hp : payload b < 128 := Nat.mod_lt _ (by decide)
    simp only [wireValue, List.length_cons, Nat.pow_succ]
    omega

/-- Minimality against every representation in the specified base-128 format. -/
theorem encode_length_minimal (x : Nat) (bs : List Byte) (hr : represents bs x) :
    (Reference.encode x).length ≤ bs.length := by
  have hp : 0 < bs.length := by
    cases bs with
    | nil => simp [represents, wireShape] at hr
    | cons b bs => simp
  apply encode_length_le bs.length x hp
  rw [← hr.2]
  exact wireValue_lt_pow bs

theorem encode_last_nonzero (x : Nat) (hx : 0 < x) :
    ∃ last, (Reference.encode x).getLast? = some last ∧ payload last ≠ 0 := by
  rw [Reference.encode]
  split
  · rename_i hs
    refine ⟨⟨x, by omega⟩, ?_, ?_⟩
    · simp
    · simp [payload, Nat.mod_eq_of_lt hs]
      omega
  · rename_i hs
    have hq : 0 < x / 128 := by omega
    rw [List.getLast?_cons_of_ne_nil (encode_nonempty (x / 128))]
    exact encode_last_nonzero (x / 128) hq
termination_by x
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem encode_canonical (x : Nat) : canonical (Reference.encode x) := by
  by_cases hx : x = 0
  · left
    rw [hx]
    exact encode_length_small 0 (by decide)
  · right
    exact encode_last_nonzero x (by omega)

end VerifiedVarint.Spec
