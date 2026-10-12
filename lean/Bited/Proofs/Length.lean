import Bited.Proofs.Encode
import Mathlib.Data.Nat.Size

namespace Bited.Spec

/-- The exact §4.3 length: at least one byte, otherwise ceil(bit_length / 7). -/
def encodedLength (x : Nat) : Nat := max 1 ((x.size + 6) / 7)

theorem encode_length_formula (x : Nat) : (Reference.encode x).length = encodedLength x := by
  have hp := encode_length_pos x
  have hv := wireValue_lt_pow (Reference.encode x)
  rw [encode_value] at hv
  have hpow (k : Nat) : 128 ^ k = 2 ^ (7 * k) := by
    rw [Nat.pow_mul]
  rw [hpow] at hv
  have hs : x.size ≤ 7 * (Reference.encode x).length := Nat.size_le.mpr hv
  have hsize : x.size ≤ 7 * encodedLength x := by
    unfold encodedLength
    omega
  have hpositive : 0 < encodedLength x := by unfold encodedLength; omega
  apply Nat.le_antisymm
  · apply encode_length_le (encodedLength x) x hpositive
    rw [hpow]
    exact Nat.size_le.mp hsize
  · unfold encodedLength
    omega

theorem encodedLength_zero : encodedLength 0 = 1 := by rfl

end Bited.Spec
