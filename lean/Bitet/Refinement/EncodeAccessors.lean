import Bitet.Refinement.EncodeArray

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

/-- The extracted accessor exposes exactly the valid prefix under the constructor invariant. -/
theorem encoded64_as_bytes_refines (encoded : Generated.encode.Encoded64)
    (hbound : encoded.len.val ≤ 10) :
    Generated.encode.Encoded64.as_bytes encoded ⦃ bytes =>
      bytes.val = encoded.bytes.val.take encoded.len.val ∧
      bytes.length = encoded.len.val ⦄ := by
  unfold Generated.encode.Encoded64.as_bytes
  simp only [Array.index_SliceIndexRangeToUsizeSlice]
  apply WP.spec_mono (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    ⟨encoded.len⟩ encoded.bytes.to_slice (by
      rw [Array.length_to_slice]
      change encoded.len.val ≤ 10
      exact hbound))
  intro bytes h
  simpa only [Array.val_to_slice, List.slice_zero_j] using h

theorem encoded64_len_refines (encoded : Generated.encode.Encoded64) :
    Generated.encode.Encoded64.impl.len encoded = .ok encoded.len := by rfl

theorem encoded64_is_empty_refines (encoded : Generated.encode.Encoded64) :
    Generated.encode.Encoded64.is_empty encoded = .ok false := by rfl

/-- End-to-end correspondence through all three actual public fixed-array accessors.
    No validity assumption is required: the actual encoder establishes it. -/
theorem encode_u64_public_refines (value : U64) :
    (do
      let encoded ← Generated.encode.encode_u64 value
      let bytes ← Generated.encode.Encoded64.as_bytes encoded
      let len ← Generated.encode.Encoded64.impl.len encoded
      let empty ← Generated.encode.Encoded64.is_empty encoded
      ok (bytes, len, empty)) ⦃ result =>
        result.1.val.map specByte = Reference.encode value.val ∧
        result.1.length = result.2.1.val ∧
        result.2.1.val = (Reference.encode value.val).length ∧
        1 ≤ result.2.1.val ∧ result.2.1.val ≤ 10 ∧
        result.2.2 = false ⦄ := by
  apply WP.spec_bind (encode_u64_refines value)
  intro encoded h
  apply WP.spec_bind (encoded64_as_bytes_refines encoded h.2.2.1)
  intro bytes hb
  simp only [encoded64_len_refines, encoded64_is_empty_refines]
  step*

end Bitet.Refinement
