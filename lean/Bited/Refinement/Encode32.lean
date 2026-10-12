import Bited.Refinement.EncodeAccessors
import Bited.Refinement.ZigZag32
import Mathlib.Tactic.IntervalCases

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

theorem encode_length_u32_bounds (value : U32) :
    1 ≤ (Reference.encode value.val).length ∧ (Reference.encode value.val).length ≤ 5 := by
  refine ⟨Spec.encode_length_pos value.val, ?_⟩
  apply Spec.encode_length_le 5 value.val (by decide)
  have h := value.bv.isLt
  change value.val < 2^32 at h
  norm_num
  omega

theorem encoded_len_u32_refines (value : U32) :
    Generated.encode.encoded_len_u32 value ⦃ len =>
      len.val = (Reference.encode value.val).length ∧ 1 ≤ len.val ∧ len.val ≤ 5 ⦄ := by
  unfold Generated.encode.encoded_len_u32
  simp only [lift, bind_ok]
  apply WP.spec_mono (encoded_len_u64_refines (UScalar.cast .U64 value))
  intro len h
  rw [u32_widen_value] at h
  exact ⟨h.1, by rw [h.1]; exact (encode_length_u32_bounds value).1,
    by rw [h.1]; exact (encode_length_u32_bounds value).2⟩

theorem encode_u32_into_refines (value : U32) (out : Slice U8) :
    Generated.encode.encode_u32_into value out ⦃ result =>
      match result.1 with
      | .Err err => result.2 = out ∧
        err.required.val = (Reference.encode value.val).length ∧
        err.available.val = out.length ∧ out.length < err.required.val
      | .Ok len => len.val = (Reference.encode value.val).length ∧
        (result.2.val.take len.val).map specByte = Reference.encode value.val ∧
        suffixFrame len.val result.2 out ⦄ := by
  unfold Generated.encode.encode_u32_into
  simp only [lift, bind_ok]
  apply WP.spec_mono (encode_u64_into_refines (UScalar.cast .U64 value) out)
  intro result h
  rcases result with ⟨r, out'⟩
  cases r <;> simpa only [u32_widen_value] using h

theorem first_five_eq_take {α : Type} (xs : List α) (h : 5 ≤ xs.length) :
    [xs[0], xs[1], xs[2], xs[3], xs[4]] = xs.take 5 := by
  apply List.ext_getElem
  · simp; omega
  · intro i hi hj
    have hi' : i < 5 := by simpa using hi
    interval_cases i <;> simp <;> rfl

theorem encode_u32_refines (value : U32) :
    Generated.encode.encode_u32 value ⦃ encoded =>
      encoded.len.val = (Reference.encode value.val).length ∧
      1 ≤ encoded.len.val ∧ encoded.len.val ≤ 5 ∧
      (encoded.bytes.val.take encoded.len.val).map specByte = Reference.encode value.val ⦄ := by
  unfold Generated.encode.encode_u32
  simp only [lift, bind_ok]
  apply WP.spec_bind (encode_u64_refines (UScalar.cast .U64 value))
  intro encoded h
  rw [u32_widen_value] at h
  have hb := encode_length_u32_bounds value
  have hlen : encoded.bytes.val.length = 10 := by simpa using encoded.bytes.property
  step*
  have htake := first_five_eq_take encoded.bytes.val (by omega)
  simp only [Array.make_val, i1_post, i2_post, i3_post, i4_post, i5_post]
  erw [htake, List.take_take, Nat.min_eq_left (by omega)]
  exact ⟨h.1, h.2.1, by omega, h.2.2.2⟩

theorem encoded32_as_bytes_refines (encoded : Generated.encode.Encoded32)
    (hbound : encoded.len.val ≤ 5) :
    Generated.encode.Encoded32.as_bytes encoded ⦃ bytes =>
      bytes.val = encoded.bytes.val.take encoded.len.val ∧
      bytes.length = encoded.len.val ⦄ := by
  unfold Generated.encode.Encoded32.as_bytes
  simp only [Array.index_SliceIndexRangeToUsizeSlice]
  apply WP.spec_mono (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
    ⟨encoded.len⟩ encoded.bytes.to_slice (by
      rw [Array.length_to_slice]
      change encoded.len.val ≤ 5
      exact hbound))
  intro bytes h
  simpa only [Array.val_to_slice, List.slice_zero_j] using h

theorem encoded32_len_refines (encoded : Generated.encode.Encoded32) :
    Generated.encode.Encoded32.impl.len encoded = .ok encoded.len := by rfl

theorem encoded32_is_empty_refines (encoded : Generated.encode.Encoded32) :
    Generated.encode.Encoded32.is_empty encoded = .ok false := by rfl

theorem encode_u32_public_refines (value : U32) :
    (do
      let encoded ← Generated.encode.encode_u32 value
      let bytes ← Generated.encode.Encoded32.as_bytes encoded
      let len ← Generated.encode.Encoded32.impl.len encoded
      let empty ← Generated.encode.Encoded32.is_empty encoded
      ok (bytes, len, empty)) ⦃ result =>
        result.1.val.map specByte = Reference.encode value.val ∧
        result.1.length = result.2.1.val ∧
        result.2.1.val = (Reference.encode value.val).length ∧
        1 ≤ result.2.1.val ∧ result.2.1.val ≤ 5 ∧
        result.2.2 = false ⦄ := by
  apply WP.spec_bind (encode_u32_refines value)
  intro encoded h
  apply WP.spec_bind (encoded32_as_bytes_refines encoded h.2.2.1)
  intro bytes hb
  simp only [encoded32_len_refines, encoded32_is_empty_refines]
  step*

theorem encode_u32_zero_suffix (value : U32) :
    Generated.encode.encode_u32 value ⦃ encoded =>
      ∀ j, encoded.len.val ≤ j → j < 5 → encoded.bytes.val[j]? = some 0#u8 ⦄ := by
  unfold Generated.encode.encode_u32
  simp only [lift, bind_ok]
  apply WP.spec_bind (encode_u64_zero_suffix (UScalar.cast .U64 value))
  intro encoded hzero
  have hlen : encoded.bytes.val.length = 10 := by simpa using encoded.bytes.property
  step*
  intro j hge hj
  have htake := first_five_eq_take encoded.bytes.val (by omega)
  simp only [Array.make_val, i1_post, i2_post, i3_post, i4_post, i5_post]
  erw [htake]
  simp only [List.getElem?_take, hj, ↓reduceIte]
  exact hzero j hge (by omega)

theorem encode_u32_contract (value : U32) :
    Generated.encode.encode_u32 value ⦃ encoded =>
      let emitted := (encoded.bytes.val.take encoded.len.val).map specByte
      encoded.len.val = emitted.length ∧ 1 ≤ encoded.len.val ∧ encoded.len.val ≤ 5 ∧
      Spec.bounded 32 emitted value.val ∧ Spec.canonical emitted ∧
      (∀ bs, Spec.represents bs value.val → encoded.len.val ≤ bs.length) ∧
      (∀ j, encoded.len.val ≤ j → j < 5 → encoded.bytes.val[j]? = some 0#u8) ⦄ := by
  apply WP.spec_mono (WP.spec_and (encode_u32_refines value) (encode_u32_zero_suffix value))
  intro encoded h
  rcases h with ⟨⟨hlen, hlo, hhi, hbytes⟩, hzero⟩
  dsimp
  rw [hbytes]
  refine ⟨hlen, hlo, hhi, ?_, Spec.encode_canonical value.val, ?_, hzero⟩
  · exact ⟨Spec.encode_represents value.val, (encode_length_u32_bounds value).2, value.bv.isLt⟩
  · intro bs hrep
    rw [hlen]
    exact Spec.encode_length_minimal value.val bs hrep

theorem encode_u32_into_contract (value : U32) (out : Slice U8) :
    Generated.encode.encode_u32_into value out ⦃ result =>
      match result.1 with
      | .Err err => result.2 = out ∧
        err.required.val = (Reference.encode value.val).length ∧
        err.available.val = out.length ∧ out.length < err.required.val
      | .Ok len =>
        let emitted := (result.2.val.take len.val).map specByte
        len.val = emitted.length ∧ Spec.bounded 32 emitted value.val ∧
        Spec.canonical emitted ∧
        (∀ bs, Spec.represents bs value.val → len.val ≤ bs.length) ∧
        suffixFrame len.val result.2 out ⦄ := by
  apply WP.spec_mono (encode_u32_into_refines value out)
  rintro ⟨result, out'⟩ hr
  cases result with
  | Err err => exact hr
  | Ok len =>
    rcases hr with ⟨hlen, hbytes, hf⟩
    dsimp
    rw [hbytes]
    refine ⟨hlen, ?_, Spec.encode_canonical value.val, ?_, hf⟩
    · refine ⟨Spec.encode_represents value.val, ?_, ?_⟩
      · exact (encode_length_u32_bounds value).2
      · exact value.bv.isLt
    · intro bs hrep
      rw [hlen]
      exact Spec.encode_length_minimal value.val bs hrep

end Bited.Refinement
