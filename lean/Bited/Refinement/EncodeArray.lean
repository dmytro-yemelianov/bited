import Bited.Refinement.EncodeContent

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

theorem array_prefix_set (out : Aeneas.Std.Array U8 10#usize) (i : Usize) (b : U8) (hi : i.val < out.length) :
    ((out.set i b).val.take (i.val + 1)).map UScalar.val =
      (out.val.take i.val).map UScalar.val ++ [b.val] := by
  simp only [Array.set_val_eq]
  rw [List.take_succ_eq_append_getElem (by simpa using hi)]
  simp only [List.getElem_set_self, List.map_append, List.map_cons, List.map_nil]
  rw [List.take_set, List.set_eq_of_length_le (by simp)]

/-- Byte-content progress for the actual extracted fixed-array loop. -/
theorem encode_u64_body_content (value : U64) (out : Aeneas.Std.Array U8 10#usize) (i : Usize)
    (expected : List Nat) (required : Nat) (hcap : required ≤ out.length) (_hb : required ≤ 10)
    (hlen : i.val + (Reference.encode value.val).length = required)
    (hcontent : (out.val.take i.val).map UScalar.val ++ referenceBytes value.val = expected) :
    Generated.encode.encode_u64_loop.body value out i ⦃ r =>
      match r with
      | .cont (next, out', nextI) =>
        required ≤ out'.length ∧
        nextI.val + (Reference.encode next.val).length = required ∧
        (out'.val.take nextI.val).map UScalar.val ++ referenceBytes next.val = expected ∧
        next.val < value.val
      | .done (last, out', lastI) =>
        last.val < 128 ∧ lastI.val < out'.length ∧
        lastI.val + 1 = required ∧
        (out'.val.take lastI.val).map UScalar.val ++ referenceBytes last.val = expected ⦄ := by
  have hp := Spec.encode_length_pos value.val
  have hi : i.val < out.length := by omega
  unfold Generated.encode.encode_u64_loop.body
  step*
  · have hx : 128 ≤ value.val := by scalar_tac
    have hv : value1.val = value.val / 128 := by
      simpa only [Nat.shiftRight_eq_div_pow] using value1_post
    have hbyte : i3.val = value.val % 128 + 128 := by
      have h2 : i2 = i1 &&& 127#u8 := UScalar.eq_of_val_eq i2_post
      rw [i3_post, h2, i1_post]
      exact continuation_byte_value value
    constructor
    · simpa only [a_post, Array.set_length] using hcap
    · constructor
      · rw [Spec.encode_length_step value.val hx] at hlen
        rw [hv]
        omega
      · constructor
        · rw [a_post, i4_post, array_prefix_set out i i3 hi, hbyte, hv, List.append_assoc]
          rw [referenceBytes_step value.val hx] at hcontent
          simpa only [List.singleton_append] using hcontent
        · rw [hv]
          exact Nat.div_lt_self (by omega) (by decide)
  · have hx : value.val < 128 := by scalar_tac
    rw [Spec.encode_length_small value.val hx] at hlen
    exact ⟨hx, hi, by omega, hcontent⟩

theorem encode_u64_loop_content (value : U64) (out : Aeneas.Std.Array U8 10#usize) (i : Usize)
    (expected : List Nat) (required : Nat) (hcap : required ≤ out.length) (hb : required ≤ 10)
    (hlen : i.val + (Reference.encode value.val).length = required)
    (hcontent : (out.val.take i.val).map UScalar.val ++ referenceBytes value.val = expected) :
    Generated.encode.encode_u64_loop value out i ⦃ result =>
      result.1.val < 128 ∧ result.2.2.val < result.2.1.length ∧
      result.2.2.val + 1 = required ∧
      (result.2.1.val.take result.2.2.val).map UScalar.val ++ referenceBytes result.1.val = expected ⦄ := by
  unfold Generated.encode.encode_u64_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Aeneas.Std.Array U8 10#usize × Usize) => state.1.val)
    (fun state => required ≤ state.2.1.length ∧
      state.2.2.val + (Reference.encode state.1.val).length = required ∧
      (state.2.1.val.take state.2.2.val).map UScalar.val ++ referenceBytes state.1.val = expected)
  · rintro ⟨current, currentOut, currentI⟩ ⟨hcap', hlen', hcontent'⟩
    apply WP.spec_mono (encode_u64_body_content current currentOut currentI expected required
      hcap' hb hlen' hcontent')
    intro r h
    cases r with
    | done result => exact h
    | cont state => exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
  · exact ⟨hcap, hlen, hcontent⟩


/-- The caller's suffix is a frame: even out-of-range optional reads agree. -/
def arraySuffixFrame (start : Nat) (out original : Aeneas.Std.Array U8 10#usize) : Prop :=
  out.length = original.length ∧
    ∀ j, start ≤ j → out.val[j]? = original.val[j]?

theorem arraySuffixFrame_set (start : Nat) (out original : Aeneas.Std.Array U8 10#usize) (i : Usize) (b : U8)
    (hf : arraySuffixFrame start out original) (hi : i.val < start) :
    arraySuffixFrame start (out.set i b) original := by
  rcases hf with ⟨hlen, hframe⟩
  constructor
  · simpa only [Array.set_length] using hlen
  · intro j hj
    simp only [Array.set_val_eq]
    rw [List.getElem?_set_ne (i := i.val) (j := j) (by omega)]
    exact hframe j hj

/-- Safety, arithmetic progress and suffix preservation for every write step. -/
theorem encode_u64_body_frame (value : U64) (out original : Aeneas.Std.Array U8 10#usize)
    (i : Usize) (required : Nat) (hr : required ≤ original.length) (_hb : required ≤ 10)
    (hinv : i.val + (Reference.encode value.val).length = required)
    (hf : arraySuffixFrame required out original) :
    Generated.encode.encode_u64_loop.body value out i ⦃ r =>
      match r with
      | .cont (next, out', nextI) =>
        nextI.val + (Reference.encode next.val).length = required ∧
        arraySuffixFrame required out' original ∧ next.val < value.val
      | .done (last, out', lastI) =>
        last.val < 128 ∧ lastI.val + 1 = required ∧
        arraySuffixFrame required out' original ⦄ := by
  have hp := Spec.encode_length_pos value.val
  have hi : i.val < required := by omega
  have hlen := hf.1
  unfold Generated.encode.encode_u64_loop.body
  step*
  · have hx : 128 ≤ value.val := by scalar_tac
    have hv : value1.val = value.val / 128 := by
      simpa only [Nat.shiftRight_eq_div_pow] using value1_post
    rw [Spec.encode_length_step value.val hx] at hinv
    constructor
    · rw [hv]
      omega
    · constructor
      · rw [a_post]
        exact arraySuffixFrame_set required out original i i3 hf hi
      · rw [hv]
        exact Nat.div_lt_self (by omega) (by decide)
  · have hx : value.val < 128 := by scalar_tac
    rw [Spec.encode_length_small value.val hx] at hinv
    exact ⟨hx, by omega, hf⟩

theorem encode_u64_loop_frame (value : U64) (out original : Aeneas.Std.Array U8 10#usize)
    (i : Usize) (required : Nat) (hr : required ≤ original.length) (hb : required ≤ 10)
    (hinv : i.val + (Reference.encode value.val).length = required)
    (hf : arraySuffixFrame required out original) :
    Generated.encode.encode_u64_loop value out i ⦃ result =>
      result.1.val < 128 ∧ result.2.2.val + 1 = required ∧
      arraySuffixFrame required result.2.1 original ⦄ := by
  unfold Generated.encode.encode_u64_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Aeneas.Std.Array U8 10#usize × Usize) => state.1.val)
    (fun state => state.2.2.val + (Reference.encode state.1.val).length = required ∧
      arraySuffixFrame required state.2.1 original)
  · rintro ⟨current, currentOut, currentI⟩ ⟨hinv', hf'⟩
    apply WP.spec_mono
      (encode_u64_body_frame current currentOut original currentI required hr hb hinv' hf')
    intro r h
    cases r with
    | done result => exact h
    | cont state => exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · exact ⟨hinv, hf⟩

/-- Fixed-array output agrees with the independent encoder for every u64. -/
theorem encode_u64_refines (value : U64) :
    Generated.encode.encode_u64 value ⦃ encoded =>
      encoded.len.val = (Reference.encode value.val).length ∧
      1 ≤ encoded.len.val ∧ encoded.len.val ≤ 10 ∧
      (encoded.bytes.val.take encoded.len.val).map specByte = Reference.encode value.val ⦄ := by
  have hb := encode_length_u64_bounds value
  unfold Generated.encode.encode_u64
  apply WP.spec_bind (encode_u64_loop_content value (Array.repeat 10#usize 0#u8) 0#usize
    (referenceBytes value.val) (Reference.encode value.val).length
    (by rw [Array.length, Array.length_eq]; change _ ≤ 10; exact hb.2) hb.2 (by simp) (by simp))
  rintro ⟨last, bytes, i⟩ ⟨hlast, hbound, hi, hcontent⟩
  dsimp at hlast hbound hi hcontent
  step*
  have hbyte : i1.val = last.val := by
    rw [i1_post, UScalar.cast_val_eq]
    change last.val % 256 = last.val
    omega
  have hlen : i2.val = (Reference.encode value.val).length := by omega
  refine ⟨hlen, by omega, by omega, ?_⟩
  apply List.map_injective_iff.mpr Fin.val_injective
  rw [List.map_map]
  change (bytes2.val.take i2.val).map UScalar.val = referenceBytes value.val
  rw [bytes2_post, i2_post, array_prefix_set bytes i i1 hbound, hbyte]
  rw [referenceBytes_small last.val hlast] at hcontent
  exact hcontent

/-- Every private unused array byte retains its initialized zero value. -/
theorem encode_u64_zero_suffix (value : U64) :
    Generated.encode.encode_u64 value ⦃ encoded =>
      ∀ j, encoded.len.val ≤ j → j < 10 → encoded.bytes.val[j]? = some 0#u8 ⦄ := by
  have hb := encode_length_u64_bounds value
  unfold Generated.encode.encode_u64
  apply WP.spec_bind (encode_u64_loop_frame value (Array.repeat 10#usize 0#u8)
    (Array.repeat 10#usize 0#u8) 0#usize (Reference.encode value.val).length
    (by rw [Array.length, Array.length_eq]; change _ ≤ 10; exact hb.2)
    hb.2 (by simp) (by simp [arraySuffixFrame]))
  rintro ⟨last, bytes, i⟩ ⟨hlast, hi, hf⟩
  dsimp at hlast hi hf
  step*
  have hf' : arraySuffixFrame (Reference.encode value.val).length bytes2
      (Array.repeat 10#usize 0#u8) := by
    rw [bytes2_post]
    exact arraySuffixFrame_set _ bytes _ i i1 hf (by omega)
  intro j hge hj
  have hge' : (Reference.encode value.val).length ≤ j := by omega
  rw [hf'.2 j hge', Array.repeat_val]
  change (List.replicate 10 0#u8)[j]? = some 0#u8
  simp only [List.getElem?_replicate, hj, ↓reduceIte]

/-- Full fixed-array encoding contract, including the initialized private suffix. -/
theorem encode_u64_contract (value : U64) :
    Generated.encode.encode_u64 value ⦃ encoded =>
      let emitted := (encoded.bytes.val.take encoded.len.val).map specByte
      encoded.len.val = emitted.length ∧ 1 ≤ encoded.len.val ∧ encoded.len.val ≤ 10 ∧
      Spec.bounded 64 emitted value.val ∧ Spec.canonical emitted ∧
      (∀ bs, Spec.represents bs value.val → encoded.len.val ≤ bs.length) ∧
      (∀ j, encoded.len.val ≤ j → j < 10 → encoded.bytes.val[j]? = some 0#u8) ⦄ := by
  apply WP.spec_mono (WP.spec_and (encode_u64_refines value) (encode_u64_zero_suffix value))
  intro encoded h
  rcases h with ⟨⟨hlen, hlo, hhi, hbytes⟩, hzero⟩
  dsimp
  rw [hbytes]
  refine ⟨hlen, hlo, hhi, ?_, Spec.encode_canonical value.val, ?_, hzero⟩
  · exact ⟨Spec.encode_represents value.val, (encode_length_u64_bounds value).2, value.bv.isLt⟩
  · intro bs hrep
    rw [hlen]
    exact Spec.encode_length_minimal value.val bs hrep

end Bited.Refinement
