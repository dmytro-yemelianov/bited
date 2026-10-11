import VerifiedVarint.Refinement.Encode

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

/-- Natural-valued byte list, independent of the Rust bitwise emitter. -/
def referenceBytes (value : Nat) : List Nat := (Reference.encode value).map Fin.val

theorem referenceBytes_step (value : Nat) (hv : 128 ≤ value) :
    referenceBytes value = (value % 128 + 128) :: referenceBytes (value / 128) := by
  unfold referenceBytes
  rw [Reference.encode]
  simp [show ¬value < 128 by omega]

theorem referenceBytes_small (value : Nat) (hv : value < 128) :
    referenceBytes value = [value] := by
  unfold referenceBytes
  rw [Reference.encode]
  simp [hv]

/-- Truncating to u8, masking seven bits, and setting continuation is arithmetic. -/
theorem continuation_byte_value (value : U64) :
    ((UScalar.cast .U8 value &&& 127#u8) ||| 128#u8).val = value.val % 128 + 128 := by
  rw [UScalar.val_or, UScalar.val_and, UScalar.cast_val_eq]
  change (value.val % 256 &&& 127) ||| 128 = value.val % 128 + 128
  have hm : value.val % 256 &&& 127 = value.val % 128 := by
    change value.val % 256 &&& (2 ^ 7 - 1) = value.val % 128
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hm, Nat.or_comm]
  have h := Nat.two_pow_add_eq_or_of_lt (i := 7) (b := value.val % 128) (by omega) 1
  change 128 + value.val % 128 = 128 ||| value.val % 128 at h
  exact h.symm.trans (Nat.add_comm _ _)

theorem output_prefix_set (out : Slice U8) (i : Usize) (b : U8) (hi : i.val < out.length) :
    ((out.set i b).val.take (i.val + 1)).map UScalar.val =
      (out.val.take i.val).map UScalar.val ++ [b.val] := by
  simp only [Slice.set_val_eq]
  rw [List.take_succ_eq_append_getElem (by simpa using hi)]
  simp only [List.getElem_set_self, List.map_append, List.map_cons, List.map_nil]
  rw [List.take_set, List.set_eq_of_length_le (by simp)]

/-- Byte-content progress for the actual extracted mutable-slice loop. -/
theorem encode_u64_into_body_content (value : U64) (out : Slice U8) (i : Usize)
    (expected : List Nat) (required : Nat) (hcap : required ≤ out.length) (_hb : required ≤ 10)
    (hlen : i.val + (Reference.encode value.val).length = required)
    (hcontent : (out.val.take i.val).map UScalar.val ++ referenceBytes value.val = expected) :
    Generated.encode.encode_u64_into_loop.body value out i ⦃ r =>
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
  unfold Generated.encode.encode_u64_into_loop.body
  step*
  · have hx : 128 ≤ value.val := by scalar_tac
    have hv : value1.val = value.val / 128 := by
      simpa only [Nat.shiftRight_eq_div_pow] using value1_post
    have hbyte : i3.val = value.val % 128 + 128 := by
      have h2 : i2 = i1 &&& 127#u8 := UScalar.eq_of_val_eq i2_post
      rw [i3_post, h2, i1_post]
      exact continuation_byte_value value
    constructor
    · simpa only [s_post, Slice.set_length] using hcap
    · constructor
      · rw [Spec.encode_length_step value.val hx] at hlen
        rw [hv]
        omega
      · constructor
        · rw [s_post, i4_post, output_prefix_set out i i3 hi, hbyte, hv, List.append_assoc]
          rw [referenceBytes_step value.val hx] at hcontent
          simpa only [List.singleton_append] using hcontent
        · rw [hv]
          exact Nat.div_lt_self (by omega) (by decide)
  · have hx : value.val < 128 := by scalar_tac
    rw [Spec.encode_length_small value.val hx] at hlen
    exact ⟨hx, hi, by omega, hcontent⟩

theorem encode_u64_into_loop_content (value : U64) (out : Slice U8) (i : Usize)
    (expected : List Nat) (required : Nat) (hcap : required ≤ out.length) (hb : required ≤ 10)
    (hlen : i.val + (Reference.encode value.val).length = required)
    (hcontent : (out.val.take i.val).map UScalar.val ++ referenceBytes value.val = expected) :
    Generated.encode.encode_u64_into_loop value out i ⦃ result =>
      result.1.val < 128 ∧ result.2.2.val < result.2.1.length ∧
      result.2.2.val + 1 = required ∧
      (result.2.1.val.take result.2.2.val).map UScalar.val ++ referenceBytes result.1.val = expected ⦄ := by
  unfold Generated.encode.encode_u64_into_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Slice U8 × Usize) => state.1.val)
    (fun state => required ≤ state.2.1.length ∧
      state.2.2.val + (Reference.encode state.1.val).length = required ∧
      (state.2.1.val.take state.2.2.val).map UScalar.val ++ referenceBytes state.1.val = expected)
  · rintro ⟨current, currentOut, currentI⟩ ⟨hcap', hlen', hcontent'⟩
    apply WP.spec_mono (encode_u64_into_body_content current currentOut currentI expected required
      hcap' hb hlen' hcontent')
    intro r h
    cases r with
    | done result => exact h
    | cont state => exact ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
  · exact ⟨hcap, hlen, hcontent⟩

/-- The successful public buffer prefix equals the independent mathematical encoder. -/
theorem encode_u64_into_success_content (value : U64) (out : Slice U8)
    (hcapacity : (Reference.encode value.val).length ≤ out.length) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      ∃ len out', result = (.Ok len, out') ∧
        len.val = (Reference.encode value.val).length ∧
        (out'.val.take len.val).map UScalar.val = referenceBytes value.val ⦄ := by
  unfold Generated.encode.encode_u64_into
  apply WP.spec_bind (encoded_len_u64_refines value)
  intro required hrequired
  have hc : ¬out.len < required := by
    intro hlt
    have h : out.len.val < required.val := by scalar_tac
    simp only [Slice.len_val] at h
    omega
  simp only [hc, ↓reduceIte]
  apply WP.spec_bind (encode_u64_into_loop_content value out 0#usize (referenceBytes value.val)
    required.val (by omega) hrequired.2.2 (by simp [hrequired.1]) (by simp))
  rintro ⟨last, out', i⟩ ⟨hlast, hbound, hi, hcontent⟩
  dsimp at hlast hbound hi hcontent
  step*
  have hbyte : i1.val = last.val := by
    rw [i1_post, UScalar.cast_val_eq]
    change last.val % 256 = last.val
    omega
  refine ⟨required, out2, rfl, rfl, hrequired.1, ?_⟩
  rw [out2_post, ← hi, output_prefix_set out' i i1 hbound, hbyte]
  rw [referenceBytes_small last.val hlast] at hcontent
  exact hcontent

def specByte (b : U8) : Spec.Byte := ⟨b.val, b.bv.isLt⟩

theorem output_bytes_eq_reference (out : Slice U8) (len : Nat) (value : Nat)
    (h : (out.val.take len).map UScalar.val = referenceBytes value) :
    (out.val.take len).map specByte = Reference.encode value := by
  apply List.map_injective_iff.mpr Fin.val_injective
  simpa only [List.map_map, Function.comp_def, specByte, referenceBytes] using h

/-- All properties of the successful public mutable-slice encoder in one theorem. -/
theorem encode_u64_into_success_refines (value : U64) (out : Slice U8)
    (hcapacity : (Reference.encode value.val).length ≤ out.length) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      ∃ len out', result = (.Ok len, out') ∧
        len.val = (Reference.encode value.val).length ∧
        (out'.val.take len.val).map specByte = Reference.encode value.val ∧
        suffixFrame len.val out' out ⦄ := by
  apply WP.spec_mono (WP.spec_and (encode_u64_into_success_frame value out hcapacity)
    (encode_u64_into_success_content value out hcapacity))
  intro result h
  rcases h.1 with ⟨len, out', he, hlen, hf⟩
  rcases h.2 with ⟨len', out'', he', hlen', hcontent⟩
  have hpair := he.symm.trans he'
  have hout : out' = out'' := congrArg Prod.snd hpair
  have hlenEq : len = len' := by
    have hresult := congrArg Prod.fst hpair
    cases hresult
    rfl
  refine ⟨len, out', he, hlen, ?_, hf⟩
  apply output_bytes_eq_reference
  rw [hout, hlenEq]
  exact hcontent

/-- Complete value/byte/length/error/frame correspondence for all caller buffers. -/
theorem encode_u64_into_refines (value : U64) (out : Slice U8) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      match result.1 with
      | .Err err => result.2 = out ∧
        err.required.val = (Reference.encode value.val).length ∧
        err.available.val = out.length ∧ out.length < err.required.val
      | .Ok len => len.val = (Reference.encode value.val).length ∧
        (result.2.val.take len.val).map specByte = Reference.encode value.val ∧
        suffixFrame len.val result.2 out ⦄ := by
  by_cases hc : (Reference.encode value.val).length ≤ out.length
  · apply WP.spec_mono (encode_u64_into_success_refines value out hc)
    intro result hr
    rcases hr with ⟨len, out', rfl, hlen, hbytes, hf⟩
    exact ⟨hlen, hbytes, hf⟩
  · apply WP.spec_mono (encode_u64_into_short value out (by omega))
    intro result hr
    rcases hr with ⟨err, rfl, hreq, havail⟩
    exact ⟨rfl, hreq, havail, by omega⟩

/-- Successful Rust output represents the input canonically and has minimal length;
    errors have the exact capacity contract. This covers the mutable-slice API. -/
theorem encode_u64_into_contract (value : U64) (out : Slice U8) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      match result.1 with
      | .Err err => result.2 = out ∧
        err.required.val = (Reference.encode value.val).length ∧
        err.available.val = out.length ∧ out.length < err.required.val
      | .Ok len =>
        let emitted := (result.2.val.take len.val).map specByte
        len.val = emitted.length ∧ Spec.bounded 64 emitted value.val ∧
        Spec.canonical emitted ∧
        (∀ bs, Spec.represents bs value.val → len.val ≤ bs.length) ∧
        suffixFrame len.val result.2 out ⦄ := by
  apply WP.spec_mono (encode_u64_into_refines value out)
  rintro ⟨result, out'⟩ hr
  cases result with
  | Err err => exact hr
  | Ok len =>
    rcases hr with ⟨hlen, hbytes, hf⟩
    dsimp
    rw [hbytes]
    refine ⟨hlen, ?_, Spec.encode_canonical value.val, ?_, hf⟩
    · refine ⟨Spec.encode_represents value.val, ?_, ?_⟩
      · exact (encode_length_u64_bounds value).2
      · exact value.bv.isLt
    · intro bs hrep
      rw [hlen]
      exact Spec.encode_length_minimal value.val bs hrep

end VerifiedVarint.Refinement
