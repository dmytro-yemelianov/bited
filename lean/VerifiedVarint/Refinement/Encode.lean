import VerifiedVarint.Generated.Funs
import VerifiedVarint.Proofs.Encode

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

theorem encode_length_u64_bounds (value : U64) :
    1 ≤ (Reference.encode value.val).length ∧ (Reference.encode value.val).length ≤ 10 := by
  constructor
  · have h := Spec.encode_length_pos value.val
    omega
  · apply Spec.encode_length_le 10 value.val (by decide)
    have h := value.bv.isLt
    change value.val < 2 ^ 64 at h
    norm_num at h ⊢
    omega

/-- One length transition agrees with division by 128, with checked addition. -/
theorem encoded_len_u64_body_refines (value : U64) (len : Usize) (total : Nat)
    (ht : total ≤ 10) (hl : 1 ≤ len.val)
    (hinv : len.val + (Reference.encode value.val).length = total + 1) :
    Generated.encode.encoded_len_u64_loop.body value len ⦃ r =>
      match r with
      | .cont (next, nextLen) =>
        1 ≤ nextLen.val ∧
        nextLen.val + (Reference.encode next.val).length = total + 1 ∧
        next.val < value.val
      | .done result => result.val = total ⦄ := by
  unfold Generated.encode.encoded_len_u64_loop.body
  have hp := Spec.encode_length_pos value.val
  have hlen : len.val ≤ 10 := by omega
  step*
  · have hx : 128 ≤ value.val := by scalar_tac
    have hv : value1.val = value.val / 128 := by
      simpa only [Nat.shiftRight_eq_div_pow] using value1_post
    rw [Spec.encode_length_step value.val hx] at hinv
    rw [hv]
    have hd : value.val / 128 < value.val := Nat.div_lt_self (by omega) (by decide)
    omega
  · have hx : value.val < 128 := by scalar_tac
    rw [Spec.encode_length_small value.val hx] at hinv
    omega

/-- Universal correspondence of the actual Rust length function to the
    independent list encoder, including termination and the 1..10 bound. -/
@[step]
theorem encoded_len_u64_refines (value : U64) :
    Generated.encode.encoded_len_u64 value ⦃ len =>
      len.val = (Reference.encode value.val).length ∧
      1 ≤ len.val ∧ len.val ≤ 10 ⦄ := by
  have hb := encode_length_u64_bounds value
  unfold Generated.encode.encoded_len_u64 Generated.encode.encoded_len_u64_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Usize) => state.1.val)
    (fun state => 1 ≤ state.2.val ∧
      state.2.val + (Reference.encode state.1.val).length =
        (Reference.encode value.val).length + 1)
  · rintro ⟨current, len⟩ ⟨hl, hinv⟩
    apply WP.spec_mono
      (encoded_len_u64_body_refines current len _ hb.2 hl hinv)
    intro r hr
    cases r with
    | done result =>
      dsimp at hr ⊢
      rw [hr]
      exact ⟨rfl, hb⟩
    | cont state =>
      rcases state with ⟨next, nextLen⟩
      dsimp at hr ⊢
      exact ⟨⟨hr.1, hr.2.1⟩, hr.2.2⟩
  · simp [Nat.add_comm]

theorem encoded_len_u64_minimal (value : U64) :
    Generated.encode.encoded_len_u64 value ⦃ len =>
      ∀ bs, Spec.represents bs value.val → len.val ≤ bs.length ⦄ := by
  apply WP.spec_mono (encoded_len_u64_refines value)
  intro len h bs hr
  rw [h.1]
  exact Spec.encode_length_minimal value.val bs hr

/-- Insufficient capacity returns exact counts and preserves every byte. -/
theorem encode_u64_into_short (value : U64) (out : Slice U8)
    (hshort : out.length < (Reference.encode value.val).length) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      ∃ err, result = (.Err err, out) ∧
        err.required.val = (Reference.encode value.val).length ∧
        err.available.val = out.length ⦄ := by
  unfold Generated.encode.encode_u64_into
  step*

/-- The caller's suffix is a frame: even out-of-range optional reads agree. -/
def suffixFrame (start : Nat) (out original : Slice U8) : Prop :=
  out.length = original.length ∧
    ∀ j, start ≤ j → out.val[j]? = original.val[j]?

theorem suffixFrame_set (start : Nat) (out original : Slice U8) (i : Usize) (b : U8)
    (hf : suffixFrame start out original) (hi : i.val < start) :
    suffixFrame start (out.set i b) original := by
  rcases hf with ⟨hlen, hframe⟩
  constructor
  · simpa using hlen
  · intro j hj
    simp only [Slice.set_val_eq]
    rw [List.getElem?_set_ne (i := i.val) (j := j) (by omega)]
    exact hframe j hj

/-- Safety, arithmetic progress and suffix preservation for every write step. -/
theorem encode_u64_into_body_frame (value : U64) (out original : Slice U8)
    (i : Usize) (required : Nat) (hr : required ≤ original.length) (_hb : required ≤ 10)
    (hinv : i.val + (Reference.encode value.val).length = required)
    (hf : suffixFrame required out original) :
    Generated.encode.encode_u64_into_loop.body value out i ⦃ r =>
      match r with
      | .cont (next, out', nextI) =>
        nextI.val + (Reference.encode next.val).length = required ∧
        suffixFrame required out' original ∧ next.val < value.val
      | .done (last, out', lastI) =>
        last.val < 128 ∧ lastI.val + 1 = required ∧
        suffixFrame required out' original ⦄ := by
  have hp := Spec.encode_length_pos value.val
  have hi : i.val < required := by omega
  have hlen := hf.1
  unfold Generated.encode.encode_u64_into_loop.body
  step*
  · have hx : 128 ≤ value.val := by scalar_tac
    have hv : value1.val = value.val / 128 := by
      simpa only [Nat.shiftRight_eq_div_pow] using value1_post
    rw [Spec.encode_length_step value.val hx] at hinv
    constructor
    · rw [hv]
      omega
    · constructor
      · rw [s_post]
        exact suffixFrame_set required out original i i3 hf hi
      · rw [hv]
        exact Nat.div_lt_self (by omega) (by decide)
  · have hx : value.val < 128 := by scalar_tac
    rw [Spec.encode_length_small value.val hx] at hinv
    exact ⟨hx, by omega, hf⟩

theorem encode_u64_into_loop_frame (value : U64) (out original : Slice U8)
    (i : Usize) (required : Nat) (hr : required ≤ original.length) (hb : required ≤ 10)
    (hinv : i.val + (Reference.encode value.val).length = required)
    (hf : suffixFrame required out original) :
    Generated.encode.encode_u64_into_loop value out i ⦃ result =>
      result.1.val < 128 ∧ result.2.2.val + 1 = required ∧
      suffixFrame required result.2.1 original ⦄ := by
  unfold Generated.encode.encode_u64_into_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Slice U8 × Usize) => state.1.val)
    (fun state => state.2.2.val + (Reference.encode state.1.val).length = required ∧
      suffixFrame required state.2.1 original)
  · rintro ⟨current, currentOut, currentI⟩ ⟨hinv', hf'⟩
    apply WP.spec_mono
      (encode_u64_into_body_frame current currentOut original currentI required hr hb hinv' hf')
    intro r h
    cases r with
    | done result => exact h
    | cont state => exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · exact ⟨hinv, hf⟩

/-- On sufficient capacity the public encoder is total and preserves the suffix. -/
theorem encode_u64_into_success_frame (value : U64) (out : Slice U8)
    (hcapacity : (Reference.encode value.val).length ≤ out.length) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      ∃ len out', result = (.Ok len, out') ∧
        len.val = (Reference.encode value.val).length ∧
        suffixFrame len.val out' out ⦄ := by
  unfold Generated.encode.encode_u64_into
  apply WP.spec_bind (encoded_len_u64_refines value)
  intro required hrequired
  have hc : ¬out.len < required := by
    intro hlt
    have h : out.len.val < required.val := by scalar_tac
    simp only [Slice.len_val] at h
    omega
  simp only [hc, ↓reduceIte]
  apply WP.spec_bind (encode_u64_into_loop_frame value out out 0#usize required.val
    (by omega) hrequired.2.2 (by simp [hrequired.1]) (by simp [suffixFrame]))
  rintro ⟨last, out', i⟩ ⟨hlast, hi, hf⟩
  step*
  refine ⟨required, out2, rfl, rfl, hrequired.1, ?_⟩
  rw [out2_post]
  apply suffixFrame_set required.val out' out i i1 hf
  dsimp at hi
  omega

/-- Totality and frame behavior of the public mutable-slice API for every buffer.
    Emitted-byte correctness is proved separately in EncodeContent. -/
theorem encode_u64_into_total_frame (value : U64) (out : Slice U8) :
    Generated.encode.encode_u64_into value out ⦃ result =>
      match result.1 with
      | .Err err => result.2 = out ∧
        err.required.val = (Reference.encode value.val).length ∧
        err.available.val = out.length
      | .Ok len => len.val = (Reference.encode value.val).length ∧
        suffixFrame len.val result.2 out ⦄ := by
  by_cases hc : (Reference.encode value.val).length ≤ out.length
  · apply WP.spec_mono (encode_u64_into_success_frame value out hc)
    intro result hr
    rcases hr with ⟨len, out', rfl, hlen, hf⟩
    exact ⟨hlen, hf⟩
  · apply WP.spec_mono (encode_u64_into_short value out (by omega))
    intro result hr
    rcases hr with ⟨err, rfl, hreq, havail⟩
    exact ⟨rfl, hreq, havail⟩

end VerifiedVarint.Refinement
