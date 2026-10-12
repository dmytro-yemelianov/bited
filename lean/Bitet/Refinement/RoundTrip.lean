import Bitet.Refinement.Decode32
import Bitet.Refinement.Encode32
import Bitet.Proofs.DecodeLanguage
import Bitet.Refinement.SignedApi32

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

theorem decode_encode_u64 (value : U64) :
    (do
      let encoded ← Generated.encode.encode_u64 value
      let bytes ← Generated.encode.Encoded64.as_bytes encoded
      Generated.decode.decode_u64 bytes .Canonical) ⦃ result =>
      match result with
      | .Err _ => False
      | .Ok d => d.value = value ∧ d.consumed.val = (Reference.encode value.val).length ∧ d.canonical = true ⦄ := by
  apply WP.spec_bind (encode_u64_refines value)
  intro encoded he
  apply WP.spec_bind (encoded64_as_bytes_refines encoded he.2.2.1)
  intro bytes hb
  apply WP.spec_mono (decode_u64_refines bytes .Canonical)
  intro result h
  have hbytes : bytes.val.map specByte = Reference.encode value.val := by rw [hb.1]; exact he.2.2.2
  rw [hbytes] at h
  have href := Reference.decode_encode 64 (Or.inr rfl) value.val value.bv.isLt []
  simp only [List.append_nil] at href
  rw [referencePolicy, href] at h
  cases result with
  | Err e => simp [referenceOutcome] at h
  | Ok d =>
    simp only [referenceOutcome, Except.ok.injEq] at h
    have hv := congrArg Reference.Decoded.value h
    have hc := congrArg Reference.Decoded.consumed h
    have hcanon := congrArg Reference.Decoded.canonical h
    exact ⟨UScalar.eq_of_val_eq hv, hc, hcanon⟩

theorem decode_encode_u32 (value : U32) :
    (do
      let encoded ← Generated.encode.encode_u32 value
      let bytes ← Generated.encode.Encoded32.as_bytes encoded
      Generated.decode.decode_u32 bytes .Canonical) ⦃ result =>
      match result with
      | .Err _ => False
      | .Ok d => d.value = value ∧ d.consumed.val = (Reference.encode value.val).length ∧ d.canonical = true ⦄ := by
  apply WP.spec_bind (encode_u32_refines value)
  intro encoded he
  apply WP.spec_bind (encoded32_as_bytes_refines encoded he.2.2.1)
  intro bytes hb
  apply WP.spec_mono (decode_u32_refines bytes .Canonical)
  intro result h
  have hbytes : bytes.val.map specByte = Reference.encode value.val := by rw [hb.1]; exact he.2.2.2
  rw [hbytes] at h
  have href := Reference.decode_encode 32 (Or.inl rfl) value.val value.bv.isLt []
  simp only [List.append_nil] at href
  rw [referencePolicy, href] at h
  cases result with
  | Err e => simp [referenceOutcome32] at h
  | Ok d =>
    simp only [referenceOutcome32, Except.ok.injEq] at h
    have hv := congrArg Reference.Decoded.value h
    have hc := congrArg Reference.Decoded.consumed h
    have hcanon := congrArg Reference.Decoded.canonical h
    exact ⟨UScalar.eq_of_val_eq hv, hc, hcanon⟩

theorem decode_encode_i64 (value : I64) :
    (do
      let encoded ← Generated.api.encode_i64 value
      let bytes ← Generated.encode.Encoded64.as_bytes encoded
      Generated.api.decode_i64 bytes .Canonical) ⦃ result =>
      match result with
      | .Err _ => False
      | .Ok d => d.value = value ∧ d.consumed.val = (Reference.encode (Spec.zigzag value.val)).length ∧ d.canonical = true ⦄ := by
  apply WP.spec_bind (encode_i64_refines value)
  intro encoded he
  apply WP.spec_bind (encoded64_as_bytes_refines encoded he.2.2.1)
  intro bytes hb
  apply WP.spec_mono (decode_i64_refines bytes .Canonical)
  intro result h
  have hbytes : bytes.val.map specByte = Reference.encode (Spec.zigzag value.val) := by rw [hb.1]; exact he.2.2.2
  rw [hbytes] at h
  have hdom := (Spec.zigzag_bounds 64 (by decide)).1 value.val (by
    unfold Spec.signedDomain
    scalar_tac)
  have href := Reference.decode_encode 64 (Or.inr rfl) (Spec.zigzag value.val) hdom []
  simp only [List.append_nil] at href
  rw [referencePolicy, href] at h
  simp only [signedReference, Spec.zigzag_left_inverse] at h
  cases result with
  | Err e => simp [signedOutcome64] at h
  | Ok d =>
    simp only [signedOutcome64, Except.ok.injEq] at h
    have hv := congrArg SignedDecoded.value h
    have hc := congrArg SignedDecoded.consumed h
    have hcanon := congrArg SignedDecoded.canonical h
    exact ⟨IScalar.eq_of_val_eq hv, hc, hcanon⟩

theorem decode_encode_i32 (value : I32) :
    (do
      let encoded ← Generated.api.encode_i32 value
      let bytes ← Generated.encode.Encoded32.as_bytes encoded
      Generated.api.decode_i32 bytes .Canonical) ⦃ result =>
      match result with
      | .Err _ => False
      | .Ok d => d.value = value ∧ d.consumed.val = (Reference.encode (Spec.zigzag value.val)).length ∧ d.canonical = true ⦄ := by
  apply WP.spec_bind (encode_i32_refines value)
  intro encoded he
  apply WP.spec_bind (encoded32_as_bytes_refines encoded he.2.2.1)
  intro bytes hb
  apply WP.spec_mono (decode_i32_refines bytes .Canonical)
  intro result h
  have hbytes : bytes.val.map specByte = Reference.encode (Spec.zigzag value.val) := by rw [hb.1]; exact he.2.2.2
  rw [hbytes] at h
  have hdom := (Spec.zigzag_bounds 32 (by decide)).1 value.val (by
    unfold Spec.signedDomain
    scalar_tac)
  have href := Reference.decode_encode 32 (Or.inl rfl) (Spec.zigzag value.val) hdom []
  simp only [List.append_nil] at href
  rw [referencePolicy, href] at h
  simp only [signedReference, Spec.zigzag_left_inverse] at h
  cases result with
  | Err e => simp [signedOutcome32] at h
  | Ok d =>
    simp only [signedOutcome32, Except.ok.injEq] at h
    have hv := congrArg SignedDecoded.value h
    have hc := congrArg SignedDecoded.consumed h
    have hcanon := congrArg SignedDecoded.canonical h
    exact ⟨IScalar.eq_of_val_eq hv, hc, hcanon⟩

end Bitet.Refinement
