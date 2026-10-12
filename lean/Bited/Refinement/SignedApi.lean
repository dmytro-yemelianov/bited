import Bited.Refinement.Encode32
import Bited.Refinement.Exact

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

theorem encoded_len_i64_refines (value : I64) :
    Generated.api.encoded_len_i64 value ⦃ len =>
      len.val = (Reference.encode (Spec.zigzag value.val)).length ∧ 1 ≤ len.val ∧ len.val ≤ 10 ⦄ := by
  unfold Generated.api.encoded_len_i64
  apply WP.spec_bind (zigzag64_refines value)
  intro u hu
  apply WP.spec_mono (encoded_len_u64_refines u)
  intro len h
  simpa only [hu] using h

theorem encoded_len_i32_refines (value : I32) :
    Generated.api.encoded_len_i32 value ⦃ len =>
      len.val = (Reference.encode (Spec.zigzag value.val)).length ∧ 1 ≤ len.val ∧ len.val ≤ 5 ⦄ := by
  unfold Generated.api.encoded_len_i32
  apply WP.spec_bind (zigzag32_refines value)
  intro u hu
  apply WP.spec_mono (encoded_len_u32_refines u)
  intro len h
  simpa only [hu] using h

theorem encode_i64_refines (value : I64) :
    Generated.api.encode_i64 value ⦃ encoded =>
      encoded.len.val = (Reference.encode (Spec.zigzag value.val)).length ∧
      1 ≤ encoded.len.val ∧ encoded.len.val ≤ 10 ∧
      (encoded.bytes.val.take encoded.len.val).map specByte = Reference.encode (Spec.zigzag value.val) ⦄ := by
  unfold Generated.api.encode_i64
  apply WP.spec_bind (zigzag64_refines value)
  intro u hu
  apply WP.spec_mono (encode_u64_refines u)
  intro encoded h
  simpa only [hu] using h

theorem encode_i32_refines (value : I32) :
    Generated.api.encode_i32 value ⦃ encoded =>
      encoded.len.val = (Reference.encode (Spec.zigzag value.val)).length ∧
      1 ≤ encoded.len.val ∧ encoded.len.val ≤ 5 ∧
      (encoded.bytes.val.take encoded.len.val).map specByte = Reference.encode (Spec.zigzag value.val) ⦄ := by
  unfold Generated.api.encode_i32
  apply WP.spec_bind (zigzag32_refines value)
  intro u hu
  apply WP.spec_mono (encode_u32_refines u)
  intro encoded h
  simpa only [hu] using h

def bufferContract (value : Nat) (out : Slice U8)
    (result : core.result.Result Usize Generated.encode.EncodeError × Slice U8) : Prop :=
  match result.1 with
  | .Err err => result.2 = out ∧ err.required.val = (Reference.encode value).length ∧
      err.available.val = out.length ∧ out.length < err.required.val
  | .Ok len => len.val = (Reference.encode value).length ∧
      (result.2.val.take len.val).map specByte = Reference.encode value ∧ suffixFrame len.val result.2 out

theorem encode_i64_into_refines (value : I64) (out : Slice U8) :
    Generated.api.encode_i64_into value out ⦃ result => bufferContract (Spec.zigzag value.val) out result ⦄ := by
  unfold Generated.api.encode_i64_into
  apply WP.spec_bind (zigzag64_refines value)
  intro u hu
  apply WP.spec_mono (encode_u64_into_refines u out)
  rintro ⟨r, out'⟩ h
  cases r <;> simpa only [bufferContract, hu] using h

theorem encode_i32_into_refines (value : I32) (out : Slice U8) :
    Generated.api.encode_i32_into value out ⦃ result => bufferContract (Spec.zigzag value.val) out result ⦄ := by
  unfold Generated.api.encode_i32_into
  apply WP.spec_bind (zigzag32_refines value)
  intro u hu
  apply WP.spec_mono (encode_u32_into_refines u out)
  rintro ⟨r, out'⟩ h
  cases r <;> simpa only [bufferContract, hu] using h

structure SignedDecoded where
  value : Int
  consumed : Nat
  canonical : Bool
  deriving DecidableEq

def signedReference (result : Reference.Outcome) : Except Reference.DecodeError SignedDecoded :=
  match result with
  | .error e => .error e
  | .ok d => .ok ⟨Spec.unzigzag d.value, d.consumed, d.canonical⟩

def signedOutcome64
    (result : core.result.Result (Generated.decode.Decoded I64) Generated.decode.DecodeError) :
    Except Reference.DecodeError SignedDecoded :=
  match result with
  | .Err e => .error ⟨referenceError e.kind, e.consumed.val⟩
  | .Ok d => .ok ⟨d.value.val, d.consumed.val, d.canonical⟩

theorem decode_i64_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.api.decode_i64 input policy ⦃ result => signedOutcome64 result =
      signedReference (Reference.decode 64 (referencePolicy policy) (input.val.map specByte)) ⦄ := by
  unfold Generated.api.decode_i64
  apply WP.spec_bind (decode_u64_refines input policy)
  intro result h
  rw [← h]
  cases result with
  | Err e => simp [signedOutcome64, referenceOutcome, signedReference]
  | Ok d =>
    simp only []
    apply WP.spec_bind (unzigzag64_refines d.value)
    intro n hn
    simp only [WP.spec_ok, signedOutcome64, referenceOutcome, signedReference, hn]

def signedExact (length : Nat) (result : Except Reference.DecodeError SignedDecoded) :
    Except Reference.DecodeError SignedDecoded :=
  match result with
  | .error e => .error e
  | .ok d => if d.consumed = length then .ok d else .error ⟨.trailingBytes, d.consumed⟩

theorem signed_exact_commutes64
    (result : core.result.Result (Generated.decode.Decoded I64) Generated.decode.DecodeError)
    (length : Nat) :
    signedOutcome64 (exactResult result length) = signedExact length (signedOutcome64 result) := by
  cases result with
  | Err e => rfl
  | Ok d => simp [exactResult, signedOutcome64, signedExact]; split_ifs <;> rfl

theorem decode_i64_exact_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.api.decode_i64_exact input policy ⦃ result => signedOutcome64 result =
      signedExact input.length (signedReference
        (Reference.decode 64 (referencePolicy policy) (input.val.map specByte))) ⦄ := by
  unfold Generated.api.decode_i64_exact
  apply WP.spec_bind (decode_i64_refines input policy)
  intro result h
  rw [exact_refines]
  simp only [WP.spec_ok, Slice.len_val]
  rw [signed_exact_commutes64, h]

end Bited.Refinement
