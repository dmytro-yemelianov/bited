import VerifiedVarint.Refinement.Decode32
import VerifiedVarint.Refinement.SignedApi

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

def signedOutcome32
    (result : core.result.Result (Generated.decode.Decoded I32) Generated.decode.DecodeError) :
    Except Reference.DecodeError SignedDecoded :=
  match result with
  | .Err e => .error ⟨referenceError e.kind, e.consumed.val⟩
  | .Ok d => .ok ⟨d.value.val, d.consumed.val, d.canonical⟩

theorem decode_i32_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.api.decode_i32 input policy ⦃ result => signedOutcome32 result =
      signedReference (Reference.decode 32 (referencePolicy policy) (input.val.map specByte)) ⦄ := by
  unfold Generated.api.decode_i32
  apply WP.spec_bind (decode_u32_refines input policy)
  intro result h
  rw [← h]
  cases result with
  | Err e => simp [signedOutcome32, referenceOutcome32, signedReference]
  | Ok d =>
    simp only []
    apply WP.spec_bind (unzigzag32_refines d.value)
    intro n hn
    simp only [WP.spec_ok, signedOutcome32, referenceOutcome32, signedReference, hn]

theorem signed_exact_commutes32
    (result : core.result.Result (Generated.decode.Decoded I32) Generated.decode.DecodeError)
    (length : Nat) :
    signedOutcome32 (exactResult result length) = signedExact length (signedOutcome32 result) := by
  cases result with
  | Err e => rfl
  | Ok d => simp [exactResult, signedOutcome32, signedExact]; split_ifs <;> rfl

theorem decode_i32_exact_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.api.decode_i32_exact input policy ⦃ result => signedOutcome32 result =
      signedExact input.length (signedReference
        (Reference.decode 32 (referencePolicy policy) (input.val.map specByte))) ⦄ := by
  unfold Generated.api.decode_i32_exact
  apply WP.spec_bind (decode_i32_refines input policy)
  intro result h
  rw [exact_refines]
  simp only [WP.spec_ok, Slice.len_val]
  rw [signed_exact_commutes32, h]


theorem exact_reference_commutes32
    (result : core.result.Result (Generated.decode.Decoded U32) Generated.decode.DecodeError)
    (length : Nat) :
    referenceOutcome32 (exactResult result length) = Reference.exact length (referenceOutcome32 result) := by
  cases result with
  | Err e => rfl
  | Ok d => simp [exactResult, referenceOutcome32, Reference.exact]; split_ifs <;> rfl

theorem decode_u32_exact_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.api.decode_u32_exact input policy ⦃ r =>
      referenceOutcome32 r = Reference.exact input.length
        (Reference.decode 32 (referencePolicy policy) (input.val.map specByte)) ⦄ := by
  unfold Generated.api.decode_u32_exact
  apply WP.spec_bind (decode_u32_refines input policy)
  intro result h
  rw [exact_refines]
  simp only [WP.spec_ok, Slice.len_val]
  rw [exact_reference_commutes32, h]

end VerifiedVarint.Refinement
