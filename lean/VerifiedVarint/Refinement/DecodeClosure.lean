import VerifiedVarint.Refinement.RoundTrip
import VerifiedVarint.Refinement.DecodeContract
import VerifiedVarint.Proofs.DecodeCost

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result
attribute [local instance] Classical.propDecidable

theorem decode_u32_complete (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (emitted rest : List Spec.Byte) (value : Nat)
    (hb : Spec.bounded 32 emitted value)
    (hpolicy : referencePolicy policy = .canonical → Spec.canonical emitted)
    (hinput : input.val.map specByte = emitted ++ rest) :
    Generated.decode.decode_u32 input policy ⦃ result =>
      referenceOutcome32 result = .ok ⟨value, emitted.length, decide (Spec.canonical emitted)⟩ ⦄ := by
  apply WP.spec_mono (decode_u32_refines input policy)
  intro result h
  rw [h, hinput]
  exact Reference.decode_complete 32 (Or.inl rfl) _ _ _ _ hb hpolicy

/-- Successful prefix decoding followed by the canonical encoder normalizes every
    accepted bounded spelling and preserves an already-canonical prefix. -/
theorem decode_u32_normalize (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    (do
      let decoded ← Generated.decode.decode_u32 input policy
      match decoded with
      | .Err e => ok (.Err e : core.result.Result (Generated.decode.Decoded U32 × Generated.encode.Encoded32) Generated.decode.DecodeError)
      | .Ok d => do
        let encoded ← Generated.encode.encode_u32 d.value
        ok (.Ok (d, encoded))) ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (d, encoded) =>
        let emitted := (encoded.bytes.val.take encoded.len.val).map specByte
        Spec.bounded 32 emitted d.value.val ∧ Spec.canonical emitted ∧
        (∀ bs, Spec.represents bs d.value.val → emitted.length ≤ bs.length) ∧
        (d.canonical = true → emitted = (input.val.take d.consumed.val).map specByte) ⦄ := by
  apply WP.spec_bind (decode_u32_sound input policy)
  intro decoded hd
  cases decoded with
  | Err e => simp
  | Ok d =>
    apply WP.spec_bind (WP.spec_and (encode_u32_contract d.value) (encode_u32_refines d.value))
    intro encoded he
    have hp := he.1
    have hb := he.2
    dsimp at hp hd
    have hminimal : ∀ bs, Spec.represents bs d.value.val →
        ((encoded.bytes.val.take encoded.len.val).map specByte).length ≤ bs.length := by
      intro bs hs
      rw [← hp.1]
      exact hp.2.2.2.2.2.1 bs hs
    have hsame : d.canonical = true →
        (encoded.bytes.val.take encoded.len.val).map specByte = (input.val.take d.consumed.val).map specByte := by
      intro hc
      have hs := Spec.canonical_eq_encode _ hd.1.1.1 (hd.2.1.mp hc)
      rw [hd.1.1.2] at hs
      rw [hb.2.2.2, hs]
    simpa using And.intro hp.2.2.2.1 (And.intro hp.2.2.2.2.1 (And.intro hminimal hsame))

theorem decode_u32_consumption_bounded (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u32 input policy ⦃ result =>
      Reference.consumed (referenceOutcome32 result) ≤ 5 ∧
      Reference.consumed (referenceOutcome32 result) ≤ input.length ⦄ := by
  apply WP.spec_mono (decode_u32_refines input policy)
  intro result h
  rw [h]
  simpa [Spec.maxBytes, Slice.length] using
    Reference.decode_consumption_bounds 32 (referencePolicy policy) (input.val.map specByte)

theorem decode_u64_complete (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (emitted rest : List Spec.Byte) (value : Nat)
    (hb : Spec.bounded 64 emitted value)
    (hpolicy : referencePolicy policy = .canonical → Spec.canonical emitted)
    (hinput : input.val.map specByte = emitted ++ rest) :
    Generated.decode.decode_u64 input policy ⦃ result =>
      referenceOutcome result = .ok ⟨value, emitted.length, decide (Spec.canonical emitted)⟩ ⦄ := by
  apply WP.spec_mono (decode_u64_refines input policy)
  intro result h
  rw [h, hinput]
  exact Reference.decode_complete 64 (Or.inr rfl) _ _ _ _ hb hpolicy

/-- Successful prefix decoding followed by the canonical encoder normalizes every
    accepted bounded spelling and preserves an already-canonical prefix. -/
theorem decode_u64_normalize (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    (do
      let decoded ← Generated.decode.decode_u64 input policy
      match decoded with
      | .Err e => ok (.Err e : core.result.Result (Generated.decode.Decoded U64 × Generated.encode.Encoded64) Generated.decode.DecodeError)
      | .Ok d => do
        let encoded ← Generated.encode.encode_u64 d.value
        ok (.Ok (d, encoded))) ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (d, encoded) =>
        let emitted := (encoded.bytes.val.take encoded.len.val).map specByte
        Spec.bounded 64 emitted d.value.val ∧ Spec.canonical emitted ∧
        (∀ bs, Spec.represents bs d.value.val → emitted.length ≤ bs.length) ∧
        (d.canonical = true → emitted = (input.val.take d.consumed.val).map specByte) ⦄ := by
  apply WP.spec_bind (decode_u64_sound input policy)
  intro decoded hd
  cases decoded with
  | Err e => simp
  | Ok d =>
    apply WP.spec_bind (WP.spec_and (encode_u64_contract d.value) (encode_u64_refines d.value))
    intro encoded he
    have hp := he.1
    have hb := he.2
    dsimp at hp hd
    have hminimal : ∀ bs, Spec.represents bs d.value.val →
        ((encoded.bytes.val.take encoded.len.val).map specByte).length ≤ bs.length := by
      intro bs hs
      rw [← hp.1]
      exact hp.2.2.2.2.2.1 bs hs
    have hsame : d.canonical = true →
        (encoded.bytes.val.take encoded.len.val).map specByte = (input.val.take d.consumed.val).map specByte := by
      intro hc
      have hs := Spec.canonical_eq_encode _ hd.1.1.1 (hd.2.1.mp hc)
      rw [hd.1.1.2] at hs
      rw [hb.2.2.2, hs]
    simpa using And.intro hp.2.2.2.1 (And.intro hp.2.2.2.2.1 (And.intro hminimal hsame))

theorem decode_u64_consumption_bounded (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy ⦃ result =>
      Reference.consumed (referenceOutcome result) ≤ 10 ∧
      Reference.consumed (referenceOutcome result) ≤ input.length ⦄ := by
  apply WP.spec_mono (decode_u64_refines input policy)
  intro result h
  rw [h]
  simpa [Spec.maxBytes, Slice.length] using
    Reference.decode_consumption_bounds 64 (referencePolicy policy) (input.val.map specByte)

end VerifiedVarint.Refinement
