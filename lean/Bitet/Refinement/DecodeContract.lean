import Bitet.Refinement.DecodeCorrespondence
import Bitet.Proofs.Decode
import Bitet.Refinement.Decode32

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

theorem decode_u64_sound (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok d =>
        let emitted := (input.val.take d.consumed.val).map specByte
        Spec.bounded 64 emitted d.value.val ∧
        (d.canonical = true ↔ Spec.canonical emitted) ∧
        (policy = .Canonical → Spec.canonical emitted) ∧
        d.consumed.val ≤ input.length ⦄ := by
  apply WP.spec_mono (decode_u64_refines input policy)
  intro result h
  cases result with
  | Err e => trivial
  | Ok d =>
    have href : Reference.decode 64 (referencePolicy policy) (input.val.map specByte) =
        .ok ⟨d.value.val, d.consumed.val, d.canonical⟩ := h.symm
    obtain ⟨emitted, rest, hbs, hr, hlen, hcons, hflag, hpolicy⟩ :=
      Reference.decode_success_shape 64 (referencePolicy policy) (input.val.map specByte) _ href
    dsimp at hr hcons hflag
    have hp : (input.val.take d.consumed.val).map specByte = emitted := by
      rw [List.map_take, hbs, hcons, List.take_append_of_le_length (by rfl), List.take_length]
    dsimp
    rw [hp]
    refine ⟨⟨hr, hlen, d.value.bv.isLt⟩, hflag, ?_, ?_⟩
    · intro hc
      apply hpolicy
      cases policy <;> simp_all [referencePolicy]
    · have hl := congrArg List.length hbs
      simp only [List.length_map, List.length_append] at hl
      change d.consumed.val ≤ input.val.length
      omega

theorem decode_u32_sound (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u32 input policy ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok d =>
        let emitted := (input.val.take d.consumed.val).map specByte
        Spec.bounded 32 emitted d.value.val ∧
        (d.canonical = true ↔ Spec.canonical emitted) ∧
        (policy = .Canonical → Spec.canonical emitted) ∧
        d.consumed.val ≤ input.length ⦄ := by
  apply WP.spec_mono (decode_u32_refines input policy)
  intro result h
  cases result with
  | Err e => trivial
  | Ok d =>
    have href : Reference.decode 32 (referencePolicy policy) (input.val.map specByte) =
        .ok ⟨d.value.val, d.consumed.val, d.canonical⟩ := h.symm
    obtain ⟨emitted, rest, hbs, hr, hlen, hcons, hflag, hpolicy⟩ :=
      Reference.decode_success_shape 32 (referencePolicy policy) (input.val.map specByte) _ href
    dsimp at hr hcons hflag
    have hp : (input.val.take d.consumed.val).map specByte = emitted := by
      rw [List.map_take, hbs, hcons, List.take_append_of_le_length (by rfl), List.take_length]
    dsimp
    rw [hp]
    refine ⟨⟨hr, hlen, d.value.bv.isLt⟩, hflag, ?_, ?_⟩
    · intro hc
      apply hpolicy
      cases policy <;> simp_all [referencePolicy]
    · have hl := congrArg List.length hbs
      simp only [List.length_map, List.length_append] at hl
      change d.consumed.val ≤ input.val.length
      omega

end Bitet.Refinement
