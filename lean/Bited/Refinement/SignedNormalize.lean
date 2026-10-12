import Bited.Refinement.DecodeClosure
import Bited.Proofs.Length

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

set_option maxHeartbeats 2000000 in
theorem decode_i32_normalize (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    (do
      let decoded ← Generated.api.decode_i32 input policy
      match decoded with
      | .Err e => ok (.Err e : core.result.Result (Generated.decode.Decoded I32 × Generated.encode.Encoded32) Generated.decode.DecodeError)
      | .Ok d => do
        let encoded ← Generated.api.encode_i32 d.value
        ok (.Ok (d, encoded))) ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (d, encoded) =>
        let emitted := (encoded.bytes.val.take encoded.len.val).map specByte
        Spec.bounded 32 emitted (Spec.zigzag d.value.val) ∧ Spec.canonical emitted ∧
        (∀ bs, Spec.represents bs (Spec.zigzag d.value.val) → emitted.length ≤ bs.length) ∧
        (d.canonical = true → emitted = (input.val.take d.consumed.val).map specByte) ⦄ := by
  apply WP.spec_bind (decode_i32_refines input policy)
  intro decoded hd
  cases decoded with
  | Err e => simp
  | Ok d =>
    cases href : Reference.decode 32 (referencePolicy policy) (input.val.map specByte) with
    | error e => simp [signedOutcome32, signedReference, href] at hd
    | ok natural =>
      simp only [href, signedReference, signedOutcome32, Except.ok.injEq] at hd
      have hv := congrArg SignedDecoded.value hd
      have hc := congrArg SignedDecoded.consumed hd
      have hflag := congrArg SignedDecoded.canonical hd
      dsimp only at hv hc hflag
      have hzz : Spec.zigzag d.value.val = natural.value := by
        rw [hv, Spec.zigzag_right_inverse]
      obtain ⟨emitted, rest, hbs, hr, hlen, hcons, hcan, hp⟩ :=
        Reference.decode_success_shape 32 _ _ natural href
      have hprefix : (input.val.take d.consumed.val).map specByte = emitted := by
        rw [List.map_take, hbs, hc, hcons, List.take_append_of_le_length (by rfl), List.take_length]
      apply WP.spec_bind (encode_i32_refines d.value)
      intro encoded he
      have hbytes := he.2.2.2
      have hdomain := (Spec.zigzag_bounds 32 (by decide)).1 d.value.val (by
        unfold Spec.signedDomain
        scalar_tac)
      have hbounded : Spec.bounded 32 (Reference.encode (Spec.zigzag d.value.val)) (Spec.zigzag d.value.val) :=
        Spec.encode_bounded 32 (by decide) _ hdomain
      have hminimal : ∀ bs, Spec.represents bs (Spec.zigzag d.value.val) →
          ((encoded.bytes.val.take encoded.len.val).map specByte).length ≤ bs.length := by
        intro bs hb
        rw [hbytes]
        exact Spec.encode_length_minimal _ bs hb
      have hsame : d.canonical = true →
          (encoded.bytes.val.take encoded.len.val).map specByte = (input.val.take d.consumed.val).map specByte := by
        intro htrue
        rw [hbytes, hprefix, hzz]
        symm
        have heq := Spec.canonical_eq_encode emitted hr.1 (hcan.mp (by rw [← hflag]; exact htrue))
        rw [hr.2] at heq
        exact heq
      have hb : Spec.bounded 32 ((encoded.bytes.val.take encoded.len.val).map specByte) (Spec.zigzag d.value.val) := by
        rw [hbytes]
        exact hbounded
      have hcanonical : Spec.canonical ((encoded.bytes.val.take encoded.len.val).map specByte) := by
        rw [hbytes]
        exact Spec.encode_canonical _
      simpa using And.intro hb (And.intro hcanonical (And.intro hminimal hsame))

theorem encoded_len_i32_formula (value : I32) :
    Generated.api.encoded_len_i32 value ⦃ len => len.val = Spec.encodedLength (Spec.zigzag value.val) ⦄ := by
  apply WP.spec_mono (encoded_len_i32_refines value)
  intro len h
  rw [h.1, Spec.encode_length_formula]

set_option maxHeartbeats 2000000 in
theorem decode_i64_normalize (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    (do
      let decoded ← Generated.api.decode_i64 input policy
      match decoded with
      | .Err e => ok (.Err e : core.result.Result (Generated.decode.Decoded I64 × Generated.encode.Encoded64) Generated.decode.DecodeError)
      | .Ok d => do
        let encoded ← Generated.api.encode_i64 d.value
        ok (.Ok (d, encoded))) ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (d, encoded) =>
        let emitted := (encoded.bytes.val.take encoded.len.val).map specByte
        Spec.bounded 64 emitted (Spec.zigzag d.value.val) ∧ Spec.canonical emitted ∧
        (∀ bs, Spec.represents bs (Spec.zigzag d.value.val) → emitted.length ≤ bs.length) ∧
        (d.canonical = true → emitted = (input.val.take d.consumed.val).map specByte) ⦄ := by
  apply WP.spec_bind (decode_i64_refines input policy)
  intro decoded hd
  cases decoded with
  | Err e => simp
  | Ok d =>
    cases href : Reference.decode 64 (referencePolicy policy) (input.val.map specByte) with
    | error e => simp [signedOutcome64, signedReference, href] at hd
    | ok natural =>
      simp only [href, signedReference, signedOutcome64, Except.ok.injEq] at hd
      have hv := congrArg SignedDecoded.value hd
      have hc := congrArg SignedDecoded.consumed hd
      have hflag := congrArg SignedDecoded.canonical hd
      dsimp only at hv hc hflag
      have hzz : Spec.zigzag d.value.val = natural.value := by
        rw [hv, Spec.zigzag_right_inverse]
      obtain ⟨emitted, rest, hbs, hr, hlen, hcons, hcan, hp⟩ :=
        Reference.decode_success_shape 64 _ _ natural href
      have hprefix : (input.val.take d.consumed.val).map specByte = emitted := by
        rw [List.map_take, hbs, hc, hcons, List.take_append_of_le_length (by rfl), List.take_length]
      apply WP.spec_bind (encode_i64_refines d.value)
      intro encoded he
      have hbytes := he.2.2.2
      have hdomain := (Spec.zigzag_bounds 64 (by decide)).1 d.value.val (by
        unfold Spec.signedDomain
        scalar_tac)
      have hbounded : Spec.bounded 64 (Reference.encode (Spec.zigzag d.value.val)) (Spec.zigzag d.value.val) :=
        Spec.encode_bounded 64 (by decide) _ hdomain
      have hminimal : ∀ bs, Spec.represents bs (Spec.zigzag d.value.val) →
          ((encoded.bytes.val.take encoded.len.val).map specByte).length ≤ bs.length := by
        intro bs hb
        rw [hbytes]
        exact Spec.encode_length_minimal _ bs hb
      have hsame : d.canonical = true →
          (encoded.bytes.val.take encoded.len.val).map specByte = (input.val.take d.consumed.val).map specByte := by
        intro htrue
        rw [hbytes, hprefix, hzz]
        symm
        have heq := Spec.canonical_eq_encode emitted hr.1 (hcan.mp (by rw [← hflag]; exact htrue))
        rw [hr.2] at heq
        exact heq
      have hb : Spec.bounded 64 ((encoded.bytes.val.take encoded.len.val).map specByte) (Spec.zigzag d.value.val) := by
        rw [hbytes]
        exact hbounded
      have hcanonical : Spec.canonical ((encoded.bytes.val.take encoded.len.val).map specByte) := by
        rw [hbytes]
        exact Spec.encode_canonical _
      simpa using And.intro hb (And.intro hcanonical (And.intro hminimal hsame))

theorem encoded_len_i64_formula (value : I64) :
    Generated.api.encoded_len_i64 value ⦃ len => len.val = Spec.encodedLength (Spec.zigzag value.val) ⦄ := by
  apply WP.spec_mono (encoded_len_i64_refines value)
  intro len h
  rw [h.1, Spec.encode_length_formula]

end Bited.Refinement
