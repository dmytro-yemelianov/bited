import VerifiedVarint.Refinement.StreamInvariant
import VerifiedVarint.Refinement.Decode32
import VerifiedVarint.Proofs.StreamEquivalence

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

def stepView32 : Generated.stream.Step U32 → Reference.Step
  | .NeedMore => .needMore
  | .Closed => .closed
  | .Error e => .error ⟨referenceError e.kind, e.consumed.val⟩
  | .Done d => .done ⟨d.value.val, d.consumed.val, d.canonical⟩

theorem state_live (width : Nat) (state : Generated.stream.State)
    (hi : streamInvariant width (stateView state)) (ht : state.terminal = none) :
    state.count.val < Spec.maxBytes width ∧ state.acc.val < 2 ^ (7 * state.count.val) := by
  exact hi.2.1 (by simp [stateView, ht])

theorem stream_u64_push_refines (decoder : Generated.stream.DecoderU64) (byte : U8)
    (hi : streamInvariant 64 (stateView decoder.state)) :
    Generated.stream.DecoderU64.push decoder byte ⦃ result =>
      (stepView64 result.1, stateView result.2.state) = Reference.push 64 (stateView decoder.state) (specByte byte) ∧
      streamInvariant 64 (stateView result.2.state) ⦄ := by
  unfold Generated.stream.DecoderU64.push
  apply WP.spec_bind (stream_state_push64_refines decoder.state byte (by
    intro ht
    simpa [Spec.maxBytes] using state_live 64 decoder.state hi ht))
  rintro ⟨s, state⟩ h
  have hi' : streamInvariant 64 (stateView state) := by
    have he := congrArg Prod.snd h
    dsimp only at he
    rw [he]
    exact stream_push_invariant 64 (Or.inr rfl) _ _ hi
  simpa using And.intro h hi'

set_option maxHeartbeats 2000000 in
theorem stream_u32_push_refines (decoder : Generated.stream.DecoderU32) (byte : U8)
    (hi : streamInvariant 32 (stateView decoder.state)) :
    Generated.stream.DecoderU32.push decoder byte ⦃ result =>
      (stepView32 result.1, stateView result.2.state) = Reference.push 32 (stateView decoder.state) (specByte byte) ∧
      streamInvariant 32 (stateView result.2.state) ⦄ := by
  unfold Generated.stream.DecoderU32.push
  apply WP.spec_bind (stream_state_push32_refines decoder.state byte (by
    intro ht
    simpa [Spec.maxBytes] using state_live 32 decoder.state hi ht))
  rintro ⟨s, state⟩ h
  have hi' : streamInvariant 32 (stateView state) := by
    have he := congrArg Prod.snd h.1
    dsimp only at he
    rw [he]
    exact stream_push_invariant 32 (Or.inl rfl) _ _ hi
  cases s with
  | NeedMore => simpa [stepView32, stepView64] using And.intro h.1 hi'
  | Closed => simpa [stepView32, stepView64] using And.intro h.1 hi'
  | Error e => simpa [stepView32, stepView64] using And.intro h.1 hi'
  | Done d =>
    step*
    have hv : i.val = d.value.val := by
      rw [i_post, UScalar.cast_val_eq]
      change d.value.val % (2^32) = d.value.val
      exact Nat.mod_eq_of_lt h.2
    simpa [stepView32, stepView64, hv] using And.intro h.1 hi'

set_option maxHeartbeats 2000000 in
theorem stream_u32_finish_refines (decoder : Generated.stream.DecoderU32)
    (hi : streamInvariant 32 (stateView decoder.state)) :
    Generated.stream.DecoderU32.finish decoder ⦃ result =>
      (referenceOutcome32 result.1, stateView result.2.state) = Reference.finish (stateView decoder.state) ∧
      streamInvariant 32 (stateView result.2.state) ⦄ := by
  unfold Generated.stream.DecoderU32.finish
  apply WP.spec_bind (stream_state_finish_refines decoder.state)
  rintro ⟨r, state⟩ h
  have hi' : streamInvariant 32 (stateView state) := by
    have he := congrArg Prod.snd h
    dsimp only at he
    rw [he]
    exact stream_finish_invariant 32 _ hi
  cases r with
  | Err e => simpa [referenceOutcome32, referenceOutcome] using And.intro h hi'
  | Ok d =>
    have hd : d.value.val < 2^32 := by
      apply hi'.2.2 ⟨d.value.val, d.consumed.val, d.canonical⟩
      have hf : (Reference.finish (stateView decoder.state)).2.terminal =
          some (Reference.finish (stateView decoder.state)).1 := by
        cases ht : (stateView decoder.state).terminal <;> simp [Reference.finish, ht]
      rw [← h] at hf
      exact hf
    step*
    have hv : i.val = d.value.val := by
      rw [i_post, UScalar.cast_val_eq]
      change d.value.val % (2^32) = d.value.val
      exact Nat.mod_eq_of_lt hd
    simpa [referenceOutcome32, referenceOutcome, hv] using And.intro h hi'

end VerifiedVarint.Refinement
