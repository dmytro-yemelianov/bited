import Bited.Refinement.DecodeCorrespondence
import Bited.Reference.Stream

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

def stateView (state : Generated.stream.State) : Reference.State :=
  ⟨referencePolicy state.policy, state.acc.val, state.count.val, state.terminal.map referenceOutcome⟩

def stepView64 : Generated.stream.Step U64 → Reference.Step
  | .NeedMore => .needMore
  | .Closed => .closed
  | .Error e => .error ⟨referenceError e.kind, e.consumed.val⟩
  | .Done d => .done ⟨d.value.val, d.consumed.val, d.canonical⟩

theorem stream_state_new_refines (policy : Generated.decode.DecodePolicy) :
    Generated.stream.State.new policy ⦃ state => stateView state = Reference.initial (referencePolicy policy) ⦄ := by
  simp [Generated.stream.State.new, stateView, Reference.initial]

theorem stream_state_finish_refines (state : Generated.stream.State) :
    Generated.stream.State.finish state ⦃ result =>
      (referenceOutcome result.1, stateView result.2) = Reference.finish (stateView state) ⦄ := by
  cases h : state.terminal <;>
    simp [Generated.stream.State.finish, Reference.finish, stateView, referenceOutcome, referenceError, h]

theorem stream_state_push_closed (state : Generated.stream.State) (byte : U8)
    (limit : Usize) (lastMax : U8)
    (terminal : core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError)
    (h : state.terminal = some terminal) :
    Generated.stream.State.push state byte limit lastMax = .ok (.Closed, state) := by
  simp [Generated.stream.State.push, core.option.Option.is_some, h]

theorem stream_state_finish_idempotent (state : Generated.stream.State) :
    (do
      let first ← Generated.stream.State.finish state
      let second ← Generated.stream.State.finish first.2
      ok (first, second)) ⦃ result => result.2 = result.1 ⦄ := by
  cases h : state.terminal <;> simp [Generated.stream.State.finish, h]

theorem stream_u64_new_refines (policy : Generated.decode.DecodePolicy) :
    Generated.stream.DecoderU64.new policy ⦃ decoder =>
      stateView decoder.state = Reference.initial (referencePolicy policy) ⦄ := by
  simp [Generated.stream.DecoderU64.new, Generated.stream.State.new, stateView, Reference.initial]

theorem stream_u32_new_refines (policy : Generated.decode.DecodePolicy) :
    Generated.stream.DecoderU32.new policy ⦃ decoder =>
      stateView decoder.state = Reference.initial (referencePolicy policy) ⦄ := by
  simp [Generated.stream.DecoderU32.new, Generated.stream.State.new, stateView, Reference.initial]

theorem stream_u64_reset_refines (decoder : Generated.stream.DecoderU64)
    (policy : Generated.decode.DecodePolicy) :
    Generated.stream.DecoderU64.reset decoder policy ⦃ result =>
      stateView result.state = Reference.initial (referencePolicy policy) ⦄ := by
  simp [Generated.stream.DecoderU64.reset, Generated.stream.State.new, stateView, Reference.initial]

theorem stream_u32_reset_refines (decoder : Generated.stream.DecoderU32)
    (policy : Generated.decode.DecodePolicy) :
    Generated.stream.DecoderU32.reset decoder policy ⦃ result =>
      stateView result.state = Reference.initial (referencePolicy policy) ⦄ := by
  simp [Generated.stream.DecoderU32.reset, Generated.stream.State.new, stateView, Reference.initial]

theorem stream_u64_bytes_seen_refines (decoder : Generated.stream.DecoderU64) :
    Generated.stream.DecoderU64.bytes_seen decoder ⦃ count => count.val = (stateView decoder.state).count ⦄ := by
  simp [Generated.stream.DecoderU64.bytes_seen, Generated.stream.DecoderU32.bytes_seen, stateView]

theorem stream_u32_bytes_seen_refines (decoder : Generated.stream.DecoderU32) :
    Generated.stream.DecoderU32.bytes_seen decoder ⦃ count => count.val = (stateView decoder.state).count ⦄ := by
  simp [Generated.stream.DecoderU64.bytes_seen, Generated.stream.DecoderU32.bytes_seen, stateView]

theorem stream_u64_finish_refines (decoder : Generated.stream.DecoderU64) :
    Generated.stream.DecoderU64.finish decoder ⦃ result =>
      (referenceOutcome result.1, stateView result.2.state) = Reference.finish (stateView decoder.state) ⦄ := by
  unfold Generated.stream.DecoderU64.finish
  apply WP.spec_bind (stream_state_finish_refines decoder.state)
  rintro ⟨result, state⟩ h
  simpa using h

end Bited.Refinement
