import Bited.Refinement.StreamTransition
import Bited.Refinement.StreamBase

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

def pushFlow (state : Reference.State) (flow : ControlFlow (Nat × Nat) Reference.Outcome) :
    Reference.Step × Reference.State :=
  match flow with
  | .cont (next, count) => (.needMore, { state with acc := next, count })
  | .done (.error e) => (.error e, { state with count := state.count + 1, terminal := some (.error e) })
  | .done (.ok d) => (.done d, { state with acc := d.value, count := state.count + 1, terminal := some (.ok d) })

theorem reference_push_flow (width : Nat) (state : Reference.State) (byte : Spec.Byte)
    (h : state.terminal = none) :
    Reference.push width state byte =
      pushFlow state (advanceFlow (state.count + 1) (Reference.advance width state.policy state.count state.acc byte)) := by
  rw [Reference.push, h]
  cases ha : Reference.advance width state.policy state.count state.acc byte with
  | error e => simp [pushFlow, advanceFlow, h]
  | ok triple =>
    rcases triple with ⟨next, isDone, canonical⟩
    cases isDone <;> simp [pushFlow, advanceFlow, h]

set_option maxHeartbeats 2000000 in
theorem stream_state_push32_refines (state : Generated.stream.State) (byte : U8)
    (hlive : state.terminal = none → state.count.val < 5 ∧ state.acc.val < 2 ^ (7 * state.count.val)) :
    Generated.stream.State.push state byte 5#usize 15#u8 ⦃ result =>
      (stepView64 result.1, stateView result.2) = Reference.push 32 (stateView state) (specByte byte) ∧
      (match result.1 with | .Done d => d.value.val < 2^32 | _ => True) ⦄ := by
  cases ht : state.terminal with
  | some terminal =>
    rw [stream_state_push_closed state byte _ _ terminal ht]
    simp [stepView64, stateView, Reference.push, ht]
  | none =>
    have hc := (hlive ht).1
    have ha := (hlive ht).2
    unfold Generated.stream.State.push
    simp only [core.option.Option.is_some, ht, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (transition_u32_contract state.acc state.count byte state.policy hc ha)
    intro result hr
    have href : Reference.push 32 (stateView state) (specByte byte) =
        pushFlow (stateView state) (byteStep (referencePolicy state.policy) 5 15 state.count.val state.acc.val byte.val) := by
      rw [reference_push_flow _ _ _ (by simp [stateView, ht]), advance_flow32]
      rfl
    rw [href, ← hr.1]
    cases result with
    | Err e =>
      step*
      simp only [stepView64, stateView, referenceOutcome, transitionFlow, pushFlow, i_post, ht, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.map_none]
    | Ok triple =>
      rcases triple with ⟨next, isDone, canonical⟩
      cases isDone <;> step* <;>
        simp only [stepView64, stateView, referenceOutcome, transitionFlow, pushFlow, i_post, ht, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.map_none]
      all_goals try rfl
      all_goals exact ⟨True.intro, hr.2.2.2⟩

set_option maxHeartbeats 2000000 in
theorem stream_state_push64_refines (state : Generated.stream.State) (byte : U8)
    (hlive : state.terminal = none → state.count.val < 10 ∧ state.acc.val < 2 ^ (7 * state.count.val)) :
    Generated.stream.State.push state byte 10#usize 1#u8 ⦃ result =>
      (stepView64 result.1, stateView result.2) = Reference.push 64 (stateView state) (specByte byte) ⦄ := by
  cases ht : state.terminal with
  | some terminal =>
    rw [stream_state_push_closed state byte _ _ terminal ht]
    simp [stepView64, stateView, Reference.push, ht]
  | none =>
    have hc := (hlive ht).1
    have ha := (hlive ht).2
    unfold Generated.stream.State.push
    simp only [core.option.Option.is_some, ht, Bool.false_eq_true, ↓reduceIte]
    apply WP.spec_bind (transition_u64_contract state.acc state.count byte state.policy hc ha)
    intro result hr
    have href : Reference.push 64 (stateView state) (specByte byte) =
        pushFlow (stateView state) (byteStep (referencePolicy state.policy) 10 1 state.count.val state.acc.val byte.val) := by
      rw [reference_push_flow _ _ _ (by simp [stateView, ht]), advance_flow64]
      rfl
    rw [href, ← hr.1]
    cases result with
    | Err e =>
      step*
      simp only [stepView64, stateView, referenceOutcome, transitionFlow, pushFlow, i_post, ht, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.map_none]
    | Ok triple =>
      rcases triple with ⟨next, isDone, canonical⟩
      cases isDone <;> step* <;>
        simp only [stepView64, stateView, referenceOutcome, transitionFlow, pushFlow, i_post, ht, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, Option.map_some, Option.map_none]

end Bited.Refinement
