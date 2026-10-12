import Bitet.Refinement.Transition
import Bitet.Refinement.TransitionDecision

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

def byteStep (policy : Reference.Policy) (limit lastMax count acc byte : Nat) :
    ControlFlow (Nat × Nat) Reference.Outcome :=
  let next := acc + byte % 128 * 2 ^ (7 * count)
  match byteDecision policy limit lastMax count byte with
  | .next j => .cont (next, j)
  | .accepted j canonical => .done (.ok ⟨next, j, canonical⟩)
  | .rejected e => .done (.error e)

def transitionFlow (count : Nat)
    (result : core.result.Result (U64 × Bool × Bool) Generated.decode.DecodeError) :
    ControlFlow (Nat × Nat) Reference.Outcome :=
  match result with
  | .Err e => .done (.error ⟨referenceError e.kind, e.consumed.val⟩)
  | .Ok (next, isDone, canonical) => if isDone then .done (.ok ⟨next.val, count, canonical⟩)
      else .cont (next.val, count)

theorem transition_u32_refines (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 5)
    (ha : acc.val < 2 ^ (7 * count.val)) :
    Generated.decode.transition acc count byte policy 5#usize 15#u8 ⦃ result =>
      transitionFlow (count.val + 1) result = byteStep (referencePolicy policy) 5 15 count.val acc.val byte.val ⦄ := by
  apply WP.spec_mono (WP.spec_and (transition_u32_decision acc count byte policy hc)
    (transition_u32_value acc count byte policy hc ha))
  intro result h
  unfold byteStep
  rw [← h.1]
  cases result with
  | Err e => rfl
  | Ok triple =>
    rcases triple with ⟨next, isDone, canonical⟩
    cases isDone <;> dsimp [transitionDecision, transitionFlow] at h ⊢ <;> rw [h.2.1]

theorem transition_u64_refines (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 10)
    (ha : acc.val < 2 ^ (7 * count.val)) :
    Generated.decode.transition acc count byte policy 10#usize 1#u8 ⦃ result =>
      transitionFlow (count.val + 1) result = byteStep (referencePolicy policy) 10 1 count.val acc.val byte.val ⦄ := by
  apply WP.spec_mono (WP.spec_and (transition_u64_decision acc count byte policy hc)
    (transition_u64_value acc count byte policy hc ha))
  intro result h
  unfold byteStep
  rw [← h.1]
  cases result with
  | Err e => rfl
  | Ok triple =>
    rcases triple with ⟨next, isDone, canonical⟩
    cases isDone <;> dsimp [transitionDecision, transitionFlow] at h ⊢ <;> rw [h.2.1]

@[step]
theorem transition_u32_contract (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 5)
    (ha : acc.val < 2 ^ (7 * count.val)) :
    Generated.decode.transition acc count byte policy 5#usize 15#u8 ⦃ result =>
      transitionFlow (count.val + 1) result = byteStep (referencePolicy policy) 5 15 count.val acc.val byte.val ∧
      (match result with
      | .Err _ => True
      | .Ok (next, _, _) => next.val = acc.val + byte.val % 128 * 2 ^ (7 * count.val) ∧
        next.val < 2 ^ (7 * (count.val + 1)) ∧ next.val < 2^32) ⦄ :=
  WP.spec_and (transition_u32_refines acc count byte policy hc ha)
    (transition_u32_value acc count byte policy hc ha)

@[step]
theorem transition_u64_contract (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 10)
    (ha : acc.val < 2 ^ (7 * count.val)) :
    Generated.decode.transition acc count byte policy 10#usize 1#u8 ⦃ result =>
      transitionFlow (count.val + 1) result = byteStep (referencePolicy policy) 10 1 count.val acc.val byte.val ∧
      (match result with
      | .Err _ => True
      | .Ok (next, _, _) => next.val = acc.val + byte.val % 128 * 2 ^ (7 * count.val) ∧
        next.val < 2 ^ (7 * (count.val + 1)) ∧ next.val < 2^64) ⦄ :=
  WP.spec_and (transition_u64_refines acc count byte policy hc ha)
    (transition_u64_value acc count byte policy hc ha)

end Bitet.Refinement
