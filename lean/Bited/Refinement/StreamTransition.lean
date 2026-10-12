import Bited.Refinement.TransitionContract
import Bited.Reference.Stream

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.ControlFlow

def advanceFlow (count : Nat) (result : Except Reference.DecodeError (Nat × Bool × Bool)) :
    ControlFlow (Nat × Nat) Reference.Outcome :=
  match result with
  | .error e => .done (.error e)
  | .ok (next, isDone, canonical) => if isDone then .done (.ok ⟨next, count, canonical⟩)
      else .cont (next, count)

set_option maxHeartbeats 2000000 in
theorem advance_flow32 (policy : Reference.Policy) (count acc : Nat) (byte : Spec.Byte) :
    advanceFlow (count + 1) (Reference.advance 32 policy count acc byte) =
      byteStep policy 5 15 count acc byte.val := by
  cases policy <;>
    simp [Reference.advance, Spec.maxBytes, Spec.payload, Spec.continues, advanceFlow, byteStep, byteDecision]
  all_goals split_ifs <;> simp_all <;> omega

set_option maxHeartbeats 2000000 in
theorem advance_flow64 (policy : Reference.Policy) (count acc : Nat) (byte : Spec.Byte) :
    advanceFlow (count + 1) (Reference.advance 64 policy count acc byte) =
      byteStep policy 10 1 count acc byte.val := by
  cases policy <;>
    simp [Reference.advance, Spec.maxBytes, Spec.payload, Spec.continues, advanceFlow, byteStep, byteDecision]
  all_goals split_ifs <;> simp_all <;> omega

end Bited.Refinement
