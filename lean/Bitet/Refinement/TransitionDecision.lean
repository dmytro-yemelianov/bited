import Bitet.Refinement.DecodeDecision

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

def transitionDecision (count : Nat)
    (result : core.result.Result (U64 × Bool × Bool) Generated.decode.DecodeError) : DecodeDecision :=
  match result with
  | .Err e => .rejected ⟨referenceError e.kind, e.consumed.val⟩
  | .Ok (_, done, canonical) => if done then .accepted count canonical else .next count

def byteDecision (policy : Reference.Policy) (limit lastMax count byte : Nat) : DecodeDecision :=
  if count = limit - 1 ∧ byte % 128 > lastMax then .rejected ⟨.overflow, count + 1⟩
  else if count = limit - 1 ∧ 128 ≤ byte then .rejected ⟨.tooLong, count + 1⟩
  else if 128 ≤ byte then .next (count + 1)
  else
    let canonical := count = 0 || byte % 128 != 0
    if policy = .canonical ∧ !canonical then .rejected ⟨.nonCanonical, count + 1⟩
    else .accepted (count + 1) canonical

set_option maxHeartbeats 2000000 in
theorem transition_u32_decision (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 5) :
    Generated.decode.transition acc count byte policy 5#usize 15#u8 ⦃ result =>
      transitionDecision (count.val + 1) result =
        byteDecision (referencePolicy policy) 5 15 count.val byte.val ⦄ := by
  unfold Generated.decode.transition
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals
    have hp : payload.val = byte.val % 128 := by rw [payload_post, decode_payload_value]
    have hm : i.val = if byte.val < 128 then 0 else 128 := by
      rw [i_post, decode_continuation_mask]
  all_goals by_cases hb : byte.val < 128
  all_goals try simp_all [transitionDecision, byteDecision, referencePolicy, referenceError]
  all_goals by_cases hz : count = 0#usize
  all_goals try simp_all
  all_goals step*
  all_goals try subst count
  all_goals try simp_all [transitionDecision, byteDecision, referencePolicy, referenceError,
    Generated.decode.DecodePolicy.read_discriminant, show (1#isize : Isize) ≠ 0#isize by scalar_tac]
  all_goals try simp only [scalar_bne_val] at *
  all_goals repeat' (split <;> try omega <;> try simp_all)
  all_goals try simp_all [transitionDecision, byteDecision, referencePolicy, referenceError, UScalar.lt_equiv]
  all_goals simp_all [Generated.decode.DecodePolicy.read_discriminant, show (1#isize : Isize) ≠ 0#isize by scalar_tac]

set_option maxHeartbeats 2000000 in
theorem transition_u64_decision (acc : U64) (count : Usize) (byte : U8)
    (policy : Generated.decode.DecodePolicy) (hc : count.val < 10) :
    Generated.decode.transition acc count byte policy 10#usize 1#u8 ⦃ result =>
      transitionDecision (count.val + 1) result =
        byteDecision (referencePolicy policy) 10 1 count.val byte.val ⦄ := by
  unfold Generated.decode.transition
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals
    have hp : payload.val = byte.val % 128 := by rw [payload_post, decode_payload_value]
    have hm : i.val = if byte.val < 128 then 0 else 128 := by
      rw [i_post, decode_continuation_mask]
  all_goals by_cases hb : byte.val < 128
  all_goals try simp_all [transitionDecision, byteDecision, referencePolicy, referenceError]
  all_goals by_cases hz : count = 0#usize
  all_goals try simp_all
  all_goals step*
  all_goals try subst count
  all_goals try simp_all [transitionDecision, byteDecision, referencePolicy, referenceError,
    Generated.decode.DecodePolicy.read_discriminant, show (1#isize : Isize) ≠ 0#isize by scalar_tac]
  all_goals try simp only [scalar_bne_val] at *
  all_goals repeat' (split <;> try omega <;> try simp_all)
  all_goals try simp_all [transitionDecision, byteDecision, referencePolicy, referenceError, UScalar.lt_equiv]
  all_goals simp_all [Generated.decode.DecodePolicy.read_discriminant, show (1#isize : Isize) ≠ 0#isize by scalar_tac]

end Bitet.Refinement
