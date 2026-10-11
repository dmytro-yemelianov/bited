import VerifiedVarint.Refinement.DecodeValue
import Mathlib.Data.Nat.Bitwise

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

theorem decode_continuation_mask (byte : U8) :
    (byte &&& 128#u8).val = if byte.val < 128 then 0 else 128 := by
  rw [UScalar.val_and]
  change byte.val &&& 2 ^ 7 = _
  rw [Nat.and_two_pow]
  by_cases h : byte.val < 128
  · have ht : byte.val.testBit 7 = false := Nat.testBit_lt_two_pow h
    simp [h, ht]
  · have ht : byte.val.testBit 7 = true :=
      Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) byte.bv.isLt
    simp [h, ht]

theorem scalar_bne_val {ty} (x y : UScalar ty) : (x != y) = (x.val != y.val) := by
  apply Bool.eq_iff_iff.mpr
  simp

def referencePolicy : Generated.decode.DecodePolicy → Reference.Policy
  | .Canonical => .canonical
  | .BoundedNonCanonical => .boundedNoncanonical

def referenceError : Generated.decode.DecodeErrorKind → Reference.DecodeErrorKind
  | .Truncated => .truncated
  | .Overflow => .overflow
  | .TooLong => .tooLong
  | .NonCanonical => .nonCanonical
  | .TrailingBytes => .trailingBytes

inductive DecodeDecision where
  | next (count : Nat)
  | accepted (count : Nat) (canonical : Bool)
  | rejected (error : Reference.DecodeError)
  deriving DecidableEq

def decodeDecision : ControlFlow (U64 × Usize)
    (core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError) → DecodeDecision
  | .cont (_, j) => .next j.val
  | .done (.Ok d) => .accepted d.consumed.val d.canonical
  | .done (.Err e) => .rejected ⟨referenceError e.kind, e.consumed.val⟩

/-- Value-independent byte decision using natural arithmetic and an explicit policy. -/
def referenceDecision (policy : Reference.Policy) (count available byte : Nat) : DecodeDecision :=
  if count < 10 then
    if count = available then .rejected ⟨.truncated, count⟩
    else if count = 9 ∧ byte % 128 > 1 then .rejected ⟨.overflow, count + 1⟩
    else if count = 9 ∧ 128 ≤ byte then .rejected ⟨.tooLong, count + 1⟩
    else if 128 ≤ byte then .next (count + 1)
    else
      let canonical := count = 0 || byte % 128 != 0
      if policy = .canonical ∧ !canonical then .rejected ⟨.nonCanonical, count + 1⟩
      else .accepted (count + 1) canonical
  else .rejected ⟨.tooLong, count⟩

set_option maxHeartbeats 2000000 in
/-- Every decision of the actual extracted byte transition, including exact
    failures, consumption, precedence and the canonical flag. -/
theorem decode_u64_body_decision (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (acc : U64) (i : Usize) (hi : i.val ≤ 10) (hlen : i.val ≤ input.length) :
    Generated.decode.decode_u64_loop.body input policy acc i ⦃ r =>
      decodeDecision r = referenceDecision (referencePolicy policy) i.val input.length
        input.val[i.val]!.val ⦄ := by
  unfold Generated.decode.decode_u64_loop.body
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals try
    have hstrict : i.val < input.length := by
      have hnot : i ≠ input.len := by assumption
      have hne := UScalar.neq_to_neq_val.mp hnot
      simp only [Slice.len_val] at hne
      omega
    have hbyte : byte = input.val[i.val]! := by
      rw [byte_post, getElem!_pos input.val i.val (by simpa only [Slice.length] using hstrict)]
    have hp : p.val = input.val[i.val]!.val % 128 := by
      rw [p_post, decode_payload_value, hbyte]
    have hc : i2.val = if input.val[i.val]!.val < 128 then 0 else 128 := by
      rw [i2_post, decode_continuation_mask, hbyte]
    by_cases hb : input.val[i.val]!.val < 128
    all_goals try simp_all [decodeDecision, referenceDecision, referencePolicy, referenceError]
    all_goals by_cases hz : i = 0#usize
    all_goals try simp_all
    all_goals step*
    all_goals try simp_all [decodeDecision, referenceDecision, referencePolicy, referenceError]
  all_goals try subst i
  all_goals try simp_all [decodeDecision, referenceDecision, referencePolicy, referenceError,
    Generated.decode.DecodePolicy.read_discriminant, Slice.length,
    show (1#isize : Isize) ≠ 0#isize by decide]
  all_goals try simp only [Slice.length, Generated.decode.DecodePolicy.read_discriminant,
    scalar_bne_val] at *
  all_goals repeat' (split <;> try omega <;> try simp_all)
  all_goals try simp_all
  all_goals simp_all [decodeDecision, referenceDecision, referencePolicy, referenceError,
    UScalar.lt_equiv]
  all_goals have hstrict' : i.val < input.val.length := hstrict
  all_goals omega

end VerifiedVarint.Refinement
