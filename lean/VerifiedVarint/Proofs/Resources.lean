import VerifiedVarint.Proofs.Length
import VerifiedVarint.Refinement.DecodeClosure
import VerifiedVarint.Refinement.StreamLifecycle

namespace VerifiedVarint.Reference
open Spec

/-- Ghost byte-read counter follows the decoder's fuel/list transition structure.
    It counts input-byte accesses, not slice-header loads or processor instructions. -/
def decodeTrace (lastMax : Nat) (policy : Policy) : Nat → Nat → Nat → List Spec.Byte → Outcome × Nat
  | 0, count, _, _ => (.error ⟨.tooLong, count⟩, 0)
  | _ + 1, count, _, [] => (.error ⟨.truncated, count⟩, 0)
  | remaining + 1, count, acc, b :: bs =>
      if remaining = 0 ∧ payload b > lastMax then (.error ⟨.overflow, count + 1⟩, 1)
      else if remaining = 0 ∧ continues b then (.error ⟨.tooLong, count + 1⟩, 1)
      else
        let next := acc + payload b * 2 ^ (7 * count)
        if continues b then
          let result := decodeTrace lastMax policy remaining (count + 1) next bs
          (result.1, result.2 + 1)
        else
          let canonical := count = 0 || payload b != 0
          if policy = .canonical ∧ !canonical then (.error ⟨.nonCanonical, count + 1⟩, 1)
          else (.ok ⟨next, count + 1, canonical⟩, 1)

set_option maxHeartbeats 2000000 in
theorem decodeTrace_contract (lastMax : Nat) (policy : Policy) (fuel count acc : Nat) (bs : List Spec.Byte) :
    let trace := decodeTrace lastMax policy fuel count acc bs
    trace.1 = decodeAux lastMax policy fuel count acc bs ∧
    consumed trace.1 = count + trace.2 ∧ trace.2 ≤ fuel ∧ trace.2 ≤ bs.length := by
  induction fuel generalizing count acc bs with
  | zero => simp [decodeTrace, decodeAux, consumed]
  | succ fuel ih =>
    cases bs with
    | nil => simp [decodeTrace, decodeAux, consumed]
    | cons byte rest =>
      simp only [decodeTrace, decodeAux]
      split_ifs
      all_goals try simp [consumed]
      all_goals have h := ih (count + 1) (acc + payload byte * 2 ^ (7 * count)) rest
      all_goals dsimp only at h
      all_goals cases heq : (decodeTrace lastMax policy fuel (count + 1) (acc + payload byte * 2 ^ (7 * count)) rest).1
      all_goals simp_all [consumed]
      all_goals omega

/-- Conservative abstract charges. A word operation is a fixed-width arithmetic,
    bitwise, Boolean or comparison primitive; memory measures count byte-buffer
    accesses separately. Header/state access charges are explicit fixed allowances.
    These charges are neither CPU instructions nor cycles. -/
structure Cost where
  transitions : Nat
  emittedBytes : Nat
  wordOperations : Nat
  byteReads : Nat
  byteWrites : Nat
  stateAccesses : Nat
  deriving DecidableEq

def prefixCost (reads : Nat) : Cost := ⟨reads, 0, 64 * reads + 16, reads, 0, 12 * reads + 8⟩
def exactCost (reads : Nat) : Cost := { prefixCost reads with wordOperations := 64 * reads + 17 }
def emissionCost (length : Nat) : Cost := ⟨length, length, 32 * length + 16, 0, length, 8 * length + 8⟩
/-- Fixed-array initialization and the u32 adapter's five copied bytes are
    charged separately from canonical emission. -/
def fixedArray64Cost (length : Nat) : Cost :=
  { emissionCost length with byteWrites := length + 10, wordOperations := 32 * length + 32 }
def fixedArray32Cost (length : Nat) : Cost :=
  { emissionCost length with byteReads := 5, byteWrites := length + 15, wordOperations := 32 * length + 48 }

def atomicEmissionCost (length : Nat) : Cost :=
  { emissionCost length with transitions := 2 * length, wordOperations := 64 * length + 32 }
def pushCost (sealed : Bool) : Cost :=
  if sealed then ⟨0, 0, 1, 0, 0, 1⟩ else ⟨1, 0, 64, 1, 0, 12⟩

theorem decoder_cost_bounded (width : Nat) (policy : Policy) (bs : List Spec.Byte) :
    let trace := decodeTrace (2 ^ (width - 7 * (maxBytes width - 1)) - 1)
      policy (maxBytes width) 0 0 bs
    trace.1 = decode width policy bs ∧
    (prefixCost trace.2).transitions ≤ maxBytes width ∧
    (prefixCost trace.2).byteReads ≤ maxBytes width ∧
    (prefixCost trace.2).wordOperations ≤ 64 * maxBytes width + 16 ∧
    (prefixCost trace.2).byteWrites = 0 := by
  have h := decodeTrace_contract (2 ^ (width - 7 * (maxBytes width - 1)) - 1)
    policy (maxBytes width) 0 0 bs
  dsimp only at h ⊢
  simp only [decode, prefixCost]
  exact ⟨h.1, h.2.2.1, h.2.2.1, by omega, True.intro⟩

theorem push_cost_bounded (sealed : Bool) :
    (pushCost sealed).transitions ≤ 1 ∧ (pushCost sealed).byteReads ≤ 1 ∧
    (pushCost sealed).wordOperations ≤ 64 := by cases sealed <;> decide

end VerifiedVarint.Reference

namespace VerifiedVarint.Refinement
open Aeneas Aeneas.Std

/-- Extraction proves total checked access. The byte-read accounting is tied to
    the reference transition trace by complete outcome correspondence and the
    proved count increment at each actual decoder body transition. -/
theorem decode_u64_resource_contract (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy ⦃ result =>
      let cost := Reference.prefixCost (Reference.consumed (referenceOutcome result))
      cost.transitions ≤ 10 ∧ cost.byteReads ≤ 10 ∧ cost.wordOperations ≤ 656 ∧ cost.byteWrites = 0 ⦄ := by
  apply WP.spec_mono (decode_u64_consumption_bounded input policy)
  intro result h
  dsimp [Reference.prefixCost]
  exact ⟨h.1, h.1, by omega, rfl⟩

theorem decode_u32_resource_contract (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u32 input policy ⦃ result =>
      let cost := Reference.prefixCost (Reference.consumed (referenceOutcome32 result))
      cost.transitions ≤ 5 ∧ cost.byteReads ≤ 5 ∧ cost.wordOperations ≤ 336 ∧ cost.byteWrites = 0 ⦄ := by
  apply WP.spec_mono (decode_u32_consumption_bounded input policy)
  intro result h
  dsimp [Reference.prefixCost]
  exact ⟨h.1, h.1, by omega, rfl⟩

theorem encode_u64_resource_contract (value : U64) :
    Generated.encode.encode_u64 value ⦃ encoded =>
      let cost := Reference.fixedArray64Cost encoded.len.val
      cost.transitions ≤ 10 ∧ cost.emittedBytes ≤ 10 ∧ cost.byteWrites ≤ 20 ∧ cost.wordOperations ≤ 352 ⦄ := by
  apply WP.spec_mono (encode_u64_refines value)
  intro encoded h
  dsimp [Reference.fixedArray64Cost, Reference.emissionCost]
  exact ⟨h.2.2.1, h.2.2.1, by omega, by omega⟩

theorem encode_u32_resource_contract (value : U32) :
    Generated.encode.encode_u32 value ⦃ encoded =>
      let cost := Reference.fixedArray32Cost encoded.len.val
      cost.transitions ≤ 5 ∧ cost.emittedBytes ≤ 5 ∧ cost.byteWrites ≤ 20 ∧ cost.wordOperations ≤ 208 ⦄ := by
  apply WP.spec_mono (encode_u32_refines value)
  intro encoded h
  dsimp [Reference.fixedArray32Cost, Reference.emissionCost]
  exact ⟨h.2.2.1, h.2.2.1, by omega, by omega⟩

theorem encoded_len_u64_formula (value : U64) :
    Generated.encode.encoded_len_u64 value ⦃ len => len.val = Spec.encodedLength value.val ⦄ := by
  apply WP.spec_mono (encoded_len_u64_refines value)
  intro len h
  rw [h.1, Spec.encode_length_formula]

theorem encoded_len_u32_formula (value : U32) :
    Generated.encode.encoded_len_u32 value ⦃ len => len.val = Spec.encodedLength value.val ⦄ := by
  apply WP.spec_mono (encoded_len_u32_refines value)
  intro len h
  rw [h.1, Spec.encode_length_formula]

end VerifiedVarint.Refinement
