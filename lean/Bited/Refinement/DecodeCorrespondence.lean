import Bited.Refinement.DecodeDecision
import Mathlib.Tactic.SplitIfs

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

def referenceOutcome : core.result.Result (Generated.decode.Decoded U64)
    Generated.decode.DecodeError → Reference.Outcome
  | .Ok d => .ok ⟨d.value.val, d.consumed.val, d.canonical⟩
  | .Err e => .error ⟨referenceError e.kind, e.consumed.val⟩

def referenceFlow : ControlFlow (U64 × Usize)
    (core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError) →
    ControlFlow (Nat × Nat) Reference.Outcome
  | .cont (value, count) => .cont (value.val, count.val)
  | .done result => .done (referenceOutcome result)

def referenceStep (policy : Reference.Policy) (count available acc byte : Nat) :
    ControlFlow (Nat × Nat) Reference.Outcome :=
  let next := acc + byte % 128 * 2 ^ (7 * count)
  match referenceDecision policy count available byte with
  | .next j => .cont (next, j)
  | .accepted j canonical => .done (.ok ⟨next, j, canonical⟩)
  | .rejected error => .done (.error error)

theorem decode_u64_body_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (acc : U64) (i : Usize) (hi : i.val ≤ 10) (hlen : i.val ≤ input.length)
    (ha : acc.val < 2 ^ (7 * i.val)) :
    Generated.decode.decode_u64_scan_loop.body input policy acc i ⦃ r =>
      referenceFlow r = referenceStep (referencePolicy policy) i.val input.length acc.val
        input.val[i.val]!.val ⦄ := by
  apply WP.spec_mono (WP.spec_and (decode_u64_body_decision input policy acc i hi hlen)
    (decode_u64_body_value input policy acc i hi hlen ha))
  intro r hr
  unfold referenceStep
  rw [← hr.1]
  cases r with
  | cont state =>
    rcases state with ⟨value, j⟩
    dsimp [decodeDecision, referenceFlow] at hr ⊢
    rw [hr.2.2.1]
  | done result =>
    cases result with
    | Err e => rfl
    | Ok d =>
      dsimp [decodeDecision, referenceFlow, referenceOutcome] at hr ⊢
      rw [hr.2.2.1]

set_option maxHeartbeats 2000000 in
/-- Unfolding the independent fuel/list decoder agrees with the arithmetic step.
    The slice is only an adapter; Reference.decodeAux still drives the meaning. -/
theorem decodeAux64_step (input : Slice U8) (policy : Reference.Policy) (acc count : Nat)
    (hi : count ≤ 10) (hlen : count ≤ input.length) :
    match referenceStep policy count input.length acc input.val[count]!.val with
    | .done result => Reference.decodeAux 1 policy (10 - count) count acc
        ((input.val.drop count).map specByte) = result
    | .cont (next, j) => Reference.decodeAux 1 policy (10 - count) count acc
        ((input.val.drop count).map specByte) =
      Reference.decodeAux 1 policy (10 - j) j next ((input.val.drop j).map specByte) := by
  by_cases hten : count = 10
  · simp [hten, referenceStep, referenceDecision, Reference.decodeAux]
  · have hlt : count < 10 := by omega
    have hf : 10 - count = (9 - count) + 1 := by omega
    have hlast : (9 - count = 0) ↔ count = 9 := by omega
    by_cases hend : count = input.length
    · have hd : input.val.drop count = [] := by
        apply List.drop_eq_nil_of_le
        simpa only [Slice.length] using (le_of_eq hend.symm)
      have hlt' : input.length < 10 := by omega
      rw [hd, List.map_nil, hf, Reference.decodeAux]
      simp [referenceStep, referenceDecision, hend, hlt']
    · have hstrict : count < input.val.length := by
        simp only [Slice.length] at hlen hend
        omega
      have hd := List.cons_getElem_drop_succ (l := input.val) (n := count) (h := hstrict)
      have hb := getElem!_pos input.val count hstrict
      rw [← hd, List.map_cons, hf, Reference.decodeAux]
      simp only [Spec.payload, Spec.continues, specByte, hlast]
      simp only [referenceStep, referenceDecision, hlt, hend, ↓reduceIte, hb]
      have hsub : 10 - (count + 1) = 9 - count := by omega
      by_cases h9 : count = 9
      · subst count
        by_cases hov : 1 < input.val[9].val % 128
        · split_ifs <;> simp_all <;> try omega
        · by_cases hc : 128 ≤ input.val[9].val
          · split_ifs <;> simp_all <;> try omega
          · by_cases hcanon : policy = .canonical ∧ input.val[9].val % 128 = 0
            all_goals split_ifs <;> simp_all <;> try omega
      · by_cases hc : 128 ≤ input.val[count].val
        · split_ifs <;> simp_all <;> try omega
        · by_cases hz : count = 0
          · split_ifs <;> simp_all <;> try omega
          · by_cases hp : input.val[count].val % 128 = 0
            all_goals cases policy <;> split_ifs <;> simp_all <;> try omega


/-- Universal correspondence of the complete actual Rust prefix decoder,
    including both policies, every value/error/consumption count and canonical flag. -/
theorem decode_u64_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy ⦃ r =>
      referenceOutcome r = Reference.decode 64 (referencePolicy policy)
        (input.val.map specByte) ⦄ := by
  rw [decode_u64_eq_scan]
  unfold Generated.decode.decode_u64_scan Generated.decode.decode_u64_scan_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Usize) => 10 - state.2.val)
    (fun state => state.2.val ≤ 10 ∧ state.2.val ≤ input.length ∧
      state.1.val < 2 ^ (7 * state.2.val) ∧
      Reference.decodeAux 1 (referencePolicy policy) (10 - state.2.val) state.2.val
        state.1.val ((input.val.drop state.2.val).map specByte) =
      Reference.decode 64 (referencePolicy policy) (input.val.map specByte))
  · rintro ⟨acc, i⟩ ⟨hi, hlen, ha, hmeaning⟩
    dsimp at hi hlen ha hmeaning
    apply WP.spec_mono (WP.spec_and (decode_u64_body_total input policy acc i hi hlen)
      (WP.spec_and (decode_u64_body_refines input policy acc i hi hlen ha)
        (decode_u64_body_value input policy acc i hi hlen ha)))
    intro r hr
    have hs := decodeAux64_step input (referencePolicy policy) acc.val i.val hi hlen
    rw [← hr.2.1] at hs
    cases r with
    | cont state =>
      rcases state with ⟨next, j⟩
      dsimp [referenceFlow] at hs hr ⊢
      exact ⟨⟨hr.1.1, hr.1.2.1, hr.2.2.2.2, hs.symm.trans hmeaning⟩, by omega⟩
    | done result =>
      dsimp [referenceFlow] at hs
      exact hs.symm.trans hmeaning
  · simp [Reference.decode, Spec.maxBytes]

end Bited.Refinement
