import Bited.Refinement.TransitionContract
import Bited.Refinement.DecodeCorrespondence

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

def referenceDecision32 (policy : Reference.Policy) (count available byte : Nat) : DecodeDecision :=
  if count < 5 then
    if count = available then .rejected ⟨.truncated, count⟩
    else if count = 4 ∧ byte % 128 > 15 then .rejected ⟨.overflow, count + 1⟩
    else if count = 4 ∧ 128 ≤ byte then .rejected ⟨.tooLong, count + 1⟩
    else if 128 ≤ byte then .next (count + 1)
    else
      let canonical := count = 0 || byte % 128 != 0
      if policy = .canonical ∧ !canonical then .rejected ⟨.nonCanonical, count + 1⟩
      else .accepted (count + 1) canonical
  else .rejected ⟨.tooLong, count⟩

def referenceStep32 (policy : Reference.Policy) (count available acc byte : Nat) :
    ControlFlow (Nat × Nat) Reference.Outcome :=
  let next := acc + byte % 128 * 2 ^ (7 * count)
  match referenceDecision32 policy count available byte with
  | .next j => .cont (next, j)
  | .accepted j canonical => .done (.ok ⟨next, j, canonical⟩)
  | .rejected e => .done (.error e)

def referenceOutcome32 : core.result.Result (Generated.decode.Decoded U32) Generated.decode.DecodeError → Reference.Outcome
  | .Err e => .error ⟨referenceError e.kind, e.consumed.val⟩
  | .Ok d => .ok ⟨d.value.val, d.consumed.val, d.canonical⟩

def referenceFlow32 : ControlFlow (U64 × Usize)
    (core.result.Result (Generated.decode.Decoded U32) Generated.decode.DecodeError) →
    ControlFlow (Nat × Nat) Reference.Outcome
  | .cont (acc, count) => .cont (acc.val, count.val)
  | .done r => .done (referenceOutcome32 r)

theorem referenceStep32_byte (policy : Reference.Policy) (count available acc byte : Nat)
    (hc : count < 5) (ha : count < available) :
    referenceStep32 policy count available acc byte = byteStep policy 5 15 count acc byte := by
  simp [referenceStep32, referenceDecision32, byteStep, byteDecision, hc, show count ≠ available by omega]
  split_ifs <;> rfl

set_option maxHeartbeats 2000000 in
theorem decode_u32_body_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (acc : U64) (i : Usize) (hi : i.val ≤ 5) (hlen : i.val ≤ input.length)
    (ha : acc.val < 2 ^ (7 * i.val)) :
    Generated.decode.decode_u32_loop.body input policy acc i ⦃ r =>
      referenceFlow32 r = referenceStep32 (referencePolicy policy) i.val input.length acc.val
        input.val[i.val]!.val ∧
      (match r with
      | .done _ => True
      | .cont (next, j) => j.val = i.val + 1 ∧ j.val ≤ 5 ∧ j.val ≤ input.length ∧
          next.val < 2 ^ (7 * j.val)) ⦄ := by
  unfold Generated.decode.decode_u32_loop.body
  step*
  all_goals try
    have heq : i = input.len := by assumption
    have hl : i.val = input.length := by simpa only [Slice.len_val] using congrArg UScalar.val heq
    simp [referenceFlow32, referenceOutcome32, referenceStep32, referenceDecision32,
      referenceError, Slice.len_val, show i.val < 5 by scalar_tac, hl] at *
  all_goals try
    have hbig : 5 ≤ i.val := by scalar_tac
    simp [referenceFlow32, referenceOutcome32, referenceStep32, referenceDecision32,
      referenceError, show ¬i.val < 5 by omega]
  all_goals try subst r
  all_goals try (rcases t with ⟨next, isDone, canonical⟩; dsimp only [] at *; step*)
  all_goals try
    have hstrict : i.val < input.length := by scalar_tac
    have hbyte : i2 = input.val[i.val]! := by
      rw [i2_post, getElem!_pos input.val i.val (by simpa only [Slice.length] using hstrict)]
    have hpost := r_post
    rw [hbyte] at hpost
    rw [referenceStep32_byte _ _ _ _ _ (by scalar_tac) hstrict, ← hpost]
  all_goals try
    have hcast : i4.val = next.val := by
      rw [i4_post, UScalar.cast_val_eq]
      change next.val % (2^32) = next.val
      apply Nat.mod_eq_of_lt
      exact r_post1.2.2
    simp_all [referenceFlow32, referenceOutcome32, transitionFlow]
  all_goals try simp_all [referenceFlow32, referenceOutcome32, transitionFlow]
  all_goals rw [← r_post1.1]
  all_goals exact r_post1.2.1

set_option maxHeartbeats 2000000 in
theorem decodeAux32_step (input : Slice U8) (policy : Reference.Policy) (acc count : Nat)
    (hi : count ≤ 5) (hlen : count ≤ input.length) :
    match referenceStep32 policy count input.length acc input.val[count]!.val with
    | .done result => Reference.decodeAux 15 policy (5 - count) count acc
        ((input.val.drop count).map specByte) = result
    | .cont (next, j) => Reference.decodeAux 15 policy (5 - count) count acc
        ((input.val.drop count).map specByte) =
      Reference.decodeAux 15 policy (5 - j) j next ((input.val.drop j).map specByte) := by
  by_cases hten : count = 5
  · simp [hten, referenceStep32, referenceDecision32, Reference.decodeAux]
  · have hlt : count < 5 := by omega
    have hf : 5 - count = (4 - count) + 1 := by omega
    have hlast : (4 - count = 0) ↔ count = 4 := by omega
    by_cases hend : count = input.length
    · have hd : input.val.drop count = [] := by
        apply List.drop_eq_nil_of_le
        simpa only [Slice.length] using (le_of_eq hend.symm)
      have hlt' : input.length < 5 := by omega
      rw [hd, List.map_nil, hf, Reference.decodeAux]
      simp [referenceStep32, referenceDecision32, hend, hlt']
    · have hstrict : count < input.val.length := by
        simp only [Slice.length] at hlen hend
        omega
      have hd := List.cons_getElem_drop_succ (l := input.val) (n := count) (h := hstrict)
      have hb := getElem!_pos input.val count hstrict
      rw [← hd, List.map_cons, hf, Reference.decodeAux]
      simp only [Spec.payload, Spec.continues, specByte, hlast]
      simp only [referenceStep32, referenceDecision32, hlt, hend, ↓reduceIte, hb]
      have hsub : 5 - (count + 1) = 4 - count := by omega
      by_cases h9 : count = 4
      · subst count
        by_cases hov : 15 < input.val[4].val % 128
        · split_ifs <;> simp_all <;> try omega
        · by_cases hc : 128 ≤ input.val[4].val
          · split_ifs <;> simp_all <;> try omega
          · by_cases hcanon : policy = .canonical ∧ input.val[4].val % 128 = 0
            all_goals split_ifs <;> simp_all <;> try omega
      · by_cases hc : 128 ≤ input.val[count].val
        · split_ifs <;> simp_all <;> try omega
        · by_cases hz : count = 0
          · split_ifs <;> simp_all <;> try omega
          · by_cases hp : input.val[count].val % 128 = 0
            all_goals cases policy <;> split_ifs <;> simp_all <;> try omega


theorem decode_u32_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u32 input policy ⦃ r =>
      referenceOutcome32 r = Reference.decode 32 (referencePolicy policy)
        (input.val.map specByte) ⦄ := by
  unfold Generated.decode.decode_u32 Generated.decode.decode_u32_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Usize) => 5 - state.2.val)
    (fun state => state.2.val ≤ 5 ∧ state.2.val ≤ input.length ∧
      state.1.val < 2 ^ (7 * state.2.val) ∧
      Reference.decodeAux 15 (referencePolicy policy) (5 - state.2.val) state.2.val
        state.1.val ((input.val.drop state.2.val).map specByte) =
      Reference.decode 32 (referencePolicy policy) (input.val.map specByte))
  · rintro ⟨acc, i⟩ ⟨hi, hlen, ha, hmeaning⟩
    dsimp at hi hlen ha hmeaning
    apply WP.spec_mono (decode_u32_body_refines input policy acc i hi hlen ha)
    intro r hr
    have hs := decodeAux32_step input (referencePolicy policy) acc.val i.val hi hlen
    rw [← hr.1] at hs
    cases r with
    | cont state =>
      rcases state with ⟨next, j⟩
      dsimp [referenceFlow32] at hs hr ⊢
      exact ⟨⟨hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, hs.symm.trans hmeaning⟩, by omega⟩
    | done result =>
      dsimp [referenceFlow32] at hs
      exact hs.symm.trans hmeaning
  · simp [Reference.decode, Spec.maxBytes]

end Bited.Refinement
