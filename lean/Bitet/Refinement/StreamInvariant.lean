import Bitet.Refinement.StreamPush

namespace Bitet.Refinement
open Aeneas Aeneas.Std

/-- The private state invariant; all reachable states are bounded, and every
    still-open state has room for another byte. -/
def streamInvariant (width : Nat) (state : Reference.State) : Prop :=
  state.count ≤ Spec.maxBytes width ∧
  (state.terminal = none → state.count < Spec.maxBytes width ∧ state.acc < 2 ^ (7 * state.count)) ∧
  (∀ d, state.terminal = some (.ok d) → d.value < 2 ^ width)

set_option maxHeartbeats 2000000 in
theorem advance_bounds (width : Nat) (hw : width = 32 ∨ width = 64)
    (policy : Reference.Policy) (count acc : Nat) (byte : Spec.Byte)
    (hc : count < Spec.maxBytes width) (ha : acc < 2 ^ (7 * count))
    (next : Nat) (isDone canonical : Bool)
    (h : Reference.advance width policy count acc byte = .ok (next, isDone, canonical)) :
    next < 2 ^ (7 * (count + 1)) ∧ next < 2 ^ width ∧
      (isDone = false → count + 1 < Spec.maxBytes width) := by
  have hp : Spec.payload byte < 128 := Nat.mod_lt _ (by decide)
  rcases hw with rfl | rfl
  all_goals
    unfold Reference.advance at h
    norm_num [Spec.maxBytes] at hc h ⊢
    split_ifs at h <;> try cases h
    all_goals
      interval_cases count <;> norm_num at ha ⊢
      all_goals simp_all [Spec.continues] <;> omega

theorem stream_initial_invariant (width : Nat) (hw : width = 32 ∨ width = 64)
    (policy : Reference.Policy) : streamInvariant width (Reference.initial policy) := by
  rcases hw with rfl | rfl <;> simp [streamInvariant, Reference.initial, Spec.maxBytes]

set_option maxHeartbeats 2000000 in
theorem stream_push_invariant (width : Nat) (hw : width = 32 ∨ width = 64)
    (state : Reference.State) (byte : Spec.Byte) (hi : streamInvariant width state) :
    streamInvariant width (Reference.push width state byte).2 := by
  cases ht : state.terminal with
  | some result => simpa [Reference.push, ht] using hi
  | none =>
    have hc := (hi.2.1 ht).1
    have ha := (hi.2.1 ht).2
    cases h : Reference.advance width state.policy state.count state.acc byte with
    | error e =>
      simp [Reference.push, ht, h, streamInvariant]
      omega
    | ok triple =>
      rcases triple with ⟨next, isDone, canonical⟩
      have hb := advance_bounds width hw _ _ _ _ hc ha next isDone canonical h
      cases isDone <;> simp [Reference.push, ht, h, streamInvariant] at hb ⊢ <;> omega

theorem stream_finish_invariant (width : Nat) (state : Reference.State)
    (hi : streamInvariant width state) : streamInvariant width (Reference.finish state).2 := by
  cases ht : state.terminal with
  | some result => simpa [Reference.finish, ht] using hi
  | none => simp [Reference.finish, ht, streamInvariant, hi.1]

theorem stream_runBytes_invariant (width : Nat) (hw : width = 32 ∨ width = 64)
    (state : Reference.State) (bs : List Spec.Byte) (hi : streamInvariant width state) :
    streamInvariant width (Reference.runBytes width state bs) := by
  induction bs generalizing state with
  | nil => exact hi
  | cons byte rest ih =>
    have hn := stream_push_invariant width hw state byte hi
    cases hs : (Reference.push width state byte).1 <;> simp only [Reference.runBytes, hs]
    · exact ih _ hn
    all_goals exact hn

end Bitet.Refinement
