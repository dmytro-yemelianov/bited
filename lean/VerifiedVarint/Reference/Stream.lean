import VerifiedVarint.Reference.Decode

namespace VerifiedVarint.Reference
open Spec

inductive Step where
  | needMore
  | done (value : Decoded)
  | error (failure : DecodeError)
  | closed
  deriving DecidableEq

structure State where
  policy : Policy
  acc : Nat
  count : Nat
  terminal : Option Outcome
  deriving DecidableEq

def initial (policy : Policy) : State := ⟨policy, 0, 0, none⟩

/-- One independent arithmetic transition; accepted lower groups are in `acc`. -/
def advance (width : Nat) (policy : Policy) (count acc : Nat) (byte : Byte) :
    Except DecodeError (Nat × Bool × Bool) :=
  let limit := maxBytes width
  let lastMax := 2 ^ (width - 7 * (limit - 1)) - 1
  if count = limit - 1 ∧ payload byte > lastMax then .error ⟨.overflow, count + 1⟩
  else if count = limit - 1 ∧ continues byte then .error ⟨.tooLong, count + 1⟩
  else
    let next := acc + payload byte * 2 ^ (7 * count)
    let canonical := count = 0 || payload byte != 0
    if !continues byte ∧ policy = .canonical ∧ !canonical then .error ⟨.nonCanonical, count + 1⟩
    else .ok (next, !continues byte, canonical)

def push (width : Nat) (state : State) (byte : Byte) : Step × State :=
  match state.terminal with
  | some _ => (.closed, state)
  | none =>
    match advance width state.policy state.count state.acc byte with
    | .error e => (.error e, { state with count := state.count + 1, terminal := some (.error e) })
    | .ok (next, isDone, canonical) =>
      if isDone then
        let decoded := Decoded.mk next (state.count + 1) canonical
        (.done decoded, { state with acc := next, count := state.count + 1, terminal := some (.ok decoded) })
      else (.needMore, { state with acc := next, count := state.count + 1 })

def finish (state : State) : Outcome × State :=
  match state.terminal with
  | some result => (result, state)
  | none =>
    let result : Outcome := .error ⟨.truncated, state.count⟩
    (result, { state with terminal := some result })

def reset (_state : State) (policy : Policy) : State := initial policy

/-- A chunk consumer stops upon a terminal result and leaves the remainder to its caller. -/
def runBytes (width : Nat) (state : State) : List Byte → State
  | [] => state
  | byte :: rest =>
    match (push width state byte).1 with
    | .needMore => runBytes width (push width state byte).2 rest
    | _ => (push width state byte).2

def runChunks (width : Nat) (state : State) : List (List Byte) → State
  | [] => state
  | chunk :: rest => runChunks width (runBytes width state chunk) rest

theorem push_closed (width : Nat) (state : State) (byte : Byte) (result : Outcome)
    (h : state.terminal = some result) : push width state byte = (.closed, state) := by
  simp [push, h]

theorem finish_stored (state : State) (result : Outcome) (h : state.terminal = some result) :
    finish state = (result, state) := by simp [finish, h]

theorem finish_idempotent (state : State) : finish (finish state).2 = finish state := by
  unfold finish
  cases h : state.terminal <;> simp [h]

theorem finish_seals (state : State) (width : Nat) (byte : Byte) :
    push width (finish state).2 byte = (.closed, (finish state).2) := by
  unfold finish
  cases h : state.terminal <;> simp [push, h]

theorem reset_ready (state : State) (policy : Policy) :
    (reset state policy).count = 0 ∧ (reset state policy).acc = 0 ∧
      (reset state policy).terminal = none ∧ (reset state policy).policy = policy := by
  simp [reset, initial]

theorem runBytes_closed (width : Nat) (state : State) (bs : List Byte)
    (result : Outcome) (h : state.terminal = some result) : runBytes width state bs = state := by
  cases bs <;> simp [runBytes, push, h]

theorem push_terminal (width : Nat) (state : State) (byte : Byte)
    (h : (push width state byte).1 ≠ .needMore) : (push width state byte).2.terminal ≠ none := by
  cases ht : state.terminal with
  | some result => simp [push, ht]
  | none =>
    cases ha : advance width state.policy state.count state.acc byte with
    | error e => simp [push, ht, ha]
    | ok triple =>
      rcases triple with ⟨next, isDone, canonical⟩
      cases isDone <;> simp [push, ht, ha] at h ⊢

theorem runBytes_sealed (width : Nat) (state : State) (bs : List Byte)
    (h : state.terminal ≠ none) : runBytes width state bs = state := by
  cases ht : state.terminal with
  | none => exact False.elim (h ht)
  | some result => exact runBytes_closed width state bs result ht

theorem runBytes_append (width : Nat) (state : State) (xs ys : List Byte) :
    runBytes width state (xs ++ ys) = runBytes width (runBytes width state xs) ys := by
  induction xs generalizing state with
  | nil => simp [runBytes]
  | cons byte xs ih =>
    cases hs : (push width state byte).1
    · simp only [List.cons_append, runBytes, hs]
      exact ih _
    all_goals simp only [List.cons_append, runBytes, hs]
    all_goals symm
    all_goals apply runBytes_sealed
    all_goals apply push_terminal
    all_goals simp [hs]

theorem stream_partition_invariant (width : Nat) (state : State) (chunks : List (List Byte)) :
    runChunks width state chunks = runBytes width state chunks.flatten := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk rest ih =>
    simp only [runChunks, List.flatten_cons]
    rw [runBytes_append, ih]

end VerifiedVarint.Reference
