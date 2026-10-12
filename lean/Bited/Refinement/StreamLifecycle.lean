import Bited.Refinement.Streaming

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

/-- Private states admitted by the public lifecycle, including early finish/reset. -/
inductive StreamReachable (width : Nat) : Reference.State → Prop
  | initial (policy) : StreamReachable width (Reference.initial policy)
  | push {state} (prior : StreamReachable width state) (byte) :
      StreamReachable width (Reference.push width state byte).2
  | finish {state} (prior : StreamReachable width state) :
      StreamReachable width (Reference.finish state).2
  | reset {state} (prior : StreamReachable width state) (policy) :
      StreamReachable width (Reference.reset state policy)

theorem reachable_stream_invariant (width : Nat) (hw : width = 32 ∨ width = 64)
    (state : Reference.State) (h : StreamReachable width state) : streamInvariant width state := by
  induction h with
  | initial policy => exact stream_initial_invariant width hw policy
  | push prior byte ih => exact stream_push_invariant width hw _ byte ih
  | finish prior ih => exact stream_finish_invariant width _ ih
  | reset prior policy ih => exact stream_initial_invariant width hw policy

theorem stream_u64_finish_contract (decoder : Generated.stream.DecoderU64)
    (hi : streamInvariant 64 (stateView decoder.state)) :
    Generated.stream.DecoderU64.finish decoder ⦃ result =>
      (referenceOutcome result.1, stateView result.2.state) = Reference.finish (stateView decoder.state) ∧
      streamInvariant 64 (stateView result.2.state) ⦄ := by
  apply WP.spec_mono (stream_u64_finish_refines decoder)
  intro result hr
  refine ⟨hr, ?_⟩
  have he := congrArg Prod.snd hr
  dsimp only at he
  rw [he]
  exact stream_finish_invariant 64 _ hi

theorem stream_u64_finish_idempotent (decoder : Generated.stream.DecoderU64) :
    (do
      let first ← Generated.stream.DecoderU64.finish decoder
      let second ← Generated.stream.DecoderU64.finish first.2
      ok (first, second)) ⦃ result => result.2 = result.1 ⦄ := by
  cases ht : decoder.state.terminal <;>
    simp [Generated.stream.DecoderU64.finish, Generated.stream.State.finish, ht]

set_option maxHeartbeats 2000000 in
theorem stream_u32_finish_idempotent (decoder : Generated.stream.DecoderU32) :
    (do
      let first ← Generated.stream.DecoderU32.finish decoder
      let second ← Generated.stream.DecoderU32.finish first.2
      ok (first, second)) ⦃ result => result.2 = result.1 ⦄ := by
  cases ht : decoder.state.terminal with
  | none => simp [Generated.stream.DecoderU32.finish, Generated.stream.State.finish, ht]
  | some terminal =>
    cases terminal with
    | Err e => simp [Generated.stream.DecoderU32.finish, Generated.stream.State.finish, ht]
    | Ok d =>
      simp only [Generated.stream.DecoderU32.finish, Generated.stream.State.finish, ht]
      step*
      simp_all
      step*
      simp_all

theorem rust_stream64_chunks_equivalence (policy : Generated.decode.DecodePolicy)
    (chunks : List (List U8)) :
    (do
      let decoder ← Generated.stream.DecoderU64.new policy
      let next ← runStream64 decoder chunks.flatten
      Generated.stream.DecoderU64.finish next) ⦃ result =>
        referenceOutcome result.1 = Reference.decode 64 (referencePolicy policy) (chunks.map (List.map specByte)).flatten ⦄ := by
  simpa [List.map_flatten] using rust_stream64_slice_equivalence policy chunks.flatten

theorem rust_stream32_chunks_equivalence (policy : Generated.decode.DecodePolicy)
    (chunks : List (List U8)) :
    (do
      let decoder ← Generated.stream.DecoderU32.new policy
      let next ← runStream32 decoder chunks.flatten
      Generated.stream.DecoderU32.finish next) ⦃ result =>
        referenceOutcome32 result.1 = Reference.decode 32 (referencePolicy policy) (chunks.map (List.map specByte)).flatten ⦄ := by
  simpa [List.map_flatten] using rust_stream32_slice_equivalence policy chunks.flatten


theorem stream_u32_push_closed (decoder : Generated.stream.DecoderU32) (byte : U8)
    (terminal : core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError)
    (ht : decoder.state.terminal = some terminal) :
    Generated.stream.DecoderU32.push decoder byte = .ok (.Closed, decoder) := by
  simp [Generated.stream.DecoderU32.push,
    stream_state_push_closed decoder.state byte _ _ terminal ht]

def runChunks32 (decoder : Generated.stream.DecoderU32) : List (List U8) → Result Generated.stream.DecoderU32
  | [] => ok decoder
  | chunk :: rest => do
    let next ← runStream32 decoder chunk
    runChunks32 next rest

theorem runChunks32_refines (decoder : Generated.stream.DecoderU32) (chunks : List (List U8))
    (hi : streamInvariant 32 (stateView decoder.state)) :
    runChunks32 decoder chunks ⦃ result =>
      stateView result.state = Reference.runChunks 32 (stateView decoder.state) (chunks.map (List.map specByte)) ∧
      streamInvariant 32 (stateView result.state) ⦄ := by
  induction chunks generalizing decoder with
  | nil => simp [runChunks32, Reference.runChunks, hi]
  | cons chunk rest ih =>
    unfold runChunks32
    apply WP.spec_bind (runStream32_refines decoder chunk hi)
    intro next hn
    apply WP.spec_mono (ih next hn.2)
    intro result hr
    refine ⟨?_, hr.2⟩
    rw [hr.1, hn.1]
    rfl

theorem rust_chunk_session32_refines (policy : Generated.decode.DecodePolicy)
    (chunks : List (List U8)) :
    (do
      let decoder ← Generated.stream.DecoderU32.new policy
      let next ← runChunks32 decoder chunks
      Generated.stream.DecoderU32.finish next) ⦃ result =>
        referenceOutcome32 result.1 = Reference.decode 32 (referencePolicy policy) (chunks.map (List.map specByte)).flatten ⦄ := by
  apply WP.spec_bind (stream_u32_new_refines policy)
  intro decoder hd
  have hi : streamInvariant 32 (stateView decoder.state) := by
    rw [hd]
    exact stream_initial_invariant 32 (Or.inl rfl) _
  apply WP.spec_bind (runChunks32_refines decoder chunks hi)
  intro next hn
  apply WP.spec_mono (stream_u32_finish_refines next hn.2)
  intro result hr
  have he := congrArg Prod.fst hr.1
  dsimp only at he
  rw [he, hn.1, hd]
  exact Reference.streaming_chunks_equivalence 32 _ _ (by decide)

theorem stream_u64_push_closed (decoder : Generated.stream.DecoderU64) (byte : U8)
    (terminal : core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError)
    (ht : decoder.state.terminal = some terminal) :
    Generated.stream.DecoderU64.push decoder byte = .ok (.Closed, decoder) := by
  simp [Generated.stream.DecoderU64.push,
    stream_state_push_closed decoder.state byte _ _ terminal ht]

def runChunks64 (decoder : Generated.stream.DecoderU64) : List (List U8) → Result Generated.stream.DecoderU64
  | [] => ok decoder
  | chunk :: rest => do
    let next ← runStream64 decoder chunk
    runChunks64 next rest

theorem runChunks64_refines (decoder : Generated.stream.DecoderU64) (chunks : List (List U8))
    (hi : streamInvariant 64 (stateView decoder.state)) :
    runChunks64 decoder chunks ⦃ result =>
      stateView result.state = Reference.runChunks 64 (stateView decoder.state) (chunks.map (List.map specByte)) ∧
      streamInvariant 64 (stateView result.state) ⦄ := by
  induction chunks generalizing decoder with
  | nil => simp [runChunks64, Reference.runChunks, hi]
  | cons chunk rest ih =>
    unfold runChunks64
    apply WP.spec_bind (runStream64_refines decoder chunk hi)
    intro next hn
    apply WP.spec_mono (ih next hn.2)
    intro result hr
    refine ⟨?_, hr.2⟩
    rw [hr.1, hn.1]
    rfl

theorem rust_chunk_session64_refines (policy : Generated.decode.DecodePolicy)
    (chunks : List (List U8)) :
    (do
      let decoder ← Generated.stream.DecoderU64.new policy
      let next ← runChunks64 decoder chunks
      Generated.stream.DecoderU64.finish next) ⦃ result =>
        referenceOutcome result.1 = Reference.decode 64 (referencePolicy policy) (chunks.map (List.map specByte)).flatten ⦄ := by
  apply WP.spec_bind (stream_u64_new_refines policy)
  intro decoder hd
  have hi : streamInvariant 64 (stateView decoder.state) := by
    rw [hd]
    exact stream_initial_invariant 64 (Or.inr rfl) _
  apply WP.spec_bind (runChunks64_refines decoder chunks hi)
  intro next hn
  apply WP.spec_mono (stream_u64_finish_refines next)
  intro result hr
  have he := congrArg Prod.fst hr
  dsimp only at he
  rw [he, hn.1, hd]
  exact Reference.streaming_chunks_equivalence 64 _ _ (by decide)

end Bited.Refinement
