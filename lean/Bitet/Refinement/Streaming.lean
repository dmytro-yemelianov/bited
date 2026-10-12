import Bitet.Refinement.StreamApi

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

/-- Execute the public byte-at-a-time API, stopping at its first terminal step. -/
def runStream32 (decoder : Generated.stream.DecoderU32) : List U8 → Result Generated.stream.DecoderU32
  | [] => ok decoder
  | byte :: rest => do
    let (step, next) ← Generated.stream.DecoderU32.push decoder byte
    match step with
    | .NeedMore => runStream32 next rest
    | _ => ok next

set_option maxHeartbeats 2000000 in
theorem runStream32_refines (decoder : Generated.stream.DecoderU32) (bytes : List U8)
    (hi : streamInvariant 32 (stateView decoder.state)) :
    runStream32 decoder bytes ⦃ result =>
      stateView result.state = Reference.runBytes 32 (stateView decoder.state) (bytes.map specByte) ∧
      streamInvariant 32 (stateView result.state) ⦄ := by
  induction bytes generalizing decoder with
  | nil => simp [runStream32, Reference.runBytes, hi]
  | cons byte rest ih =>
    unfold runStream32
    apply WP.spec_bind (stream_u32_push_refines decoder byte hi)
    rintro ⟨step, next⟩ h
    have hs := congrArg Prod.fst h.1
    have hn := congrArg Prod.snd h.1
    dsimp only at hs hn
    cases step with
    | NeedMore =>
      apply WP.spec_mono (ih next h.2)
      intro result hr
      refine ⟨?_, hr.2⟩
      rw [hr.1]
      simp only [List.map_cons, Reference.runBytes, ← hs, stepView32]
      rw [hn]
    | Done d =>
      simpa [List.map_cons, Reference.runBytes, ← hs, stepView32, ← hn] using And.intro hn h.2
    | Error e =>
      simpa [List.map_cons, Reference.runBytes, ← hs, stepView32, ← hn] using And.intro hn h.2
    | Closed =>
      simpa [List.map_cons, Reference.runBytes, ← hs, stepView32, ← hn] using And.intro hn h.2

set_option maxHeartbeats 2000000 in
theorem rust_stream32_slice_equivalence (policy : Generated.decode.DecodePolicy) (bytes : List U8) :
    (do
      let decoder ← Generated.stream.DecoderU32.new policy
      let next ← runStream32 decoder bytes
      Generated.stream.DecoderU32.finish next) ⦃ result =>
        referenceOutcome32 result.1 = Reference.decode 32 (referencePolicy policy) (bytes.map specByte) ⦄ := by
  apply WP.spec_bind (stream_u32_new_refines policy)
  intro decoder hd
  have hi : streamInvariant 32 (stateView decoder.state) := by
    rw [hd]
    exact stream_initial_invariant 32 (Or.inl rfl) _
  apply WP.spec_bind (runStream32_refines decoder bytes hi)
  intro next hn
  apply WP.spec_mono (stream_u32_finish_refines next hn.2)
  intro result hr
  have he := congrArg Prod.fst hr.1
  dsimp only at he
  rw [he, hn.1, hd]
  exact Reference.stream_slice_equivalence 32 _ _ (by decide)

/-- Execute the public byte-at-a-time API, stopping at its first terminal step. -/
def runStream64 (decoder : Generated.stream.DecoderU64) : List U8 → Result Generated.stream.DecoderU64
  | [] => ok decoder
  | byte :: rest => do
    let (step, next) ← Generated.stream.DecoderU64.push decoder byte
    match step with
    | .NeedMore => runStream64 next rest
    | _ => ok next

set_option maxHeartbeats 2000000 in
theorem runStream64_refines (decoder : Generated.stream.DecoderU64) (bytes : List U8)
    (hi : streamInvariant 64 (stateView decoder.state)) :
    runStream64 decoder bytes ⦃ result =>
      stateView result.state = Reference.runBytes 64 (stateView decoder.state) (bytes.map specByte) ∧
      streamInvariant 64 (stateView result.state) ⦄ := by
  induction bytes generalizing decoder with
  | nil => simp [runStream64, Reference.runBytes, hi]
  | cons byte rest ih =>
    unfold runStream64
    apply WP.spec_bind (stream_u64_push_refines decoder byte hi)
    rintro ⟨step, next⟩ h
    have hs := congrArg Prod.fst h.1
    have hn := congrArg Prod.snd h.1
    dsimp only at hs hn
    cases step with
    | NeedMore =>
      apply WP.spec_mono (ih next h.2)
      intro result hr
      refine ⟨?_, hr.2⟩
      rw [hr.1]
      simp only [List.map_cons, Reference.runBytes, ← hs, stepView64]
      rw [hn]
    | Done d =>
      simpa [List.map_cons, Reference.runBytes, ← hs, stepView64, ← hn] using And.intro hn h.2
    | Error e =>
      simpa [List.map_cons, Reference.runBytes, ← hs, stepView64, ← hn] using And.intro hn h.2
    | Closed =>
      simpa [List.map_cons, Reference.runBytes, ← hs, stepView64, ← hn] using And.intro hn h.2

set_option maxHeartbeats 2000000 in
theorem rust_stream64_slice_equivalence (policy : Generated.decode.DecodePolicy) (bytes : List U8) :
    (do
      let decoder ← Generated.stream.DecoderU64.new policy
      let next ← runStream64 decoder bytes
      Generated.stream.DecoderU64.finish next) ⦃ result =>
        referenceOutcome result.1 = Reference.decode 64 (referencePolicy policy) (bytes.map specByte) ⦄ := by
  apply WP.spec_bind (stream_u64_new_refines policy)
  intro decoder hd
  have hi : streamInvariant 64 (stateView decoder.state) := by
    rw [hd]
    exact stream_initial_invariant 64 (Or.inr rfl) _
  apply WP.spec_bind (runStream64_refines decoder bytes hi)
  intro next hn
  apply WP.spec_mono (stream_u64_finish_refines next)
  intro result hr
  have he := congrArg Prod.fst hr
  dsimp only at he
  rw [he, hn.1, hd]
  exact Reference.stream_slice_equivalence 64 _ _ (by decide)

end Bitet.Refinement
