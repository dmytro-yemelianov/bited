import Bited.Generated.Funs
import Bited.Refinement.DecodeFastPath

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

def consumed (r : core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError) : Nat :=
  match r with
  | .Ok d => d.consumed.val
  | .Err e => e.consumed.val

@[step]
theorem decode_policy_eq_spec (p q : Generated.decode.DecodePolicy) :
    Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq p q
      ⦃ _ => True ⦄ := by
  simp [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]

/-- Safety of every scalar byte transition, including malformed input. -/
theorem decode_u64_body_total (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (acc : U64) (i : Usize) (hi : i.val ≤ 10) (hlen : i.val ≤ input.length) :
    Generated.decode.decode_u64_scan_loop.body input policy acc i ⦃ r =>
      match r with
      | .cont (_, next) => next.val ≤ 10 ∧ next.val ≤ input.length ∧ next.val = i.val + 1
      | .done result => consumed result ≤ 10 ∧ consumed result ≤ input.length ⦄ := by
  unfold Generated.decode.decode_u64_scan_loop.body
  cases policy <;> simp only [Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals step*
  all_goals try
    have hstrict : i.val < input.length := by
      have hnot : i ≠ input.len := by assumption
      have hne := UScalar.neq_to_neq_val.mp hnot
      simp only [Slice.len_val] at hne
      omega
  all_goals try simp_all [consumed]
  all_goals by_cases hz : i = 0#usize
  all_goals try simp_all
  all_goals step*

/-- The entire extracted prefix decoder terminates without Rust panic for
    every slice and both policies, and never consumes beyond ten/input bytes. -/
theorem decode_u64_total (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy
      ⦃ r => consumed r ≤ 10 ∧ consumed r ≤ input.length ⦄ := by
  rw [decode_u64_eq_scan]
  unfold Generated.decode.decode_u64_scan Generated.decode.decode_u64_scan_loop
  apply loop.spec_decr_nat
    (fun (state : U64 × Usize) => 10 - state.2.val)
    (fun state => state.2.val ≤ 10 ∧ state.2.val ≤ input.length)
  · rintro ⟨acc, i⟩ ⟨hi, hlen⟩
    apply WP.spec_mono (decode_u64_body_total input policy acc i hi hlen)
    intro r hr
    cases r with
    | done result => exact hr
    | cont state =>
      rcases state with ⟨acc', next⟩
      dsimp at hr ⊢
      exact ⟨⟨hr.1, hr.2.1⟩, by omega⟩
  · simp

/-- Overflow is decisive at byte ten, even when continuation is also set. -/
theorem decode_u64_last_overflow (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (acc : U64) (hlen : 10 ≤ input.length)
    (hp : input.val[9].val &&& 127 > 1) :
    Generated.decode.decode_u64_scan_loop.body input policy acc 9#usize
      ⦃ r => r = .done (.Err ⟨.Overflow, 10#usize⟩) ⦄ := by
  unfold Generated.decode.decode_u64_scan_loop.body
  step*
  congr 3
  scalar_tac

end Bited.Refinement
