import Bitet.Refinement.DecodeCorrespondence

namespace Bitet.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

def exactResult {T : Type} (result : core.result.Result (Generated.decode.Decoded T) Generated.decode.DecodeError)
    (length : Nat) : core.result.Result (Generated.decode.Decoded T) Generated.decode.DecodeError :=
  match result with
  | .Err e => .Err e
  | .Ok d => if d.consumed.val = length then .Ok d
      else .Err ⟨.TrailingBytes, d.consumed⟩

theorem exact_refines {T : Type}
    (result : core.result.Result (Generated.decode.Decoded T) Generated.decode.DecodeError)
    (length : Usize) :
    Generated.api.exact result length = .ok (exactResult result length.val) := by
  cases result with
  | Err e => rfl
  | Ok d =>
    simp only [Generated.api.exact, exactResult, scalar_bne_val]
    by_cases h : d.consumed.val = length.val <;> simp [h]

theorem exact_reference_commutes
    (result : core.result.Result (Generated.decode.Decoded U64) Generated.decode.DecodeError)
    (length : Nat) :
    referenceOutcome (exactResult result length) = Reference.exact length (referenceOutcome result) := by
  cases result with
  | Err e => rfl
  | Ok d => simp [exactResult, referenceOutcome, Reference.exact]; split_ifs <;> rfl

theorem decode_u64_exact_refines (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.api.decode_u64_exact input policy ⦃ r =>
      referenceOutcome r = Reference.exact input.length
        (Reference.decode 64 (referencePolicy policy) (input.val.map specByte)) ⦄ := by
  unfold Generated.api.decode_u64_exact
  apply WP.spec_bind (decode_u64_refines input policy)
  intro result h
  rw [exact_refines]
  simp only [WP.spec_ok, Slice.len_val]
  rw [exact_reference_commutes, h]

end Bitet.Refinement
