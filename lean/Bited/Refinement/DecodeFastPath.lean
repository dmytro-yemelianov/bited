import Bited.Generated.Funs

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result Aeneas.Std.ControlFlow

/-! The inline one/two-byte fast path of `decode_u64` returns exactly what the
    shared scan returns. Every other refinement theorem is proved on the scan. -/

theorem ok_of_spec {α : Type} {m : Result α} {v : α} (h : m ⦃ z => z = v ⦄) : m = ok v := by
  revert h
  cases m <;> simp


/-! Literal scalar steps taken by the first two scan iterations. -/

theorem usize_mul_7_0 : (7#usize * 0#usize : Result Usize) = ok 0#usize := by
  apply ok_of_spec; step*
theorem usize_mul_7_1 : (7#usize * 1#usize : Result Usize) = ok 7#usize := by
  apply ok_of_spec; step*
theorem usize_add_0_1 : (0#usize + 1#usize : Result Usize) = ok 1#usize := by
  apply ok_of_spec; step*
theorem usize_add_1_1 : (1#usize + 1#usize : Result Usize) = ok 2#usize := by
  apply ok_of_spec; step*
theorem u64_shl_0 (x : U64) : (x <<< 0#usize : Result U64) = ok x := by
  apply ok_of_spec; step*

/-- One unrolling of the extracted scan loop. -/
theorem decode_u64_scan_loop_unfold (input : Slice U8)
    (policy : Generated.decode.DecodePolicy) (acc : U64) (i : Usize) :
    Generated.decode.decode_u64_scan_loop input policy acc i =
      (do
        let r ← Generated.decode.decode_u64_scan_loop.body input policy acc i
        match r with
        | .cont s => Generated.decode.decode_u64_scan_loop input policy s.1 s.2
        | .done x => ok x) := by
  unfold Generated.decode.decode_u64_scan_loop
  rw [loop]
  simp only
  congr 1
  funext r
  cases r <;> rfl

theorem index_ok (input : Slice U8) (i : Usize) (h : i.val < input.length) :
    input.index_usize i = ok input.val[i.val] := by
  simp [Slice.index_usize, getElem?_pos, h]

theorem u64_shl_7 (x : U64) : (x <<< 7#usize : Result U64) = ok ⟨x.bv <<< 7⟩ := by
  apply ok_of_spec
  step*
  rw [UScalar.eq_equiv_bv_eq]
  simp_all

/-- First scan iteration: a terminator returns, a continuation byte moves to index 1. -/
theorem scan_first (input : Slice U8) (policy : Generated.decode.DecodePolicy)
    (h : 0 < input.length) :
    Generated.decode.decode_u64_scan_loop input policy 0#u64 0#usize =
      if input.val[0].val &&& 128 = 0 then
        ok (.Ok { value := UScalar.cast .U64 (input.val[0] &&& 127#u8), consumed := 1#usize,
                  canonical := true })
      else
        Generated.decode.decode_u64_scan_loop input policy
          (UScalar.cast .U64 (input.val[0] &&& 127#u8)) 1#usize := by
  rw [decode_u64_scan_loop_unfold]
  unfold Generated.decode.decode_u64_scan_loop.body
  have hz : (0#usize) ≠ input.len := by scalar_tac
  have hb := index_ok input 0#usize (by scalar_tac)
  cases policy <;>
    by_cases hc : input.val[0].val &&& 128 = 0 <;>
    simp_all [lift, usize_mul_7_0, usize_add_0_1, u64_shl_0,
      Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]

/-- Second scan iteration, for any accumulator. -/
theorem scan_second (input : Slice U8) (policy : Generated.decode.DecodePolicy) (acc : U64)
    (h : 1 < input.length) :
    Generated.decode.decode_u64_scan_loop input policy acc 1#usize =
      if input.val[1].val &&& 128 = 0 then
        match policy with
        | .Canonical =>
          if input.val[1].val &&& 127 = 0 then
            ok (.Err { kind := .NonCanonical, consumed := 2#usize })
          else
            ok (.Ok { value := acc ||| ⟨(UScalar.cast .U64 (input.val[1] &&& 127#u8)).bv <<< 7⟩,
                      consumed := 2#usize, canonical := true })
        | .BoundedNonCanonical =>
            ok (.Ok { value := acc ||| ⟨(UScalar.cast .U64 (input.val[1] &&& 127#u8)).bv <<< 7⟩,
                      consumed := 2#usize, canonical := !(input.val[1].val &&& 127 = 0) })
      else
        Generated.decode.decode_u64_scan_loop input policy
          (acc ||| ⟨(UScalar.cast .U64 (input.val[1] &&& 127#u8)).bv <<< 7⟩) 2#usize := by
  rw [decode_u64_scan_loop_unfold]
  unfold Generated.decode.decode_u64_scan_loop.body
  have hz : (1#usize) ≠ input.len := by scalar_tac
  have hb := index_ok input 1#usize (by scalar_tac)
  cases policy <;>
    by_cases hc : input.val[1].val &&& 128 = 0 <;>
    by_cases hp : input.val[1].val &&& 127 = 0 <;>
    simp_all [lift, usize_mul_7_1, usize_add_1_1, u64_shl_7,
      Generated.decode.DecodePolicy.read_discriminant,
      Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]
  all_goals (rw [UScalar.eq_equiv]; simp_all)

/-- The inline one/two-byte fast path returns exactly what the shared scan
    returns, for every slice and both policies; the scan carries all proofs. -/
theorem decode_u64_eq_scan (input : Slice U8) (policy : Generated.decode.DecodePolicy) :
    Generated.decode.decode_u64 input policy =
      Generated.decode.decode_u64_scan input policy := by
  unfold Generated.decode.decode_u64 Generated.decode.decode_u64_scan
  by_cases h0 : input.length = 0
  · have : input.len = 0#usize := by scalar_tac
    simp [this]
  have hv0 : 0 < input.val.length := by scalar_tac
  have hb0 := index_ok input 0#usize (by scalar_tac)
  have hl0 : input.len ≠ 0#usize := by scalar_tac
  rw [scan_first input policy (by omega)]
  by_cases hc0 : input.val[0].val &&& 128 = 0
  · have e0 : (input.len != 0#usize) = true := by simpa using hl0
    have c0 : input.val[0] &&& 128#u8 = 0#u8 := by rw [UScalar.eq_equiv]; simpa using hc0
    simp [hb0, lift, e0, c0, hc0]
  have e0 : (input.len != 0#usize) = true := by simpa using hl0
  have c0 : ¬ input.val[0] &&& 128#u8 = 0#u8 := by rw [UScalar.eq_equiv]; simpa using hc0
  by_cases h1 : input.length = 1
  · have e1 : input.len = 1#usize := by scalar_tac
    simp [hb0, lift, c0, hc0, e1]
  have hv1 : 1 < input.val.length := by scalar_tac
  have hb1 := index_ok input 1#usize (by scalar_tac)
  have hl1 : input.len ≠ 1#usize := by scalar_tac
  have e1 : (input.len != 1#usize) = true := by simpa using hl1
  rw [scan_second input policy _ (by omega)]
  simp only [hb0, hb1, lift, e0, hc0, e1, bind_ok, if_true, if_false, u64_shl_7]
  have hc1' : (input.val[1] &&& 128#u8 = 0#u8) ↔ (input.val[1].val &&& 128 = 0) := by
    rw [UScalar.eq_equiv]; simp
  have hp1' : (input.val[1] &&& 127#u8 = 0#u8) ↔ (input.val[1].val &&& 127 = 0) := by
    rw [UScalar.eq_equiv]; simp
  cases policy <;>
    by_cases hc1 : input.val[1].val &&& 128 = 0 <;>
    by_cases hp1 : input.val[1].val &&& 127 = 0 <;>
    simp [c0, hc1, hp1, hc1', hp1', Generated.decode.DecodePolicy.read_discriminant,
      Generated.decode.DecodePolicy.Insts.CoreCmpPartialEqDecodePolicy.eq]

end Bited.Refinement
