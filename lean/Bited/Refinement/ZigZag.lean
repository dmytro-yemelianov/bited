import Bited.Generated.Funs
import Bited.Reference.ZigZag
import Bited.Spec.ZigZag

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

/-- The sign mask selects the doubled magnitude or its bitwise complement. -/
theorem zigzag64_sign_split (x : BitVec 64) :
    (x <<< 1) ^^^ x.sshiftRight 63 =
      if x.msb then ~~~(x <<< 1) else x <<< 1 := by
  have hmask : x.sshiftRight 63 = if x.msb then BitVec.allOnes 64 else (0 : BitVec 64) := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sshiftRight]
    have hlo := BitVec.le_toInt x
    have hhi := BitVec.toInt_lt (x := x)
    have hi := BitVec.toInt_eq_msb_cond x
    cases hs : x.msb <;> simp_all [Int.shiftRight_eq_div_pow] <;> omega
  rw [hmask]
  cases x.msb <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact BitVec.xor_zero
  · exact BitVec.xor_allOnes

/-- The executable model agrees with the mathematical contract for every i64. -/
theorem zigzag64_bit_model_value (n : I64) :
    (Reference.zigzag64 n).val = Spec.zigzag n.val := by
  have hb := n.bv.isLt
  have hi := BitVec.toInt_eq_msb_cond n.bv
  have hm := BitVec.msb_eq_true_iff_two_mul_ge (x := n.bv)
  change ((n.bv <<< 1) ^^^ n.bv.sshiftRight 63).toNat =
    Spec.zigzag n.bv.toInt
  rw [zigzag64_sign_split]
  cases hs : n.bv.msb <;>
    simp only [hs, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_not,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one] at *
  · rw [hi]
    norm_num at hb hm ⊢
    unfold Spec.zigzag
    split_ifs <;> omega
  · rw [hi]
    norm_num at hb hm ⊢
    unfold Spec.zigzag
    split_ifs <;> omega

theorem zigzag64_to_bit_model (n : I64) :
    Generated.zigzag.zigzag_i64_to_u64 n = ok (Reference.zigzag64 n) := by
  simp [Generated.zigzag.zigzag_i64_to_u64, Reference.zigzag64,
    HShiftLeft.hShiftLeft, HShiftRight.hShiftRight,
    UScalar.shiftLeft_IScalar, UScalar.shiftLeft,
    IScalar.shiftRight_IScalar, IScalar.shiftRight,
    IScalar.hcast, IScalar.toNat, lift,
    -BitVec.shiftLeft_eq, -BitVec.ushiftRight_eq]
  rfl

theorem zigzag64_refines (n : I64) :
    Generated.zigzag.zigzag_i64_to_u64 n
      ⦃ u => u.val = Spec.zigzag n.val ⦄ := by
  rw [zigzag64_to_bit_model]
  simpa using zigzag64_bit_model_value n

theorem unzigzag64_parity_split (x : BitVec 64) :
    (x >>> 1) ^^^ -(x &&& (1 : BitVec 64)) =
      if x.toNat % 2 = 0 then x >>> 1 else ~~~(x >>> 1) := by
  have hm : x &&& (1 : BitVec 64) = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp
    omega
  rw [hm]
  by_cases h : x.toNat % 2 = 0
  · simp [h]
  · have h1 : x.toNat % 2 = 1 := by omega
    simp only [h1]
    change (x >>> 1) ^^^ -(1 : BitVec 64) = ~~~(x >>> 1)
    change (x >>> 1) ^^^ BitVec.allOnes 64 = ~~~(x >>> 1)
    exact BitVec.xor_allOnes

theorem unzigzag64_bit_model_value (u : U64) :
    (Reference.unzigzag64 u).val = Spec.unzigzag u.val := by
  change ((u.bv >>> 1) ^^^ -(u.bv &&& (1 : BitVec 64))).toInt = Spec.unzigzag u.bv.toNat
  rw [unzigzag64_parity_split]
  have hb := u.bv.isLt
  unfold Spec.unzigzag
  by_cases h : u.bv.toNat % 2 = 0 <;>
    simp only [h, ↓reduceIte, BitVec.toInt_eq_msb_cond, BitVec.msb_ushiftRight,
      BitVec.msb_not, BitVec.toNat_not, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow]
  all_goals norm_num at hb ⊢
  all_goals omega

theorem zigzag64_bit_model_right_inverse (u : U64) :
    Reference.zigzag64 (Reference.unzigzag64 u) = u := by
  apply UScalar.eq_of_val_eq
  rw [zigzag64_bit_model_value, unzigzag64_bit_model_value, Spec.zigzag_right_inverse]

theorem zigzag64_bit_model_left_inverse (n : I64) :
    Reference.unzigzag64 (Reference.zigzag64 n) = n := by
  apply IScalar.eq_of_val_eq
  rw [unzigzag64_bit_model_value, zigzag64_bit_model_value, Spec.zigzag_left_inverse]

/-- Casting the low-bit mask can only produce zero or one. -/
theorem unzigzag64_mask_cases (u : U64) (i2 : U64) (i3 : I64)
    (h2 : i2.bv = u.bv &&& 1#u64.bv)
    (h3 : i3 = UScalar.hcast .I64 i2) :
    i3 = 0#i64 ∨ i3 = 1#i64 := by
  have hm : i2.val = u.val % 2 := by
    have h := congrArg BitVec.toNat h2
    change i2.bv.toNat = (u.bv &&& (1 : BitVec 64)).toNat at h
    rw [BitVec.toNat_and] at h
    change i2.val = u.val &&& 1 at h
    simpa only [Nat.and_one_is_mod] using h
  have hc : i2.val = 0 ∨ i2.val = 1 := by omega
  rcases hc with h | h
  · have hz : i2 = 0#u64 := UScalar.eq_of_val_eq h
    left
    rw [h3, hz]
    rfl
  · have hz : i2 = 1#u64 := UScalar.eq_of_val_eq h
    right
    rw [h3, hz]
    rfl

theorem unzigzag64_to_bit_model (u : U64) :
    Generated.zigzag.zigzag_u64_to_i64 u
      ⦃ n => n = Reference.unzigzag64 u ⦄ := by
  unfold Generated.zigzag.zigzag_u64_to_i64
  step*
  · have h := unzigzag64_mask_cases u i2 i3 i2_post1 i3_post
    rcases h with h | h <;> rw [h] <;> simp [I64.min_eq]
  · have h := unzigzag64_mask_cases u i2 i3 i2_post1 i3_post
    rcases h with h | h
    · have h4 : i4 = 0#i64 := by
        apply IScalar.eq_of_val_eq
        simpa [h] using i4_post
      rw [h4]
      have hb1 : i1.bv = i.bv := by rw [i1_post]; rfl
      have hshift : i1.bv = u.bv >>> 1 := hb1.trans i_post1
      have hb3 : i3.bv = i2.bv := by rw [i3_post]; rfl
      have hm : u.bv &&& (1 : BitVec 64) = i3.bv := by
        rw [hb3]
        exact i2_post1.symm
      rw [h] at hm

      unfold Reference.unzigzag64
      apply I64.bv_eq_imp_eq
      change u.bv &&& (1 : BitVec 64) = 0 at hm
      change i1.bv ^^^ (0 : BitVec 64) = (u.bv >>> 1) ^^^ -(u.bv &&& (1 : BitVec 64))
      rw [hshift, hm]
      rfl
    · have h4 : i4 = (-1)#i64 := by
        apply IScalar.eq_of_val_eq
        simpa [h] using i4_post
      rw [h4]
      have hb1 : i1.bv = i.bv := by rw [i1_post]; rfl
      have hshift : i1.bv = u.bv >>> 1 := hb1.trans i_post1
      have hb3 : i3.bv = i2.bv := by rw [i3_post]; rfl
      have hm : u.bv &&& (1 : BitVec 64) = i3.bv := by
        rw [hb3]
        exact i2_post1.symm
      rw [h] at hm

      unfold Reference.unzigzag64
      apply I64.bv_eq_imp_eq
      change u.bv &&& (1 : BitVec 64) = 1 at hm
      change i1.bv ^^^ (-1 : BitVec 64) = (u.bv >>> 1) ^^^ -(u.bv &&& (1 : BitVec 64))
      rw [hshift, hm]

theorem unzigzag64_refines (u : U64) :
    Generated.zigzag.zigzag_u64_to_i64 u
      ⦃ n => n.val = Spec.unzigzag u.val ⦄ := by
  apply WP.spec_mono (unzigzag64_to_bit_model u)
  intro n hn
  rw [hn]
  exact unzigzag64_bit_model_value u

/-- Round trips of the actual extracted functions, with totality. -/
theorem zigzag64_rust_left_inverse (n : I64) :
    (do let u ← Generated.zigzag.zigzag_i64_to_u64 n
        Generated.zigzag.zigzag_u64_to_i64 u)
      ⦃ m => m = n ⦄ := by
  apply WP.spec_bind (Pₘ := fun u => u = Reference.zigzag64 n)
  · rw [zigzag64_to_bit_model]
    simp
  · intro u hu
    rw [hu]
    apply WP.spec_mono (unzigzag64_to_bit_model (Reference.zigzag64 n))
    intro m hm
    rw [hm, zigzag64_bit_model_left_inverse]

theorem zigzag64_rust_right_inverse (u : U64) :
    (do let n ← Generated.zigzag.zigzag_u64_to_i64 u
        Generated.zigzag.zigzag_i64_to_u64 n)
      ⦃ v => v = u ⦄ := by
  apply WP.spec_bind (unzigzag64_to_bit_model u)
  intro n hn
  rw [hn, zigzag64_to_bit_model, zigzag64_bit_model_right_inverse]
  simp

/-- Kernel-checked feasibility endpoint; no native evaluation axiom. -/
theorem zigzag64_signed_min :
    Generated.zigzag.zigzag_i64_to_u64 (-9223372036854775808)#i64 =
      ok 18446744073709551615#u64 := by
  rw [zigzag64_to_bit_model]
  rfl

theorem unzigzag64_unsigned_max :
    Generated.zigzag.zigzag_u64_to_i64 18446744073709551615#u64
      ⦃ n => n = (-9223372036854775808)#i64 ⦄ := by
  unfold Generated.zigzag.zigzag_u64_to_i64
  step*
  · have h3 : i3 = 1#i64 := by bv_tac 64
    rw [h3]
    simp [I64.min_eq]
  · have h1 : i1 = 9223372036854775807#i64 := by bv_tac 64
    have h3 : i3 = 1#i64 := by bv_tac 64
    have h4 : i4 = (-1)#i64 := by
      apply IScalar.eq_of_val_eq
      simpa [h3] using i4_post
    rw [h1, h4]
    rfl

end Bited.Refinement
