import Bited.Refinement.ZigZag

namespace Bited.Refinement
open Aeneas Aeneas.Std Aeneas.Std.Result

theorem i32_widen_value (n : I32) : (IScalar.cast .I64 n).val = n.val := by
  have h := IScalar.cast_inBounds_spec .I64 n (by scalar_tac)
  simpa only [lift, WP.spec_ok] using h

theorem u32_widen_value (u : U32) : (UScalar.cast .U64 u).val = u.val := by
  have h := UScalar.cast_inBounds_spec .U64 u (by scalar_tac)
  simpa only [lift, WP.spec_ok] using h

theorem zigzag32_refines (n : I32) :
    Generated.zigzag.zigzag_i32_to_u32 n ⦃ u => u.val = Spec.zigzag n.val ⦄ := by
  unfold Generated.zigzag.zigzag_i32_to_u32
  simp only [lift, bind_ok]
  apply WP.spec_bind (zigzag64_refines (IScalar.cast .I64 n))
  intro u hu
  have hn : Spec.signedDomain 32 n.val := by
    unfold Spec.signedDomain
    scalar_tac
  have hb := (Spec.zigzag_bounds 32 (by decide)).1 n.val hn
  have hu' : u.val = Spec.zigzag n.val := by simpa only [i32_widen_value] using hu
  have hc := UScalar.cast_inBounds_spec .U32 u (by
    unfold Spec.unsignedDomain at hb
    simp only [UScalar.max, UScalarTy.numBits]
    omega)
  simp only [lift, WP.spec_ok] at hc
  simp only [WP.spec_ok]
  omega

theorem unzigzag32_refines (u : U32) :
    Generated.zigzag.zigzag_u32_to_i32 u ⦃ n => n.val = Spec.unzigzag u.val ⦄ := by
  unfold Generated.zigzag.zigzag_u32_to_i32
  simp only [lift, bind_ok]
  apply WP.spec_bind (unzigzag64_refines (UScalar.cast .U64 u))
  intro n hn
  have hu : Spec.unsignedDomain 32 u.val := by
    unfold Spec.unsignedDomain
    scalar_tac
  have hb := (Spec.zigzag_bounds 32 (by decide)).2 u.val hu
  have hn' : n.val = Spec.unzigzag u.val := by simpa only [u32_widen_value] using hn
  have hc := IScalar.cast_inBounds_spec .I32 n (by
    unfold Spec.signedDomain at hb
    simp only [IScalar.min, IScalar.max, IScalarTy.numBits]
    omega)
  simp only [lift, WP.spec_ok] at hc
  simp only [WP.spec_ok]
  omega

theorem zigzag32_rust_left_inverse (n : I32) :
    (do let u ← Generated.zigzag.zigzag_i32_to_u32 n
        Generated.zigzag.zigzag_u32_to_i32 u) ⦃ m => m = n ⦄ := by
  apply WP.spec_bind (zigzag32_refines n)
  intro u hu
  apply WP.spec_mono (unzigzag32_refines u)
  intro m hm
  apply IScalar.eq_of_val_eq
  rw [hm, hu, Spec.zigzag_left_inverse]

theorem zigzag32_rust_right_inverse (u : U32) :
    (do let n ← Generated.zigzag.zigzag_u32_to_i32 u
        Generated.zigzag.zigzag_i32_to_u32 n) ⦃ v => v = u ⦄ := by
  apply WP.spec_bind (unzigzag32_refines u)
  intro n hn
  apply WP.spec_mono (zigzag32_refines n)
  intro v hv
  apply UScalar.eq_of_val_eq
  rw [hv, hn, Spec.zigzag_right_inverse]

end Bited.Refinement
