import VerifiedVarint.Refinement.DecodeArithmetic

namespace VerifiedVarint.Refinement

/-- A fifth payload uses at most four bits; all prior digits occupy lower bits. -/
theorem decode_digit_bounds32 (acc payload count : Nat) (hc : count < 5)
    (hp : payload < 128) (hlast : count = 4 → payload ≤ 15)
    (ha : acc < 2 ^ (7 * count)) : acc + payload * 2 ^ (7 * count) < 2 ^ 32 := by
  interval_cases count <;> norm_num at ha hlast ⊢ <;> omega

end VerifiedVarint.Refinement
