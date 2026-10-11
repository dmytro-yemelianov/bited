import VerifiedVarint.Spec.Bytes
import Lean.Elab.Tactic.Omega

namespace VerifiedVarint.Reference
open Spec

/-- Mathematical division-based encoder. It does not call the extracted model. -/
def encode (x : Nat) : List Byte :=
  if hx : x < 128 then [⟨x, by omega⟩]
  else ⟨x % 128 + 128, by omega⟩ :: encode (x / 128)
termination_by x
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

end VerifiedVarint.Reference
