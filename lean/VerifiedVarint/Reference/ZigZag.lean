import Aeneas

namespace VerifiedVarint.Reference
open Aeneas.Std

/-- Fixed-width executable bit-vector model, separate from the extracted code. -/
def zigzag64 (n : I64) : U64 :=
  ⟨(n.bv <<< 1) ^^^ (n.bv.sshiftRight 63)⟩

def unzigzag64 (u : U64) : I64 :=
  ⟨(u.bv >>> 1) ^^^ (-(u.bv &&& 1))⟩

end VerifiedVarint.Reference
