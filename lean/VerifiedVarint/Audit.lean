import VerifiedVarint.Public
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  for entry in env.constants.toList do
    let declName := entry.1
    let declInfo := entry.2
    if (`VerifiedVarint).isPrefixOf declName then
      let axioms ← collectAxioms declName
      records := records.push <| Json.mkObj [
        ("name", toJson declName.toString),
        ("kind", toJson (if declInfo.isTheorem then "theorem" else "declaration")),
        ("axioms", toJson (axioms.map Name.toString)),
        ("statement", toJson (toString (repr declInfo.type))) ]
  logInfo m!"VVZ_AUDIT {Json.compress (toJson records)}"
