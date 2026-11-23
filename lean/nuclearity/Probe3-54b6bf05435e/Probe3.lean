import Mathlib
open Lean in
run_cmd do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let s := n.toString
    if s.startsWith "Submodule." && ((s.splitOn "mkQ").length > 1 || (s.splitOn "liftQ").length > 1 || (s.splitOn "quotientEquiv").length > 1 || (s.splitOn "orthogonal").length > 1 && (s.splitOn "Quotient").length > 1 || s.endsWith "isCompl_orthogonal") then
      logInfo m!"{n} : {ci.type}"
