import Mathlib

/- Round 173 H: formalising the quotient/orthogonal identification in
   manuscript (10.4.2.5). No quotient nuclearity is assumed or claimed. -/
open scoped InnerProductSpace
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    let s := n.toString
    if (s.startsWith "Submodule." && ((s.splitOn "quotientEquiv").length > 1 ||
        (s.splitOn "orthogonalProjection").length > 1 ||
        (s.splitOn "liftQ").length > 1)) then
      logInfo m!"{n}"

#check Submodule.mkQ
#check Submodule.mapQ
#check Submodule.quotientEquivOfIsCompl
#check Submodule.orthogonalProjection
#check Submodule.norm_orthogonalProjection_apply_le
