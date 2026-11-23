import Mathlib

/- Round 173 B. Named premise: closed-subspace Bochner convolution invariance
   and the quotient intertwining used at manuscript 27711--27728.
   This file does not assume or prove quotient nuclearity. -/

run_cmd do
  let env ← Lean.getEnv
  for (n, _) in env.constants.toList do
    let t := n.toString
    if (t.splitOn "mkQ").length > 1 || (t.splitOn "liftQ").length > 1 ||
       (t.splitOn "integral_mem").length > 1 ||
       (t.splitOn "quotientEquiv").length > 1 ||
       (t.splitOn "isCompl").length > 1 && (t.splitOn "orthogonal").length > 1 then
      Lean.logInfo m!"{n}"

namespace Round173B
variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Typed algebra in (10.4.2.5); no nuclearity premise is asserted. -/
theorem typed_factorisation
    (Q : H →L[ℂ] E) (S : E →L[ℂ] H) (P A : H →L[ℂ] H)
    (B : E →L[ℂ] E) (hP : S.comp Q = P) (hA : Q.comp A = B.comp Q) :
    P.comp A = S.comp (B.comp Q) := by
  rw [← hP, ContinuousLinearMap.comp_assoc, hA]
end Round173B
#check Round173B.typed_factorisation
#print axioms Round173B.typed_factorisation
