import Mathlib

/-! Round 88, D. Actual global nuclear bound is not yet proved.
This initial checkpoint records only the order of a rank-one lift after convolution.
The analytic lift and summability estimates remain open. -/

namespace GlobalNuclearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def liftedTerm (A : E →L[ℂ] E) (v : E) (η : E →L[ℂ] ℂ) : E →L[ℂ] E :=
  (η.smulRight v).comp A

-- This is the reverse order: the authentic A ∘ P instead uses η.smulRight (A v).
theorem convolution_after_rankOne (A : E →L[ℂ] E) (v : E)
    (η : E →L[ℂ] ℂ) :
    A.comp (η.smulRight v) = η.smulRight (A v) := by
  ext x
  simp

#check convolution_after_rankOne
#print axioms convolution_after_rankOne
end GlobalNuclearBound

namespace GlobalNuclearBound
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
/-- The missing term when quotient invariance provides P A = P A P.
This is an exact algebraic reduction, not a nuclearity assertion. -/
theorem missingOffDiagonal (A P : E →L[ℂ] E)
    (h : ∀ x, P (A x) = P (A (P x))) :
    A.comp P = P.comp A +
      (ContinuousLinearMap.id ℂ E - P).comp (A.comp P) := by
  ext x
  change A (P x) = P (A x) + (A (P x) - P (A (P x)))
  rw [h x]
  abel
#check missingOffDiagonal
#print axioms missingOffDiagonal
end GlobalNuclearBound
