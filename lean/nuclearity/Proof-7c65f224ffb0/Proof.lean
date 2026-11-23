import Mathlib

/-! Round 88 G. Structural reduction for the missing global bound.
This does not construct the genuine weighted idele-class operator and
does not assert nuclearity or summability. In application A is convolution
and P is the manuscript's spectral projection. -/

namespace NuclearBoundR88G

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem convolution_after_projection_split
    (A P : E →L[ℂ] E) :
    A.comp P = P.comp (A.comp P) +
      (ContinuousLinearMap.id ℂ E - P).comp (A.comp P) := by
  ext x
  simp

theorem lifted_vector_norm_split (A P : E →L[ℂ] E) (u : E) :
    ‖A u‖ ≤ ‖P (A u)‖ + ‖A u - P (A u)‖ := by
  calc
    ‖A u‖ = ‖P (A u) + (A u - P (A u))‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

#check convolution_after_projection_split
#check lifted_vector_norm_split
#print axioms convolution_after_projection_split
#print axioms lifted_vector_norm_split

end NuclearBoundR88G
