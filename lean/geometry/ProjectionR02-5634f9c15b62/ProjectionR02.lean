import Mathlib

namespace GeometryR02

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- One-sided compression needs only invariance of the kernel, not commutation. -/
theorem compression_of_invariant_kernel (P A : H →L[ℂ] H)
    (hP : P.comp P = P)
    (hInv : ∀ x : H, P x = 0 → P (A x) = 0) :
    P.comp A = (P.comp A).comp P := by
  ext x
  have hx : P (x - P x) = 0 := by
    have hp := congrArg (fun T : H →L[ℂ] H => T x) hP
    simpa only [ContinuousLinearMap.comp_apply, map_sub, sub_eq_zero] using hp.symm
  have hz := hInv (x - P x) hx
  simpa only [map_sub, sub_eq_zero, ContinuousLinearMap.comp_apply] using hz

/-- The quotient intertwiner gives the requested operator order. -/
theorem quotient_factorization {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (A P : H →L[ℂ] H) (q : H →L[ℂ] Q) (j : Q →L[ℂ] H) (B : Q →L[ℂ] Q)
    (hP : j.comp q = P) (hB : q.comp A = B.comp q) :
    P.comp A = j.comp (B.comp q) := by
  rw [← hP, ContinuousLinearMap.comp_assoc, hB]

#print axioms compression_of_invariant_kernel
#print axioms quotient_factorization
#check Submodule.starProjection
#check Submodule.starProjection_apply_mem
#check Submodule.sub_starProjection_mem_orthogonal

end GeometryR02
