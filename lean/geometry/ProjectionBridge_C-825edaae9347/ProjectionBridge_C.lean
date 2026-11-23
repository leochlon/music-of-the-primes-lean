import Mathlib

noncomputable section
namespace GeometricTraceC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [E.HasOrthogonalProjection]

/-- The actual orthogonal projection onto the complement of the geometric space. -/
def P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - E.starProjection

theorem P_eq_orthogonal : P E = Eᗮ.starProjection :=
  (Submodule.starProjection_orthogonal E).symm

theorem P_kills {x : H} (hx : x ∈ E) : P E x = 0 := by
  change x - E.starProjection x = 0
  rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

/-- Convolution preserves E, which is enough for compression in the required order. -/
theorem compression (A : H →L[ℂ] H) (hA : ∀ x ∈ E, A x ∈ E) :
    (P E).comp A = ((P E).comp A).comp (P E) := by
  ext x
  have hz : P E (A (E.starProjection x)) = 0 :=
    P_kills E (hA _ (E.starProjection_apply_mem x))
  change P E (A x) = P E (A (x - E.starProjection x))
  rw [map_sub, map_sub, hz, sub_zero]

/-- The nonzero constant term is essential in the weighted translation estimate. -/
theorem translation_weight_core (t u : ℝ) :
    1 + (t + u)^2 ≤ 2 * (1 + t^2) * (1 + u^2) := by
  nlinarith [sq_nonneg (t - u), sq_nonneg (t * u)]

end GeometricTraceC
#print axioms GeometricTraceC.P_eq_orthogonal
#print axioms GeometricTraceC.compression
#print axioms GeometricTraceC.translation_weight_core
