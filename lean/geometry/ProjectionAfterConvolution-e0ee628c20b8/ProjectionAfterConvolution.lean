import Mathlib

noncomputable section

namespace GeometricTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [E.HasOrthogonalProjection]

/-- Complement of the genuine orthogonal projector, in the original Hilbert metric. -/
def spectralProjection : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - E.starProjection

theorem spectralProjection_vanishes {x : H} (hx : x ∈ E) :
    spectralProjection E x = 0 := by
  change x - E.starProjection x = 0
  rw [Submodule.starProjection_eq_self_iff.mpr hx, sub_self]

/-- Only invariance of E is needed; no commutation with the projector is assumed. -/
theorem projection_after_convolution (B : H →L[ℂ] H)
    (hB : ∀ x ∈ E, B x ∈ E) :
    (spectralProjection E).comp B =
      ((spectralProjection E).comp B).comp (spectralProjection E) := by
  ext x
  have hx : E.starProjection x ∈ E := (E.orthogonalProjection x).property
  have hz : spectralProjection E (B (E.starProjection x)) = 0 :=
    spectralProjection_vanishes E (hB _ hx)
  change spectralProjection E (B x) =
    spectralProjection E (B (x - E.starProjection x))
  rw [map_sub, map_sub, hz, sub_zero]

theorem weighted_translation_core (u v : ℝ) :
    1 + (u + v)^2 ≤ 2 * (1 + u^2) * (1 + v^2) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (u * v)]

def inverseTest {G : Type*} [Group G] (f : G → ℂ) : G → ℂ := fun x => f x⁻¹

theorem inverse_log_test {G : Type*} [Group G] (ell : G → ℝ)
    (hell : ∀ x, ell x⁻¹ = -ell x) (phi : G → ℂ) :
    inverseTest (fun x => (ell x : ℂ) * phi x) =
      fun x => -(ell x : ℂ) * inverseTest phi x := by
  funext x
  simp [inverseTest, hell]

end GeometricTrace

#print axioms GeometricTrace.projection_after_convolution
#print axioms GeometricTrace.weighted_translation_core
#print axioms GeometricTrace.inverse_log_test
