import Mathlib

namespace GeometricTrace

-- The exact integrability threshold on a boundary line, used in DERIVATION.md.
theorem boundary_exponent (s : ℝ) (m : ℕ) :
    (2 * (m : ℝ) - s < -1) ↔ (2 * (m : ℝ) + 1 < s) := by
  constructor <;> intro h <;> linarith

-- Includes inversion, conjugate inversion, and any fixed scalar weight.
-- ell is logarithmic norm: its inversion law is supplied explicitly.
def sharp {G : Type*} [Inv G] (q phi : G → ℂ) (x : G) : ℂ :=
  q x * phi x⁻¹

theorem sharp_log {G : Type*} [Inv G] (q phi ell : G → ℂ)
    (hell : ∀ x, ell x⁻¹ = -ell x) (x : G) :
    sharp q (fun y => ell y * phi y) x = -ell x * sharp q phi x := by
  simp only [sharp, hell]
  ring

-- This establishes the operator-order bridge, with its real invariance input exposed.
theorem projection_order {R : Type*} [Ring R] (A P : R)
    (hInv : P * A * (1 - P) = 0) : P * A * P = P * A := by
  have h : P * A - P * A * P = 0 := by simpa [mul_sub] using hInv
  exact (sub_eq_zero.mp h).symm

end GeometricTrace

#print axioms GeometricTrace.boundary_exponent
#print axioms GeometricTrace.sharp_log
#print axioms GeometricTrace.projection_order

namespace GeometricTrace

-- Adapted after independent publication from E's round-2 geometric_compression.
-- V is an actual submodule with its genuine orthogonal projection.
theorem actual_projection_order {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (hA : ∀ v ∈ V, A v ∈ V) :
    (ContinuousLinearMap.id ℂ H - V.starProjection).comp A =
      ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A).comp
        (ContinuousLinearMap.id ℂ H - V.starProjection) := by
  ext x
  have hm : A (V.starProjection x) ∈ V := hA _ (V.starProjection_apply_mem x)
  have hz : V.starProjection (A (V.starProjection x)) = A (V.starProjection x) :=
    V.starProjection_eq_self_iff.mpr hm
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hz]
  abel

#print axioms actual_projection_order
end GeometricTrace
