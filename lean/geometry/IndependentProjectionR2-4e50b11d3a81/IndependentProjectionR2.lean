import Mathlib

noncomputable section
namespace IndependentGeometryR2
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def geom (M : Submodule ℂ H) [CompleteSpace M] : H →L[ℂ] H :=
  M.subtypeL.comp M.orthogonalProjection

def spec (M : Submodule ℂ H) [CompleteSpace M] : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - geom M

theorem spec_kills (M : Submodule ℂ H) [CompleteSpace M] (y : M) :
    spec M (y : H) = 0 := by
  simp [spec, geom, Submodule.orthogonalProjection_mem_subspace_eq_self]

/-- Convolution is applied first. Invariance of the geometric subspace suffices;
    commutation of convolution with orthogonal projection is not assumed. -/
theorem spectral_after_convolution (M : Submodule ℂ H) [CompleteSpace M]
    (A : H →L[ℂ] H) (hA : ∀ y ∈ M, A y ∈ M) :
    (spec M).comp A = ((spec M).comp A).comp (spec M) := by
  ext x
  have hk : spec M (A (geom M x)) = 0 :=
    spec_kills M ⟨A (geom M x), hA _ (M.orthogonalProjection x).property⟩
  change spec M (A x) = spec M (A (x - geom M x))
  rw [map_sub, map_sub, hk, sub_zero]

/-- A boundary jet with degree m requires the STRICT inequality 2m < s-1.
    This arithmetic check identifies the endpoint excluded by integrability. -/
theorem boundary_endpoint_excluded (m : ℕ) :
    ¬ ((2 : ℝ) * m < ((2 : ℝ) * m + 1) - 1) := by
  linarith

end IndependentGeometryR2
