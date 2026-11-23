import Mathlib

/- Independent adaptation of the orthogonal-subspace identities used in ALPO
GroundTheory/AutomorphicForms/CuspidalProjection/OrthogonalProjectionOntoCompSubtypeL.lean.
This proves the operator-order step, not the adelic trace theorem. -/
set_option linter.unusedSectionVars false
noncomputable section
namespace GeometricTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (M : Submodule ℂ H) [CompleteSpace M]

def geom : H →L[ℂ] H := M.subtypeL.comp M.orthogonalProjection
def spec : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - geom M

theorem geom_mem (x : H) : geom M x ∈ M := (M.orthogonalProjection x).property

theorem geom_fix (x : H) (hx : x ∈ M) : geom M x = x := by
  exact congrArg (fun y : M => (y : H))
    (M.orthogonalProjection_mem_subspace_eq_self (⟨x, hx⟩ : M))

theorem spec_kills (x : H) (hx : x ∈ M) : spec M x = 0 := by
  change x - geom M x = 0
  rw [geom_fix M x hx, sub_self]

/-- Convolution first, genuine complementary orthogonal projection second.
Only invariance of the geometric subspace is required; commutation is not assumed. -/
theorem projection_after_convolution (A : H →L[ℂ] H)
    (hA : ∀ x ∈ M, A x ∈ M) :
    (spec M).comp A = ((spec M).comp A).comp (spec M) := by
  ext x
  change A x - geom M (A x) =
    A (x - geom M x) - geom M (A (x - geom M x))
  rw [map_sub, map_sub, geom_fix M _ (hA _ (geom_mem M x))]
  abel

/-- Transporting a quotient operator by a section gives the requested order. -/
theorem quotient_factorization {QH : Type*} [NormedAddCommGroup QH]
    [NormedSpace ℂ QH] (Q : H →L[ℂ] QH) (S : QH →L[ℂ] H)
    (A : H →L[ℂ] H) (B : QH →L[ℂ] QH)
    (hSQ : S.comp Q = spec M) (hQA : Q.comp A = B.comp Q) :
    (spec M).comp A = S.comp (B.comp Q) := by
  rw [← hSQ, ContinuousLinearMap.comp_assoc, hQA]

/-- Correct change from the kernel against weighted measure to the Haar kernel. -/
theorem kernel_weight_cancel (k : ℂ) (w : ℝ) (hw : w ≠ 0) :
    (k / (w : ℂ)) * (w : ℂ) = k := by
  exact div_mul_cancel₀ k (Complex.ofReal_ne_zero.mpr hw)

end GeometricTrace
