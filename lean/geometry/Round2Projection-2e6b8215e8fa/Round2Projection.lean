import Mathlib

noncomputable section
namespace GeometricTraceRound2
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The actual orthogonal projection onto a closed geometric subspace. -/
def geometric (E : Submodule ℂ H) [CompleteSpace E] : H →L[ℂ] H :=
  E.starProjection

def spectral (E : Submodule ℂ H) [CompleteSpace E] : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - geometric E

/-- Adapted from ALPO's `pc_rop_pc`; no unitary-action assumption. -/
theorem geometric_invariance (E : Submodule ℂ H) [CompleteSpace E]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ E, A x ∈ E) :
    (geometric E).comp (A.comp (geometric E)) = A.comp (geometric E) := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (hA _ (E.starProjection_apply_mem x))

/-- Invariance suffices for compression in the user's operator order. -/
theorem spectral_compression (E : Submodule ℂ H) [CompleteSpace E]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ E, A x ∈ E) :
    (spectral E).comp (A.comp (spectral E)) = (spectral E).comp A := by
  have h := geometric_invariance E A hA
  ext x
  have hx : geometric E (A (geometric E x)) = A (geometric E x) :=
    DFunLike.congr_fun h x
  simp only [spectral, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hx]
  abel

/-- The order discrepancy takes values in the genuine geometric space. -/
theorem discrepancy_mem (E : Submodule ℂ H) [CompleteSpace E]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ E, A x ∈ E) (x : H) :
    A (spectral E x) - spectral E (A x) ∈ E := by
  have hx : A (spectral E x) - spectral E (A x) =
      geometric E (A x) - A (geometric E x) := by
    simp only [spectral, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
    abel
  rw [hx]
  exact E.sub_mem (E.starProjection_apply_mem _) (hA _ (E.starProjection_apply_mem _))
end GeometricTraceRound2
#print axioms GeometricTraceRound2.spectral_compression
#print axioms GeometricTraceRound2.discrepancy_mem
