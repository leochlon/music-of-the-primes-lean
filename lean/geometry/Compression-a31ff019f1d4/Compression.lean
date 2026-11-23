import Mathlib

set_option linter.unusedSectionVars false

noncomputable section

namespace GeometricTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def geometric (V : Submodule ℂ H) [CompleteSpace V] : H →L[ℂ] H :=
  V.subtypeL.comp V.orthogonalProjection

/-- The genuine complementary orthogonal projection, in the given Hilbert metric. -/
def spectral (V : Submodule ℂ H) [CompleteSpace V] : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - geometric V

theorem spectral_vanish (V : Submodule ℂ H) [CompleteSpace V] (x : V) :
    spectral V (x : H) = 0 := by
  simp [spectral, geometric, Submodule.orthogonalProjection_mem_subspace_eq_self]

/-- Invariance suffices for projection after convolution; no commutation is assumed. -/
theorem projection_after_invariant_operator
    (V : Submodule ℂ H) [CompleteSpace V] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ V, A x ∈ V) :
    (spectral V).comp A = ((spectral V).comp A).comp (spectral V) := by
  ext x
  have hx : A (geometric V x) ∈ V := hA _ (V.orthogonalProjection x).property
  have hz : spectral V (A (geometric V x)) = 0 :=
    spectral_vanish V ⟨A (geometric V x), hx⟩
  change spectral V (A x) = spectral V (A (x - geometric V x))
  rw [map_sub, map_sub, hz, sub_zero]

variable {QH : Type*} [NormedAddCommGroup QH] [NormedSpace ℂ QH]

/-- An explicit factorization implication; construction of Q, S, B is separate. -/
theorem quotient_factorization (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (Q : H →L[ℂ] QH) (S : QH →L[ℂ] H)
    (B : QH →L[ℂ] QH)
    (hSQ : S.comp Q = spectral V) (hQA : Q.comp A = B.comp Q) :
    (spectral V).comp A = (S.comp B).comp Q := by
  rw [← hSQ, ContinuousLinearMap.comp_assoc, hQA,
    ← ContinuousLinearMap.comp_assoc]

end GeometricTrace

#print axioms GeometricTrace.projection_after_invariant_operator
#print axioms GeometricTrace.quotient_factorization
