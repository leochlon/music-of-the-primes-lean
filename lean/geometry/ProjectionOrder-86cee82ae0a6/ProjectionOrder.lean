import Mathlib

/- The target projection is geometric: the complement of the orthogonal
projection onto a complete submodule. No commutation is assumed. -/
namespace GeometricTrace
set_option linter.unusedSectionVars false

noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (N : Submodule ℂ H) [CompleteSpace N]

def geomProjection : H →L[ℂ] H := N.subtypeL.comp N.orthogonalProjection
def specProjection : H →L[ℂ] H := ContinuousLinearMap.id ℂ H - geomProjection N

theorem geomProjection_mem (x : H) : geomProjection N x ∈ N :=
  (N.orthogonalProjection x).property

theorem specProjection_of_mem {x : H} (hx : x ∈ N) : specProjection N x = 0 := by
  have hp := N.orthogonalProjection_mem_subspace_eq_self (⟨x, hx⟩ : N)
  have he : geomProjection N x = x := congrArg (fun z : N => (z : H)) hp
  change x - geomProjection N x = 0
  rw [he, sub_self]

theorem convolution_then_projection (A : H →L[ℂ] H)
    (hN : ∀ x ∈ N, A x ∈ N) :
    (specProjection N).comp A =
      ((specProjection N).comp A).comp (specProjection N) := by
  ext x
  have hz : specProjection N (A (geomProjection N x)) = 0 :=
    specProjection_of_mem N (hN _ (geomProjection_mem N x))
  change specProjection N (A x) =
    specProjection N (A (x - geomProjection N x))
  rw [map_sub, map_sub, hz, sub_zero]

end
end GeometricTrace

#print axioms GeometricTrace.convolution_then_projection
