import Mathlib

/-! The two polar corrections for h = ell * k on the actual weighted space.
The adelic definitions, division by ell, and Haar integral evaluation are in
APPLICATION_R04.md. No equality with the projected trace is assumed. -/
noncomputable section
namespace GeometricTraceC.PolarBoundary

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Actual boundary operator once its compact defect vector and Mellin row
are constructed. Both maps have the original weighted Hilbert norm. -/
def correction (L₀ L₁ : H →L[ℂ] ℂ) (c₀ c₁ : H) : H →L[ℂ] H :=
  L₀.smulRight c₀ + L₁.smulRight c₁

theorem correction_apply (L₀ L₁ : H →L[ℂ] ℂ) (c₀ c₁ f : H) :
    correction L₀ L₁ c₀ c₁ f = L₀ f • c₀ + L₁ f • c₁ := rfl

/-- No independence or orthogonality of the two defect vectors is needed. -/
theorem correction_range (L₀ L₁ : H →L[ℂ] ℂ) (c₀ c₁ f : H) :
    correction L₀ L₁ c₀ c₁ f ∈ Submodule.span ℂ ({c₀,c₁} : Set H) := by
  apply Submodule.add_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- Diagonal of the two-dimensional cyclic factorization. The off-diagonal
pairings remain present; the trace does not depend on them. -/
theorem cyclic_matrix_trace (L₀ L₁ : H →L[ℂ] ℂ) (c₀ c₁ : H) :
    Matrix.trace (fun i j : Fin 2 => (![L₀,L₁] i) (![c₀,c₁] j)) =
      L₀ c₀ + L₁ c₁ := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- The Mellin boundary integral discharges these two scalar evaluations. -/
theorem evaluated_cyclic_trace (L₀ L₁ : H →L[ℂ] ℂ) (c₀ c₁ : H)
    (m₀ m₁ : ℂ) (h₀ : L₀ c₀ = m₀) (h₁ : L₁ c₁ = m₁) :
    Matrix.trace (fun i j : Fin 2 => (![L₀,L₁] i) (![c₀,c₁] j)) = m₀ + m₁ := by
  rw [cyclic_matrix_trace, h₀, h₁]

/-- The two rank-one factors used in the original ALPO row theorem really
have these rows, for its second-variable-linear inner-product convention. -/
theorem rank_one_row {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (e : ℂ) (r f : E) :
    inner ℂ (star e • r) f = e * inner ℂ r f := by
  simp [mul_comm]

theorem cyclic_row_density {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (e : ℂ) (r c : E) :
    inner ℂ (star e • r) (star e • c) =
      (e * star e) * inner ℂ r c := by
  simp [mul_comm, mul_left_comm, mul_assoc]

end GeometricTraceC.PolarBoundary
#print axioms GeometricTraceC.PolarBoundary.cyclic_matrix_trace
#print axioms GeometricTraceC.PolarBoundary.correction_range

#print axioms GeometricTraceC.PolarBoundary.rank_one_row
#print axioms GeometricTraceC.PolarBoundary.cyclic_row_density
