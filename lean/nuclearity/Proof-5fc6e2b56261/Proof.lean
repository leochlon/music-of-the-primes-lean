import Mathlib

/-
Round 173 E. Manuscript 27158--27167: a fixed finite-rank block precomposed
with strongly convergent self-adjoint cutoffs converges with explicit finite
nuclear error cost. No total spectral summability or quotient nuclearity is
assumed or concluded. Native spectral-block and cutoff identification remain.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
open Filter
namespace Round173E
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A finite nuclear representation, with the actual functional norm cost. -/
def FiniteNuclearCost (T : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∃ (d : ℕ) (f : Fin d → H →L[ℂ] ℂ) (u : Fin d → H),
    T = ∑ i, (f i).smulRight (u i) ∧ ∑ i, ‖f i‖ * ‖u i‖ ≤ c

def block {d : ℕ} (u v : Fin d → H) : H →L[ℂ] H :=
  ∑ i, (innerSL ℂ (v i)).smulRight (u i)

theorem inner_functional_norm_le (v : H) : ‖innerSL ℂ v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
  intro x
  simpa only [innerSL_apply_apply] using (norm_inner_le_norm v x)

theorem block_finite_nuclear_cost {d : ℕ} (u v : Fin d → H) :
    FiniteNuclearCost (block u v) (∑ i, ‖v i‖ * ‖u i‖) := by
  refine ⟨d, fun i => innerSL ℂ (v i), u, rfl, ?_⟩
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (inner_functional_norm_le (v i)) (norm_nonneg (u i)))

theorem block_cutoff_error {d : ℕ} (u v : Fin d → H) (P : H →L[ℂ] H)
    (hself : ∀ x y, inner ℂ x (P y) = inner ℂ (P x) y) :
    (block u v).comp P - block u v = block u (fun i => P (v i) - v i) := by
  ext z
  simp [block, hself, sub_smul, Finset.sum_sub_distrib]

/-- The finite-block S1 repair: an explicit nuclear error representation has
cost tending to zero. Valid for nets, including the manuscript's finite-set net.
It does not claim that the sum of costs of infinitely many blocks is finite. -/
theorem finite_block_cutoffs_nuclear_error
    {J : Type*} (l : Filter J) {d : ℕ} (u v : Fin d → H)
    (P : J → H →L[ℂ] H)
    (hself : ∀ j x y, inner ℂ x (P j y) = inner ℂ (P j x) y)
    (hstrong : ∀ x, Tendsto (fun j => P j x) l (nhds x)) :
    (∀ j, FiniteNuclearCost ((block u v).comp (P j) - block u v)
      (∑ i, ‖P j (v i) - v i‖ * ‖u i‖)) ∧
    (∀ j, 0 ≤ ∑ i, ‖P j (v i) - v i‖ * ‖u i‖) ∧
    Tendsto (fun j => ∑ i, ‖P j (v i) - v i‖ * ‖u i‖) l (nhds 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    rw [block_cutoff_error u v (P j) (hself j)]
    exact block_finite_nuclear_cost u _
  · intro j
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · have hi : ∀ i : Fin d,
        Tendsto (fun j => ‖P j (v i) - v i‖ * ‖u i‖) l (nhds 0) := by
      intro i
      simpa using (((hstrong (v i)).sub (tendsto_const_nhds (x := v i))).norm.mul_const ‖u i‖)
    simpa using tendsto_finset_sum Finset.univ (fun i _ => hi i)

#check finite_block_cutoffs_nuclear_error
#print axioms finite_block_cutoffs_nuclear_error
end Round173E
