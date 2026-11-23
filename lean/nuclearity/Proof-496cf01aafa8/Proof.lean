import Mathlib

/-!
Manuscript premise repaired: 10.3.1.21 (27158--27167) must follow from
strong orthogonal cutoff convergence, not constancy of singular values.
This file supplies a finite rank-one decomposition of each cutoff error and
proves its explicit nuclear representation cost tends to zero. It does not
assume or establish nuclearity of the infinite quotient operator.
-/
noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace Round173C
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

/-- The manuscript's finite spectral block, with coefficients absorbed into v. -/
def spectralBlock (s : Finset ι) (η v : ι → E) : E →L[ℂ] E :=
  ∑ i ∈ s, (innerSL ℂ (η i)).smulRight (v i)

/-- A genuine orthogonal cutoff gives the exact rank-one error decomposition. -/
theorem spectralBlock_cutoff_decomposition (s : Finset ι) (η v : ι → E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    spectralBlock s η v - (spectralBlock s η v).comp U.starProjection =
      spectralBlock s (fun i => η i - U.starProjection (η i)) v := by
  ext x
  simp only [spectralBlock, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [inner_sub_left, U.inner_starProjection_left_eq_right, sub_smul]

/-- The sum is the cost of the displayed finite nuclear representation. -/
def cutoffCost (s : Finset ι) (η v : ι → E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] : ℝ :=
  ∑ i ∈ s, ‖innerSL ℂ (η i - U.starProjection (η i))‖ * ‖v i‖

theorem cutoffCost_nonneg (s : Finset ι) (η v : ι → E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    0 ≤ cutoffCost s η v U := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))


/-- Every displayed finite block has a finite rank-one cost, with no basis
conditioning assumption and no suppressed coefficient-vector norms. -/
theorem spectralBlock_norm_le_cost (s : Finset ι) (η v : ι → E) :
    ‖spectralBlock s η v‖ ≤ ∑ i ∈ s, ‖innerSL ℂ (η i)‖ * ‖v i‖ := by
  unfold spectralBlock
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  simp only [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc
    ‖((innerSL ℂ) (η i)) x‖ * ‖v i‖ ≤
        (‖innerSL ℂ (η i)‖ * ‖x‖) * ‖v i‖ :=
      mul_le_mul_of_nonneg_right (((innerSL ℂ) (η i)).le_opNorm x) (norm_nonneg _)
    _ = (‖innerSL ℂ (η i)‖ * ‖v i‖) * ‖x‖ := by ring

/-- The same explicit nuclear error cost controls the operator norm. -/
theorem spectralBlock_cutoff_norm_le (s : Finset ι) (η v : ι → E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] :
    ‖spectralBlock s η v - (spectralBlock s η v).comp U.starProjection‖ ≤
      cutoffCost s η v U := by
  rw [spectralBlock_cutoff_decomposition]
  exact spectralBlock_norm_le_cost s _ v

/-- The actual finite nuclear cost vanishes; no infinite spectral sum is assumed. -/
theorem spectralBlock_cutoff_nuclear_cost_tendsto
    (s : Finset ι) (η v : ι → E) (U : ℕ → Submodule ℂ E)
    [∀ n, (U n).HasOrthogonalProjection]
    (hstrong : ∀ i ∈ s,
      Tendsto (fun n => (U n).starProjection (η i)) atTop (𝓝 (η i))) :
    Tendsto (fun n => cutoffCost s η v (U n)) atTop (𝓝 0) := by
  have hterm (i : ι) (hi : i ∈ s) :
      Tendsto (fun n =>
        ‖innerSL ℂ (η i - (U n).starProjection (η i))‖ * ‖v i‖)
        atTop (𝓝 0) := by
    have hd : Tendsto (fun n => η i - (U n).starProjection (η i))
        atTop (𝓝 (0 : E)) := by
      simpa using (tendsto_const_nhds (x := η i)).sub (hstrong i hi)
    have hf := ((innerSL ℂ).continuous.tendsto (0 : E)).comp hd
    simpa using hf.norm.mul_const ‖v i‖
  simpa only [cutoffCost, Finset.sum_const_zero] using tendsto_finset_sum s hterm

#check spectralBlock_norm_le_cost
#print axioms spectralBlock_norm_le_cost
#check spectralBlock_cutoff_norm_le
#print axioms spectralBlock_cutoff_norm_le
#check spectralBlock_cutoff_decomposition
#print axioms spectralBlock_cutoff_decomposition
#check spectralBlock_cutoff_nuclear_cost_tendsto
#print axioms spectralBlock_cutoff_nuclear_cost_tendsto
end Round173C
