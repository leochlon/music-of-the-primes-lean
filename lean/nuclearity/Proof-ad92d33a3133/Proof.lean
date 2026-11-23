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
    {κ : Type*} (L : Filter κ)
    (s : Finset ι) (η v : ι → E) (U : κ → Submodule ℂ E)
    [∀ n, (U n).HasOrthogonalProjection]
    (hstrong : ∀ i ∈ s,
      Tendsto (fun n => (U n).starProjection (η i)) L (𝓝 (η i))) :
    Tendsto (fun n => cutoffCost s η v (U n)) L (𝓝 0) := by
  have hterm (i : ι) (hi : i ∈ s) :
      Tendsto (fun n =>
        ‖innerSL ℂ (η i - (U n).starProjection (η i))‖ * ‖v i‖)
        L (𝓝 0) := by
    have hd : Tendsto (fun n => η i - (U n).starProjection (η i))
        L (𝓝 (0 : E)) := by
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

/-! The actual unresolved conditioning step in (10.3.1.18) is not a
consequence of primal normalization.  The construction at (7.1.4.12)--
(7.1.4.19) instead uses a finite inverse jet matrix.  This section makes
that construction and its finite nuclear representation cost explicit.
No uniform inverse bound or infinite spectral summability is assumed. -/
namespace Round175C
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def jetMatrix (δ : ι → E →L[ℂ] ℂ) (u : ι → E) : Matrix ι ι ℂ :=
  fun i j => δ i (u j)

def normalizedJetVector (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (j : ι) : E :=
  ∑ k, (jetMatrix δ u)⁻¹ k j • u k

def inverseColumnCost (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (j : ι) : ℝ :=
  ∑ k, ‖(jetMatrix δ u)⁻¹ k j‖ * ‖u k‖

theorem normalizedJetVector_biorthogonal
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E)
    (hinv : IsUnit (jetMatrix δ u).det) (i j : ι) :
    δ i (normalizedJetVector δ u j) = if i = j then 1 else 0 := by
  classical
  simp only [normalizedJetVector, map_sum, map_smul, smul_eq_mul]
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j)
    (Matrix.mul_nonsing_inv (jetMatrix δ u) hinv)
  simpa only [Matrix.mul_apply, Matrix.one_apply, jetMatrix, mul_comm] using h

theorem normalizedJetVector_norm_le
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (j : ι) :
    ‖normalizedJetVector δ u j‖ ≤ inverseColumnCost δ u j := by
  unfold normalizedJetVector inverseColumnCost
  simpa only [norm_smul] using
    (norm_sum_le (s := Finset.univ) (f := fun k => (jetMatrix δ u)⁻¹ k j • u k))

/-- Other spectral jets still vanish after the finite normalization. -/
theorem normalizedJetVector_vanishing
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E)
    (ζ : E →L[ℂ] ℂ) (hzero : ∀ k, ζ (u k) = 0) (j : ι) :
    ζ (normalizedJetVector δ u j) = 0 := by
  simp [normalizedJetVector, hzero]

/-- For the manuscript's triangular block, a i j is the appropriate
binomial coefficient times Mellin moment, and is zero above the triangle. -/
def normalizedSpectralBlock (δ : ι → E →L[ℂ] ℂ) (u : ι → E)
    (a : Matrix ι ι ℂ) : E →L[ℂ] E :=
  ∑ i, ∑ j, (a i j • δ j).smulRight (normalizedJetVector δ u i)

def blockRepresentationCost (δ : ι → E →L[ℂ] ℂ) (u : ι → E)
    (a : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, ‖a i j • δ j‖ * ‖normalizedJetVector δ u i‖

def inverseMatrixBlockCost (δ : ι → E →L[ℂ] ℂ) (u : ι → E)
    (a : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, (‖a i j‖ * ‖δ j‖) * inverseColumnCost δ u i

/-- The normalized finite block realizes exactly the required jet matrix. -/
theorem normalizedSpectralBlock_jet_action
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (a : Matrix ι ι ℂ)
    (hinv : IsUnit (jetMatrix δ u).det) (k : ι) (x : E) :
    δ k (normalizedSpectralBlock δ u a x) = ∑ j, a k j * δ j x := by
  classical
  simp [normalizedSpectralBlock, normalizedJetVector_biorthogonal δ u hinv]

/-- Vanishing against jets at other zeros survives the whole block. -/
theorem normalizedSpectralBlock_vanishing
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (a : Matrix ι ι ℂ)
    (ζ : E →L[ℂ] ℂ) (hzero : ∀ k, ζ (u k) = 0) (x : E) :
    ζ (normalizedSpectralBlock δ u a x) = 0 := by
  simp [normalizedSpectralBlock, normalizedJetVector_vanishing δ u ζ hzero]

/-- The representation cost bounds this actual finite operator. -/
theorem normalizedSpectralBlock_norm_le
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (a : Matrix ι ι ℂ) :
    ‖normalizedSpectralBlock δ u a‖ ≤ blockRepresentationCost δ u a := by
  unfold normalizedSpectralBlock blockRepresentationCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  simp only [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc
    ‖(a i j • δ j) x‖ * ‖normalizedJetVector δ u i‖ ≤
      (‖a i j • δ j‖ * ‖x‖) * ‖normalizedJetVector δ u i‖ :=
      mul_le_mul_of_nonneg_right ((a i j • δ j).le_opNorm x) (norm_nonneg _)
    _ = (‖a i j‖ * ‖δ j‖ * ‖normalizedJetVector δ u i‖) * ‖x‖ := by
      rw [norm_smul]
      ring

/-- Explicit finite nuclear representation with the inverse-matrix cost
retained.  This is a finite block certificate, not an infinite S1 bound. -/
theorem finite_jet_normalization_cost
    (δ : ι → E →L[ℂ] ℂ) (u : ι → E) (a : Matrix ι ι ℂ)
    (hinv : IsUnit (jetMatrix δ u).det) :
    (∀ i j, δ i (normalizedJetVector δ u j) = if i = j then 1 else 0) ∧
    (∀ x, normalizedSpectralBlock δ u a x =
      ∑ i, ∑ j, (a i j * δ j x) • normalizedJetVector δ u i) ∧
    0 ≤ blockRepresentationCost δ u a ∧
    blockRepresentationCost δ u a ≤ inverseMatrixBlockCost δ u a := by
  refine ⟨normalizedJetVector_biorthogonal δ u hinv, ?_, ?_, ?_⟩
  · intro x
    simp [normalizedSpectralBlock, ContinuousLinearMap.smulRight_apply]
  · exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (normalizedJetVector_norm_le δ u i)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))

#check normalizedJetVector_biorthogonal
#print axioms normalizedJetVector_biorthogonal
#check normalizedJetVector_norm_le
#print axioms normalizedJetVector_norm_le
#check normalizedJetVector_vanishing
#print axioms normalizedJetVector_vanishing
#check normalizedSpectralBlock_jet_action
#print axioms normalizedSpectralBlock_jet_action
#check normalizedSpectralBlock_vanishing
#print axioms normalizedSpectralBlock_vanishing
#check normalizedSpectralBlock_norm_le
#print axioms normalizedSpectralBlock_norm_le
#check finite_jet_normalization_cost
#print axioms finite_jet_normalization_cost
end Round175C
