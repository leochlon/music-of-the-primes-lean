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

/-! The finite jet nondegeneracy premise in (7.1.4.18)--(7.1.4.19),
feeding the representation cost (10.3.1.18).  The native analytic jet
identities remain to be proved.  No uniform conditioning is assumed. -/
namespace Round176C
open Round175C
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {n : ℕ}

theorem triangular_jet_det
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E)
    (htri : ∀ i j, i < j → δ i (u j) = 0) :
    (jetMatrix δ u).det = ∏ i, δ i (u i) := by
  apply Matrix.det_of_lowerTriangular
  intro i j hij
  exact htri i j hij

/-- At a zero of exact order n, u_j has germ (z-rho)^j g(z).
The displayed diagonal is j! g(rho), and only g(rho) != 0 is needed. -/
theorem exact_order_jet_isUnit
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E) (c : ℂ)
    (hc : c ≠ 0)
    (htri : ∀ i j, i < j → δ i (u j) = 0)
    (hdiag : ∀ i, δ i (u i) = (i.val.factorial : ℂ) * c) :
    IsUnit (jetMatrix δ u).det := by
  rw [isUnit_iff_ne_zero, triangular_jet_det δ u htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  rw [hdiag i]
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val) hc

/-- The exact conditioning cost uses the reciprocal determinant, rather
than an unsupported uniform bound for the biorthogonal vectors. -/
theorem inverseColumnCost_eq_adjugate
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E)
    (hinv : IsUnit (jetMatrix δ u).det) (j : Fin n) :
    inverseColumnCost δ u j =
      ‖(jetMatrix δ u).det‖⁻¹ *
        ∑ k, ‖(jetMatrix δ u).adjugate k j‖ * ‖u k‖ := by
  unfold inverseColumnCost
  rw [Matrix.nonsing_inv_apply _ hinv]
  have hv : (↑(hinv.unit⁻¹) : ℂ) = ((jetMatrix δ u).det)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hinv.unit_spec]
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, hv, norm_inv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- A finite normalization with determinant nondegeneracy DERIVED from
exact-order jets. This discharges the algebraic premise left in C175. -/
theorem exact_order_jet_normalization_cost
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E)
    (a : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c ≠ 0)
    (htri : ∀ i j, i < j → δ i (u j) = 0)
    (hdiag : ∀ i, δ i (u i) = (i.val.factorial : ℂ) * c) :
    (∀ i j, δ i (normalizedJetVector δ u j) = if i = j then 1 else 0) ∧
    (∀ x, normalizedSpectralBlock δ u a x =
      ∑ i, ∑ j, (a i j * δ j x) • normalizedJetVector δ u i) ∧
    0 ≤ blockRepresentationCost δ u a ∧
    blockRepresentationCost δ u a ≤
      ∑ i, ∑ j, (‖a i j‖ * ‖δ j‖) *
        (‖(jetMatrix δ u).det‖⁻¹ *
          ∑ k, ‖(jetMatrix δ u).adjugate k i‖ * ‖u k‖) := by
  have hi := exact_order_jet_isUnit δ u c hc htri hdiag
  obtain ⟨hb, hr, hp, hcost⟩ := finite_jet_normalization_cost δ u a hi
  refine ⟨hb, hr, hp, ?_⟩
  simpa only [inverseMatrixBlockCost, inverseColumnCost_eq_adjugate δ u hi] using hcost

#check triangular_jet_det
#print axioms triangular_jet_det
#check exact_order_jet_isUnit
#print axioms exact_order_jet_isUnit
#check inverseColumnCost_eq_adjugate
#print axioms inverseColumnCost_eq_adjugate
#check exact_order_jet_normalization_cost
#print axioms exact_order_jet_normalization_cost
end Round176C

namespace Round176C
/-- In coordinates centered at the zero, the manuscript representatives
have germs z^j g(z). This derives the below-diagonal jet vanishing. -/
theorem germ_jet_below (g : ℂ → ℂ) (i j : ℕ) (hij : i < j)
    (hg : ContDiffAt ℂ i g 0) :
    iteratedDeriv i (fun z => z ^ j * g z) 0 = 0 := by
  have hp : ContDiffAt ℂ i (fun z : ℂ => z ^ j) 0 := contDiffAt_id.pow j
  change iteratedDeriv i ((fun z : ℂ => z ^ j) * g) 0 = 0
  rw [iteratedDeriv_mul hp hg]
  apply Finset.sum_eq_zero
  intro k hk
  have hkj : k < j := by have := Finset.mem_range.mp hk; omega
  have hne : j - k ≠ 0 := by omega
  simp [iteratedDeriv_pow, zero_pow hne]

/-- The diagonal jets are j! times the nonvanishing residual germ. -/
theorem germ_jet_diagonal (g : ℂ → ℂ) (j : ℕ)
    (hg : ContDiffAt ℂ j g 0) :
    iteratedDeriv j (fun z => z ^ j * g z) 0 = (j.factorial : ℂ) * g 0 := by
  have hp : ContDiffAt ℂ j (fun z : ℂ => z ^ j) 0 := contDiffAt_id.pow j
  change iteratedDeriv j ((fun z : ℂ => z ^ j) * g) 0 = _
  rw [iteratedDeriv_mul hp hg, Finset.sum_eq_single j]
  · simp [iteratedDeriv_pow, Nat.descFactorial_self]
  · intro k hk hkj
    have hne : j - k ≠ 0 := by have := Finset.mem_range.mp hk; omega
    simp [iteratedDeriv_pow, zero_pow hne]
  · simp

#check germ_jet_below
#print axioms germ_jet_below
#check germ_jet_diagonal
#print axioms germ_jet_diagonal
end Round176C

namespace Round176C
open Round175C
/-- The local residual-germ model supplies the previously abstract
triangular hypotheses and yields the finite manuscript block cost. -/
theorem germ_jet_normalization_cost
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E)
    (a : Matrix (Fin n) (Fin n) ℂ) (g : ℂ → ℂ) (hg0 : g 0 ≠ 0)
    (hg : ∀ i : Fin n, ContDiffAt ℂ i.val g 0)
    (hjet : ∀ i j, δ i (u j) =
      iteratedDeriv i.val (fun z => z ^ j.val * g z) 0) :
    (∀ i j, δ i (normalizedJetVector δ u j) = if i = j then 1 else 0) ∧
    (∀ x, normalizedSpectralBlock δ u a x =
      ∑ i, ∑ j, (a i j * δ j x) • normalizedJetVector δ u i) ∧
    0 ≤ blockRepresentationCost δ u a ∧
    blockRepresentationCost δ u a ≤
      ∑ i, ∑ j, (‖a i j‖ * ‖δ j‖) *
        (‖(jetMatrix δ u).det‖⁻¹ *
          ∑ k, ‖(jetMatrix δ u).adjugate k i‖ * ‖u k‖) := by
  apply exact_order_jet_normalization_cost δ u a (g 0) hg0
  · intro i j hij
    rw [hjet i j]
    exact germ_jet_below g i.val j.val hij (hg i)
  · intro i
    rw [hjet i i]
    exact germ_jet_diagonal g i.val (hg i)

#check germ_jet_normalization_cost
#print axioms germ_jet_normalization_cost
end Round176C

/-! New premise: exact finite conditioning data for (10.3.1.18), from
(7.1.4.12). The residual germ supplies EVERY jet-matrix entry; primal
normalization does not supply a bound on its inverse. -/
namespace Round177C
open Round175C Round176C

/-- All entries, including the non-diagonal entries omitted by the
triangular nondegeneracy result, of the manuscript's residual-germ jets. -/
theorem germ_jet_entry (g : ℂ → ℂ) (i j : ℕ)
    (hg : ContDiffAt ℂ i g 0) :
    iteratedDeriv i (fun z => z ^ j * g z) 0 =
      (i.choose j : ℂ) * (j.factorial : ℂ) * iteratedDeriv (i-j) g 0 := by
  by_cases hij : i < j
  · rw [germ_jet_below g i j hij hg, Nat.choose_eq_zero_of_lt hij]
    simp
  · have hp : ContDiffAt ℂ i (fun z : ℂ => z ^ j) 0 := contDiffAt_id.pow j
    change iteratedDeriv i ((fun z : ℂ => z ^ j) * g) 0 = _
    rw [iteratedDeriv_mul hp hg, Finset.sum_eq_single j]
    · simp [iteratedDeriv_pow, Nat.descFactorial_self]
    · intro k hk hkj
      by_cases hlt : k < j
      · have hne : j - k ≠ 0 := by omega
        simp [iteratedDeriv_pow, zero_pow hne]
      · have hgt : j < k := by omega
        simp [iteratedDeriv_pow, hgt]
    · intro hj
      exact False.elim (hj (Finset.mem_range.mpr (by omega)))

def residualJetMatrix (n : ℕ) (g : ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (i.val.choose j.val : ℂ) * (j.val.factorial : ℂ) *
    iteratedDeriv (i.val-j.val) g 0

theorem jetMatrix_eq_residual
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E) (g : ℂ → ℂ)
    (hg : ∀ i : Fin n, ContDiffAt ℂ i.val g 0)
    (hjet : ∀ i j, δ i (u j) =
      iteratedDeriv i.val (fun z => z ^ j.val * g z) 0) :
    jetMatrix δ u = residualJetMatrix n g := by
  ext i j
  exact (hjet i j).trans (germ_jet_entry g i.val j.val (hg i))

/-- Exact determinant: the inverse cost necessarily retains the residual
value g(0). No lower bound in spectral height is postulated here. -/
theorem residualJetMatrix_det (n : ℕ) (g : ℂ → ℂ) :
    (residualJetMatrix n g).det =
      (∏ i : Fin n, (i.val.factorial : ℂ)) * (g 0)^n := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [residualJetMatrix, Finset.prod_mul_distrib]
  · intro i j hij
    have h : i.val < j.val := hij
    simp [residualJetMatrix, Nat.choose_eq_zero_of_lt h]

/-- The manuscript finite representation cost, now entirely explicit in
residual derivatives, residual value, jet norms and provisional vector norms.
This does not supply the native membership or the infinite spectral sum. -/
theorem residual_germ_block_cost
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {n : ℕ}
    (δ : Fin n → E →L[ℂ] ℂ) (u : Fin n → E)
    (a : Matrix (Fin n) (Fin n) ℂ) (g : ℂ → ℂ) (hg0 : g 0 ≠ 0)
    (hg : ∀ i : Fin n, ContDiffAt ℂ i.val g 0)
    (hjet : ∀ i j, δ i (u j) =
      iteratedDeriv i.val (fun z => z ^ j.val * g z) 0) :
    blockRepresentationCost δ u a ≤
      ∑ i, ∑ j, (‖a i j‖ * ‖δ j‖) *
        (‖(∏ k : Fin n, (k.val.factorial : ℂ)) * (g 0)^n‖⁻¹ *
          ∑ k, ‖(residualJetMatrix n g).adjugate k i‖ * ‖u k‖) := by
  obtain ⟨_, _, _, hc⟩ := germ_jet_normalization_cost δ u a g hg0 hg hjet
  rw [jetMatrix_eq_residual δ u g hg hjet, residualJetMatrix_det] at hc
  exact hc

#check germ_jet_entry
#print axioms germ_jet_entry
#check jetMatrix_eq_residual
#print axioms jetMatrix_eq_residual
#check residualJetMatrix_det
#print axioms residualJetMatrix_det
#check residual_germ_block_cost
#print axioms residual_germ_block_cost
end Round177C


/-!
Round 173 F: completeness-to-identification component of the manuscript route.

The missing ARITHMETIC premise is that the common kernel of the permitted
continuous native Mellin jets is exactly the closed geometric image G_a.
The theorems below do not assume nuclearity or a summability estimate. They
prove the precise Hilbert-space consequences of that premise, including the
correct closed span and identification of projected operators by their jets.
H, G, and the jets are parameters: attachment to W_I^s(C_K) is NOT claimed.
-/

noncomputable section
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
namespace Round173F

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

def jetSpan (r : ι → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range r)).topologicalClosure

theorem jet_mem_span (r : ι → H) (i : ι) : r i ∈ jetSpan r :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The corrected interval windows must exhaust this space, rather than
intersections of an increasing family of jet kernels (manuscript 25554). -/
theorem jetSpan_orthogonal_eq_commonKernel (r : ι → H) (x : H) :
    x ∈ (jetSpan r)ᗮ ↔ ∀ i, ⟪r i, x⟫_ℂ = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_orthogonal _ _).mp hx _ (jet_mem_span r i)
  · intro hx
    have hs : Submodule.span ℂ (Set.range r) ≤ (innerSL ℂ x).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change ⟪x, r i⟫_ℂ = 0
      exact inner_eq_zero_symm.mp (hx i)
    have hc : jetSpan r ≤ (innerSL ℂ x).ker :=
      Submodule.topologicalClosure_minimal _ hs (innerSL ℂ x).isClosed_ker
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    have hxy : ⟪x, y⟫_ℂ = 0 := hc hy
    exact inner_eq_zero_symm.mp hxy

/-- Discharges the functional-analytic span implication needed at manuscript
27198--27211, conditional on the still-unproved actual native annihilator
identity. No uniform conditioning of biorthogonals is asserted. -/
theorem jetSpan_eq_geometric_orthogonal
    (G : Submodule ℂ H) (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G) :
    jetSpan r = Gᗮ := by
  have hclosed : IsClosed (jetSpan r : Set H) :=
    Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace (jetSpan r) := hclosed.completeSpace_coe
  have hv : (jetSpan r)ᗮ = G := by
    ext x
    exact (jetSpan_orthogonal_eq_commonKernel r x).trans (hkernel x)
  rw [← hv, Submodule.orthogonal_orthogonal]

/-- Exact quotient totality, without selecting an arbitrary model quotient.
This is a criterion, not a proof of its arithmetic right-hand side. -/
theorem quotient_totality_iff
    (G : Submodule ℂ H) (δ : ι → H →L[ℂ] ℂ)
    (hvanish : ∀ i, G ≤ (δ i).ker) :
    (∀ q : H ⧸ G,
      (∀ i, G.liftQ (δ i).toLinearMap (hvanish i) q = 0) → q = 0) ↔
    (∀ x : H, (∀ i, δ i x = 0) → x ∈ G) := by
  constructor
  · intro h x hx
    have hz : G.mkQ x = 0 := h (G.mkQ x) (by
      intro i
      exact hx i)
    have hm : x ∈ G.mkQ.ker := hz
    simpa only [Submodule.ker_mkQ] using hm
  · intro h q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      intro hx
      have hm : x ∈ G := h x (by intro i; exact hx i)
      have hz : x ∈ G.mkQ.ker := by simpa only [Submodule.ker_mkQ] using hm
      exact hz

/-- A candidate finite-rank limit has the same genuine projection as A once
all actual continuous jets agree and their common kernel is G. In the target
application A is convolution FIRST; projection is applied SECOND. -/
theorem projected_operator_eq_of_jet_agreement
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (δ : ι → H →L[ℂ] ℂ)
    (hkernel : ∀ x, (∀ i, δ i x = 0) → x ∈ G)
    (A T : H →L[ℂ] H)
    (hjets : ∀ i x, δ i (T x) = δ i (A x)) :
    Gᗮ.starProjection.comp T = Gᗮ.starProjection.comp A := by
  ext x
  have hg : T x - A x ∈ G := hkernel _ (by
    intro i
    rw [map_sub, hjets, sub_self])
  have hp : Gᗮ.starProjection (T x - A x) = 0 := by
    have hp' : Gᗮ.orthogonalProjection (T x - A x) = 0 :=
      Submodule.orthogonalProjection_eq_zero_iff.mpr (by
      simpa only [Submodule.orthogonal_orthogonal] using hg)
    simpa only [Submodule.starProjection_apply, Submodule.coe_zero] using
      congrArg (fun z : Gᗮ => (z : H)) hp'
  simpa only [map_sub, sub_eq_zero, ContinuousLinearMap.comp_apply] using hp

/-- The reconstruction implication used after the manuscript's S1 Cauchy
argument: pointwise convergence and eventual jet agreement suffice. The
convergence and arithmetic common-kernel premise still have to be proved
for the manuscript's actual finite blocks; neither is manufactured here. -/
theorem projected_limit_identification
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (δ : ι → H →L[ℂ] ℂ)
    (hkernel : ∀ x, (∀ i, δ i x = 0) → x ∈ G)
    {κ : Type*} (l : Filter κ) [Filter.NeBot l]
    (A T : H →L[ℂ] H) (blocks : κ → H →L[ℂ] H)
    (hlim : ∀ x, Filter.Tendsto (fun n => blocks n x) l (nhds (T x)))
    (hjets : ∀ i x, ∀ᶠ n in l, δ i (blocks n x) = δ i (A x)) :
    Gᗮ.starProjection.comp T = Gᗮ.starProjection.comp A := by
  apply projected_operator_eq_of_jet_agreement G δ hkernel A T
  intro i x
  have ht := ((δ i).continuous.tendsto (T x)).comp (hlim x)
  have ha : Filter.Tendsto (fun n => δ i (blocks n x)) l (nhds (δ i (A x))) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm (hjets i x)) tendsto_const_nhds
  exact tendsto_nhds_unique ht ha

#check jetSpan_orthogonal_eq_commonKernel
#print axioms jetSpan_orthogonal_eq_commonKernel
#check jetSpan_eq_geometric_orthogonal
#print axioms jetSpan_eq_geometric_orthogonal
#check quotient_totality_iff
#print axioms quotient_totality_iff
#check projected_operator_eq_of_jet_agreement
#print axioms projected_operator_eq_of_jet_agreement
#check projected_limit_identification
#print axioms projected_limit_identification
end Round173F

/-! Round 175: the finite-jet-span cutoff convergence premise of 10.2/10.3.
These are actual orthogonal projections. No nuclear cost is presumed. -/
namespace Round175F
open Filter
open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

noncomputable def window (r : ι → H) (J : Finset ι) : Submodule ℂ H :=
  (Submodule.span ℂ (r '' (J : Set ι))).topologicalClosure

instance window_complete (r : ι → H) (J : Finset ι) : CompleteSpace (window r J) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem window_mono (r : ι → H) {J K : Finset ι} (h : J ⊆ K) :
    window r J ≤ window r K := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  exact Set.image_mono h

theorem generator_mem_window (r : ι → H) {J : Finset ι} {i : ι} (hi : i ∈ J) :
    r i ∈ window r J :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem span_mem_some_window (r : ι → H) {y : H}
    (hy : y ∈ Submodule.span ℂ (Set.range r)) :
    ∃ J : Finset ι, y ∈ window r J := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨{i}, generator_mem_window r (by simp)⟩
  | zero => exact ⟨∅, (window r ∅).zero_mem⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨J, hJ⟩ := ihx
      obtain ⟨K, hK⟩ := ihy
      exact ⟨J ∪ K, (window r (J ∪ K)).add_mem
        (window_mono r Finset.subset_union_left hJ)
        (window_mono r Finset.subset_union_right hK)⟩
  | smul a x hx ih =>
      obtain ⟨J, hJ⟩ := ih
      exact ⟨J, (window r J).smul_mem a hJ⟩

/-- Quantitative approximation used for strong convergence. -/
theorem cutoff_error_le (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x y : H) (hy : y ∈ U) :
    ‖U.starProjection x - x‖ ≤ 2 * ‖x - y‖ := by
  have hfix : U.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hy
  calc
    ‖U.starProjection x - x‖ = ‖U.starProjection (x-y) + (y-x)‖ := by
      rw [map_sub, hfix]
      congr 1
      abel
    _ ≤ ‖U.starProjection (x-y)‖ + ‖y-x‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + ‖y-x‖ := by
      apply add_le_add_left
      exact (U.starProjection.le_opNorm _).trans
        (by simpa using mul_le_mul_of_nonneg_right U.starProjection_norm_le (norm_nonneg (x-y)))
    _ = 2 * ‖x-y‖ := by rw [norm_sub_rev y x]; ring

/-- This proves the strong convergence assumed by the previous fixed-block
cost lemmas, on the closed spectral span, without any basis conditioning. -/
theorem finite_jet_cutoffs_tendsto (r : ι → H) (x : H)
    (hx : x ∈ Round173F.jetSpan r) :
    Tendsto (fun J : Finset ι => (window r J).starProjection x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨J, hJ⟩ := span_mem_some_window r hy
  refine ⟨J, fun K hK => ?_⟩
  rw [dist_eq_norm]
  apply (cutoff_error_le (window r K) x y (window_mono r hK hJ)).trans_lt
  rw [dist_eq_norm] at hxy
  linarith

/-- Each included native Riesz jet is preserved exactly by the cutoff. -/
theorem finite_jet_cutoff_preserves (r : ι → H) (J : Finset ι)
    (i : ι) (hi : i ∈ J) (x : H) :
    ⟪r i, (window r J).starProjection x⟫_ℂ = ⟪r i, x⟫_ℂ := by
  rw [← (window r J).inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr (generator_mem_window r hi)]

/-- Native application criterion: the actual common-kernel theorem, still
an arithmetic obligation, identifies the strong limit with G-perp. -/
theorem finite_jet_cutoffs_tendsto_on_geometric_complement
    (G : Submodule ℂ H) (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (x : H) (hx : x ∈ Gᗮ) :
    Tendsto (fun J : Finset ι => (window r J).starProjection x) atTop (𝓝 x) := by
  apply finite_jet_cutoffs_tendsto r x
  rwa [Round173F.jetSpan_eq_geometric_orthogonal G r hkernel]


/-- The cutoff range is finite dimensional, not only topologically closed. -/
theorem window_finiteDimensional (r : ι → H) (J : Finset ι) :
    FiniteDimensional ℂ (window r J) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (r '' (J : Set ι))) :=
    FiniteDimensional.span_of_finite ℂ (J.finite_toSet.image r)
  have hc : IsClosed (Submodule.span ℂ (r '' (J : Set ι)) : Set H) :=
    (Submodule.span ℂ (r '' (J : Set ι))).closed_of_finiteDimensional
  have he : window r J = Submodule.span ℂ (r '' (J : Set ι)) := by
    apply SetLike.coe_injective
    exact hc.closure_eq
  rw [he]
  infer_instance

/-- The manuscript's fixed finite block is unchanged once all its input
jet representatives occur in the cutoff. No singular-value convergence
inference or biorthogonal norm bound is used. -/
theorem finiteBlock_cutoff_stabilizes (r v : ι → H) (J K : Finset ι)
    (hJK : J ⊆ K) :
    (∑ i ∈ J, (innerSL ℂ (r i)).smulRight (v i)).comp (window r K).starProjection =
      ∑ i ∈ J, (innerSL ℂ (r i)).smulRight (v i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finite_jet_cutoff_preserves r K i (hJK hi)]

#check window_finiteDimensional
#print axioms window_finiteDimensional
#check finiteBlock_cutoff_stabilizes
#print axioms finiteBlock_cutoff_stabilizes

#check cutoff_error_le
#print axioms cutoff_error_le
#check finite_jet_cutoffs_tendsto
#print axioms finite_jet_cutoffs_tendsto
#check finite_jet_cutoff_preserves
#print axioms finite_jet_cutoff_preserves
#check finite_jet_cutoffs_tendsto_on_geometric_complement
#print axioms finite_jet_cutoffs_tendsto_on_geometric_complement
end Round175F

/-! Round 176: FULL_SPACE_PROJECTED_APPROXIMATION, the operator-identification
premise at manuscript 27198--27211. The finite windows are the repaired
finite jet spans, not the decreasing kernels printed in (9.3.2.10).
No nuclearity, infinite cost bound, or summability is assumed or concluded.
The actual native common-kernel identity remains an application obligation. -/
namespace Round176F
open Filter
open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

theorem window_le_spectral_span (r : ι → H) (J : Finset ι) :
    Round175F.window r J ≤ Round173F.jetSpan r := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

/-- Each corrected cutoff ignores precisely the geometric component of
its input, provided the actual common-kernel identity has been proved. -/
theorem cutoff_after_genuine_projection
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (J : Finset ι) (x : H) :
    (Round175F.window r J).starProjection (Gᗮ.starProjection x) =
      (Round175F.window r J).starProjection x := by
  have hle : Round175F.window r J ≤ Gᗮ := by
    rw [← Round173F.jetSpan_eq_geometric_orthogonal G r hkernel]
    exact window_le_spectral_span r J
  have hz : (Round175F.window r J).orthogonalProjection
      (x - Gᗮ.starProjection x) = 0 :=
    Submodule.orthogonalProjection_eq_zero_iff.mpr
      ((Submodule.orthogonal_le hle)
        (Submodule.sub_starProjection_mem_orthogonal x))
  have hz' : (Round175F.window r J).starProjection
      (x - Gᗮ.starProjection x) = 0 := by
    simpa only [Submodule.starProjection_apply, Submodule.coe_zero] using
      congrArg (fun y : Round175F.window r J => (y : H)) hz
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hz')).symm

/-- Strong approximation of the required composition, convolution FIRST
and spectral projection SECOND. A is any supplied continuous operator;
its native convolution construction is not silently asserted here. -/
theorem projected_operator_cutoffs_tendsto
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (A : H →L[ℂ] H) (x : H) :
    Tendsto (fun J : Finset ι =>
      ((Round175F.window r J).starProjection.comp A) x) atTop
      (𝓝 ((Gᗮ.starProjection.comp A) x)) := by
  have ht := Round175F.finite_jet_cutoffs_tendsto_on_geometric_complement
    G r hkernel (Gᗮ.starProjection (A x))
    (Gᗮ.starProjection_apply_mem (A x))
  simpa only [cutoff_after_genuine_projection G r hkernel,
    ContinuousLinearMap.comp_apply] using ht

/-- The approximants have an explicitly finite-dimensional containing
range. This is finite rank, not an infinite nuclear-cost estimate. -/
theorem projected_cutoff_range
    (r : ι → H) (J : Finset ι) (A : H →L[ℂ] H) :
    FiniteDimensional ℂ (Round175F.window r J) ∧
      ∀ x, ((Round175F.window r J).starProjection.comp A) x ∈
        Round175F.window r J := by
  exact ⟨Round175F.window_finiteDimensional r J,
    fun x => (Round175F.window r J).starProjection_apply_mem (A x)⟩

/-- Once any candidate block limit agrees with these cutoffs pointwise,
uniqueness identifies it with the actual projected composition. -/
theorem projected_operator_identified_by_cutoffs
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (A T : H →L[ℂ] H)
    (hlim : ∀ x, Tendsto (fun J : Finset ι =>
      ((Round175F.window r J).starProjection.comp A) x) atTop (𝓝 (T x))) :
    T = Gᗮ.starProjection.comp A := by
  ext x
  exact tendsto_nhds_unique (hlim x)
    (projected_operator_cutoffs_tendsto G r hkernel A x)

#check cutoff_after_genuine_projection
#print axioms cutoff_after_genuine_projection
#check projected_operator_cutoffs_tendsto
#print axioms projected_operator_cutoffs_tendsto
#check projected_cutoff_range
#print axioms projected_cutoff_range
#check projected_operator_identified_by_cutoffs
#print axioms projected_operator_identified_by_cutoffs
/-- Finite-window identification needs only the included jets, not the
unproved totality of every native spectral jet. This is the exact range
and interpolation criterion to check for any proposed finite block. -/
theorem finite_window_jet_unique
    (r : ι → H) (J : Finset ι) (x y : H)
    (hx : x ∈ Round175F.window r J) (hy : y ∈ Round175F.window r J)
    (hjets : ∀ i ∈ J, ⟪r i, x⟫_ℂ = ⟪r i, y⟫_ℂ) : x = y := by
  have hs : Submodule.span ℂ (r '' (J : Set ι)) ≤
      (innerSL ℂ (x - y)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change ⟪x - y, r i⟫_ℂ = 0
    apply inner_eq_zero_symm.mp
    rw [inner_sub_right, hjets i hi, sub_self]
  have hc : Round175F.window r J ≤ (innerSL ℂ (x - y)).ker :=
    Submodule.topologicalClosure_minimal _ hs (innerSL ℂ (x - y)).isClosed_ker
  have hz : ⟪x - y, x - y⟫_ℂ = 0 :=
    hc ((Round175F.window r J).sub_mem hx hy)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem finite_window_operator_identification
    (r : ι → H) (J : Finset ι) (A B : H →L[ℂ] H)
    (hrange : ∀ x, B x ∈ Round175F.window r J)
    (hjets : ∀ i ∈ J, ∀ x, ⟪r i, B x⟫_ℂ = ⟪r i, A x⟫_ℂ) :
    B = (Round175F.window r J).starProjection.comp A := by
  ext x
  apply finite_window_jet_unique r J (B x)
    ((Round175F.window r J).starProjection (A x)) (hrange x)
    ((Round175F.window r J).starProjection_apply_mem (A x))
  intro i hi
  rw [Round175F.finite_jet_cutoff_preserves r J i hi, hjets i hi x]

#check finite_window_jet_unique
#print axioms finite_window_jet_unique
#check finite_window_operator_identification
#print axioms finite_window_operator_identification
end Round176F

/-! Round 177: FINITE_SPECTRAL_COMPRESSION_IDENTIFICATION.
The finite triangular jet action in (10.3.1.12) must identify the finite
matrix with the genuine orthogonal compression before its cost can be used.
The native jet action and finite biorthogonals remain application premises;
no infinite nuclear cost, nuclearity, or summability is assumed here. -/
namespace Round177F
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

/-- Finite triangular jet action forces compression on the input too.
This does NOT assert A commutes with the projection. -/
theorem triangular_jet_action_compression
    (r : ι → H) (J : Finset ι) (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J, c i j * ⟪r j, x⟫_ℂ) :
    ((Round175F.window r J).starProjection.comp A).comp
      (Round175F.window r J).starProjection =
      (Round175F.window r J).starProjection.comp A := by
  ext x
  apply Round176F.finite_window_jet_unique r J
    ((Round175F.window r J).starProjection
      (A ((Round175F.window r J).starProjection x)))
    ((Round175F.window r J).starProjection (A x))
    ((Round175F.window r J).starProjection_apply_mem _)
    ((Round175F.window r J).starProjection_apply_mem _)
  intro i hi
  rw [Round175F.finite_jet_cutoff_preserves r J i hi,
    Round175F.finite_jet_cutoff_preserves r J i hi,
    hact i hi, hact i hi]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Round175F.finite_jet_cutoff_preserves r J j hj]

/-- Projecting finite biorthogonal representatives gives the exact output
cutoff, even if the original representatives lie outside the finite window.
Thus no unjustified identification of global biorthogonals with an
orthogonal finite spectral subspace is needed. -/
theorem projected_biorthogonal_reconstruction
    [DecidableEq ι] (r v : ι → H) (J : Finset ι) (A : H →L[ℂ] H)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0) :
    (∑ j ∈ J, ((innerSL ℂ (r j)).comp A).smulRight
      ((Round175F.window r J).starProjection (v j))) =
      (Round175F.window r J).starProjection.comp A := by
  apply Round176F.finite_window_operator_identification r J A
  · intro x
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    apply Submodule.sum_mem
    intro j hj
    exact (Round175F.window r J).smul_mem _
      ((Round175F.window r J).starProjection_apply_mem (v j))
  · intro i hi x
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sum, inner_smul_right]
    simp_rw [Round175F.finite_jet_cutoff_preserves r J i hi]
    calc
      (∑ j ∈ J, ⟪r j, A x⟫_ℂ * ⟪r i, v j⟫_ℂ) =
          ∑ j ∈ J, ⟪r j, A x⟫_ℂ * (if i = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hdual i hi j hj]
      _ = ⟪r i, A x⟫_ℂ := by simp [hi]

/-- Exact finite rank-one matrix representation of the actual cutoff.
The two finite sums have nuclear cost
sum_i sum_j ||c i j|| ||innerSL(r j)|| ||P_J(v i)||.
No uniform bound or infinite summability of this expression is asserted. -/
theorem spectral_matrix_eq_genuine_cutoff
    [DecidableEq ι] (r v : ι → H) (J : Finset ι)
    (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J, c i j * ⟪r j, x⟫_ℂ) :
    (∑ i ∈ J, ∑ j ∈ J, (c i j • innerSL ℂ (r j)).smulRight
      ((Round175F.window r J).starProjection (v i))) =
      (Round175F.window r J).starProjection.comp A := by
  rw [← projected_biorthogonal_reconstruction r v J A hdual]
  ext x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hact i hi, Finset.sum_smul]

/-- Orthogonal projection of the output representatives cannot increase
this explicit finite nuclear representation cost. Conditioning remains
visible in the norms of the supplied biorthogonal representatives. -/
theorem finite_spectral_cost_le
    (r v : ι → H) (J : Finset ι) (c : ι → ι → ℂ) :
    (∑ i ∈ J, ∑ j ∈ J,
      ‖c i j • innerSL ℂ (r j)‖ *
        ‖(Round175F.window r J).starProjection (v i)‖) ≤
    ∑ i ∈ J, ∑ j ∈ J, ‖c i j‖ * ‖innerSL ℂ (r j)‖ * ‖v i‖ := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact ((Round175F.window r J).starProjection.le_opNorm _).trans
    (by simpa using mul_le_mul_of_nonneg_right (Round175F.window r J).starProjection_norm_le (norm_nonneg (v i)))

#check triangular_jet_action_compression
#print axioms triangular_jet_action_compression
#check projected_biorthogonal_reconstruction
#print axioms projected_biorthogonal_reconstruction
#check spectral_matrix_eq_genuine_cutoff
#print axioms spectral_matrix_eq_genuine_cutoff
#check finite_spectral_cost_le
#print axioms finite_spectral_cost_le
/-- Exhausting finite matrices converge to the required projected operator,
conditional on the native common-kernel and triangular-action identities.
This is strong convergence; it is explicitly not S1 convergence. -/
theorem spectral_matrices_tendsto_projected_operator
    [DecidableEq ι] (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r v : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (J : ℕ → Finset ι)
    (hcofinal : Filter.Tendsto J Filter.atTop Filter.atTop)
    (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hdual : ∀ n, ∀ i ∈ J n, ∀ j ∈ J n,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ n, ∀ i ∈ J n, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J n, c i j * ⟪r j, x⟫_ℂ)
    (x : H) :
    Filter.Tendsto (fun n =>
      (∑ i ∈ J n, ∑ j ∈ J n, (c i j • innerSL ℂ (r j)).smulRight
        ((Round175F.window r (J n)).starProjection (v i))) x)
      Filter.atTop (nhds ((Gᗮ.starProjection.comp A) x)) := by
  have he (n : ℕ) := spectral_matrix_eq_genuine_cutoff r v (J n) A c
    (hdual n) (hact n)
  simp_rw [he]
  exact (Round176F.projected_operator_cutoffs_tendsto G r hkernel A x).comp hcofinal

#check spectral_matrices_tendsto_projected_operator
#print axioms spectral_matrices_tendsto_projected_operator
end Round177F

/-! Round179E. CONSTRUCTED_FINITE_SPECTRAL_COMPRESSION_COST.
The inverse-jet representatives in the manuscript's finite normalization
must give the genuine orthogonal compression before their nuclear costs
can enter (10.3.1.18)--(10.3.1.22). This joins those two checked pieces.
Native jet/germ realization and the infinite total cost remain unproved.
-/
namespace Round179E
open scoped InnerProductSpace
open Round175C
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {n : ℕ}

theorem residual_germ_genuine_compression_cost
    (r u : Fin n → H) (A : H →L[ℂ] H)
    (a : Matrix (Fin n) (Fin n) ℂ) (g : ℂ → ℂ) (hg0 : g 0 ≠ 0)
    (hg : ∀ i : Fin n, ContDiffAt ℂ i.val g 0)
    (hjet : ∀ i j, ⟪r i, u j⟫_ℂ =
      iteratedDeriv i.val (fun z => z ^ j.val * g z) 0)
    (hact : ∀ i x, ⟪r i, A x⟫_ℂ = ∑ j, a i j * ⟪r j, x⟫_ℂ) :
    let δ := fun i => innerSL ℂ (r i)
    let P := (Round175F.window r Finset.univ).starProjection
    let v := fun i => P (normalizedJetVector δ u i)
    (∀ i j, ⟪r i, v j⟫_ℂ = if i = j then 1 else 0) ∧
    (∑ i, ∑ j, (a i j • δ j).smulRight (v i)) = P.comp A ∧
    (∑ i, ∑ j, ‖a i j • δ j‖ * ‖v i‖) ≤
      ∑ i, ∑ j, (‖a i j‖ * ‖δ j‖) *
        (‖(∏ k : Fin n, (k.val.factorial : ℂ)) * (g 0)^n‖⁻¹ *
          ∑ k, ‖(Round177C.residualJetMatrix n g).adjugate k i‖ * ‖u k‖) := by
  classical
  dsimp only
  let δ := fun i => innerSL ℂ (r i)
  let w := normalizedJetVector δ u
  have hj : ∀ i j, δ i (u j) =
      iteratedDeriv i.val (fun z => z ^ j.val * g z) 0 := hjet
  have hb : ∀ i j, ⟪r i, w j⟫_ℂ = if i = j then 1 else 0 :=
    (Round176C.germ_jet_normalization_cost δ u a g hg0 hg hj).1
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [Round175F.finite_jet_cutoff_preserves r Finset.univ i (Finset.mem_univ i)]
    exact hb i j
  · simpa using Round177F.spectral_matrix_eq_genuine_cutoff r w Finset.univ A a
      (by intro i hi j hj; exact hb i j)
      (by intro i hi x; simpa using hact i x)
  · calc
      _ ≤ blockRepresentationCost δ u a := by
        unfold blockRepresentationCost
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (Submodule.norm_starProjection_apply_le
            (Round175F.window r Finset.univ) (w i)) (norm_nonneg _)
      _ ≤ _ := Round177C.residual_germ_block_cost δ u a g hg0 hg hj

#check residual_germ_genuine_compression_cost
#print axioms residual_germ_genuine_compression_cost

/-- Whole finite windows need their full interpolation matrix: distinct
zero blocks need not have orthogonal Riesz spans. This is the finite-window
cost to control before passing to the manuscript's infinite S1 limit. -/
theorem whole_window_genuine_compression_cost
    (r u : Fin n → H) (A : H →L[ℂ] H)
    (a : Matrix (Fin n) (Fin n) ℂ)
    (hinv : IsUnit (jetMatrix (fun i => innerSL ℂ (r i)) u).det)
    (hact : ∀ i x, ⟪r i, A x⟫_ℂ = ∑ j, a i j * ⟪r j, x⟫_ℂ) :
    let δ := fun i => innerSL ℂ (r i)
    let P := (Round175F.window r Finset.univ).starProjection
    let v := fun i => P (normalizedJetVector δ u i)
    (∑ i, ∑ j, (a i j • δ j).smulRight (v i)) = P.comp A ∧
    (∑ i, ∑ j, ‖a i j • δ j‖ * ‖v i‖) ≤ inverseMatrixBlockCost δ u a := by
  classical
  dsimp only
  let δ := fun i => innerSL ℂ (r i)
  let w := normalizedJetVector δ u
  have hb : ∀ i j, ⟪r i, w j⟫_ℂ = if i = j then 1 else 0 :=
    normalizedJetVector_biorthogonal δ u hinv
  constructor
  · simpa using Round177F.spectral_matrix_eq_genuine_cutoff r w Finset.univ A a
      (by intro i hi j hj; exact hb i j)
      (by intro i hi x; simpa using hact i x)
  · calc
      _ ≤ blockRepresentationCost δ u a := by
        unfold blockRepresentationCost
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (Submodule.norm_starProjection_apply_le
            (Round175F.window r Finset.univ) (w i)) (norm_nonneg _)
      _ ≤ _ := (finite_jet_normalization_cost δ u a hinv).2.2.2

#check whole_window_genuine_compression_cost
#print axioms whole_window_genuine_compression_cost
end Round179E

namespace Round179C
open Round175C Round176C
theorem other_root_residual_jet_zero
    (rho sigma : ℂ) (hne : sigma ≠ rho) (N d k : ℕ) (hk : k < N)
    (g : ℂ → ℂ) (hg : ContDiffAt ℂ k g 0) :
    iteratedDeriv k (fun z => z^N * (g z / (z + (sigma-rho))^d)) 0 = 0 := by
  apply germ_jet_below _ k N hk
  apply hg.div
  · exact (contDiffAt_id.add contDiffAt_const).pow d
  · simpa using pow_ne_zero d (sub_ne_zero.mpr hne)


end Round179C

/-! Round 180C. Named premise: MULTI_ROOT_RESIDUAL_WINDOW_COST.
Manuscript (7.1.4.12)--(7.1.4.19) and (10.3.1.15)--(10.3.1.22).
Derive the finite-window biorthogonality from SAME-root and OTHER-root
residual germs, then identify the genuine orthogonal compression and retain
its finite conditioning cost. Native membership, jet identities, height
bounds and the infinite p=1 sum are not assumed or concluded. -/
namespace Round180C
open Round175C Round176C
open scoped InnerProductSpace
variable {H B : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [DecidableEq B] (n N : B → ℕ)

theorem residual_window_biorthogonal
    (rho : B → ℂ) (hrho : Function.Injective rho)
    (hn : ∀ b, n b ≤ N b)
    (r : (Σ b, Fin (n b)) → H) (u : ∀ b, Fin (n b) → H)
    (g : B → ℂ → ℂ) (hg0 : ∀ b, g b 0 ≠ 0)
    (hg : ∀ b (i : Fin (n b)), ContDiffAt ℂ i.val (g b) 0)
    (hsame : ∀ b i j, ⟪r ⟨b,i⟩, u b j⟫_ℂ =
      iteratedDeriv i.val (fun z => z^j.val * g b z) 0)
    (hcross : ∀ b c, b ≠ c → ∀ (i : Fin (n b)) (j : Fin (n c)),
      ⟪r ⟨b,i⟩, u c j⟫_ℂ = iteratedDeriv i.val
        (fun z => z^(N b) * (g b z / (z + (rho b-rho c))^(N c-j.val))) 0)
    (p q : Σ b, Fin (n b)) :
    ⟪r p, normalizedJetVector (fun j => innerSL ℂ (r ⟨q.1,j⟩)) (u q.1) q.2⟫_ℂ =
      if p = q then 1 else 0 := by
  classical
  rcases p with ⟨b,i⟩
  rcases q with ⟨c,j⟩
  by_cases hbc : b = c
  · subst c
    have hb := (germ_jet_normalization_cost
      (fun k => innerSL ℂ (r ⟨b,k⟩)) (u b) 0 (g b) (hg0 b)
      (hg b) (hsame b)).1 i j
    simpa using hb
  · have hpq : (Sigma.mk b i : Σ b, Fin (n b)) ≠ Sigma.mk c j := by
      intro he
      exact hbc (congrArg Sigma.fst he)
    rw [if_neg hpq]
    apply normalizedJetVector_vanishing
      (fun k => innerSL ℂ (r ⟨c,k⟩)) (u c) (innerSL ℂ (r ⟨b,i⟩)) _ j
    intro k
    change ⟪r ⟨b,i⟩, u c k⟫_ℂ = 0
    rw [hcross b c hbc i k]
    exact Round179C.other_root_residual_jet_zero (rho c) (rho b)
      (fun he => hbc (hrho he)) (N b) (N c-k.val) i.val
      (lt_of_lt_of_le i.isLt (hn b)) (g b) (hg b i)

variable [Fintype B] [CompleteSpace H]

theorem residual_window_genuine_compression_cost
    (rho : B → ℂ) (hrho : Function.Injective rho)
    (hn : ∀ b, n b ≤ N b)
    (r : (Σ b, Fin (n b)) → H) (u : ∀ b, Fin (n b) → H)
    (g : B → ℂ → ℂ) (hg0 : ∀ b, g b 0 ≠ 0)
    (hg : ∀ b (i : Fin (n b)), ContDiffAt ℂ i.val (g b) 0)
    (hsame : ∀ b i j, ⟪r ⟨b,i⟩, u b j⟫_ℂ =
      iteratedDeriv i.val (fun z => z^j.val * g b z) 0)
    (hcross : ∀ b c, b ≠ c → ∀ (i : Fin (n b)) (j : Fin (n c)),
      ⟪r ⟨b,i⟩, u c j⟫_ℂ = iteratedDeriv i.val
        (fun z => z^(N b) * (g b z / (z + (rho b-rho c))^(N c-j.val))) 0)
    (A : H →L[ℂ] H) (a : (Σ b, Fin (n b)) → (Σ b, Fin (n b)) → ℂ)
    (hact : ∀ i x, ⟪r i, A x⟫_ℂ = ∑ j, a i j * ⟪r j, x⟫_ℂ) :
    let delta := fun b j => innerSL ℂ (r ⟨b,j⟩)
    let P := (Round175F.window r Finset.univ).starProjection
    let v := fun i : Σ b, Fin (n b) => P (normalizedJetVector (delta i.1) (u i.1) i.2)
    (∑ i, ∑ j, (a i j • innerSL ℂ (r j)).smulRight (v i)) = P.comp A ∧
    (∑ i, ∑ j, ‖a i j • innerSL ℂ (r j)‖ * ‖v i‖) ≤
      ∑ i, ∑ j, (‖a i j‖ * ‖innerSL ℂ (r j)‖) *
        inverseColumnCost (delta i.1) (u i.1) i.2 := by
  classical
  dsimp only
  let w := fun i : Σ b, Fin (n b) =>
    normalizedJetVector (fun j => innerSL ℂ (r ⟨i.1,j⟩)) (u i.1) i.2
  have hb : ∀ p q, ⟪r p, w q⟫_ℂ = if p = q then 1 else 0 :=
    residual_window_biorthogonal n N rho hrho hn r u g hg0 hg hsame hcross
  constructor
  · simpa using Round177F.spectral_matrix_eq_genuine_cutoff r w Finset.univ A a
      (by intro i hi j hj; exact hb i j)
      (by intro i hi x; simpa using hact i x)
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact (Submodule.norm_starProjection_apply_le
      (Round175F.window r Finset.univ) (w i)).trans
      (normalizedJetVector_norm_le _ _ _)

#check residual_window_biorthogonal
#print axioms residual_window_biorthogonal
#check residual_window_genuine_compression_cost
#print axioms residual_window_genuine_compression_cost
end Round180C
