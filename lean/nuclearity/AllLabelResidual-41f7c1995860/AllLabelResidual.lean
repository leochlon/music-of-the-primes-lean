import Mathlib

namespace Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Riesz-normalized lift for one coefficient. Its norm is controlled
by the reciprocal of the coefficient vector's norm, not by an upper
bound on that norm. -/
noncomputable def canonicalLift (v : H) : H :=
  ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ • v

/-- Exact normalization of the actual Riesz lift. -/
theorem canonicalLift_pairing (v : H) (hv : v ≠ 0) :
    inner ℂ v (canonicalLift v) = 1 := by
  rw [canonicalLift, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have hn : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  simpa only [Complex.ofReal_pow] using inv_mul_cancel₀ hn

/-- The exact primal cost; an upper dual bound cannot give this upper cost. -/
theorem canonicalLift_norm (v : H) :
    ‖canonicalLift v‖ = ‖v‖⁻¹ := by
  rw [canonicalLift, norm_smul, norm_inv]
  have hn : ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ = ‖v‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v‖)]
  rw [hn]
  by_cases hv : ‖v‖ = 0
  · simp [hv]
  · field_simp

/-- Quantitative minimum-norm property, without a lift-bound hypothesis. -/
theorem canonicalLift_minimal (v u : H) (hu : inner ℂ v u = 1) :
    ‖canonicalLift v‖ ≤ ‖u‖ := by
  have h : 1 ≤ ‖v‖ * ‖u‖ := by
    simpa [hu] using norm_inner_le_norm (𝕜 := ℂ) v u
  have hv : 0 < ‖v‖ := by
    have := norm_nonneg u
    have := norm_nonneg v
    nlinarith
  rw [canonicalLift_norm, inv_eq_one_div]
  exact (div_le_iff₀ hv).mpr (by nlinarith)

/-- Exact smoothed rank-one cost; this exhibits the denominator the
actual global lift estimate must control. -/
theorem canonicalLift_smoothed_cost (A : H →L[ℂ] H) (v : H) :
    ‖A (canonicalLift v)‖ * ‖innerSL ℂ v‖ = ‖A v‖ / ‖v‖ := by
  rw [canonicalLift, map_smul, norm_smul, norm_inv, innerSL_apply_norm]
  have hn : ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ = ‖v‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v‖)]
  rw [hn]
  by_cases hv : ‖v‖ = 0
  · simp [hv]
  · field_simp

#check canonicalLift_pairing
#print axioms canonicalLift_pairing
#check canonicalLift_norm
#print axioms canonicalLift_norm
#check canonicalLift_minimal
#print axioms canonicalLift_minimal
#check canonicalLift_smoothed_cost
#print axioms canonicalLift_smoothed_cost
end Round93H

namespace Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a genuine orthogonal residual r of a coefficient vector v, this
is the required simultaneous normalization. Orthogonality, not a bound,
is the hypothesis. Apply with r=v-Qv for the closed span of other jets. -/
theorem residualLift_pairing (v r : H) (hr : r ≠ 0)
    (hortho : inner ℂ (v-r) r = 0) :
    inner ℂ v (canonicalLift r) = 1 := by
  have h : inner ℂ v r = inner ℂ r r := by
    rw [inner_sub_left] at hortho
    exact sub_eq_zero.mp hortho
  rw [canonicalLift, inner_smul_right, h]
  simpa only [canonicalLift, inner_smul_right] using canonicalLift_pairing r hr

/-- The coefficient vector's orthogonal residual determines the exact
smoothed rank-one cost, exposing the inverse-Gram conditioning factor. -/
theorem residualLift_smoothed_cost (A : H →L[ℂ] H) (v r : H) :
    ‖A (canonicalLift r)‖ * ‖innerSL ℂ v‖ =
      ‖A r‖ * ‖v‖ / ‖r‖^2 := by
  rw [canonicalLift, map_smul, norm_smul, norm_inv, innerSL_apply_norm]
  have hn : ‖((‖r‖ ^ 2 : ℝ) : ℂ)‖ = ‖r‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖r‖)]
  rw [hn]
  ring

#check residualLift_pairing
#print axioms residualLift_pairing
#check residualLift_smoothed_cost
#print axioms residualLift_smoothed_cost
end Round93H

namespace Round95H
open Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def orthogonalResidual (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v : H) : H := v - M.starProjection v

 theorem orthogonalResidual_mem (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v : H) : orthogonalResidual M v ∈ Mᗮ :=
  Submodule.sub_starProjection_mem_orthogonal v

 theorem orthogonalResidual_pairing (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v u : H) (hu : u ∈ Mᗮ) :
    inner ℂ (orthogonalResidual M v) u = inner ℂ v u := by
  have hp := (M.mem_orthogonal u).mp hu (M.starProjection v)
    (M.starProjection_apply_mem v)
  simp only [orthogonalResidual, inner_sub_left, hp, sub_zero]

 theorem orthogonalResidual_nonzero_of_lift (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v u : H) (hu : u ∈ Mᗮ)
    (hvu : inner ℂ v u = 1) : orthogonalResidual M v ≠ 0 := by
  have h := orthogonalResidual_pairing M v u hu
  rw [hvu] at h
  intro hz
  rw [hz, inner_zero_left] at h
  exact zero_ne_one h

 theorem orthogonalResidualLift_pairing (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v : H) (hr : orthogonalResidual M v ≠ 0) :
    inner ℂ v (canonicalLift (orthogonalResidual M v)) = 1 := by
  apply residualLift_pairing v _ hr
  have h := (M.mem_orthogonal (orthogonalResidual M v)).mp
    (orthogonalResidual_mem M v) (M.starProjection v) (M.starProjection_apply_mem v)
  have he : v - orthogonalResidual M v = M.starProjection v := by
    unfold orthogonalResidual
    abel
  rw [he]
  exact h

 theorem orthogonalResidualLift_annihilates (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v w : H) (hw : w ∈ M) :
    inner ℂ w (canonicalLift (orthogonalResidual M v)) = 0 := by
  have h := (M.mem_orthogonal (orthogonalResidual M v)).mp
    (orthogonalResidual_mem M v) w hw
  simp only [canonicalLift, inner_smul_right, h, mul_zero]

 theorem orthogonalResidualLift_minimal (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v u : H) (hu : u ∈ Mᗮ)
    (hvu : inner ℂ v u = 1) :
    ‖canonicalLift (orthogonalResidual M v)‖ ≤ ‖u‖ := by
  apply canonicalLift_minimal
  rw [orthogonalResidual_pairing M v u hu, hvu]

 theorem orthogonalResidualLift_exact_cost (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (A : H →L[ℂ] H) (v : H) :
    ‖A (canonicalLift (orthogonalResidual M v))‖ * ‖innerSL ℂ v‖ =
      ‖A (orthogonalResidual M v)‖ * ‖v‖ / ‖orthogonalResidual M v‖^2 :=
  residualLift_smoothed_cost A v (orthogonalResidual M v)

#check orthogonalResidual_nonzero_of_lift
#print axioms orthogonalResidual_nonzero_of_lift
#check orthogonalResidualLift_pairing
#print axioms orthogonalResidualLift_pairing
#check orthogonalResidualLift_annihilates
#print axioms orthogonalResidualLift_annihilates
#check orthogonalResidualLift_minimal
#print axioms orthogonalResidualLift_minimal
#check orthogonalResidualLift_exact_cost
#print axioms orthogonalResidualLift_exact_cost
end Round95H

namespace Round95H
open Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {ι : Type*}

noncomputable def otherCoefficientSpace (v : ι → H) (i : ι) : Submodule ℂ H :=
  (Submodule.span ℂ (v '' {j | j ≠ i})).topologicalClosure

noncomputable instance otherCoefficientSpace_hasProjection (v : ι → H) (i : ι) :
    (otherCoefficientSpace v i).HasOrthogonalProjection := by
  letI : CompleteSpace (otherCoefficientSpace v i) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

 theorem otherCoefficient_mem (v : ι → H) (i j : ι) (hj : j ≠ i) :
    v j ∈ otherCoefficientSpace v i := by
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨j, hj, rfl⟩

 theorem all_other_coefficients_annihilated (v : ι → H) (i j : ι) (hj : j ≠ i) :
    inner ℂ (v j)
      (canonicalLift (orthogonalResidual (otherCoefficientSpace v i) (v i))) = 0 :=
  orthogonalResidualLift_annihilates _ _ _ (otherCoefficient_mem v i j hj)

 theorem residual_eq_zero_iff_closed_dependence (v : ι → H) (i : ι) :
    orthogonalResidual (otherCoefficientSpace v i) (v i) = 0 ↔
      v i ∈ otherCoefficientSpace v i := by
  rw [orthogonalResidual, sub_eq_zero, eq_comm]
  exact Submodule.starProjection_eq_self_iff

#check all_other_coefficients_annihilated
#print axioms all_other_coefficients_annihilated
#check residual_eq_zero_iff_closed_dependence
#print axioms residual_eq_zero_iff_closed_dependence
end Round95H
