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
