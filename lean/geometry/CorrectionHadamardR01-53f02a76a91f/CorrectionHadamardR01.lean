import Mathlib

/- Exact independent Fermat extractions followed by the missing-jet
application. No RH or half-plane nonvanishing theorem is imported. -/
namespace CorrectionHadamardR01
open Complex Filter
open scoped Topology

-- Fermat S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package,
-- gapsw80_t38_logDeriv_E1_factor, lines 2001--2022; namespace-only port.
theorem logDeriv_E1_factor {ρ s : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (fun z => (1 - z / ρ) * Complex.exp (z / ρ)) s
      = (s - ρ)⁻¹ + ρ⁻¹ := by
  have h1 : (1 : ℂ) - s / ρ ≠ 0 :=
    sub_ne_zero.mpr fun h => hs ((div_eq_one_iff_eq hρ).mp h.symm)
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hρs : ρ - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hmul := logDeriv_mul (f := fun w => 1 - w / ρ)
    (g := fun w => Complex.exp (w / ρ)) s h1 (Complex.exp_ne_zero _)
    (by fun_prop) (by fun_prop)
  rw [hmul]
  have hlin : logDeriv (fun w => (1 : ℂ) - w / ρ) s = (s - ρ)⁻¹ := by
    rw [logDeriv_apply]
    simp only [deriv_const_sub, deriv_div_const, deriv_id'']
    field_simp
    ring
  have hexp : logDeriv (fun w => Complex.exp (w / ρ)) s = ρ⁻¹ := by
    have hd := (Complex.hasDerivAt_exp (s / ρ)).comp s ((hasDerivAt_id s).div_const ρ)
    have hd' : HasDerivAt (fun w : ℂ => Complex.exp (w / ρ))
        (Complex.exp (s / ρ) * (1 / ρ)) s := by simpa [Function.comp_def] using hd
    rw [logDeriv_apply, hd'.deriv]
    field_simp
  rw [hlin, hexp]

-- Same source, gapsw80_t38_eventually_large_norm, lines 2053--2067.
theorem eventually_large_norm {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, R ≤ ‖ρ j‖ := by
  have h0 := hsum.tendsto_atTop_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]

theorem inverse_square_bound {z ρ : ℂ} (hρ : ρ ≠ 0)
    (hz : 2 * ‖z‖ ≤ ‖ρ‖) :
    ‖((z - ρ)^2)⁻¹‖ ≤ 4 * (Complex.normSq ρ)⁻¹ := by
  have hp : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hd : ‖ρ‖ / 2 ≤ ‖z - ρ‖ := by
    have ht : ‖ρ‖ - ‖z‖ ≤ ‖z - ρ‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    linarith
  have hdp : 0 < ‖z - ρ‖ := lt_of_lt_of_le (by positivity) hd
  rw [norm_inv, norm_pow, Complex.normSq_eq_norm_sq]
  calc
    (‖z - ρ‖ ^ 2)⁻¹ ≤ ((‖ρ‖ / 2)^2)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).2
      nlinarith [sq_nonneg (‖z - ρ‖ - ‖ρ‖ / 2)]
    _ = 4 * (‖ρ‖ ^ 2)⁻¹ := by field_simp; ring

theorem square_series_summable {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) (z : ℂ) :
    Summable (fun j => ((z - ρ j)^2)⁻¹) := by
  refine (hsum.mul_left 4).of_norm_bounded_eventually ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_large_norm hρ0 hsum
    (show 0 < 2 * ‖z‖ + 1 by positivity)] with j hj
  exact inverse_square_bound (hρ0 j) (by linarith)

-- A zero is enumerated with multiplicity. Select its missing jets by a
-- 0/1 mask; this retains the finite boundary deficit as well as exterior zeros.
theorem missing_jet_series_summable {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    (missing : ℕ → Prop) [DecidablePred missing] (z : ℂ) :
    Summable (fun j => if missing j then ((z - ρ j)^2)⁻¹ else 0) := by
  refine (square_series_summable hρ0 hsum z).norm.of_norm_bounded ?_
  intro j
  split_ifs <;> simp

-- The reference subtraction is part of the actual unlogged test.
theorem reference_subtraction (z b ρ : ℂ) :
    ((z - ρ)⁻¹ + ρ⁻¹) - ((b - ρ)⁻¹ + ρ⁻¹) =
      (z - ρ)⁻¹ - (b - ρ)⁻¹ := by ring

end CorrectionHadamardR01
#print axioms CorrectionHadamardR01.logDeriv_E1_factor
#print axioms CorrectionHadamardR01.eventually_large_norm
#print axioms CorrectionHadamardR01.inverse_square_bound
#print axioms CorrectionHadamardR01.missing_jet_series_summable
