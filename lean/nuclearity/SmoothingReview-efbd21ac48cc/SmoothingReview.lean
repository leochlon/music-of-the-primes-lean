import Mathlib
set_option linter.unusedSectionVars false

/-! D round 33: exact logarithmic-coordinate mollifier factorization at genuine
prime powers, for the arithmetic limit in manuscript §§1.4.2–1.4.4. This proves
no global continuation and does not assert integrability of an arbitrary kernel. -/
namespace MasulloGRH.HeckeMollifier
open scoped NumberField
open MeasureTheory

variable (K : Type*) [Field K] [NumberField K]

/-- The real logarithm of a genuine finite prime-power norm is at least log 2. -/
theorem primePower_log_lowerBound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Real.log 2 ≤ Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) := by
  have hq : 2 ≤ Ideal.absNorm v.asIdeal :=
    NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hp : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal ^ (n+1) : ℕ) := by
    exact_mod_cast le_trans hq (Nat.le_pow (Nat.succ_pos n))
  apply Real.log_le_log (by norm_num)
  simpa only [Nat.cast_pow] using hp

/-- The Mellin power supported on the positive logarithmic half-line.
Its value at zero never enters our prime-power evaluation. -/
noncomputable def logMellinStep (z : ℂ) (x : ℝ) : ℂ :=
  if 0 < x then Complex.exp (-z * (x : ℂ)) else 0

/-- Exact kernel evaluation: the small logarithmic displacement never crosses
zero at any genuine prime-power norm, uniformly over all number fields. -/
theorem primePower_logMellinStep_factorization
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : ℂ) (ε u : ℝ) (hε : ε < Real.log 2) (hu : |u| ≤ ε) :
    logMellinStep z (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) - u) =
      Complex.exp (-z * (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) : ℂ)) *
        Complex.exp (z * (u : ℂ)) := by
  have hl := primePower_log_lowerBound K v n
  have hu' : u ≤ ε := le_trans (le_abs_self u) hu
  have hx : 0 < Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) - u := by
    linarith
  rw [logMellinStep, if_pos hx, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The actual logarithmic convolution factors at every arithmetic prime power.
This algebraic integral identity is valid even for a nonintegrable η; it does
not by itself assert that the mollifier has mass one or is admissible. -/
theorem primePower_logConvolution_factorization
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : ℂ) (ε : ℝ) (hε : ε < Real.log 2)
    (η : ℝ → ℂ) (hη : ∀ u, ε < |u| → η u = 0) :
    (∫ u : ℝ, η u *
      logMellinStep z (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) - u)) =
      Complex.exp (-z * (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) : ℂ)) *
        ∫ u : ℝ, η u * Complex.exp (z * (u : ℂ)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : |u| ≤ ε
  · rw [primePower_logMellinStep_factorization K v n z ε u hε hu]
    ring
  · rw [hη u (lt_of_not_ge hu)]
    simp

/-- For continuous kernels with the stated bounded support, the actual convolution
integrand is integrable. Thus its factorization need not rely on totalized integrals. -/
theorem primePower_logConvolution_integrable
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (z : ℂ) (ε : ℝ) (hε : ε < Real.log 2)
    (η : ℝ → ℂ) (hη : ∀ u, ε < |u| → η u = 0) (hηc : Continuous η) :
    Integrable (fun u : ℝ => η u *
      logMellinStep z (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) - u)) := by
  have hcompact : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-ε) ε))
    intro u hu
    apply abs_le.mp
    by_contra hh
    exact hu (hη u (lt_of_not_ge hh))
  have hM : Integrable (fun u : ℝ => η u * Complex.exp (z * (u : ℂ))) :=
    (hηc.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport
      hcompact.mul_right
  apply (hM.const_mul
    (Complex.exp (-z * (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) : ℂ)))).congr
  filter_upwards [] with u
  by_cases hu : |u| ≤ ε
  · rw [primePower_logMellinStep_factorization K v n z ε u hε hu]
    ring
  · rw [hη u (lt_of_not_ge hu)]
    simp

#check primePower_logConvolution_integrable
#print axioms primePower_logConvolution_integrable

#check primePower_log_lowerBound
#print axioms primePower_log_lowerBound
#check primePower_logMellinStep_factorization
#print axioms primePower_logMellinStep_factorization
#check primePower_logConvolution_factorization
#print axioms primePower_logConvolution_factorization
end MasulloGRH.HeckeMollifier

namespace MasulloGRH.HeckeMollifier
open MeasureTheory

theorem exp_mul_sub_one_norm_le (z : ℂ) (R ε u : ℝ)
    (hR : 0 ≤ R) (_hε : 0 ≤ ε) (hsmall : R * ε < 1)
    (hz : ‖z‖ ≤ R) (hu : |u| ≤ ε) :
    ‖Complex.exp (z * (u : ℂ)) - 1‖ ≤ 2 * R * ε := by
  have hw : ‖z * (u : ℂ)‖ ≤ R * ε := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hz hu (abs_nonneg _) hR
  have hb := Complex.locally_lipschitz_exp (r := 1) (by norm_num) le_rfl
    (0 : ℂ) (z * (u : ℂ)) (by simpa using lt_of_le_of_lt hw hsmall)
  have hb' : ‖Complex.exp (z * (u : ℂ)) - 1‖ ≤ 2 * ‖z * (u : ℂ)‖ := by
    simpa [one_add_one_eq_two] using hb
  nlinarith

/-- Uniform Mellin error; mass and L1 control are explicit kernel hypotheses. -/
theorem mellinFactor_sub_one_norm_le
    (η : ℝ → ℂ) (ε R : ℝ) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hsmall : R * ε < 1) (hc : Continuous η)
    (hsupp : ∀ u, ε < |u| → η u = 0)
    (hmass : (∫ u : ℝ, η u) = 1)
    (hL1 : (∫ u : ℝ, ‖η u‖) ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(∫ u : ℝ, η u * Complex.exp (z * (u : ℂ))) - 1‖ ≤ 2 * R * ε := by
  have hk : HasCompactSupport η := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-ε) ε))
    intro u hu
    apply abs_le.mp
    by_contra hh
    exact hu (hsupp u (lt_of_not_ge hh))
  have hi : Integrable η := hc.integrable_of_hasCompactSupport hk
  have he : Integrable (fun u : ℝ => η u * Complex.exp (z * (u : ℂ))) :=
    (hc.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).integrable_of_hasCompactSupport
      hk.mul_right
  have heq : (∫ u : ℝ, η u * Complex.exp (z * (u : ℂ))) - 1 =
      ∫ u : ℝ, η u * (Complex.exp (z * (u : ℂ)) - 1) := by
    simp only [mul_sub, mul_one]
    rw [integral_sub he hi, hmass]
  rw [heq]
  calc
    ‖∫ u : ℝ, η u * (Complex.exp (z * (u : ℂ)) - 1)‖ ≤
        ∫ u : ℝ, ‖η u * (Complex.exp (z * (u : ℂ)) - 1)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, ‖η u‖ * (2 * R * ε) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun u => norm_nonneg _)) (hi.norm.mul_const _)
      filter_upwards [] with u
      by_cases hu : |u| ≤ ε
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (exp_mul_sub_one_norm_le z R ε u hR hε hsmall hz hu) (norm_nonneg _)
      · rw [hsupp u (lt_of_not_ge hu)]
        simp
    _ = (∫ u : ℝ, ‖η u‖) * (2 * R * ε) := integral_mul_const _ _
    _ ≤ 2 * R * ε := by nlinarith [mul_nonneg hR hε]

/-- The uniform estimate applied at every genuine prime-power norm. -/
theorem primePower_logConvolution_error_norm_le
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ)
    (η : ℝ → ℂ) (ε R : ℝ) (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (hlog : ε < Real.log 2) (hsmall : R * ε < 1) (hc : Continuous η)
    (hsupp : ∀ u, ε < |u| → η u = 0)
    (hmass : (∫ u : ℝ, η u) = 1) (hL1 : (∫ u : ℝ, ‖η u‖) ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(∫ u : ℝ, η u * logMellinStep z
        (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) - u)) -
      Complex.exp (-z * (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) : ℂ))‖ ≤
      ‖Complex.exp (-z * (Real.log (Ideal.absNorm v.asIdeal ^ (n+1) : ℝ) : ℂ))‖ *
        (2 * R * ε) := by
  rw [primePower_logConvolution_factorization K v n z ε hlog η hsupp,
    ← mul_sub_one, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (mellinFactor_sub_one_norm_le η ε R hε hR hsmall hc hsupp hmass hL1 z hz)
    (norm_nonneg _)

#check exp_mul_sub_one_norm_le
#print axioms exp_mul_sub_one_norm_le
#check mellinFactor_sub_one_norm_le
#print axioms mellinFactor_sub_one_norm_le
#check primePower_logConvolution_error_norm_le
#print axioms primePower_logConvolution_error_norm_le
end MasulloGRH.HeckeMollifier

namespace MasulloGRH.HeckeMollifier
open MeasureTheory

/-- Shrinking normalized kernels have Mellin factors converging uniformly on
bounded complex parameter sets. This is the smoothing factor used at the
actual prime powers in primePower_logConvolution_error_norm_le. -/
theorem mellinFactor_tendstoUniformlyOn
    (η : ℕ → ℝ → ℂ) (ε : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hε : ∀ j, 0 ≤ ε j)
    (hlim : Filter.Tendsto ε Filter.atTop (nhds 0))
    (hc : ∀ j, Continuous (η j))
    (hsupp : ∀ j u, ε j < |u| → η j u = 0)
    (hmass : ∀ j, (∫ u : ℝ, η j u) = 1)
    (hL1 : ∀ j, (∫ u : ℝ, ‖η j u‖) ≤ 1) :
    TendstoUniformlyOn
      (fun j z => ∫ u : ℝ, η j u * Complex.exp (z * (u : ℂ)))
      (fun _ : ℂ => (1 : ℂ)) Filter.atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hs : Filter.Tendsto (fun j => R * ε j) Filter.atTop (nhds 0) := by
    simpa using hlim.const_mul R
  have hE : Filter.Tendsto (fun j => 2 * R * ε j) Filter.atTop (nhds 0) := by
    simpa using hlim.const_mul (2 * R)
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hs.eventually (gt_mem_nhds zero_lt_one),
    hE.eventually (gt_mem_nhds hδ)] with j hj hjδ
  intro z hz
  rw [dist_comm, dist_eq_norm]
  exact lt_of_le_of_lt
    (mellinFactor_sub_one_norm_le (η j) (ε j) R (hε j) hR hj
      (hc j) (hsupp j) (hmass j) (hL1 j) z hz) hjδ

#check mellinFactor_tendstoUniformlyOn
#print axioms mellinFactor_tendstoUniformlyOn
end MasulloGRH.HeckeMollifier
