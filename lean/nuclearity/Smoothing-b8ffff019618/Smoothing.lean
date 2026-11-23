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
