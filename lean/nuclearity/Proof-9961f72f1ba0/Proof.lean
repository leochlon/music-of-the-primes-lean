import Mathlib

/-!
Round 2, participant A. Inherited checked local results plus new repair work. Supporting local analytic work only.
The genuine all-number-field Hecke GRH target remains unproved.
No Hecke L-function is replaced by the elementary kernel below.
-/
namespace MasulloGRH

/-- The positive-side real-place kernel for the trivial character at z = 3/2,
up to the harmless positive Haar normalization. -/
noncomputable def realPlaceKernel (t : ℝ) : ℝ := 1 / (t ^ 2 * (t - 1))

/-- A logarithmically nonintegrable lower bound near t = 1. -/
theorem realPlaceKernel_lower (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ realPlaceKernel t := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < t ^ 2 * (t - 1) := mul_pos (sq_pos_of_pos ht0) (by linarith)
  have hb : t ^ 2 * (t - 1) ≤ 4 * (t - 1) := by
    apply mul_le_mul_of_nonneg_right
    · nlinarith
    · linarith
  exact one_div_le_one_div_of_le hp hb

/-- Subtracting a reference exponent cancels the t=1 singularity in this
concrete pair of kernels. This is not the full complex-parameter repair. -/
theorem realPlaceKernel_sub_reference (t : ℝ) (ht : 1 < t) :
    realPlaceKernel t - 1 / (t * (t - 1)) = -1 / t ^ 2 := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  unfold realPlaceKernel
  field_simp
  ring

/-- Exact logarithmic divergence of the comparison kernel. -/
theorem inverse_shift_integral (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in (1 + ε)..2, 1 / (t - 1)) = -Real.log ε := by
  have hn : (0 : ℝ) ∉ Set.uIcc ε 1 := by
    rw [Set.uIcc_of_le hε1]
    intro h
    exact (not_le_of_gt hε) h.1
  have heq : 1 + ε - 1 = ε := by ring
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) 1, heq]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  rw [integral_one_div hn, one_div, Real.log_inv]

/-- The actual local kernel has a divergent cutoff lower bound. -/
theorem realPlaceKernel_integral_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    -Real.log ε / 4 ≤ ∫ t in (1 + ε)..2, realPlaceKernel t := by
  have hab : 1 + ε ≤ 2 := by linarith
  have hpos : ∀ t ∈ Set.uIcc (1 + ε) 2, 1 < t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.uIcc (1 + ε) 2) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    change t - 1 ≠ 0
    linarith [hpos t ht]
  have hk : ContinuousOn realPlaceKernel (Set.uIcc (1 + ε) 2) := by
    unfold realPlaceKernel
    apply continuousOn_const.div ((continuousOn_id.pow 2).mul
      (continuousOn_id.sub continuousOn_const))
    intro t ht
    have h := hpos t ht
    change t ^ 2 * (t - 1) ≠ 0
    exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (by linarith)
  have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hc.div_const 4).intervalIntegrable hk.intervalIntegrable
    (fun t ht => by
      have hp : 1 < t := by linarith [ht.1]
      have hl := realPlaceKernel_lower t hp ht.2
      simpa only [div_div, mul_comm] using hl)
  rw [intervalIntegral.integral_div, inverse_shift_integral ε hε hε1] at hm
  exact hm

/-- No finite common bound exists for these positive cutoff integrals. -/
theorem realPlaceKernel_integrals_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      M < ∫ t in (1 + ε)..2, realPlaceKernel t := by
  let a : ℝ := 4 * (|M| + 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : 0 < Real.exp (-a) := Real.exp_pos _
  have he1 : Real.exp (-a) ≤ 1 := by
    calc
      Real.exp (-a) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  refine ⟨Real.exp (-a), he, he1, ?_⟩
  have hb := realPlaceKernel_integral_lower (Real.exp (-a)) he he1
  rw [Real.log_exp] at hb
  have hm : M ≤ |M| := le_abs_self M
  dsimp [a] at hb
  linarith

/-- Algebraic resolvent subtraction: the numerator is independent of the zero w.
With a zero-counting estimate this supplies quadratic, instead of linear,
decay in the imaginary part of w. No spectral convergence is assumed here. -/
theorem resolvent_subtraction (z z₀ w : ℂ) (hz : z ≠ w) (hz₀ : z₀ ≠ w) :
    1 / (z - w) - 1 / (z₀ - w) =
      (z₀ - z) / ((z - w) * (z₀ - w)) := by
  have h₁ : z - w ≠ 0 := sub_ne_zero.mpr hz
  have h₂ : z₀ - w ≠ 0 := sub_ne_zero.mpr hz₀
  field_simp
  ring

/-- A quantitative bound for the subtracted resolvent, useful for normal
convergence after a genuine zero-counting theorem has been supplied. -/
theorem resolvent_subtraction_bound (z z₀ w : ℂ) (R : ℝ) (hR : 0 < R)
    (h₁ : R ≤ ‖z - w‖) (h₂ : R ≤ ‖z₀ - w‖) :
    ‖1 / (z - w) - 1 / (z₀ - w)‖ ≤ ‖z₀ - z‖ / (R * R) := by
  have hn₁ : z - w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR h₁)
  have hn₂ : z₀ - w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR h₂)
  rw [resolvent_subtraction z z₀ w (sub_ne_zero.mp hn₁) (sub_ne_zero.mp hn₂),
    norm_div, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hR hR)
    (mul_le_mul h₁ h₂ (le_of_lt hR) (norm_nonneg _))

/-- Reference subtraction addresses vanishing at t=1, but does not by itself
satisfy the different central Mellin-moment restriction of PDF p.522. -/
theorem subtracted_resolvent_central_ne_zero (z z₀ : ℂ) (hne : z ≠ z₀) :
    1 / z - 1 / z₀ ≠ 0 := by
  intro h
  apply hne
  have hi := congrArg (fun x : ℂ => x⁻¹) (sub_eq_zero.mp h)
  simpa only [one_div, inv_inv] using hi

end MasulloGRH

#check MasulloGRH.realPlaceKernel_lower
#print axioms MasulloGRH.realPlaceKernel_lower

#check MasulloGRH.realPlaceKernel_sub_reference
#print axioms MasulloGRH.realPlaceKernel_sub_reference

#check MasulloGRH.inverse_shift_integral
#print axioms MasulloGRH.inverse_shift_integral
#check MasulloGRH.realPlaceKernel_integral_lower
#print axioms MasulloGRH.realPlaceKernel_integral_lower

#check MasulloGRH.realPlaceKernel_integrals_unbounded
#print axioms MasulloGRH.realPlaceKernel_integrals_unbounded

#check MasulloGRH.resolvent_subtraction
#print axioms MasulloGRH.resolvent_subtraction

#check MasulloGRH.resolvent_subtraction_bound
#print axioms MasulloGRH.resolvent_subtraction_bound

#check MasulloGRH.subtracted_resolvent_central_ne_zero
#print axioms MasulloGRH.subtracted_resolvent_central_ne_zero


namespace MasulloGRH

/-- A Mellin-side repair with a zero of prescribed order at the center and
quadratic decay at infinity. This is an explicit rational kernel, NOT an
L-function, and no Mellin realization or trace formula is assumed. -/
noncomputable def jetResolvent (m : ℕ) (z b w : ℂ) : ℂ :=
  (b - z) ^ (m + 1) * w ^ m / (z ^ m * (z - w) * (b - w) ^ (m + 1))

/-- The order-one repair uses one exponential and two fixed-reference terms. -/
theorem jetResolvent_one (z b w : ℂ) (hz : z ≠ 0)
    (hzw : z ≠ w) (hbw : b ≠ w) :
    jetResolvent 1 z b w =
      1 / (z - w) - 1 / (b - w) + b * (z - b) / (z * (b - w) ^ 2) := by
  unfold jetResolvent
  norm_num only [Nat.reduceAdd, pow_one]
  field_simp [hz, sub_ne_zero.mpr hzw, sub_ne_zero.mpr hbw]
  ring

/-- The central value vanishes at every positive requested jet order. -/
theorem jetResolvent_at_center (m : ℕ) (z b : ℂ) :
    jetResolvent (m + 1) z b 0 = 0 := by
  simp [jetResolvent]

/-- The prescribed jet factor is explicit; analyticity of its quotient near
zero needs z and b nonzero, as in jetResolvent_quotient_continuous. -/
theorem jetResolvent_factor (m : ℕ) (z b w : ℂ) :
    jetResolvent m z b w = w ^ m *
      ((b - z) ^ (m + 1) / (z ^ m * (z - w) * (b - w) ^ (m + 1))) := by
  unfold jetResolvent
  ring

/-- Local regularity of the quotient after removing the central power. -/
theorem jetResolvent_quotient_continuous (m : ℕ) (z b : ℂ)
    (hz : z ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun w : ℂ =>
      (b - z) ^ (m + 1) / (z ^ m * (z - w) * (b - w) ^ (m + 1))) 0 := by
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simpa using mul_ne_zero (mul_ne_zero (pow_ne_zero m hz) hz)
      (pow_ne_zero (m + 1) hb)

/-- Removing the moving simple denominator leaves this explicit factor. -/
theorem jetResolvent_clear_pole (m : ℕ) (z b w : ℂ) (hzw : z ≠ w) :
    (z - w) * jetResolvent m z b w =
      (b - z) ^ (m + 1) * w ^ m / (z ^ m * (b - w) ^ (m + 1)) := by
  unfold jetResolvent
  field_simp [sub_ne_zero.mpr hzw]

/-- The cleared factor has value one at the moving pole, so the central
correction does not erase an off-center spectral point. -/
theorem jetResolvent_pole_factor (m : ℕ) (b w : ℂ)
    (hw : w ≠ 0) (hbw : b ≠ w) :
    (b - w) ^ (m + 1) * w ^ m / (w ^ m * (b - w) ^ (m + 1)) = 1 := by
  have h₁ := pow_ne_zero m hw
  have h₂ := pow_ne_zero (m + 1) (sub_ne_zero.mpr hbw)
  field_simp

/-- An actual time-domain candidate in the logarithmic variable for order one. -/
noncomputable def firstJetTest (z b x : ℂ) : ℂ :=
  Complex.exp (-z * x) - Complex.exp (-b * x) +
    (b * (z - b) / z) * x * Complex.exp (-b * x)

/-- The correction keeps the endpoint value zero, cancelling the local kernel. -/
theorem firstJetTest_at_zero (z b : ℂ) : firstJetTest z b 0 = 0 := by
  simp [firstJetTest]

/-- The exact Laplace moment algebra; identifying the terms with improper
integrals requires Re(z)>0 and Re(b)>0 and is not asserted here. -/
theorem firstJetTest_moment (z b : ℂ) (hz : z ≠ 0) (hb : b ≠ 0) :
    1 / z - 1 / b + (b * (z - b) / z) / b ^ 2 = 0 := by
  field_simp
  ring

end MasulloGRH

#check MasulloGRH.jetResolvent_one
#print axioms MasulloGRH.jetResolvent_one
#check MasulloGRH.jetResolvent_at_center
#print axioms MasulloGRH.jetResolvent_at_center
#check MasulloGRH.jetResolvent_factor
#print axioms MasulloGRH.jetResolvent_factor
#check MasulloGRH.jetResolvent_quotient_continuous
#print axioms MasulloGRH.jetResolvent_quotient_continuous
#check MasulloGRH.jetResolvent_clear_pole
#print axioms MasulloGRH.jetResolvent_clear_pole
#check MasulloGRH.jetResolvent_pole_factor
#print axioms MasulloGRH.jetResolvent_pole_factor
#check MasulloGRH.firstJetTest_at_zero
#print axioms MasulloGRH.firstJetTest_at_zero
#check MasulloGRH.firstJetTest_moment
#print axioms MasulloGRH.firstJetTest_moment

namespace MasulloGRH
open Filter Topology

/-- The pole coefficient is a genuine punctured limit, not a value assigned
at a totalized division by zero. The off-center point remains detectable. -/
theorem jetResolvent_pole_limit (m : ℕ) (b w : ℂ)
    (hw : w ≠ 0) (hbw : b ≠ w) :
    Tendsto (fun z : ℂ => (z - w) * jetResolvent m z b w)
      (nhdsWithin w ({w}ᶜ : Set ℂ)) (nhds 1) := by
  have hc : ContinuousAt (fun z : ℂ =>
      (b - z) ^ (m + 1) * w ^ m / (z ^ m * (b - w) ^ (m + 1))) w := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero (pow_ne_zero m hw)
        (pow_ne_zero (m + 1) (sub_ne_zero.mpr hbw))
  have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({w}ᶜ : Set ℂ)))
  rw [jetResolvent_pole_factor m b w hw hbw] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (jetResolvent_clear_pole m z b w (by simpa using hz)).symm

/-- Differentiating the explicit time-domain correction at the endpoint. -/
theorem firstJetTest_hasDerivAt_zero (z b : ℂ) :
    HasDerivAt (firstJetTest z b) (-z + b + b * (z - b) / z) 0 := by
  have hz : HasDerivAt (fun x : ℂ => Complex.exp (-z * x)) (-z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (-z)).cexp
  have hb : HasDerivAt (fun x : ℂ => Complex.exp (-b * x)) (-b) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (-b)).cexp
  have hd := (hz.sub hb).add
    (((hasDerivAt_id (0 : ℂ)).const_mul (b * (z - b) / z)).mul hb)
  change HasDerivAt (fun x => firstJetTest z b x) _ _
  simpa [firstJetTest, Pi.add_def, Pi.sub_def, Pi.mul_def, sub_eq_add_neg] using hd

/-- The order-one repair removes the endpoint singularity for arbitrary
complex parameters, not merely the sample rational parameters of round 1. -/
theorem firstJetTest_endpoint_limit (z b : ℂ) :
    Tendsto (fun x : ℂ => firstJetTest z b x / (Complex.exp x - 1))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (-z + b + b * (z - b) / z)) := by
  have hn := (firstJetTest_hasDerivAt_zero z b).tendsto_slope_zero
  have hd : HasDerivAt (fun x : ℂ => Complex.exp x - 1) 1 0 := by
    simpa using (Complex.hasDerivAt_exp 0).sub_const 1
  have he := hd.tendsto_slope_zero
  simp only [zero_add, firstJetTest_at_zero, sub_zero, smul_eq_mul] at hn
  simp only [zero_add, Complex.exp_zero, sub_self, sub_zero, smul_eq_mul] at he
  have hq := hn.div he (by norm_num : (1 : ℂ) ≠ 0)
  simp only [div_one] at hq
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  exact mul_div_mul_left _ _ (inv_ne_zero hx0)

/-- A usable quadratic spectral tail bound for the order-one correction.
This bounds the limiting kernel; uniform estimates for cutoff approximants
and genuine Hecke zero counts are still required. -/
theorem jetResolvent_one_tail (z b w : ℂ) (hz : z ≠ 0)
    (hw : 0 < ‖w‖) (hzw : 2 * ‖z‖ ≤ ‖w‖) (hbw : 2 * ‖b‖ ≤ ‖w‖) :
    ‖jetResolvent 1 z b w‖ ≤ 8 * ‖b - z‖ ^ 2 / (‖z‖ * ‖w‖ ^ 2) := by
  have h₁ : ‖w‖ / 2 ≤ ‖z - w‖ := by
    have hh := norm_sub_norm_le w z
    rw [norm_sub_rev] at hh
    linarith
  have h₂ : ‖w‖ / 2 ≤ ‖b - w‖ := by
    have hh := norm_sub_norm_le w b
    rw [norm_sub_rev] at hh
    linarith
  have h₁p : 0 < ‖z - w‖ := by linarith
  have h₂p : 0 < ‖b - w‖ := by linarith
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h₂sq : ‖w‖ ^ 2 / 4 ≤ ‖b - w‖ ^ 2 := by nlinarith
  have hprod := mul_le_mul h₁ h₂sq (by positivity : 0 ≤ ‖w‖ ^ 2 / 4)
    (norm_nonneg (z - w))
  have hcub : ‖w‖ ^ 3 ≤ 8 * (‖z - w‖ * ‖b - w‖ ^ 2) := by
    nlinarith
  unfold jetResolvent
  norm_num only [Nat.reduceAdd, pow_one, norm_div, norm_mul, norm_pow]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hm := mul_le_mul_of_nonneg_left hcub (sq_nonneg ‖b - z‖)
  have hmz := mul_le_mul_of_nonneg_left hm hzp.le
  nlinarith

end MasulloGRH
#check MasulloGRH.jetResolvent_pole_limit
#print axioms MasulloGRH.jetResolvent_pole_limit
#check MasulloGRH.firstJetTest_hasDerivAt_zero
#print axioms MasulloGRH.firstJetTest_hasDerivAt_zero
#check MasulloGRH.firstJetTest_endpoint_limit
#print axioms MasulloGRH.firstJetTest_endpoint_limit
#check MasulloGRH.jetResolvent_one_tail
#print axioms MasulloGRH.jetResolvent_one_tail


namespace MasulloGRH

/-- The quotient by the central power is holomorphic near zero. Together
with jetResolvent_factor this gives an actual analytic central factor. -/
theorem jetResolvent_quotient_analytic (m : ℕ) (z b : ℂ)
    (hz : z ≠ 0) (hb : b ≠ 0) :
    AnalyticAt ℂ (fun w : ℂ =>
      (b - z) ^ (m + 1) / (z ^ m * (z - w) * (b - w) ^ (m + 1))) 0 := by
  apply AnalyticAt.div analyticAt_const
  · exact (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)).mul
      ((analyticAt_const.sub analyticAt_id).pow (m + 1))
  · simpa using mul_ne_zero (mul_ne_zero (pow_ne_zero m hz) hz)
      (pow_ne_zero (m + 1) hb)

end MasulloGRH
#check MasulloGRH.jetResolvent_quotient_analytic
#print axioms MasulloGRH.jetResolvent_quotient_analytic
