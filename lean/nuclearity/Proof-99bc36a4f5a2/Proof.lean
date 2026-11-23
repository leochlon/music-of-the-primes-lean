import Mathlib

/-!
Participant C, round 2, proof phase. Inherited results are followed by new series work.
The full all-number-field, all-continuous-unitary-Hecke-character GRH target
is unresolved. This file will record only proved supporting results.
-/

namespace MasulloGRH

/-- At z = 3/2 the positive real-place summand has this kernel on t > 1.
This bound isolates the logarithmic endpoint obstruction in PDF page 29. -/
theorem archimedean_kernel_lower_bound (t : ℝ) (h1 : 1 < t) (h2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ 1 / (t ^ 2 * (t - 1)) := by
  have ht : 0 < t := by linarith
  have hd : 0 < t - 1 := by linarith
  have hs : t ^ 2 ≤ 4 := by nlinarith
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (t - 1))
    (by positivity : 0 < t ^ 2 * (t - 1))).2
  nlinarith

#check archimedean_kernel_lower_bound
#print axioms archimedean_kernel_lower_bound

/-- A translated, truncated positive real-place integral. The translation is
u = t - 1; no Hecke L-function is defined by this auxiliary integral. -/
noncomputable def cutoffIntegral (ε : ℝ) : ℝ :=
  ∫ u in ε..1, 1 / ((u + 1) ^ 2 * u)

theorem cutoffIntegral_lower_bound (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1 / 4 : ℝ) * Real.log (1 / ε) ≤ cutoffIntegral ε := by
  have hc₁ : ContinuousOn (fun u : ℝ => (1 / 4 : ℝ) * (1 / u))
      (Set.uIcc ε 1) := by
    rw [Set.uIcc_of_le hε1]
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hε hu.1)
    exact (continuousAt_const.mul (continuousAt_const.div continuousAt_id hu0)).continuousWithinAt
  have hc₂ : ContinuousOn (fun u : ℝ => 1 / ((u + 1) ^ 2 * u))
      (Set.uIcc ε 1) := by
    rw [Set.uIcc_of_le hε1]
    intro u hu
    have hup : 0 < u := lt_of_lt_of_le hε hu.1
    have hu0 : u ≠ 0 := ne_of_gt hup
    have hu1 : u + 1 ≠ 0 := by linarith
    exact (continuousAt_const.div
      (((continuousAt_id.add continuousAt_const).pow 2).mul continuousAt_id)
      (mul_ne_zero (pow_ne_zero 2 hu1) hu0)).continuousWithinAt
  calc
    (1 / 4 : ℝ) * Real.log (1 / ε) =
        ∫ u in ε..1, (1 / 4 : ℝ) * (1 / u) := by
      rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos hε (by norm_num)]
    _ ≤ cutoffIntegral ε := by
      apply intervalIntegral.integral_mono_on hε1 hc₁.intervalIntegrable hc₂.intervalIntegrable
      intro u hu
      have hup : 0 < u := lt_of_lt_of_le hε hu.1
      have hk := archimedean_kernel_lower_bound (u + 1) (by linarith) (by linarith [hu.2])
      simpa only [add_sub_cancel_right, one_div, mul_inv_rev, inv_pow, mul_comm] using hk

#check cutoffIntegral_lower_bound
#print axioms cutoffIntegral_lower_bound

/-- The endpoint obstruction is unbounded, even at the single real parameter
z = 3/2 in the manuscript's domain Re(z) > 1. -/
theorem cutoffIntegral_unbounded (B : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ B < cutoffIntegral ε := by
  let ε := Real.exp (-(4 * (|B| + 1)))
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [Real.exp_lt_one_iff]
    have := abs_nonneg B
    linarith
  refine ⟨ε, hε, hε1, ?_⟩
  have hl := cutoffIntegral_lower_bound ε hε hε1.le
  have he : Real.log (1 / ε) = 4 * (|B| + 1) := by
    simp [ε, one_div, Real.log_inv, Real.log_exp]
  rw [he] at hl
  have := le_abs_self B
  linarith

#check cutoffIntegral_unbounded
#print axioms cutoffIntegral_unbounded

/-- Subtracting the z=1/2 kernel from the z=3/2 kernel cancels the
singularity exactly. This motivates a difference-based analytic repair. -/
theorem archimedean_kernel_difference (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    1 / (t ^ 2 * (t - 1)) - 1 / (t * (t - 1)) = -(1 / t ^ 2) := by
  have ht : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

#check archimedean_kernel_difference
#print axioms archimedean_kernel_difference

/-- In logarithmic coordinates t = exp(u), subtracting any two complex
parameters removes the endpoint singularity. For the manuscript's positive
real-place kernel set a = 1/2-z and b = 1/2-z₀. -/
theorem exponential_difference_limit (a b : ℂ) :
    Filter.Tendsto
      (fun u : ℂ => (Complex.exp (a * u) - Complex.exp (b * u)) /
        (Complex.exp u - 1))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (a - b)) := by
  have ha : HasDerivAt (fun u : ℂ => Complex.exp (a * u)) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).cexp
  have hb : HasDerivAt (fun u : ℂ => Complex.exp (b * u)) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).const_mul b).cexp
  have hd : HasDerivAt (fun u : ℂ => Complex.exp u - 1) 1 0 := by
    simpa using (Complex.hasDerivAt_exp 0).sub_const 1
  have hn := (ha.sub hb).tendsto_slope_zero
  have he := hd.tendsto_slope_zero
  simp only [Pi.sub_apply, zero_add, mul_zero, Complex.exp_zero, sub_self, sub_zero,
    smul_eq_mul] at hn he
  have hq := hn.div he (by norm_num : (1 : ℂ) ≠ 0)
  simp only [div_one] at hq
  apply hq.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := by simpa using hu
  exact mul_div_mul_left _ _ (inv_ne_zero hu0)

#check exponential_difference_limit
#print axioms exponential_difference_limit

/-- Subtracting two resolvents improves their decay in the spectral variable
from first to second order. Summability for genuine Hecke zeros is separate. -/
theorem resolvent_difference (z w r : ℂ) (hz : z ≠ r) (hw : w ≠ r) :
    1 / (z - r) - 1 / (w - r) = (w - z) / ((z - r) * (w - r)) := by
  have hz' : z - r ≠ 0 := sub_ne_zero.mpr hz
  have hw' : w - r ≠ 0 := sub_ne_zero.mpr hw
  field_simp
  ring

#check resolvent_difference
#print axioms resolvent_difference

/-- A quantitative version of the spectral improvement, suitable for a
dyadic-shell summability argument once genuine zero counts are established. -/
theorem resolvent_difference_bound (z w r : ℂ) (hr : 0 < ‖r‖)
    (hz : 2 * ‖z‖ ≤ ‖r‖) (hw : 2 * ‖w‖ ≤ ‖r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ 4 * ‖w - z‖ / ‖r‖ ^ 2 := by
  have hzL : ‖r‖ / 2 ≤ ‖z - r‖ := by
    have h := norm_sub_norm_le r z
    rw [norm_sub_rev] at h
    linarith
  have hwL : ‖r‖ / 2 ≤ ‖w - r‖ := by
    have h := norm_sub_norm_le r w
    rw [norm_sub_rev] at h
    linarith
  have hzp : 0 < ‖z - r‖ := by linarith
  have hwp : 0 < ‖w - r‖ := by linarith
  have hzne : z ≠ r := sub_ne_zero.mp (norm_pos_iff.mp hzp)
  have hwne : w ≠ r := sub_ne_zero.mp (norm_pos_iff.mp hwp)
  rw [resolvent_difference z w r hzne hwne, norm_div, norm_mul]
  apply (div_le_div_iff₀ (mul_pos hzp hwp) (sq_pos_of_pos hr)).2
  have hp := mul_le_mul hzL hwL (by positivity : 0 ≤ ‖r‖ / 2)
    (norm_nonneg (z - r))
  have hm := mul_le_mul_of_nonneg_left hp (norm_nonneg (w - z))
  nlinarith

#check resolvent_difference_bound
#print axioms resolvent_difference_bound

/-- A common parameter-disk bound for the subtracted resolvent. -/
theorem resolvent_difference_uniform_bound (z w r : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hr : 0 < ‖r‖)
    (hR : 2 * R ≤ ‖r‖) :
    ‖1 / (z-r) - 1 / (w-r)‖ ≤ 8 * R / ‖r‖ ^ 2 := by
  have hd : ‖w-z‖ ≤ 2 * R := le_trans (norm_sub_le w z) (by linarith)
  exact le_trans (resolvent_difference_bound z w r hr (by linarith) (by linarith))
    (div_le_div_of_nonneg_right (by linarith) (sq_nonneg ‖r‖))

#check resolvent_difference_uniform_bound
#print axioms resolvent_difference_uniform_bound

/-- A genuine infinite-series consequence of the inverse-square bound.
The explicit hypothesis is a summable inverse-square divisor, not GRH.
The cofinite radius hypothesis discards only finitely many exceptional terms.
This theorem alone does not assert holomorphy at any pole. -/
theorem summable_resolvent_differences {ι : Type*} (r : ι → ℂ) (z w : ℂ)
    (hs : Summable (fun i => 1 / ‖r i‖ ^ 2))
    (hr : ∀ᶠ i in Filter.cofinite,
      0 < ‖r i‖ ∧ 2 * ‖z‖ ≤ ‖r i‖ ∧ 2 * ‖w‖ ≤ ‖r i‖) :
    Summable (fun i => 1 / (z-r i) - 1 / (w-r i)) := by
  apply (hs.mul_left (4 * ‖w-z‖)).of_norm_bounded_eventually
  filter_upwards [hr] with i hi
  simpa only [mul_one_div] using resolvent_difference_bound z w (r i) hi.1 hi.2.1 hi.2.2

#check summable_resolvent_differences
#print axioms summable_resolvent_differences

/-- Uniform convergence on a parameter disk of the far spectral tail.
All inverse-square and radius hypotheses are displayed, and still need to be
proved for a genuine multiplicity-indexed Hecke divisor. -/
theorem resolvent_series_uniform_on_disk (r : ℕ → ℂ) (w : ℂ) (R : ℝ)
    (hw : ‖w‖ ≤ R) (hs : Summable (fun n => 1 / ‖r n‖ ^ 2))
    (hr : ∀ n, 0 < ‖r n‖ ∧ 2 * R ≤ ‖r n‖) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, (1 / (z-r n) - 1 / (w-r n)))
      (fun z => ∑' n, (1 / (z-r n) - 1 / (w-r n)))
      Filter.atTop {z : ℂ | ‖z‖ ≤ R} := by
  apply tendstoUniformlyOn_tsum_nat (hs.mul_left (8 * R))
  intro n z hz
  simpa only [mul_one_div] using
    resolvent_difference_uniform_bound z w (r n) R hz hw (hr n).1 (hr n).2

#check resolvent_series_uniform_on_disk
#print axioms resolvent_series_uniform_on_disk

/-- The dyadic majorant required by a multiplicity count O(T log T) is summable. -/
theorem dyadic_count_majorant_summable :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) := by
  have h₁ := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
    (r := (1 / 2 : ℝ)) (by norm_num)
  have h₂ := summable_geometric_of_norm_lt_one (x := (1 / 2 : ℝ)) (by norm_num)
  convert h₁.add h₂ using 1
  ext k
  simp only [pow_one]
  ring

#check dyadic_count_majorant_summable
#print axioms dyadic_count_majorant_summable

/-- Dominated convergence for the actual cutoff coefficients requires a
single summable majorant independent of the cutoff index. A bound only on
the limiting resolvents is insufficient. -/
theorem cutoff_spectral_limit {ι : Type*} (a : ℕ → ι → ℂ) (r : ι → ℂ)
    (z w : ℂ) (B : ι → ℝ) (hB : Summable B)
    (hlim : ∀ i, Filter.Tendsto (fun n => a n i) Filter.atTop
      (nhds (1 / (z-r i) - 1 / (w-r i))))
    (hbound : ∀ᶠ n in Filter.atTop, ∀ i, ‖a n i‖ ≤ B i) :
    Filter.Tendsto (fun n => ∑' i, a n i) Filter.atTop
      (nhds (∑' i, (1 / (z-r i) - 1 / (w-r i)))) := by
  exact tendsto_tsum_of_dominated_convergence hB hlim hbound

#check cutoff_spectral_limit
#print axioms cutoff_spectral_limit

/-- A dyadic multiplicity count implies summability of inverse-square shell
masses. Each j in range (N k) is a separate occurrence, so multiplicity is
retained. Covering the genuine divisor by these shells is a separate task. -/
theorem dyadic_inverse_square_shells (N : ℕ → ℕ) (r : ℕ → ℕ → ℂ)
    (C : ℝ)
    (hcount : ∀ k, (N k : ℝ) ≤ C * ((k : ℝ) + 1) * (2 : ℝ)^k)
    (hr : ∀ k j, j < N k → (2 : ℝ)^k ≤ ‖r k j‖) :
    Summable (fun k => ∑ j ∈ Finset.range (N k), 1 / ‖r k j‖^2) := by
  apply Summable.of_nonneg_of_le
    (fun k => Finset.sum_nonneg (fun j _ => by positivity))
    (fun k => ?_) (dyadic_count_majorant_summable.mul_left C)
  have hpow : 0 < (2 : ℝ)^k := by positivity
  calc
    (∑ j ∈ Finset.range (N k), 1 / ‖r k j‖^2) ≤
        ∑ _j ∈ Finset.range (N k), 1 / ((2 : ℝ)^k)^2 := by
      apply Finset.sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le (by positivity)
      have h := hr k j (Finset.mem_range.mp hj)
      nlinarith [norm_nonneg (r k j)]
    _ = (N k : ℝ) * (1 / ((2 : ℝ)^k)^2) := by simp
    _ ≤ (C * ((k : ℝ)+1) * (2 : ℝ)^k) * (1 / ((2 : ℝ)^k)^2) :=
      mul_le_mul_of_nonneg_right (hcount k) (by positivity)
    _ = C * (((k : ℝ)+1) * (1/2 : ℝ)^k) := by
      rw [one_div_pow]
      field_simp

#check dyadic_inverse_square_shells
#print axioms dyadic_inverse_square_shells

/-- A sequence of images eventually annihilated by a continuous functional
cannot converge to a vector on which that functional is nonzero. This is the
precise obstruction to the low-zero kernel projections on PDF p.426. -/
theorem strong_limit_annihilator {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (ell : E →L[ℂ] ℂ) (P : ℕ → E → E) (x : E)
    (hzero : ∀ᶠ n in Filter.atTop, ell (P n x) = 0)
    (hlim : Filter.Tendsto (fun n => P n x) Filter.atTop (nhds x)) :
    ell x = 0 := by
  have h₁ := ell.continuous.continuousAt.tendsto.comp hlim
  have h₂ : Filter.Tendsto (fun n => ell (P n x)) Filter.atTop (nhds (0 : ℂ)) :=
    tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm))
  exact tendsto_nhds_unique h₁ h₂

#check strong_limit_annihilator
#print axioms strong_limit_annihilator

/-- Consequently, a nonzero continuous evaluation rules out the claimed
strong identity limit when it annihilates all sufficiently late images. -/
theorem no_strong_identity_of_eventual_annihilation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (ell : E →L[ℂ] ℂ) (P : ℕ → E → E) (x : E) (hx : ell x ≠ 0)
    (hzero : ∀ᶠ n in Filter.atTop, ell (P n x) = 0) :
    ¬ Filter.Tendsto (fun n => P n x) Filter.atTop (nhds x) := by
  intro hlim
  exact hx (strong_limit_annihilator ell P x hzero hlim)

#check no_strong_identity_of_eventual_annihilation
#print axioms no_strong_identity_of_eventual_annihilation

/-- The dyadic shell estimate gives an ungrouped, multiplicity-indexed
summable inverse-square divisor, not merely a convergent grouped series. -/
theorem dyadic_inverse_square_divisor (N : ℕ → ℕ) (r : ℕ → ℕ → ℂ)
    (C : ℝ)
    (hcount : ∀ k, (N k : ℝ) ≤ C * ((k : ℝ) + 1) * (2 : ℝ)^k)
    (hr : ∀ k j, j < N k → (2 : ℝ)^k ≤ ‖r k j‖) :
    Summable (fun i : (k : ℕ) × Fin (N k) => 1 / ‖r i.1 i.2‖^2) := by
  apply (summable_sigma_of_nonneg (fun i => by positivity)).2
  constructor
  · intro k
    exact (hasSum_fintype (fun j : Fin (N k) => 1 / ‖r k j‖^2)).summable
  · apply (dyadic_inverse_square_shells N r C hcount hr).congr
    intro k
    rw [tsum_fintype]
    exact (Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ‖r k j‖^2) (N k)).symm

#check dyadic_inverse_square_divisor
#print axioms dyadic_inverse_square_divisor

end MasulloGRH
