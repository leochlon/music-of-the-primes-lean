import Mathlib

/-!
Participant F, round 2, proof phase. Initial checkpoint from frozen round 1. Supporting results only.
The target is GRH for all genuine unitary Hecke characters over all number fields.
No theorem below claims to construct their L-functions or prove that target.

At the trivial real place and real parameter z = 3/2, the positive-t summand
on manuscript PDF p.29, with dt/t included, tends to 1/(t^2*(t-1)).
The following identities isolate the singularity and a possible subtraction repair.
-/
namespace MasulloGRH

noncomputable def archKernel (t : ℝ) : ℝ := 1 / (t ^ 2 * (t - 1))

theorem archKernel_partialFractions (t : ℝ) (ht : t ≠ 0) (h1 : t ≠ 1) :
    archKernel t = 1 / (t - 1) - 1 / t - 1 / t ^ 2 := by
  unfold archKernel
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

theorem archKernel_subtraction (t : ℝ) (ht : t ≠ 0) (h1 : t ≠ 1) :
    archKernel t - 1 / (t ^ 3 * (t - 1)) = 1 / t ^ 3 := by
  unfold archKernel
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

theorem archKernel_lowerBound (t : ℝ) (hlo : 1 < t) (hhi : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ archKernel t := by
  unfold archKernel
  have ht : 0 < t := by linarith
  have hs : 0 < t - 1 := by linarith
  apply one_div_le_one_div_of_le (by positivity)
  have hsq : t ^ 2 ≤ 4 := by nlinarith
  nlinarith

theorem resolvent_subtraction (z w r : ℂ) (hz : z ≠ r) (hw : w ≠ r) :
    1 / (z - r) - 1 / (w - r) = (w - z) / ((z - r) * (w - r)) := by
  have hz' : z - r ≠ 0 := sub_ne_zero.mpr hz
  have hw' : w - r ≠ 0 := sub_ne_zero.mpr hw
  field_simp
  ring

theorem resolvent_norm_bound (z w r : ℂ) (R : ℝ) (hR : 0 < R)
    (hz : R ≤ ‖z - r‖) (hw : R ≤ ‖w - r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ ‖w - z‖ / R ^ 2 := by
  have hz0 : z ≠ r := by
    intro heq
    rw [heq, sub_self, norm_zero] at hz
    linarith
  have hw0 : w ≠ r := by
    intro heq
    rw [heq, sub_self, norm_zero] at hw
    linarith
  rw [resolvent_subtraction z w r hz0 hw0, norm_div, norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hR)
  have h := mul_le_mul hz hw (le_of_lt hR) (norm_nonneg (z - r))
  nlinarith

theorem logarithmic_endpoint_unbounded (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ B < -Real.log δ := by
  refine ⟨Real.exp (-(|B| + 1)), Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have := abs_nonneg B
    linarith
  · rw [Real.log_exp]
    have := le_abs_self B
    linarith

theorem singular_integral (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (1 + δ)..2, 1 / (t - 1)) = -Real.log δ := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) 1]
  have ha : 1 + δ - 1 = δ := by ring
  rw [ha]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  rw [integral_one_div_of_pos hδ (by norm_num),
    Real.log_div (by norm_num) (ne_of_gt hδ), Real.log_one, zero_sub]

theorem archKernel_integral_lowerBound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    -Real.log δ / 4 ≤ ∫ t in (1 + δ)..2, archKernel t := by
  have hab : 1 + δ ≤ (2 : ℝ) := by linarith
  have hp : ∀ t ∈ Set.uIcc (1 + δ) 2, 1 < t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.uIcc (1 + δ) 2) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    change t - 1 ≠ 0
    linarith [hp t ht]
  have hk : ContinuousOn archKernel (Set.uIcc (1 + δ) 2) := by
    unfold archKernel
    apply continuousOn_const.div ((continuousOn_id.pow 2).mul
      (continuousOn_id.sub continuousOn_const))
    intro t ht
    have h : 1 < t := hp t ht
    change t ^ 2 * (t - 1) ≠ 0
    have ht0 : 0 < t := by linarith
    have hs : 0 < t - 1 := by linarith
    positivity
  have hcomp := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hc.intervalIntegrable.div_const 4) hk.intervalIntegrable
    (fun t ht => by
      have ht1 : 1 < t := by linarith [ht.1]
      have h := archKernel_lowerBound t ht1 ht.2
      simpa only [div_div, mul_comm] using h)
  rw [intervalIntegral.integral_div, singular_integral δ hδ] at hcomp
  exact hcomp

theorem archKernel_integral_unbounded (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ B < ∫ t in (1 + δ)..2, archKernel t := by
  obtain ⟨δ, hδ, hδ1, hlarge⟩ := logarithmic_endpoint_unbounded (4 * B)
  refine ⟨δ, hδ, hδ1, ?_⟩
  have h := archKernel_integral_lowerBound δ hδ hδ1
  linarith

end MasulloGRH

#check MasulloGRH.archKernel_partialFractions
#print axioms MasulloGRH.archKernel_partialFractions
#check MasulloGRH.archKernel_subtraction
#print axioms MasulloGRH.archKernel_subtraction
#check MasulloGRH.archKernel_lowerBound
#print axioms MasulloGRH.archKernel_lowerBound
#check MasulloGRH.resolvent_subtraction
#print axioms MasulloGRH.resolvent_subtraction
#check MasulloGRH.resolvent_norm_bound
#print axioms MasulloGRH.resolvent_norm_bound
#check MasulloGRH.logarithmic_endpoint_unbounded
#print axioms MasulloGRH.logarithmic_endpoint_unbounded
#check MasulloGRH.singular_integral
#print axioms MasulloGRH.singular_integral
#check MasulloGRH.archKernel_integral_lowerBound
#print axioms MasulloGRH.archKernel_integral_lowerBound
#check MasulloGRH.archKernel_integral_unbounded
#print axioms MasulloGRH.archKernel_integral_unbounded

namespace MasulloGRH

/-- Triangle-inequality specialization of the round-1 denominator bound.
Adapted from frozen round-1 C/E, with the denominator estimate proved here. -/
theorem resolvent_tail_bound (z w r : ℂ) (hr : 0 < ‖r‖)
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
  have h := resolvent_norm_bound z w r (‖r‖ / 2) (by positivity) hzL hwL
  convert h using 1
  ring

/-- A common summable majorant on a parameter disk; this controls the limiting
resolvents, not the Mellin transforms of cutoff approximants. -/
theorem resolvent_disk_bound (z w r : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hr : 0 < ‖r‖)
    (hlarge : 2 * R ≤ ‖r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ (8 * R) * (1 / ‖r‖ ^ 2) := by
  have hzw : ‖w - z‖ ≤ 2 * R := (norm_sub_le w z).trans (by linarith)
  calc
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ 4 * ‖w - z‖ / ‖r‖ ^ 2 :=
      resolvent_tail_bound z w r hr (by linarith) (by linarith)
    _ ≤ (8 * R) * (1 / ‖r‖ ^ 2) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- Absolute convergence of the paired resolvent tail from an explicit
inverse-square summability hypothesis. No Hecke zero count is assumed proved. -/
theorem paired_resolvent_summable (r : ℕ → ℂ) (z w : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 0 < ‖r n‖) (hlarge : ∀ n, 2 * R ≤ ‖r n‖)
    (hs : Summable (fun n => 1 / ‖r n‖ ^ 2)) :
    Summable (fun n => 1 / (z - r n) - 1 / (w - r n)) := by
  exact (hs.mul_left (8 * R)).of_norm_bounded
    (fun n => resolvent_disk_bound z w (r n) R hz hw (hr n) (hlarge n))

/-- The paired resolvent tail converges uniformly on a closed parameter disk.
The summability hypothesis must still be established for genuine Hecke zeros. -/
theorem paired_resolvent_uniform_convergence (r : ℕ → ℂ) (w : ℂ) (R : ℝ)
    (hw : ‖w‖ ≤ R) (hr : ∀ n, 0 < ‖r n‖)
    (hlarge : ∀ n, 2 * R ≤ ‖r n‖)
    (hs : Summable (fun n => 1 / ‖r n‖ ^ 2)) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, (1 / (z - r n) - 1 / (w - r n)))
      (fun z => ∑' n, (1 / (z - r n) - 1 / (w - r n)))
      Filter.atTop {z : ℂ | ‖z‖ ≤ R} := by
  exact tendstoUniformlyOn_tsum_nat (hs.mul_left (8 * R))
    (fun n z hz => resolvent_disk_bound z w (r n) R hz hw (hr n) (hlarge n))

end MasulloGRH
#check MasulloGRH.resolvent_tail_bound
#print axioms MasulloGRH.resolvent_tail_bound
#check MasulloGRH.resolvent_disk_bound
#print axioms MasulloGRH.resolvent_disk_bound
#check MasulloGRH.paired_resolvent_summable
#print axioms MasulloGRH.paired_resolvent_summable
#check MasulloGRH.paired_resolvent_uniform_convergence
#print axioms MasulloGRH.paired_resolvent_uniform_convergence

namespace MasulloGRH

/-- Holomorphy of the paired resolvent tail. This is conditional analytic
work: the genuine zero divisor and its inverse-square count are not built here. -/
theorem paired_resolvent_differentiableOn (r : ℕ → ℂ) (w : ℂ) (R : ℝ)
    (hw : ‖w‖ ≤ R) (hr : ∀ n, 0 < ‖r n‖)
    (hlarge : ∀ n, 2 * R ≤ ‖r n‖)
    (hs : Summable (fun n => 1 / ‖r n‖ ^ 2)) :
    DifferentiableOn ℂ
      (fun z => ∑' n, (1 / (z - r n) - 1 / (w - r n)))
      {z : ℂ | ‖z‖ < R} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (hs.mul_left (8 * R))
  · intro n
    apply DifferentiableOn.sub _ (differentiableOn_const _)
    apply (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _))
    intro z hz
    apply sub_ne_zero.mpr
    intro heq
    have hzR : ‖z‖ < R := hz
    rw [heq] at hzR
    have hn := hlarge n
    have hp := hr n
    linarith
  · exact isOpen_lt continuous_norm continuous_const
  · intro n z hz
    exact resolvent_disk_bound z w (r n) R (le_of_lt hz) hw (hr n) (hlarge n)

/-- The correct sufficient hypothesis for moving a cutoff limit through the
spectral sum is a bound uniform in the cutoff index. This theorem does not
construct cutoff coefficients or assert that the manuscript supplies the bound. -/
theorem paired_resolvent_cutoff_limit (r : ℕ → ℂ) (z w : ℂ) (C : ℝ)
    (hs : Summable (fun k => 1 / ‖r k‖ ^ 2))
    (a : ℕ → ℕ → ℂ)
    (ha : ∀ k, Filter.Tendsto (fun n => a n k) Filter.atTop
      (nhds (1 / (z - r k) - 1 / (w - r k))))
    (hb : ∀ n k, ‖a n k‖ ≤ C * (1 / ‖r k‖ ^ 2)) :
    Filter.Tendsto (fun n => ∑' k, a n k) Filter.atTop
      (nhds (∑' k, (1 / (z - r k) - 1 / (w - r k)))) := by
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left C) ha
    (Filter.Eventually.of_forall hb)

end MasulloGRH
#check MasulloGRH.paired_resolvent_differentiableOn
#print axioms MasulloGRH.paired_resolvent_differentiableOn
#check MasulloGRH.paired_resolvent_cutoff_limit
#print axioms MasulloGRH.paired_resolvent_cutoff_limit

namespace MasulloGRH

/-- The intersection of the kernels of evaluations of height at most T shrinks
as T increases. This audits manuscript (9.3.2.10), PDF p.426. -/
theorem low_constraint_antitone {V I : Type*} (e : I → V → ℂ)
    (height : I → ℝ) (T U : ℝ) (hTU : T ≤ U) :
    {v : V | ∀ i, height i ≤ U → e i v = 0} ⊆
      {v : V | ∀ i, height i ≤ T → e i v = 0} := by
  intro v hv i hi
  exact hv i (hi.trans hTU)

/-- Strong convergence to the identity is incompatible with eventually
annihilating a fixed nonzero continuous coordinate of a vector. -/
theorem strong_limit_preserves_zero_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : E →L[ℂ] ℂ) (P : ℕ → E → E) (v : E) (N : ℕ)
    (hzero : ∀ n, N ≤ n → e (P n v) = 0)
    (hlim : Filter.Tendsto (fun n => P n v) Filter.atTop (nhds v)) :
    e v = 0 := by
  have hmap := (e.continuous.tendsto v).comp hlim
  have hzeroLim : Filter.Tendsto (fun n => e (P n v)) Filter.atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact (hzero n hn).symm
  exact tendsto_nhds_unique hmap hzeroLim

/-- A nonzero coordinate gives an explicit obstruction to the literal
low-zero-kernel projection scheme of Theorem 9.3.2.6. -/
theorem low_kernel_projection_not_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : E →L[ℂ] ℂ) (P : ℕ → E → E) (v : E) (N : ℕ)
    (hv : e v ≠ 0) (hzero : ∀ n, N ≤ n → e (P n v) = 0) :
    ¬ Filter.Tendsto (fun n => P n v) Filter.atTop (nhds v) := by
  intro hlim
  exact hv (strong_limit_preserves_zero_coordinate e P v N hzero hlim)

end MasulloGRH
#check MasulloGRH.low_constraint_antitone
#print axioms MasulloGRH.low_constraint_antitone
#check MasulloGRH.strong_limit_preserves_zero_coordinate
#print axioms MasulloGRH.strong_limit_preserves_zero_coordinate
#check MasulloGRH.low_kernel_projection_not_identity
#print axioms MasulloGRH.low_kernel_projection_not_identity
