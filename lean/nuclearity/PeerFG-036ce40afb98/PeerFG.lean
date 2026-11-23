import Mathlib

/-!
Participant F, round 2, proof phase. Initial checkpoint from frozen round 1. Supporting results only.
The target is GRH for all genuine unitary Hecke characters over all number fields.
No theorem below claims to construct their L-functions or prove that target.

At the trivial real place and real parameter z = 3/2, the positive-t summand
on manuscript PDF p.29, with dt/t included, tends to 1/(t^2*(t-1)).
The following identities isolate the singularity and a possible subtraction repair.
-/
namespace FrozenF

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

end FrozenF

#check FrozenF.archKernel_partialFractions
#print axioms FrozenF.archKernel_partialFractions
#check FrozenF.archKernel_subtraction
#print axioms FrozenF.archKernel_subtraction
#check FrozenF.archKernel_lowerBound
#print axioms FrozenF.archKernel_lowerBound
#check FrozenF.resolvent_subtraction
#print axioms FrozenF.resolvent_subtraction
#check FrozenF.resolvent_norm_bound
#print axioms FrozenF.resolvent_norm_bound
#check FrozenF.logarithmic_endpoint_unbounded
#print axioms FrozenF.logarithmic_endpoint_unbounded
#check FrozenF.singular_integral
#print axioms FrozenF.singular_integral
#check FrozenF.archKernel_integral_lowerBound
#print axioms FrozenF.archKernel_integral_lowerBound
#check FrozenF.archKernel_integral_unbounded
#print axioms FrozenF.archKernel_integral_unbounded

namespace FrozenF

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

end FrozenF
#check FrozenF.resolvent_tail_bound
#print axioms FrozenF.resolvent_tail_bound
#check FrozenF.resolvent_disk_bound
#print axioms FrozenF.resolvent_disk_bound
#check FrozenF.paired_resolvent_summable
#print axioms FrozenF.paired_resolvent_summable
#check FrozenF.paired_resolvent_uniform_convergence
#print axioms FrozenF.paired_resolvent_uniform_convergence

namespace FrozenF

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

end FrozenF
#check FrozenF.paired_resolvent_differentiableOn
#print axioms FrozenF.paired_resolvent_differentiableOn
#check FrozenF.paired_resolvent_cutoff_limit
#print axioms FrozenF.paired_resolvent_cutoff_limit

namespace FrozenF

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

end FrozenF
#check FrozenF.low_constraint_antitone
#print axioms FrozenF.low_constraint_antitone
#check FrozenF.strong_limit_preserves_zero_coordinate
#print axioms FrozenF.strong_limit_preserves_zero_coordinate
#check FrozenF.low_kernel_projection_not_identity
#print axioms FrozenF.low_kernel_projection_not_identity



/-!
Participant G, round 2, proof phase. Supporting results only.
The genuine all-number-field Hecke GRH construction and proof remain open here.
No declaration below is asserted to prove that target.
-/

namespace FrozenG

noncomputable section

/-- A norm twist changes the spectral parameter by a purely imaginary amount. -/
def normTwistParameter (s : ℂ) (t : ℝ) : ℂ := s + (t : ℂ) * Complex.I

theorem normTwistParameter_re (s : ℂ) (t : ℝ) :
    (normTwistParameter s t).re = s.re := by
  simp [normTwistParameter]

/-- The open critical strip is invariant under all real norm twists. -/
theorem normTwistParameter_mem_strip (s : ℂ) (t : ℝ) :
    (0 < (normTwistParameter s t).re ∧ (normTwistParameter s t).re < 1) ↔
    (0 < s.re ∧ s.re < 1) := by
  simp [normTwistParameter_re]

/-- Algebraic prerequisite for comparing finite and completed L-values at
regular points where the completing factor is nonzero. -/
theorem completion_zero_iff (A L : ℂ → ℂ) (s : ℂ) (hA : A s ≠ 0) :
    A s * L s = 0 ↔ L s = 0 := by
  simp [mul_eq_zero, hA]

/-- The logarithmic singularity in the positive real-place contribution,
written in the coordinate x = t - 1. -/
def cutoffSingularity (n : ℕ) : ℝ :=
  ∫ x in Real.exp (-(n : ℝ))..1, 1 / x

theorem cutoffSingularity_eq (n : ℕ) : cutoffSingularity n = (n : ℝ) := by
  have hp : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have he : Real.exp (-(n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have hz : (0 : ℝ) ∉ Set.uIcc (Real.exp (-(n : ℝ))) 1 := by
    rw [Set.uIcc_of_le he]
    intro h
    have hh := h.1
    linarith
  unfold cutoffSingularity
  rw [integral_one_div hz]
  rw [Real.log_div (by norm_num) (ne_of_gt hp), Real.log_one, Real.log_exp]
  ring

theorem cutoffSingularity_unbounded (A : ℝ) :
    ∃ n : ℕ, A < cutoffSingularity n := by
  obtain ⟨n, hn⟩ := exists_nat_gt A
  exact ⟨n, by simpa [cutoffSingularity_eq] using hn⟩

/-- For F = Q, chi = 1 and z = 3/2, the positive real-place integrand
apart from its factor 1/2 becomes this function after x = t - 1. -/
def realPlaceKernel (x : ℝ) : ℝ := 1 / (x * (1 + x)^2)

theorem realPlaceKernel_lower (x : ℝ) (hx : 0 < x) (h1 : x ≤ 1) :
    (1 / 4 : ℝ) * (1 / x) ≤ realPlaceKernel x := by
  have hs : (1 + x)^2 ≤ 4 := by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr h1)]
  have hd : 0 < x * (1 + x)^2 := by positivity
  have he : (1 / 4 : ℝ) * (1 / x) = 1 / (4 * x) := by ring
  rw [he, realPlaceKernel]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * x) hd).2
  nlinarith [mul_le_mul_of_nonneg_left hs hx.le]

def realPlaceCutoff (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∫ x in Real.exp (-(n : ℝ))..1, realPlaceKernel x

theorem realPlaceCutoff_lower (n : ℕ) : (n : ℝ) / 8 ≤ realPlaceCutoff n := by
  have hp : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have he : Real.exp (-(n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (Nat.cast_nonneg n)
  have hxpos : ∀ x ∈ Set.uIcc (Real.exp (-(n : ℝ))) 1, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le he] at hx
    exact lt_of_lt_of_le hp hx.1
  have hf : ContinuousOn (fun x : ℝ => 1 / x)
      (Set.uIcc (Real.exp (-(n : ℝ))) 1) :=
    continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (hxpos x hx))
  have hg : ContinuousOn realPlaceKernel
      (Set.uIcc (Real.exp (-(n : ℝ))) 1) := by
    unfold realPlaceKernel
    apply continuousOn_const.div
      (continuousOn_id.mul ((continuousOn_const.add continuousOn_id).pow 2))
    intro x hx
    have hx0 := hxpos x hx
    positivity
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) he
    (hf.intervalIntegrable.const_mul (1 / 4 : ℝ)) hg.intervalIntegrable
    (fun x hx => realPlaceKernel_lower x (lt_of_lt_of_le hp hx.1) hx.2)
  rw [intervalIntegral.integral_const_mul] at hi
  change (1 / 4 : ℝ) * cutoffSingularity n ≤ _ at hi
  rw [cutoffSingularity_eq] at hi
  unfold realPlaceCutoff
  linarith

theorem realPlaceCutoff_unbounded (A : ℝ) : ∃ n : ℕ, A < realPlaceCutoff n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (8 * A)
  have hl := realPlaceCutoff_lower n
  exact ⟨n, by linarith⟩

/-- Subtracting the singular kernel leaves a rational function regular at zero.
This is a local repair only; spectral convergence is not asserted. -/
theorem realPlaceKernel_sub_singularity (x : ℝ) (hx : x ≠ 0)
    (hplus : 1 + x ≠ 0) :
    realPlaceKernel x - 1 / x = -(2 + x) / (1 + x)^2 := by
  unfold realPlaceKernel
  field_simp
  ring

theorem realPlaceRegularized_continuousAt_zero :
    ContinuousAt (fun x : ℝ => -(2 + x) / (1 + x)^2) 0 := by
  fun_prop (disch := norm_num)

theorem realPlaceRegularized_value_zero :
    (-(2 + (0 : ℝ)) / (1 + 0)^2) = -2 := by norm_num

theorem realPlaceRegularized_bound (x : ℝ) (hx : 0 ≤ x) :
    |-(2 + x) / (1 + x)^2| ≤ 2 := by
  have hn : 0 ≤ 2 + x := by linarith
  have hd : 0 < (1 + x)^2 := by positivity
  rw [abs_div, abs_neg, abs_of_nonneg hn, abs_of_nonneg (sq_nonneg (1 + x))]
  apply (div_le_iff₀ hd).2
  nlinarith [sq_nonneg x]

/-- Algebraic ingredient for repairing the spectral sum by subtracting its
value at a fixed parameter. The difference has two resolvent denominators. -/
theorem resolvent_difference (z w r : ℂ) (hz : z - r ≠ 0) (hw : w - r ≠ 0) :
    1 / (z - r) - 1 / (w - r) = (w - z) / ((z - r) * (w - r)) := by
  field_simp
  ring

theorem resolvent_difference_norm (z w r : ℂ)
    (hz : z - r ≠ 0) (hw : w - r ≠ 0) :
    ‖1 / (z - r) - 1 / (w - r)‖ = ‖w - z‖ / (‖z - r‖ * ‖w - r‖) := by
  rw [resolvent_difference z w r hz hw, norm_div, norm_mul]


/-- A central-jet correction with an extra reference denominator for each
central factor. This preserves inverse-square decay instead of multiplying
an ordinary paired resolvent by an unbalanced polynomial. -/
def jetResolvent (d : ℕ) (c z w r : ℂ) : ℂ :=
  ((r - c) / (w - r)) ^ d * (1 / ((z - r) * (w - r)))

theorem jetResolvent_central (d : ℕ) (hd : 0 < d) (c z w : ℂ) :
    jetResolvent d c z w c = 0 := by
  simp [jetResolvent, zero_pow (Nat.ne_of_gt hd)]

/-- Exact factorization exposes the central vanishing factor. -/
theorem jetResolvent_factor (d : ℕ) (c z w r : ℂ) :
    jetResolvent d c z w r =
      (r - c)^d / ((z - r) * (w - r)^(d + 1)) := by
  unfold jetResolvent
  rw [div_pow, div_mul_div_comm, mul_one, pow_succ]
  congr 1
  ring

/-- A bound uniform over any family satisfying the displayed inequalities. -/
theorem jetResolvent_bound (d : ℕ) (c z w r : ℂ) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 < R)
    (hz : R ≤ ‖z - r‖) (hw : R ≤ ‖w - r‖)
    (hc : ‖(r - c) / (w - r)‖ ≤ B) :
    ‖jetResolvent d c z w r‖ ≤ B^d * (1 / (R * R)) := by
  have hden : ‖1 / ((z - r) * (w - r))‖ ≤ 1 / (R * R) := by
    rw [norm_div, norm_one, norm_mul]
    exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hR hR)
      (mul_le_mul hz hw hR.le (norm_nonneg _))
  rw [jetResolvent, norm_mul, norm_pow]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hc d) hden
    (norm_nonneg _) (pow_nonneg hB d)

/-- Conditional absolute convergence; inverse-square summability is an
explicit premise, not a claim about genuine Hecke zeros. Multiplicities can
be represented by repeated spectral entries in the index type. -/
theorem jetResolvent_summable {ι : Type*} (d : ℕ) (c z w : ℂ)
    (r : ι → ℂ) (R : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hR : ∀ i, 0 < R i)
    (hz : ∀ i, R i ≤ ‖z - r i‖) (hw : ∀ i, R i ≤ ‖w - r i‖)
    (hc : ∀ i, ‖(r i - c) / (w - r i)‖ ≤ B)
    (hs : Summable (fun i => 1 / (R i * R i))) :
    Summable (fun i => jetResolvent d c z w (r i)) := by
  apply (hs.mul_left (B^d)).of_norm_bounded
  intro i
  exact jetResolvent_bound d c z w (r i) B (R i) hB (hR i) (hz i) (hw i) (hc i)

/-- The coefficient left after cancelling the moving simple pole. -/
theorem jetResolvent_scaled (d : ℕ) (c z w r : ℂ) (hz : z - r ≠ 0) :
    (z - r) * jetResolvent d c z w r = ((r - c) / (w - r))^d / (w - r) := by
  unfold jetResolvent
  field_simp

theorem jetResolvent_residue_ne_zero (d : ℕ) (c w r : ℂ)
    (hc : r ≠ c) (hw : w ≠ r) :
    ((r - c) / (w - r))^d / (w - r) ≠ 0 := by
  exact div_ne_zero (pow_ne_zero d
    (div_ne_zero (sub_ne_zero.mpr hc) (sub_ne_zero.mpr hw))) (sub_ne_zero.mpr hw)


/-- The scaled kernel has a genuine punctured-neighborhood limit. This
avoids confusing Lean's totalized division value at z=r with a pole. -/
theorem jetResolvent_residue_limit (d : ℕ) (c w r : ℂ) :
    Filter.Tendsto (fun z : ℂ => (z - r) * jetResolvent d c z w r)
      (nhdsWithin r ({r}ᶜ : Set ℂ))
      (nhds (((r - c) / (w - r))^d / (w - r))) := by
  apply (tendsto_const_nhds : Filter.Tendsto
    (fun _ : ℂ => ((r - c) / (w - r))^d / (w - r))
    (nhdsWithin r ({r}ᶜ : Set ℂ))
    (nhds (((r - c) / (w - r))^d / (w - r)))).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ r := by simpa using hz
  exact (jetResolvent_scaled d c z w r (sub_ne_zero.mpr hne)).symm


/-- Uniform convergence of the limiting rational series on an arbitrary set
with uniform denominator separation and a summable majorant. -/
theorem jetResolvent_uniformly {ι : Type*} (d : ℕ) (c w : ℂ)
    (r : ι → ℂ) (R : ι → ℝ) (B : ℝ) (S : Set ℂ) (hB : 0 ≤ B)
    (hR : ∀ i, 0 < R i)
    (hz : ∀ i, ∀ z ∈ S, R i ≤ ‖z - r i‖)
    (hw : ∀ i, R i ≤ ‖w - r i‖)
    (hc : ∀ i, ‖(r i - c) / (w - r i)‖ ≤ B)
    (hs : Summable (fun i => 1 / (R i * R i))) :
    TendstoUniformlyOn
      (fun (t : Finset ι) z => ∑ i ∈ t, jetResolvent d c z w (r i))
      (fun z => ∑' i, jetResolvent d c z w (r i)) Filter.atTop S := by
  apply tendstoUniformlyOn_tsum (hs.mul_left (B^d))
  intro i z hzS
  exact jetResolvent_bound d c z w (r i) B (R i) hB (hR i)
    (hz i z hzS) (hw i) (hc i)

/-- A concrete tail majorant for bounded parameters. -/
theorem jetResolvent_tail_bound (d : ℕ) (c z w r : ℂ) (A : ℝ)
    (hc : ‖c‖ ≤ A) (hz : ‖z‖ ≤ A) (hw : ‖w‖ ≤ A)
    (hr : 2 * A ≤ ‖r‖) (hr0 : 0 < ‖r‖) :
    ‖jetResolvent d c z w r‖ ≤ 4 * (3 : ℝ)^d / ‖r‖^2 := by
  have hzr : ‖r‖ / 2 ≤ ‖z - r‖ := by
    have h := norm_sub_norm_le r z
    rw [norm_sub_rev] at h
    linarith
  have hwr : ‖r‖ / 2 ≤ ‖w - r‖ := by
    have h := norm_sub_norm_le r w
    rw [norm_sub_rev] at h
    linarith
  have hwp : 0 < ‖w - r‖ := by linarith
  have hratio : ‖(r - c) / (w - r)‖ ≤ 3 := by
    rw [norm_div]
    apply (div_le_iff₀ hwp).2
    have h := norm_sub_le r c
    linarith
  have hb := jetResolvent_bound d c z w r 3 (‖r‖ / 2)
    (by norm_num) (by positivity) hzr hwr hratio
  calc
    ‖jetResolvent d c z w r‖ ≤ (3 : ℝ)^d * (1 / ((‖r‖ / 2) * (‖r‖ / 2))) := hb
    _ = 4 * (3 : ℝ)^d / ‖r‖^2 := by ring

/-- An analytic factorization at the center, certifying at least d central
zeros when the two parameter poles lie away from the center. -/
theorem jetResolvent_analytic_factor (d : ℕ) (c z w : ℂ)
    (hz : z ≠ c) (hw : w ≠ c) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A c ∧
      ∀ r, jetResolvent d c z w r = (r - c)^d * A r := by
  refine ⟨fun r => 1 / ((z - r) * (w - r)^(d + 1)), ?_, ?_⟩
  · exact analyticAt_const.div
      ((analyticAt_const.sub analyticAt_id).mul
        ((analyticAt_const.sub analyticAt_id).pow (d + 1)))
      (mul_ne_zero (sub_ne_zero.mpr hz) (pow_ne_zero _ (sub_ne_zero.mpr hw)))
  · intro r
    rw [jetResolvent_factor]
    ring

/-- The central correction does not erase a noncentral simple pole. -/
theorem jetResolvent_not_continuousAt (d : ℕ) (c w r : ℂ)
    (hc : r ≠ c) (hw : w ≠ r) :
    ¬ ContinuousAt (fun z => jetResolvent d c z w r) r := by
  intro h
  have hprod : ContinuousAt (fun z : ℂ => (z - r) * jetResolvent d c z w r) r :=
    (continuousAt_id.sub_const r).mul h
  have hlim := hprod.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin r ({r}ᶜ : Set ℂ) ≤ nhds r)
  have hzero : Filter.Tendsto (fun z : ℂ => (z - r) * jetResolvent d c z w r)
      (nhdsWithin r ({r}ᶜ : Set ℂ)) (nhds 0) := by
    simpa only [sub_self, zero_mul] using hlim
  exact jetResolvent_residue_ne_zero d c w r hc hw
    (tendsto_nhds_unique (jetResolvent_residue_limit d c w r) hzero)

#check jetResolvent_uniformly
#print axioms jetResolvent_uniformly
#check jetResolvent_tail_bound
#print axioms jetResolvent_tail_bound
#check jetResolvent_analytic_factor
#print axioms jetResolvent_analytic_factor
#check jetResolvent_not_continuousAt
#print axioms jetResolvent_not_continuousAt

#check jetResolvent_residue_limit
#print axioms jetResolvent_residue_limit

#check jetResolvent_central
#print axioms jetResolvent_central
#check jetResolvent_factor
#print axioms jetResolvent_factor
#check jetResolvent_bound
#print axioms jetResolvent_bound
#check jetResolvent_summable
#print axioms jetResolvent_summable
#check jetResolvent_scaled
#print axioms jetResolvent_scaled
#check jetResolvent_residue_ne_zero
#print axioms jetResolvent_residue_ne_zero

#check normTwistParameter_re
#print axioms normTwistParameter_re
#check normTwistParameter_mem_strip
#print axioms normTwistParameter_mem_strip
#check completion_zero_iff
#print axioms completion_zero_iff
#check cutoffSingularity_eq
#print axioms cutoffSingularity_eq
#check cutoffSingularity_unbounded
#print axioms cutoffSingularity_unbounded
#check realPlaceKernel_lower
#print axioms realPlaceKernel_lower
#check realPlaceCutoff_lower
#print axioms realPlaceCutoff_lower
#check realPlaceCutoff_unbounded
#print axioms realPlaceCutoff_unbounded
#check realPlaceKernel_sub_singularity
#print axioms realPlaceKernel_sub_singularity
#check realPlaceRegularized_continuousAt_zero
#print axioms realPlaceRegularized_continuousAt_zero
#check realPlaceRegularized_value_zero
#print axioms realPlaceRegularized_value_zero
#check realPlaceRegularized_bound
#print axioms realPlaceRegularized_bound
#check resolvent_difference
#print axioms resolvent_difference
#check resolvent_difference_norm
#print axioms resolvent_difference_norm

end
end FrozenG

namespace CAttack
/-- The inverse-square majorant is zero at the central spectral point
because Lean totalizes division. It cannot dominate a nonzero central term. -/
theorem central_majorant_zero (C : ℝ) : C * (1 / ‖(0 : ℂ)‖^2) = 0 := by simp

theorem central_paired_value : (1 / (2 : ℂ) - 1 / (3 : ℂ)) ≠ 0 := by norm_num
#check central_majorant_zero
#print axioms central_majorant_zero
#check central_paired_value
#print axioms central_paired_value
end CAttack
