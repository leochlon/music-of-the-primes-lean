import Mathlib
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace TraceRepairE
/-- Accounting for actual full and selected multiplicities. This is not an
assertion that either sum is the trace of the manuscript operator. -/
theorem corrected_trace_with_omitted_multiplicities {ι : Type*}
    (m d w : ι → ℂ) (G P : ℂ)
    (hm : Summable (fun i => m i * w i))
    (hd : Summable (fun i => d i * w i))
    (hfull : G = P - ∑' i, m i * w i) :
    G + (∑' i, (m i - d i) * w i) = P - ∑' i, d i * w i := by
  have he : (fun i => (m i - d i) * w i) =
      (fun i => m i * w i - d i * w i) := by funext i; ring
  rw [he, hm.tsum_sub hd, hfull]
  ring

/-- The printed selected formula requires exactly the missing remainder to
vanish; summability and full explicit formula do not remove this obligation. -/
theorem selected_formula_iff_remainder_zero {ι : Type*}
    (m d w : ι → ℂ) (G P : ℂ)
    (hm : Summable (fun i => m i * w i))
    (hd : Summable (fun i => d i * w i))
    (hfull : G = P - ∑' i, m i * w i) :
    G = P - ∑' i, d i * w i ↔ (∑' i, (m i - d i) * w i) = 0 := by
  have h := corrected_trace_with_omitted_multiplicities m d w G P hm hd hfull
  constructor
  · intro he
    rw [← he] at h
    exact add_left_cancel (h.trans (add_zero G).symm)
  · intro he
    simpa [he] using h
/-- For the genuine analytic zero subtype, retained multiplicities may include
boundary jets. Full and selected sums are independent explicit hypotheses. -/
theorem genuine_zero_selected_correction (f : ℂ → ℂ)
    (d : {z : ℂ // f z = 0} → ℕ) (w : ℂ → ℂ) (G P : ℂ)
    (hm : Summable (fun i : {z : ℂ // f z = 0} =>
      (analyticOrderNatAt f i.val : ℂ) * w i.val))
    (hd : Summable (fun i : {z : ℂ // f z = 0} => (d i : ℂ) * w i.val))
    (hfull : G = P - ∑' i : {z : ℂ // f z = 0},
      (analyticOrderNatAt f i.val : ℂ) * w i.val) :
    G + (∑' i : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f i.val : ℂ) - (d i : ℂ)) * w i.val) =
      P - ∑' i : {z : ℂ // f z = 0}, (d i : ℂ) * w i.val :=
by
  have he : (fun i : {z : ℂ // f z = 0} =>
      ((analyticOrderNatAt f i.val : ℂ) - (d i : ℂ)) * w i.val) =
      (fun i : {z : ℂ // f z = 0} =>
      (analyticOrderNatAt f i.val : ℂ) * w i.val - (d i : ℂ) * w i.val) := by
    funext i
    ring
  rw [he, hm.tsum_sub hd, hfull]
  ring

/-- If T is the actual retained-jet trace, J the strict-interior zero sum,
and B its boundary contribution, the printed formula drops O+B, not just O. -/
theorem strict_interior_formula_iff_total_defect_zero
    (G P T J B O : ℂ) (htrace : T = J + B)
    (hcorrected : G + O = P - T) :
    G = P - J ↔ O + B = 0 := by
  constructor
  · intro h
    linear_combination hcorrected - htrace - h
  · intro h
    linear_combination hcorrected - htrace - h

/-- Subtracting corrected strip identities preserves precisely the difference
of their omitted contributions. This does not produce the baseline's hraw. -/
theorem width_subtraction_retains_remainder
    (G P Ta Tb Oa Ob : ℂ)
    (ha : G + Oa = P - Ta) (hb : G + Ob = P - Tb) :
    Tb - Ta = Oa - Ob := by
  linear_combination hb - ha

/-- The tensor in manuscript 10.4.3.43 convolves the coefficient functional.
At every finite stage its action is P_N(A v), with no commutation premise. -/
theorem coefficient_kernel_is_PA {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (s : Finset ι) (ell : ι → V →ₗ[ℂ] ℂ)
    (u : ι → V) (A : V →ₗ[ℂ] V) (v : V) :
    (∑ i ∈ s, (ell i).comp A v • u i) =
      (fun z => ∑ i ∈ s, ell i z • u i) (A v) := rfl

/-- The AP kernel instead acts on the output vectors. -/
theorem output_kernel_is_AP {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (s : Finset ι) (ell : ι → V →ₗ[ℂ] ℂ)
    (u : ι → V) (A : V →ₗ[ℂ] V) (v : V) :
    (∑ i ∈ s, ell i v • A (u i)) = A (∑ i ∈ s, ell i v • u i) := by
  simp only [map_sum, map_smul]

end TraceRepairE

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

open Filter Topology Set
open scoped ContDiff

namespace MasulloGRH.ConditionalMoment

/-- C.CUTOFF.CONSTRUCT: the scalar compact tests used before subtracting
two widths of the arithmetic trace. This is not an idelic admissibility claim. -/
noncomputable def positiveCutoff (t x : ℝ) : ℝ :=
  Real.smoothTransition (t * x - 1) * Real.smoothTransition (2 - x / t)

theorem positiveCutoff_smooth (t : ℝ) : ContDiff ℝ ∞ (positiveCutoff t) := by
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_id.div_const t)))

theorem positiveCutoff_bounds (t x : ℝ) :
    0 ≤ positiveCutoff t x ∧ positiveCutoff t x ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem positiveCutoff_eq_one (t x : ℝ) (hleft : 2 ≤ t * x) (hright : x ≤ t)
    (ht : 0 < t) : positiveCutoff t x = 1 := by
  unfold positiveCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t * x - 1)]
  rw [Real.smoothTransition.one_of_one_le (by
    have h : x / t ≤ 1 := (div_le_one ht).mpr hright
    linarith : 1 ≤ 2 - x / t)]
  simp

theorem positiveCutoff_support (t : ℝ) (ht : 0 < t) :
    Function.support (positiveCutoff t) ⊆ Icc (1 / t) (2 * t) := by
  intro x hx
  have hne : positiveCutoff t x ≠ 0 := hx
  have hleft : 0 < t * x - 1 := by
    by_contra h
    exact hne (by simp [positiveCutoff,
      Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)])
  have hright : 0 < 2 - x / t := by
    by_contra h
    exact hne (by simp [positiveCutoff,
      Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)])
  constructor
  · apply (div_le_iff₀ ht).mpr
    nlinarith
  · apply (div_le_iff₀ ht).mp
    linarith

theorem positiveCutoff_compact (t : ℝ) (ht : 0 < t) :
    HasCompactSupport (positiveCutoff t) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact closure_minimal (positiveCutoff_support t ht) isClosed_Icc

theorem positiveCutoff_tsupport_positive (t : ℝ) (ht : 0 < t) :
    tsupport (positiveCutoff t) ⊆ Ioi 0 := by
  have hs : tsupport (positiveCutoff t) ⊆ Icc (1 / t) (2 * t) :=
    closure_minimal (positiveCutoff_support t ht) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (one_div_pos.mpr ht) (hs hx).1

/-- C.CUTOFF.POINTWISE: exact eventual agreement, rather than an assumed
limit, at every positive logarithmic norm coordinate. -/
theorem positiveCutoff_eventually_one (x : ℝ) (hx : 0 < x) :
    ∀ᶠ n : ℕ in atTop, positiveCutoff ((n : ℝ) + 1) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max x (2 / x))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : x < (n : ℝ) + 1 := by
    have := le_max_left x (2 / x)
    linarith
  have hnq : 2 / x < (n : ℝ) + 1 := by
    have := le_max_right x (2 / x)
    linarith
  apply positiveCutoff_eq_one
  · have := (div_lt_iff₀ hx).mp hnq
    linarith
  · exact hnx.le
  · positivity

theorem positiveCutoff_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => positiveCutoff ((n : ℝ) + 1) x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [positiveCutoff_eventually_one x hx] with n hn
  exact hn.symm

/-- C.CUTOFF.COMPACT: eventual equality holds uniformly on each fixed
positive compact interval. This does not claim a uniform derivative bound. -/
theorem positiveCutoff_uniform_plateau (a b : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ Icc a b, positiveCutoff ((n : ℝ) + 1) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max b (2 / a))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ht : 0 < (n : ℝ) + 1 := by positivity
  have hnb : b < (n : ℝ) + 1 := by
    have := le_max_left b (2 / a)
    linarith
  have hnq : 2 / a < (n : ℝ) + 1 := by
    have := le_max_right b (2 / a)
    linarith
  intro x hx
  apply positiveCutoff_eq_one _ _ _ (hx.2.trans hnb.le) ht
  have hqa := (div_lt_iff₀ ha).mp hnq
  have := mul_le_mul_of_nonneg_left hx.1 ht.le
  nlinarith

/-- C.TEST.SCALAR: the first-moment exponential test before pullback to the
genuine idele class group. -/
noncomputable def momentTest (t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (positiveCutoff t x : ℂ) * (x : ℂ) * Complex.exp (-z * (x : ℂ))

theorem momentTest_smooth (t : ℝ) (z : ℂ) : ContDiff ℝ ∞ (momentTest t z) := by
  have hc : ContDiff ℝ ∞ (fun x => (positiveCutoff t x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (positiveCutoff_smooth t)
  have he : ContDiff ℝ ∞ (fun x : ℝ => Complex.exp (-z * (x : ℂ))) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  exact (hc.mul Complex.ofRealCLM.contDiff).mul he

theorem momentTest_compact (t : ℝ) (ht : 0 < t) (z : ℂ) :
    HasCompactSupport (momentTest t z) := by
  apply (isCompact_Icc (a := 1 / t) (b := 2 * t)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply positiveCutoff_support t ht
  intro h
  exact hx (by simp [momentTest, h])


end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment

/- C.CUTOFF.DERIV.BASE: these estimates supply the compact transition profiles
in the still-pending cutoff-uniform L1 second-derivative bound. -/
theorem transition_deriv_zero_left {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [h.deriv_eq]
  simp

theorem transition_deriv_zero_right {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [h.deriv_eq]
  simp

theorem transition_deriv_support :
    Function.support (deriv Real.smoothTransition) ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  constructor
  · by_contra h
    exact hx (transition_deriv_zero_left (lt_of_not_ge h))
  · by_contra h
    exact hx (transition_deriv_zero_right (lt_of_not_ge h))

theorem transition_second_support :
    Function.support (deriv (deriv Real.smoothTransition)) ⊆ Icc (0 : ℝ) 1 :=
  support_deriv_subset.trans (closure_minimal transition_deriv_support isClosed_Icc)

/-- No bound is assumed: compactness and the actual smooth transition give it. -/
theorem transition_two_derivatives_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖deriv Real.smoothTransition x‖ ≤ C ∧
      ‖deriv (deriv Real.smoothTransition) x‖ ≤ C := by
  have h1 : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have h2 : Continuous (deriv (deriv Real.smoothTransition)) :=
    ((contDiff_infty_iff_deriv.1 (show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff)).2).continuous_deriv (by simp)
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn h1.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn h2.continuousOn
  refine ⟨max 0 (max A B), le_max_left _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact ⟨(hA x hx).trans ((le_max_left A B).trans (le_max_right _ _)),
      (hB x hx).trans ((le_max_right A B).trans (le_max_right _ _))⟩
  · have hz1 : deriv Real.smoothTransition x = 0 := by
      by_contra h
      exact hx (transition_deriv_support h)
    have hz2 : deriv (deriv Real.smoothTransition) x = 0 := by
      by_contra h
      exact hx (transition_second_support h)
    simpa [hz1, hz2] using (le_max_left (0 : ℝ) (max A B))

/-- Exact chain rule for the same positiveCutoff used in the checked Mellin limit. -/
theorem positiveCutoff_deriv (t x : ℝ) :
    deriv (positiveCutoff t) x =
      (deriv Real.smoothTransition (t*x-1) * t) * Real.smoothTransition (2-x/t) +
      Real.smoothTransition (t*x-1) * (deriv Real.smoothTransition (2-x/t) * (-(1/t))) := by
  have hs : Differentiable ℝ Real.smoothTransition :=
    (show ContDiff ℝ ∞ Real.smoothTransition from Real.smoothTransition.contDiff).differentiable (by simp)
  have hl := (hs (t*x-1)).hasDerivAt.comp x (((hasDerivAt_id x).const_mul t).sub_const 1)
  have hr := (hs (2-x/t)).hasDerivAt.comp x (((hasDerivAt_id x).div_const t).const_sub 2)
  simpa [positiveCutoff] using (hl.mul hr).deriv

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment

/-- C.CUTOFF.DERIV.LOCAL: the high derivative region near zero shrinks like 1/t. -/
theorem positiveCutoff_deriv_support (t : ℝ) (ht : 0 < t) :
    Function.support (deriv (positiveCutoff t)) ⊆
      Icc (1/t) (2/t) ∪ Icc t (2*t) := by
  intro x hx
  by_contra h
  have hl : deriv Real.smoothTransition (t*x-1) = 0 := by
    by_contra hn
    have hs := transition_deriv_support hn
    apply h
    left
    constructor
    · apply (div_le_iff₀ ht).mpr
      nlinarith [hs.1]
    · apply (le_div_iff₀ ht).mpr
      nlinarith [hs.2]
  have hr : deriv Real.smoothTransition (2-x/t) = 0 := by
    by_contra hn
    have hs := transition_deriv_support hn
    apply h
    right
    constructor
    · have hh : 1 ≤ x/t := by linarith [hs.2]
      have := (le_div_iff₀ ht).mp hh
      linarith
    · have hh : x/t ≤ 2 := by linarith [hs.1]
      exact (div_le_iff₀ ht).mp hh
  exact hx (by rw [positiveCutoff_deriv, hl, hr]; ring)

theorem positiveCutoff_second_support (t : ℝ) (ht : 0 < t) :
    Function.support (deriv (deriv (positiveCutoff t))) ⊆
      Icc (1/t) (2/t) ∪ Icc t (2*t) :=
  support_deriv_subset.trans (closure_minimal (positiveCutoff_deriv_support t ht)
    (isClosed_Icc.union isClosed_Icc))

/-- C.CUTOFF.DERIV.CROSS: for t>=2 the two transition derivative factors cannot
both be nonzero. This removes the cross term in the second derivative. -/
theorem positiveCutoff_cross_zero (t x : ℝ) (ht : 2 ≤ t) :
    deriv Real.smoothTransition (t*x-1) *
      deriv Real.smoothTransition (2-x/t) = 0 := by
  by_cases hl : deriv Real.smoothTransition (t*x-1) = 0
  · rw [hl, zero_mul]
  have hleft := transition_deriv_support hl
  have hr : deriv Real.smoothTransition (2-x/t) = 0 := by
    by_contra h
    have hright := transition_deriv_support h
    have ht0 : 0 < t := by linarith
    have hxt : t ≤ x := by
      have hh : 1 ≤ x/t := by linarith [hright.2]
      simpa using (le_div_iff₀ ht0).mp hh
    have hprod := mul_le_mul_of_nonneg_left hxt ht0.le
    nlinarith [hleft.2, sq_nonneg (t-2)]
  rw [hr, mul_zero]

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
/-- C.CUTOFF.DERIV.FORMULA: exact second derivative with its cross term
removed by the proved separation of the two transition intervals. -/
theorem positiveCutoff_second_deriv (t x : ℝ) (ht : 2 ≤ t) :
    deriv (deriv (positiveCutoff t)) x =
      t^2 * deriv (deriv Real.smoothTransition) (t*x-1) * Real.smoothTransition (2-x/t) +
      (1/t)^2 * Real.smoothTransition (t*x-1) * deriv (deriv Real.smoothTransition) (2-x/t) := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hs := hc.differentiable (by simp)
  have hsd := (contDiff_infty_iff_deriv.1 hc).2.differentiable (by simp)
  have hl0 : HasDerivAt (fun y : ℝ => t*y-1) t x := by
    simpa using ((hasDerivAt_id x).const_mul t).sub_const 1
  have hr0 : HasDerivAt (fun y : ℝ => 2-y/t) (-(1/t)) x := by
    simpa using ((hasDerivAt_id x).div_const t).const_sub 2
  have hl := (hs (t*x-1)).hasDerivAt.comp x hl0
  have hr := (hs (2-x/t)).hasDerivAt.comp x hr0
  have hdl := (hsd (t*x-1)).hasDerivAt.comp x hl0
  have hdr := (hsd (2-x/t)).hasDerivAt.comp x hr0
  have h := ((hdl.mul_const t).mul hr).add (hl.mul (hdr.mul_const (-(1/t))))
  have he : deriv (positiveCutoff t) = fun y =>
      (deriv Real.smoothTransition (t*y-1)*t)*Real.smoothTransition (2-y/t) +
      Real.smoothTransition (t*y-1)*(deriv Real.smoothTransition (2-y/t)*(-(1/t))) :=
    funext (positiveCutoff_deriv t)
  rw [he]
  refine h.deriv.trans ?_
  dsimp only [Function.comp_apply]
  have hz := positiveCutoff_cross_zero t x ht
  linear_combination (-2 * t * (1/t)) * hz

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open MeasureTheory
/-- C.CUTOFF.DERIV.SCALE: exact cancellation of the shrinking interval scale
for the weighted second derivative. This is a scalar Lebesgue identity. -/
theorem dilation_weighted_second_mass (f : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, ‖x * (t^2 * f (t*x))‖) = ∫ u : ℝ, ‖u * f u‖ := by
  have he : (fun x : ℝ => ‖x * (t^2 * f (t*x))‖) =
      fun x => t * ‖(t*x) * f (t*x)‖ := by
    funext x
    rw [show x * (t^2 * f (t*x)) = t * ((t*x) * f (t*x)) by ring,
      norm_mul, Real.norm_eq_abs, abs_of_pos ht]
  rw [he, integral_const_mul, Measure.integral_comp_mul_left (fun u : ℝ => ‖u * f u‖) t]
  simp [Real.norm_eq_abs, abs_inv, abs_of_pos ht, ht.ne', smul_eq_mul, ← mul_assoc]

/-- C.CUTOFF.DERIV.SCALE: exact L1 mass of a scaled first derivative profile. -/
theorem dilation_first_mass (f : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    (∫ x : ℝ, ‖t * f (t*x)‖) = ∫ u : ℝ, ‖f u‖ := by
  simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos ht]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun u : ℝ => |f u|) t]
  simp [Real.norm_eq_abs, abs_inv, abs_of_pos ht, ht.ne', smul_eq_mul, ← mul_assoc]

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open MeasureTheory
/-- C.CUTOFF.DERIV.MASS: integrability is proved separately from the total
Bochner-integral change of variables, so the mass identity is not vacuous. -/
theorem weighted_dilation_integrable (f : ℝ → ℝ)
    (hf : Integrable (fun x : ℝ => x * f x)) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : ℝ => x * (t^2 * f (t*x))) := by
  have h := ((integrable_comp_mul_left_iff (fun x : ℝ => x * f x) ht.ne').mpr hf).const_mul t
  convert h using 1
  funext x
  ring

/-- C.CUTOFF.DERIV.LOWER: the fixed lower-transition profile has finite
weighted L1 mass, derived from the actual smooth transition and its support. -/
theorem lower_second_profile_integrable :
    Integrable (fun x : ℝ => x * deriv (deriv Real.smoothTransition) (x-1)) := by
  have hd : Continuous (deriv (deriv Real.smoothTransition)) :=
    ((contDiff_infty_iff_deriv.1 (show ContDiff ℝ ∞ Real.smoothTransition from
      Real.smoothTransition.contDiff)).2).continuous_deriv (by simp)
  have hc : Continuous (fun x : ℝ => x * deriv (deriv Real.smoothTransition) (x-1)) :=
    continuous_id.mul (hd.comp (continuous_id.sub continuous_const))
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc (a := (1 : ℝ)) (b := 2)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hne : deriv (deriv Real.smoothTransition) (x-1) ≠ 0 := by
    intro h; exact hx (by simp [h])
  have hs := transition_second_support hne
  exact (show x ∈ Icc (1 : ℝ) 2 from ⟨by linarith [hs.1], by linarith [hs.2]⟩)

/-- C.CUTOFF.DERIV.UPPER: the fixed upper-transition profile is integrable. -/
theorem upper_second_profile_integrable :
    Integrable (fun x : ℝ => x * deriv (deriv Real.smoothTransition) (2-x)) := by
  have hd : Continuous (deriv (deriv Real.smoothTransition)) :=
    ((contDiff_infty_iff_deriv.1 (show ContDiff ℝ ∞ Real.smoothTransition from
      Real.smoothTransition.contDiff)).2).continuous_deriv (by simp)
  have hc : Continuous (fun x : ℝ => x * deriv (deriv Real.smoothTransition) (2-x)) :=
    continuous_id.mul (hd.comp (continuous_const.sub continuous_id))
  apply hc.integrable_of_hasCompactSupport
  apply (isCompact_Icc (a := (1 : ℝ)) (b := 2)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hne : deriv (deriv Real.smoothTransition) (2-x) ≠ 0 := by
    intro h; exact hx (by simp [h])
  have hs := transition_second_support hne
  exact (show x ∈ Icc (1 : ℝ) 2 from ⟨by linarith [hs.2], by linarith [hs.1]⟩)

/-- C.CUTOFF.DERIV.SHRINK: exact uniform lower-transition weighted mass.
No majorant or integrability estimate is assumed. -/
theorem lower_transition_uniform_weighted_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : ℝ => x * (t^2 * deriv (deriv Real.smoothTransition) (t*x-1))) ∧
      (∫ x : ℝ, ‖x * (t^2 * deriv (deriv Real.smoothTransition) (t*x-1))‖) = C := by
  refine ⟨∫ u : ℝ, ‖u * deriv (deriv Real.smoothTransition) (u-1)‖,
    integral_nonneg (fun _ => norm_nonneg _), fun t ht => ?_⟩
  exact ⟨weighted_dilation_integrable _ lower_second_profile_integrable t ht,
    dilation_weighted_second_mass (fun u => deriv (deriv Real.smoothTransition) (u-1)) t ht⟩

end MasulloGRH.ConditionalMoment


namespace MasulloGRH.ConditionalMoment
open MeasureTheory

/-- B.CUTOFF.SECOND.L1: supplies the cutoff-uniform weighted second derivative
mass needed by two integrations by parts in the annular Mellin transform.
It assumes no analytic estimate and makes no Hecke zero-divisor claim. -/
theorem positiveCutoff_uniform_second_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
      Integrable (fun x : ℝ => x * deriv (deriv (positiveCutoff t)) x) ∧
      (∫ x : ℝ, ‖x * deriv (deriv (positiveCutoff t)) x‖) ≤ C := by
  let L : ℝ → ℝ := fun u => deriv (deriv Real.smoothTransition) (u-1)
  let U : ℝ → ℝ := fun u => deriv (deriv Real.smoothTransition) (2-u)
  refine ⟨(∫ u : ℝ, ‖u * L u‖) + (∫ u : ℝ, ‖u * U u‖),
    add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (integral_nonneg (fun _ => norm_nonneg _)), fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  let l : ℝ → ℝ := fun x => x * (t^2 * L (t*x))
  let u : ℝ → ℝ := fun x => x * ((1/t)^2 * U ((1/t)*x))
  have hl : Integrable l := weighted_dilation_integrable L
    lower_second_profile_integrable t ht0
  have hu : Integrable u := weighted_dilation_integrable U
    upper_second_profile_integrable (1/t) (one_div_pos.mpr ht0)
  have heL : (∫ x, ‖l x‖) = ∫ x, ‖x * L x‖ :=
    dilation_weighted_second_mass L t ht0
  have heU : (∫ x, ‖u x‖) = ∫ x, ‖x * U x‖ :=
    dilation_weighted_second_mass U (1/t) (one_div_pos.mpr ht0)
  have hbd (x : ℝ) : ‖x * deriv (deriv (positiveCutoff t)) x‖ ≤ ‖l x‖ + ‖u x‖ := by
    have he : x * deriv (deriv (positiveCutoff t)) x =
        l x * Real.smoothTransition (2-x/t) +
          u x * Real.smoothTransition (t*x-1) := by
      rw [positiveCutoff_second_deriv t x ht]
      dsimp [l, u, L, U]
      rw [show 1/t*x = x/t by ring]
      ring
    rw [he]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
  have hc : Continuous (fun x : ℝ => x * deriv (deriv (positiveCutoff t)) x) :=
    continuous_id.mul ((contDiff_infty_iff_deriv.1 (positiveCutoff_smooth t)).2.continuous_deriv (by simp))
  have hi : Integrable (fun x : ℝ => x * deriv (deriv (positiveCutoff t)) x) :=
    (hl.norm.add hu.norm).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  refine ⟨hi, ?_⟩
  calc
    (∫ x : ℝ, ‖x * deriv (deriv (positiveCutoff t)) x‖) ≤ ∫ x, (‖l x‖ + ‖u x‖) :=
      integral_mono hi.norm (hl.norm.add hu.norm) hbd
    _ = (∫ x, ‖x * L x‖) + (∫ x, ‖x * U x‖) := by
      rw [integral_add hl.norm hu.norm, heL, heU]

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open MeasureTheory

/-- B.CUTOFF.FIRST.PROFILE: proves integrability of the fixed profiles used
in the uniform first-derivative mass, required by the same twice-IBP estimate. -/
theorem lower_first_profile_integrable :
    Integrable (fun x : ℝ => deriv Real.smoothTransition (x-1)) := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  apply (hd.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
  apply (isCompact_Icc (a := (1 : ℝ)) (b := 2)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hs := transition_deriv_support hx
  change x - 1 ∈ Icc (0 : ℝ) 1 at hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem upper_first_profile_integrable :
    Integrable (fun x : ℝ => deriv Real.smoothTransition (2-x)) := by
  have hd : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  apply (hd.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
  apply (isCompact_Icc (a := (1 : ℝ)) (b := 2)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hs := transition_deriv_support hx
  change 2 - x ∈ Icc (0 : ℝ) 1 at hs
  exact ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- B.CUTOFF.FIRST.L1: uniform first-derivative mass of the actual cutoff;
this is the other term in (x*c_t)'' = 2*c_t' + x*c_t''. -/
theorem positiveCutoff_uniform_first_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Integrable (deriv (positiveCutoff t)) ∧
      (∫ x : ℝ, ‖deriv (positiveCutoff t) x‖) ≤ C := by
  let L : ℝ → ℝ := fun u => deriv Real.smoothTransition (u-1)
  let U : ℝ → ℝ := fun u => deriv Real.smoothTransition (2-u)
  refine ⟨(∫ u : ℝ, ‖L u‖) + (∫ u : ℝ, ‖U u‖),
    add_nonneg (integral_nonneg (fun _ => norm_nonneg _))
      (integral_nonneg (fun _ => norm_nonneg _)), fun t ht => ?_⟩
  let l : ℝ → ℝ := fun x => t * L (t*x)
  let u : ℝ → ℝ := fun x => (1/t) * U ((1/t)*x)
  have hl : Integrable l :=
    ((integrable_comp_mul_left_iff L ht.ne').mpr lower_first_profile_integrable).const_mul t
  have hu : Integrable u :=
    ((integrable_comp_mul_left_iff U (one_div_pos.mpr ht).ne').mpr
      upper_first_profile_integrable).const_mul (1/t)
  have heL : (∫ x, ‖l x‖) = ∫ x, ‖L x‖ := dilation_first_mass L t ht
  have heU : (∫ x, ‖u x‖) = ∫ x, ‖U x‖ := dilation_first_mass U (1/t) (one_div_pos.mpr ht)
  have hbd (x : ℝ) : ‖deriv (positiveCutoff t) x‖ ≤ ‖l x‖ + ‖u x‖ := by
    have he : deriv (positiveCutoff t) x =
        l x * Real.smoothTransition (2-x/t) -
          u x * Real.smoothTransition (t*x-1) := by
      rw [positiveCutoff_deriv]
      dsimp [l, u, L, U]
      rw [show 1/t*x = x/t by ring]
      ring
    rw [he]
    apply (norm_sub_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
  have hc : Continuous (deriv (positiveCutoff t)) :=
    (positiveCutoff_smooth t).continuous_deriv (by simp)
  have hi : Integrable (deriv (positiveCutoff t)) :=
    (hl.norm.add hu.norm).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  refine ⟨hi, ?_⟩
  calc
    (∫ x : ℝ, ‖deriv (positiveCutoff t) x‖) ≤ ∫ x, (‖l x‖ + ‖u x‖) :=
      integral_mono hi.norm (hl.norm.add hu.norm) hbd
    _ = (∫ x, ‖L x‖) + (∫ x, ‖U x‖) := by rw [integral_add hl.norm hu.norm, heL, heU]

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open MeasureTheory

/-- B.CUTOFF.MOMENT.DERIV: the exact derivative identity needed to turn the
two proved mass bounds into a uniform second-derivative bound for x*c_t. -/
theorem cutoffMoment_second_deriv (t x : ℝ) :
    deriv (deriv (fun y : ℝ => y * positiveCutoff t y)) x =
      2 * deriv (positiveCutoff t) x + x * deriv (deriv (positiveCutoff t)) x := by
  have hc := (positiveCutoff_smooth t).differentiable (by simp)
  have hd := (contDiff_infty_iff_deriv.1 (positiveCutoff_smooth t)).2.differentiable (by simp)
  have he : deriv (fun y : ℝ => y * positiveCutoff t y) =
      fun y => positiveCutoff t y + y * deriv (positiveCutoff t) y := by
    funext y
    simpa using ((hasDerivAt_id y).mul (hc y).hasDerivAt).deriv
  rw [he]
  have hh := ((hc x).hasDerivAt.add ((hasDerivAt_id x).mul (hd x).hasDerivAt)).deriv
  convert hh using 1 <;> simp only [Pi.add_apply, Pi.mul_apply, id_eq] <;> ring

/-- B.CUTOFF.MOMENT.L1: cutoff-uniform L1 mass of the second derivative
of the actual first-moment cutoff. This discharges the real-variable mass
premise for two integrations by parts, without an assumed convergence estimate. -/
theorem cutoffMoment_uniform_second_mass :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
      Integrable (deriv (deriv (fun x : ℝ => x * positiveCutoff t x))) ∧
      (∫ x : ℝ, ‖deriv (deriv (fun y : ℝ => y * positiveCutoff t y)) x‖) ≤ C := by
  obtain ⟨A, hA, ha⟩ := positiveCutoff_uniform_first_mass
  obtain ⟨B, hB, hb⟩ := positiveCutoff_uniform_second_mass
  refine ⟨2*A+B, by positivity, fun t ht => ?_⟩
  obtain ⟨hiA, hmA⟩ := ha t (by linarith)
  obtain ⟨hiB, hmB⟩ := hb t ht
  have he : deriv (deriv (fun x : ℝ => x * positiveCutoff t x)) =
      fun x => 2 * deriv (positiveCutoff t) x + x * deriv (deriv (positiveCutoff t)) x :=
    funext (cutoffMoment_second_deriv t)
  have hi : Integrable (deriv (deriv (fun x : ℝ => x * positiveCutoff t x))) := by
    rw [he]
    exact (hiA.const_mul 2).add hiB
  refine ⟨hi, ?_⟩
  calc
    (∫ x : ℝ, ‖deriv (deriv (fun y : ℝ => y * positiveCutoff t y)) x‖) ≤
        ∫ x : ℝ, (2 * ‖deriv (positiveCutoff t) x‖ + ‖x * deriv (deriv (positiveCutoff t)) x‖) := by
      apply integral_mono hi.norm ((hiA.norm.const_mul 2).add hiB.norm)
      intro x
      change ‖deriv (deriv (fun y : ℝ => y * positiveCutoff t y)) x‖ ≤
        2 * ‖deriv (positiveCutoff t) x‖ + ‖x * deriv (deriv (positiveCutoff t)) x‖
      rw [cutoffMoment_second_deriv]
      calc
        ‖2 * deriv (positiveCutoff t) x + x * deriv (deriv (positiveCutoff t)) x‖ ≤
            ‖2 * deriv (positiveCutoff t) x‖ + ‖x * deriv (deriv (positiveCutoff t)) x‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]; norm_num
    _ = 2 * (∫ x : ℝ, ‖deriv (positiveCutoff t) x‖) +
        (∫ x : ℝ, ‖x * deriv (deriv (positiveCutoff t)) x‖) := by
      rw [integral_add (hiA.norm.const_mul 2) hiB.norm, integral_const_mul]
    _ ≤ 2*A+B := by linarith

end MasulloGRH.ConditionalMoment


namespace MasulloGRH.ConditionalMoment
open MeasureTheory

/-- B.TEST.IBP: discharges the two integrations by parts for the compact
first-moment test. Smoothness and compact support imply every integrability
premise used below; no interchange or decay estimate is assumed. -/
theorem laplace_twice_ibp (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (z : ℂ) :
    z^2 * (∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * f x) =
      ∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * deriv (deriv f) x := by
  let e : ℝ → ℂ := fun x => Complex.exp (-z * (x : ℂ))
  have hed (x : ℝ) : HasDerivAt e ((-z) * e x) x := by
    have hinner : HasDerivAt (fun t : ℝ => -z * (t : ℂ)) (-z) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp.const_mul (-z))
    simpa [e, mul_comm] using hinner.cexp
  have hec : Continuous e := by dsimp [e]; fun_prop
  have hf1 : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.1 hf).2
  have hd0 := hf.differentiable (by simp)
  have hd1 := hf1.differentiable (by simp)
  have c0 := hf.continuous
  have c1 := hf1.continuous
  have c2 := hf1.continuous_deriv (by simp)
  have I0 : Integrable (fun x => e x * f x) :=
    (hec.mul c0).integrable_of_hasCompactSupport hc.mul_left
  have I1 : Integrable (fun x => e x * deriv f x) :=
    (hec.mul c1).integrable_of_hasCompactSupport hc.deriv.mul_left
  have I2 : Integrable (fun x => e x * deriv (deriv f) x) :=
    (hec.mul c2).integrable_of_hasCompactSupport hc.deriv.deriv.mul_left
  have J0 : Integrable (fun x => ((-z) * e x) * f x) := by
    simpa only [mul_assoc] using I0.const_mul (-z)
  have J1 : Integrable (fun x => ((-z) * e x) * deriv f x) := by
    simpa only [mul_assoc] using I1.const_mul (-z)
  have s1 : (∫ x, e x * deriv (deriv f) x) = - ∫ x, ((-z) * e x) * deriv f x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x => hed x) (fun x => (hd1 x).hasDerivAt) I2 J1 I1
  have s2 : (∫ x, e x * deriv f x) = - ∫ x, ((-z) * e x) * f x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x => hed x) (fun x => (hd0 x).hasDerivAt) I1 J0 I0
  have m1 : (∫ x, ((-z) * e x) * deriv f x) = (-z) * ∫ x, e x * deriv f x := by
    simp only [mul_assoc, integral_const_mul]
  have m0 : (∫ x, ((-z) * e x) * f x) = (-z) * ∫ x, e x * f x := by
    simp only [mul_assoc, integral_const_mul]
  change z^2 * (∫ x, e x * f x) = ∫ x, e x * deriv (deriv f) x
  rw [s1, m1, s2, m0]
  ring

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open MeasureTheory

/-- B.TEST.SPECTRAL.DECAY: the twice-IBP norm estimate for compact tests
supported on the positive half-line. It proves the damping bound and all
integrability premises rather than assuming a spectral majorant. -/
theorem laplace_square_norm_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Set.Ici 0)
    (z : ℂ) (hz : 0 ≤ z.re) :
    ‖z‖^2 * ‖∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * f x‖ ≤
      ∫ x : ℝ, ‖deriv (deriv f) x‖ := by
  have hf1 := (contDiff_infty_iff_deriv.1 hf).2
  have c2 : Continuous (deriv (deriv f)) := hf1.continuous_deriv (by simp)
  have hi : Integrable (deriv (deriv f)) :=
    c2.integrable_of_hasCompactSupport hc.deriv.deriv
  have hp1 : tsupport (deriv f) ⊆ Set.Ici 0 :=
    closure_minimal (support_deriv_subset.trans hp) isClosed_Ici
  have hp2 : Function.support (deriv (deriv f)) ⊆ Set.Ici 0 :=
    support_deriv_subset.trans hp1
  have hbd (x : ℝ) :
      ‖Complex.exp (-z * (x : ℂ)) * deriv (deriv f) x‖ ≤ ‖deriv (deriv f) x‖ := by
    by_cases hx : deriv (deriv f) x = 0
    · simp [hx]
    have hx0 : 0 ≤ x := hp2 hx
    rw [norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hx0
  have hec : Continuous (fun x : ℝ => Complex.exp (-z * (x : ℂ))) := by fun_prop
  have hj : Integrable (fun x : ℝ => Complex.exp (-z * (x : ℂ)) * deriv (deriv f) x) :=
    (hec.mul c2).integrable_of_hasCompactSupport hc.deriv.deriv.mul_left
  calc
    ‖z‖^2 * ‖∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * f x‖ =
        ‖z^2 * (∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * f x)‖ := by
      rw [norm_mul, norm_pow]
    _ = ‖∫ x : ℝ, Complex.exp (-z * (x : ℂ)) * deriv (deriv f) x‖ := by
      rw [laplace_twice_ibp f hf hc z]
    _ ≤ ∫ x : ℝ, ‖Complex.exp (-z * (x : ℂ)) * deriv (deriv f) x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, ‖deriv (deriv f) x‖ := integral_mono hj.norm hi.norm hbd

end MasulloGRH.ConditionalMoment


namespace MasulloGRH.ConditionalMoment
open MeasureTheory

/-- T4-COMPLEXIFY: transfers the proved real cutoff mass to the complex
Laplace integral. This is a derivative identity, not an assumed estimate. -/
theorem realCast_second_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    deriv (deriv (fun x => (f x : ℂ))) = fun x : ℝ => ((deriv (deriv f) x : ℝ) : ℂ) := by
  have h1 : deriv (fun x => (f x : ℂ)) = fun x : ℝ => ((deriv f x : ℝ) : ℂ) := by
    funext x
    exact ((hf.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  rw [h1]
  funext x
  exact (((contDiff_infty_iff_deriv.1 hf).2.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv

/-- T4-DECAY: the actual first-moment compact cutoff has a uniform quadratic
Laplace bound throughout Re z >= 0. No uniform estimate is a hypothesis.
The remaining arithmetic obligation is its admissible idelic pullback. -/
theorem cutoffMoment_uniform_laplace_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t → ∀ z : ℂ, 0 ≤ z.re →
      ‖z‖^2 * ‖∫ x : ℝ, Complex.exp (-z * (x : ℂ)) *
        ((x * positiveCutoff t x : ℝ) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hmass⟩ := cutoffMoment_uniform_second_mass
  refine ⟨C, hC, fun t ht z hz => ?_⟩
  have ht0 : 0 < t := by linarith
  let f : ℝ → ℝ := fun x => x * positiveCutoff t x
  have hf : ContDiff ℝ ∞ f := contDiff_id.mul (positiveCutoff_smooth t)
  have hfC : ContDiff ℝ ∞ (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hs : Function.support (fun x => (f x : ℂ)) ⊆ Icc (1/t) (2*t) := by
    intro x hx
    apply positiveCutoff_support t ht0
    intro h
    exact hx (by simp [f, h])
  have hc : HasCompactSupport (fun x => (f x : ℂ)) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hp : tsupport (fun x => (f x : ℂ)) ⊆ Ici 0 := by
    intro x hx
    exact (one_div_pos.mpr ht0).le.trans ((closure_minimal hs isClosed_Icc) hx).1
  have hdec := laplace_square_norm_bound (fun x => (f x : ℂ)) hfC hc hp z hz
  rw [realCast_second_deriv f hf] at hdec
  simp only [Complex.norm_real, Real.norm_eq_abs] at hdec
  exact hdec.trans (by simpa only [Real.norm_eq_abs] using (hmass t ht).2)

end MasulloGRH.ConditionalMoment


namespace MasulloGRH.ConditionalMoment
open MeasureTheory
/-- D6.UNIFORM: discharges the scalar hbound premise of
ConditionalGRHReviewD.entire_zeros_on_critical_line_of_analytic_inputs
once the actual idelic Mellin transform is identified. Reuses A phase-12
source and repairs its failed real-part simplification. Turns the proved
compact moment bound into the exact
inverse-square majorant on each bounded real-part strip. The parameter p is
a scalar location, not a postulated spectrum; no zero count is assumed. -/
theorem cutoffMoment_uniform_spectral_decay (b : ℝ) (z : ℂ) (hz : b < z.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 2 ≤ t → ∀ p : ℂ, p ≠ 0 → p.re ≤ b →
      ‖∫ x : ℝ, Complex.exp (-(z-p) * (x : ℂ)) *
        ((x * positiveCutoff t x : ℝ) : ℂ)‖ ≤ B / ‖p‖^2 := by
  obtain ⟨C, hC, hdecay⟩ := cutoffMoment_uniform_laplace_decay
  let δ : ℝ := z.re - b
  have hδ : 0 < δ := sub_pos.mpr hz
  let Q : ℝ := ‖z‖ / δ + 1
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q^2*C, mul_nonneg (sq_nonneg Q) hC, fun t ht p hp hpb => ?_⟩
  have hsep : δ ≤ ‖z-p‖ := by
    calc
      δ ≤ (z-p).re := by change z.re - b ≤ z.re - p.re; linarith
      _ ≤ ‖z-p‖ := Complex.re_le_norm _
  have hpn : ‖p‖ ≤ Q * ‖z-p‖ := by
    have hmul := mul_le_mul_of_nonneg_left hsep (div_nonneg (norm_nonneg z) hδ.le)
    rw [div_mul_cancel₀ _ hδ.ne'] at hmul
    calc
      ‖p‖ = ‖z-(z-p)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖z-p‖ := norm_sub_le _ _
      _ ≤ Q * ‖z-p‖ := by dsimp [Q]; nlinarith
  have hpn2 : ‖p‖^2 ≤ Q^2 * ‖z-p‖^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hpn)
      (add_nonneg (mul_nonneg hQ (norm_nonneg (z-p))) (norm_nonneg p))
    nlinarith
  have hdec := hdecay t ht (z-p) (by simp only [Complex.sub_re]; linarith)
  have hmul := mul_le_mul_of_nonneg_right hpn2
    (norm_nonneg (∫ x : ℝ, Complex.exp (-(z-p) * (x : ℂ)) *
      ((x * positiveCutoff t x : ℝ) : ℂ)))
  have hbound := mul_le_mul_of_nonneg_left hdec (sq_nonneg Q)
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hp))).mpr
  nlinarith

end MasulloGRH.ConditionalMoment

namespace ConditionalReviewC
open MeasureTheory Set Filter Topology
open MasulloGRH.ConditionalMoment
/- C.LAPLACE.VALUE: integrability, endpoint limits and integration by parts for the first-moment transform. General n is used only to inductively evaluate n=1. Ported Mathlib-only from inspected alpo FourierLipschitzOneVariableKernelEq.lean. -/
theorem norm_pow_mul_cexp_neg (n : ℕ) (r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ n * Complex.exp (-(r * t))‖ = t ^ (n : ℝ) * Real.exp (-r.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp

theorem integrableOn_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) le_rfl hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]

theorem tendsto_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]

theorem integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp [hr0]
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2 <;> simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring


end ConditionalReviewC

namespace ConditionalReviewC
open MeasureTheory Set Filter Topology
open MasulloGRH.ConditionalMoment

/-- C.TEST.CONCRETE: the exact scalar transform, with t=n+2 so the uniform
spectral estimate applies at every index. Idelic attachment is not asserted. -/
noncomputable def concreteTransform (z : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(z-w) * (x : ℂ)) *
    ((x * positiveCutoff ((n : ℝ)+2) x : ℝ) : ℂ)

/-- C.TEST.LIMIT: all scalar approximation and integral limiting premises
are proved for the actual cutoff; no convergence hypothesis is an input. -/
theorem concreteTransform_limit (z w : ℂ) (hz : w.re < z.re) :
    Tendsto (fun n => concreteTransform z n w) atTop (𝓝 (((z-w)⁻¹)^2)) := by
  let s : ℂ := z-w
  have hs : 0 < s.re := by change 0 < z.re - w.re; linarith
  let f : ℝ → ℂ := fun x => (x : ℂ) * Complex.exp (-(s * (x : ℂ)))
  have hf : IntegrableOn f (Ioi 0) := by
    simpa only [pow_one] using integrableOn_pow_mul_cexp_neg 1 hs
  have hc (n : ℕ) : Continuous (fun x : ℝ => (positiveCutoff ((n : ℝ)+2) x : ℂ)) :=
    Complex.continuous_ofReal.comp (positiveCutoff_smooth _).continuous
  have hp (x : ℝ) (hx : 0 < x) :
      Tendsto (fun n : ℕ => (positiveCutoff ((n : ℝ)+2) x : ℂ)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt (max x (2/x))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : x ≤ (n : ℝ)+2 := by linarith [le_max_left x (2/x)]
    have h2 : 2/x ≤ (n : ℝ)+2 := by linarith [le_max_right x (2/x)]
    have he := positiveCutoff_eq_one ((n : ℝ)+2) x
      ((div_le_iff₀ hx).mp h2) h1 (by positivity)
    simp only [he, Complex.ofReal_one]
  have ht : Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
      (positiveCutoff ((n : ℝ)+2) x : ℂ) * f x)
      atTop (𝓝 (∫ x in Ioi (0 : ℝ), f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hc n).aestronglyMeasurable.mul hf.aestronglyMeasurable)
      hf.norm (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (positiveCutoff_bounds _ _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (positiveCutoff_bounds _ _).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [one_mul] using (hp x hx).mul_const (f x)
  have he (n : ℕ) : concreteTransform z n w =
      ∫ x in Ioi (0 : ℝ), (positiveCutoff ((n : ℝ)+2) x : ℂ) * f x := by
    unfold concreteTransform
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : 0 < x
      · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
        dsimp [f, s]
        push_cast
        rw [neg_mul]
        ring
      · rw [Set.indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
        have h0 : positiveCutoff ((n : ℝ)+2) x = 0 := by
          unfold positiveCutoff
          rw [Real.smoothTransition.zero_of_nonpos (by
            have hx0 : x ≤ 0 := le_of_not_gt hx
            have hm : ((n : ℝ)+2)*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hx0
            linarith), zero_mul]
        simp only [h0, mul_zero, Complex.ofReal_zero]
  have hv : (∫ x in Ioi (0 : ℝ), f x) = (s⁻¹)^2 := by
    have h := integral_pow_mul_cexp_neg 1 hs
    simpa only [pow_one, Nat.factorial_one, Nat.cast_one, Nat.reduceAdd,
      one_div, inv_pow] using h
  simpa only [← he, hv, s] using ht

end ConditionalReviewC

set_option maxHeartbeats 800000
namespace ConditionalGRHReviewD
open Filter Topology

/-- Discharges precisely the analytic-continuation step for the annular
squared-resolvent, ONCE its global meromorphy and trace-derived vanishing on
Re(z)>b have been proved. This does not construct that resolvent, supply a
Hecke continuation, or assume a zero-free region for a Hecke function.
Source pattern: alpo EventuallyEqNhdsNEOfMeromorphicOfEqOnHalfPlane.lean. -/
theorem meromorphic_zero_from_halfPlane
    (F : ℂ → ℂ) (hF : MeromorphicOn F Set.univ) (b : ℝ)
    (hzero : ∀ z : ℂ, b < z.re → F z = 0) :
    ∀ p : ℂ, ∀ᶠ z in 𝓝[≠] p, F z = 0 := by
  intro p
  have hp : meromorphicOrderAt F p = ⊤ := by
    by_contra hp
    have hb : meromorphicOrderAt F ((b + 1 : ℝ) : ℂ) ≠ ⊤ :=
      hF.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
        (Set.mem_univ p) (Set.mem_univ _) hp
    apply hb
    rw [meromorphicOrderAt_eq_top_iff]
    have ho : IsOpen {z : ℂ | b < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hn : {z : ℂ | b < z.re} ∈ 𝓝 ((b + 1 : ℝ) : ℂ) :=
      ho.mem_nhds (by simp)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hn] with z hz
    exact hzero z hz
  exact meromorphicOrderAt_eq_top_iff.mp hp

end ConditionalGRHReviewD


namespace ConditionalGRHReviewD
open Filter Topology

/-- Premise D9: the local coefficient of a double pole is obtained by a
punctured limit. The regular remainder only needs continuity at the pole.
This does not assert that any Hecke zero sum has such a decomposition. -/
theorem doublePole_coefficient_limit
    (F R : ℂ → ℂ) (p m : ℂ) (hR : ContinuousAt R p)
    (hlocal : ∀ᶠ z in 𝓝[≠] p, F z = m / (z - p)^2 + R z) :
    Tendsto (fun z => (z - p)^2 * F z) (𝓝[≠] p) (𝓝 m) := by
  have hcont : ContinuousAt (fun z : ℂ => m + (z - p)^2 * R z) p :=
    continuousAt_const.add (((continuousAt_id.sub continuousAt_const).pow 2).mul hR)
  have hlim : Tendsto (fun z : ℂ => m + (z - p)^2 * R z)
      (𝓝[≠] p) (𝓝 m) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply hlim.congr'
  filter_upwards [hlocal, self_mem_nhdsWithin] with z hz hzp
  have hne : z - p ≠ 0 := sub_ne_zero.mpr hzp
  rw [hz]
  field_simp [hne]

/-- Premise D9: the final pole contradiction for the annular squared resolvent.
Global meromorphy, trace-derived half-plane vanishing, and the local expansion
remain separate explicit hypotheses; none is a hypothesis about Hecke
zero-freeness or a substitute definition of the arithmetic trace formula. -/
theorem doublePole_coefficient_zero_of_halfPlane
    (F R : ℂ → ℂ) (p m : ℂ) (b : ℝ)
    (hF : MeromorphicOn F Set.univ)
    (hzero : ∀ z : ℂ, b < z.re → F z = 0)
    (hR : ContinuousAt R p)
    (hlocal : ∀ᶠ z in 𝓝[≠] p, F z = m / (z - p)^2 + R z) :
    m = 0 := by
  have hm := doublePole_coefficient_limit F R p m hR hlocal
  have he := meromorphic_zero_from_halfPlane F hF b hzero p
  have hz : Tendsto (fun z => (z - p)^2 * F z) (𝓝[≠] p) (𝓝 (0 : ℂ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with z hz
    simp [hz]
  exact tendsto_nhds_unique hm hz

/-- Premise D9 with a genuine zero's positive integral order, after that order
and its local expansion have been independently identified. -/
theorem positive_doublePole_impossible_of_halfPlane
    (F R : ℂ → ℂ) (p : ℂ) (m : ℕ) (hm : 0 < m) (b : ℝ)
    (hF : MeromorphicOn F Set.univ)
    (hzero : ∀ z : ℂ, b < z.re → F z = 0)
    (hR : ContinuousAt R p)
    (hlocal : ∀ᶠ z in 𝓝[≠] p, F z = (m : ℂ) / (z - p)^2 + R z) :
    False := by
  have hz : (m : ℂ) = 0 :=
    doublePole_coefficient_zero_of_halfPlane F R p m b hF hzero hR hlocal
  have hm0 : m = 0 := by exact_mod_cast hz
  omega

end ConditionalGRHReviewD



namespace MasulloGRH.ConditionalMoment

/-- C.SPECTRAL.TAIL: discharges the uniform large-zero kernel estimate for
the proposed first-moment Laplace tests. This is a scalar inequality, not a
zero-counting theorem or an identification of a Hecke zero divisor. -/
theorem square_resolvent_tail (z w : ℂ) (R : ℝ) (hR : 0 < R)
    (hz : ‖z‖ ≤ R) (hw : 2 * R ≤ ‖w‖) :
    ‖((z - w)⁻¹) ^ 2‖ ≤ 4 / ‖w‖ ^ 2 := by
  have hn : 0 < ‖w‖ := by linarith
  have hd : ‖w‖ / 2 ≤ ‖z - w‖ := by
    have h := norm_sub_norm_le w z
    rw [norm_sub_rev] at h
    linarith
  have hdpos : 0 < ‖z - w‖ := lt_of_lt_of_le (by positivity) hd
  rw [norm_pow, norm_inv, inv_pow, inv_eq_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hdpos) (sq_pos_of_pos hn)).2
  have hm := mul_nonneg (sub_nonneg.mpr hd)
    (show 0 ≤ ‖z - w‖ + ‖w‖ / 2 by positivity)
  nlinarith


end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open Filter

/-- C.SPECTRAL.NORMAL: the inverse-square weighted counting premise implies
absolute summability and uniform convergence of the large-zero resolvent tail
on a closed disc. This proves the analytic M-test step only. The counting
premise and identification with the actual Hecke divisor remain obligations. -/
theorem weighted_square_resolvent_tail_uniform
    {ι : Type*} (w m : ι → ℂ) (R : ℝ) (hR : 0 < R)
    (hw : ∀ i, 2 * R ≤ ‖w i‖)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    (∀ z : ℂ, ‖z‖ ≤ R →
      Summable (fun i => ‖m i * ((z - w i)⁻¹) ^ 2‖)) ∧
    TendstoUniformlyOn
      (fun S : Finset ι => fun z : ℂ => ∑ i ∈ S, m i * ((z - w i)⁻¹) ^ 2)
      (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹) ^ 2)
      atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hbound : ∀ i (z : ℂ), ‖z‖ ≤ R →
      ‖m i * ((z - w i)⁻¹) ^ 2‖ ≤ 4 * (‖m i‖ / ‖w i‖ ^ 2) := by
    intro i z hz
    rw [norm_mul]
    calc
      ‖m i‖ * ‖((z - w i)⁻¹) ^ 2‖ ≤ ‖m i‖ * (4 / ‖w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (square_resolvent_tail z (w i) R hR hz (hw i)) (norm_nonneg _)
      _ = 4 * (‖m i‖ / ‖w i‖ ^ 2) := by ring
  constructor
  · intro z hz
    exact (hweight.mul_left 4).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => hbound i z hz)
  · exact tendstoUniformlyOn_tsum (hweight.mul_left 4) hbound

end MasulloGRH.ConditionalMoment

namespace ConditionalGRHReviewD
open Filter Topology

/-- Premise D7: the normally convergent large-zero tail is holomorphic on
its disc. The inverse-square zero weight bound remains a separate arithmetic
obligation, and this indexed family is not declared to be a Hecke divisor. -/
theorem weighted_square_resolvent_tail_differentiable
    {ι : Type*} (w m : ι → ℂ) (R : ℝ) (hR : 0 < R)
    (hw : ∀ i, 2 * R ≤ ‖w i‖)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹)^2)
      {z : ℂ | ‖z‖ < R} := by
  classical
  have hconv := (MasulloGRH.ConditionalMoment.weighted_square_resolvent_tail_uniform
    w m R hR hw hweight).2
  have hconv' := hconv.mono (show {z : ℂ | ‖z‖ < R} ⊆ {z : ℂ | ‖z‖ ≤ R}
    from by
      intro z hz
      change ‖z‖ < R at hz
      change ‖z‖ ≤ R
      exact hz.le)
  have hterm : ∀ i, DifferentiableOn ℂ
      (fun z : ℂ => m i * ((z - w i)⁻¹)^2) {z : ℂ | ‖z‖ < R} := by
    intro i z hz
    change ‖z‖ < R at hz
    have hne : z - w i ≠ 0 := by
      intro he
      have he' : z = w i := sub_eq_zero.mp he
      have hlarge := hw i
      rw [he'] at hz
      linarith
    exact (differentiableAt_const (m i)).mul
      (((differentiableAt_id.sub (differentiableAt_const (w i))).inv hne).pow 2)
      |>.differentiableWithinAt
  exact hconv'.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun S => DifferentiableOn.fun_sum fun i _ => hterm i)
    (isOpen_lt continuous_norm continuous_const)

end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
open Filter Topology

/-- Premise D7: a finite rational head plus the proven holomorphic tail is
meromorphic on the disc, including the poles of its finite head. A genuine
zero divisor still requires a proved finite-head decomposition and weight bound. -/
theorem finite_head_square_resolvent_tail_meromorphic
    {ι κ : Type*} (v n : κ → ℂ) (S : Finset κ)
    (w m : ι → ℂ) (R : ℝ) (hR : 0 < R)
    (hw : ∀ i, 2 * R ≤ ‖w i‖)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    MeromorphicOn
      (fun z : ℂ => (∑ j ∈ S, n j * ((z - v j)⁻¹)^2) +
        ∑' i, m i * ((z - w i)⁻¹)^2) {z : ℂ | ‖z‖ < R} := by
  classical
  have ht := weighted_square_resolvent_tail_differentiable w m R hR hw hweight
  intro z hz
  have hh : MeromorphicAt (fun z : ℂ => ∑ j ∈ S, n j * ((z - v j)⁻¹)^2) z := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((analyticAt_const (v := n j)).meromorphicAt.mul
        (((analyticAt_id.sub (analyticAt_const (v := v j))).meromorphicAt.inv).pow 2)).add ih
  exact hh.add (ht.analyticAt ((isOpen_lt continuous_norm continuous_const).mem_nhds hz)).meromorphicAt

end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
open Filter Topology

/-- Premise D7.GLOBAL: local finiteness and the explicit inverse-square weight
bound imply meromorphy of the full squared-resolvent sum. This proves the
finite-head splitting instead of assuming it. Identifying the points and
weights with the genuine Hecke divisor and proving the two premises are
separate arithmetic obligations. -/
theorem locally_finite_square_resolvent_meromorphic
    {ι : Type*} (w m : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    MeromorphicOn (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹)^2) Set.univ := by
  classical
  intro z _
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : ‖z‖ < R := by dsimp [R]; linarith
  let S : Finset ι := (hfinite (2 * R)).toFinset
  have hw : ∀ i : {i : ι // i ∉ S}, 2 * R ≤ ‖w i.val‖ := by
    intro i
    apply le_of_not_gt
    intro hi
    exact i.property ((hfinite (2 * R)).mem_toFinset.mpr hi)
  have hwt : Summable (fun i : {i : ι // i ∉ S} => ‖m i.val‖ / ‖w i.val‖ ^ 2) :=
    hweight.subtype _
  have ht := finite_head_square_resolvent_tail_meromorphic w m S
    (fun i : {i : ι // i ∉ S} => w i.val)
    (fun i : {i : ι // i ∉ S} => m i.val) R hR hw hwt
  have heq : (fun s : ℂ => ∑' i, m i * ((s - w i)⁻¹)^2) =ᶠ[𝓝 z]
      (fun s : ℂ => (∑ i ∈ S, m i * ((s - w i)⁻¹)^2) +
        ∑' i : {i : ι // i ∉ S}, m i.val * ((s - w i.val)⁻¹)^2) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with s hs
    have htail := (MasulloGRH.ConditionalMoment.weighted_square_resolvent_tail_uniform
      (fun i : {i : ι // i ∉ S} => w i.val)
      (fun i : {i : ι // i ∉ S} => m i.val) R hR hw hwt).1 s (le_of_lt hs)
    have hall : Summable (fun i => m i * ((s - w i)⁻¹)^2) :=
      (Finset.summable_compl_iff S).mp htail.of_norm
    exact (hall.sum_add_tsum_compl (s := S)).symm
  exact (ht z hz).congr (heq.symm.filter_mono nhdsWithin_le_nhds)

end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
open Filter Topology

/-- Premise D9.REGULAR: the full sum is analytic at any point outside its
indexed support. Applied to the divisor with one distinct zero removed, this
supplies the regular remainder once arithmetic finiteness and weights are proved. -/
theorem locally_finite_square_resolvent_analyticAt
    {ι : Type*} (w m : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2))
    (z : ℂ) (hzavoid : ∀ i, z ≠ w i) :
    AnalyticAt ℂ (fun s : ℂ => ∑' i, m i * ((s - w i)⁻¹)^2) z := by
  classical
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : ‖z‖ < R := by dsimp [R]; linarith
  let S : Finset ι := (hfinite (2 * R)).toFinset
  have hw : ∀ i : {i : ι // i ∉ S}, 2 * R ≤ ‖w i.val‖ := by
    intro i
    apply le_of_not_gt
    intro hi
    exact i.property ((hfinite (2 * R)).mem_toFinset.mpr hi)
  have hwt : Summable (fun i : {i : ι // i ∉ S} => ‖m i.val‖ / ‖w i.val‖ ^ 2) :=
    hweight.subtype _
  have hhead : AnalyticAt ℂ (fun s : ℂ => ∑ i ∈ S, m i * ((s - w i)⁻¹)^2) z := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact analyticAt_const
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((analyticAt_const (v := m i)).mul
        (((analyticAt_id.sub (analyticAt_const (v := w i))).inv
          (sub_ne_zero.mpr (hzavoid i))).pow 2)).add ih
  have htail := weighted_square_resolvent_tail_differentiable
    (fun i : {i : ι // i ∉ S} => w i.val)
    (fun i : {i : ι // i ∉ S} => m i.val) R hR hw hwt
  have ht := hhead.add (htail.analyticAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds hz))
  have heq : (fun s : ℂ => ∑' i, m i * ((s - w i)⁻¹)^2) =ᶠ[𝓝 z]
      (fun s : ℂ => (∑ i ∈ S, m i * ((s - w i)⁻¹)^2) +
        ∑' i : {i : ι // i ∉ S}, m i.val * ((s - w i.val)⁻¹)^2) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with s hs
    have htail := (MasulloGRH.ConditionalMoment.weighted_square_resolvent_tail_uniform
      (fun i : {i : ι // i ∉ S} => w i.val)
      (fun i : {i : ι // i ∉ S} => m i.val) R hR hw hwt).1 s (le_of_lt hs)
    have hall : Summable (fun i => m i * ((s - w i)⁻¹)^2) :=
      (Finset.summable_compl_iff S).mp htail.of_norm
    exact (hall.sum_add_tsum_compl (s := S)).symm
  exact ht.congr heq.symm


end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
open Filter Topology

/-- D9.SPLIT: absolute summability needed for the genuine one-zero isolation,
once local finiteness and the arithmetic inverse-square bound are established. -/
theorem locally_finite_square_resolvent_summable
    {ι : Type*} (w m : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) (z : ℂ) :
    Summable (fun i => m i * ((z - w i)⁻¹)^2) := by
  classical
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let S : Finset ι := (hfinite (2 * R)).toFinset
  have hw : ∀ i : {i : ι // i ∉ S}, 2 * R ≤ ‖w i.val‖ := by
    intro i
    apply le_of_not_gt
    intro hi
    exact i.property ((hfinite (2 * R)).mem_toFinset.mpr hi)
  have ht := (MasulloGRH.ConditionalMoment.weighted_square_resolvent_tail_uniform
    (fun i : {i : ι // i ∉ S} => w i.val)
    (fun i : {i : ι // i ∉ S} => m i.val) R hR hw (hweight.subtype _)).1
    z (by dsimp [R]; linarith)
  exact (Finset.summable_compl_iff S).mp ht.of_norm

/-- D9.ASSEMBLY: derives the local one-term decomposition and analytic remainder;
no local pole expansion or meromorphy is assumed. The half-plane identity must
still be derived from admissible trace tests for the actual Hecke divisor. -/
theorem square_resolvent_weights_zero_of_halfPlane
    {ι : Type*} (w m : ι → ℂ) (hinj : Function.Injective w)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2))
    (b : ℝ)
    (hzero : ∀ z : ℂ, b < z.re → (∑' i, m i * ((z - w i)⁻¹)^2) = 0) :
    ∀ i, m i = 0 := by
  classical
  intro i
  let J := {j : ι // j ∉ ({i} : Finset ι)}
  let rem : ℂ → ℂ := fun z => ∑' j : J, m j.val * ((z - w j.val)⁻¹)^2
  have hfin : ∀ R : ℝ, {j : J | ‖w j.val‖ < R}.Finite := by
    intro R
    exact (hfinite R).preimage Subtype.val_injective.injOn
  have hreg : AnalyticAt ℂ rem (w i) := by
    apply locally_finite_square_resolvent_analyticAt
      (fun j : J => w j.val) (fun j : J => m j.val) hfin (hweight.subtype _)
    intro j he
    have hj : j.val = i := hinj he.symm
    exact j.property (by simp [hj])
  apply doublePole_coefficient_zero_of_halfPlane
    (fun z => ∑' j, m j * ((z - w j)⁻¹)^2) rem (w i) (m i) b
    (locally_finite_square_resolvent_meromorphic w m hfinite hweight)
    hzero hreg.continuousAt
  apply Filter.Eventually.of_forall
  intro z
  have hs := (locally_finite_square_resolvent_summable w m hfinite hweight z).sum_add_tsum_compl (s := ({i} : Finset ι))
  simpa only [Finset.sum_singleton, rem, J, div_eq_mul_inv, inv_pow] using hs.symm

end ConditionalGRHReviewD


namespace ConditionalGRHReviewD
open Filter Topology

/-- D7.LIMIT: derives the vanishing squared-resolvent sum from termwise
transform limits and a proved summable majorant. These scalar hypotheses
remain obligations for the genuine compact idelic tests; this is not the
arithmetic trace hypothesis. No uniform convergence is assumed. -/
theorem square_resolvent_zero_of_test_limits
    {ι : Type*} (w m : ι → ℂ) (T : ℕ → ι → ℂ)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2))
    (z : ℂ) (C : ℝ)
    (hbound : ∀ n i, ‖T n i‖ ≤ C / ‖w i‖ ^ 2)
    (hlim : ∀ i, Tendsto (fun n => T n i) atTop (𝓝 (((z - w i)⁻¹)^2)))
    (hvanish : ∀ n, (∑' i, m i * T n i) = 0) :
    (∑' i, m i * ((z - w i)⁻¹)^2) = 0 := by
  have hdom : ∀ n i, ‖m i * T n i‖ ≤ C * (‖m i‖ / ‖w i‖ ^ 2) := by
    intro n i
    rw [norm_mul]
    calc
      ‖m i‖ * ‖T n i‖ ≤ ‖m i‖ * (C / ‖w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hbound n i) (norm_nonneg _)
      _ = C * (‖m i‖ / ‖w i‖ ^ 2) := by ring
  have ht : Tendsto (fun n => ∑' i, m i * T n i) atTop
      (𝓝 (∑' i, m i * ((z - w i)⁻¹)^2)) :=
    tendsto_tsum_of_dominated_convergence (hweight.mul_left C)
      (fun i => (hlim i).const_mul (m i)) (Eventually.of_forall hdom)
  have he : (fun n => ∑' i, m i * T n i) = (fun _ : ℕ => (0 : ℂ)) :=
    funext hvanish
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- D7.LIMIT + D9.ASSEMBLY: the remaining scalar estimates for each
half-plane parameter suffice for pole isolation. The input transforms have
not been identified with admissible genuine Hecke tests by this theorem. -/
theorem weights_zero_of_test_limits
    {ι : Type*} (w m : ι → ℂ) (hinj : Function.Injective w)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2))
    (b : ℝ) (T : ℂ → ℕ → ι → ℂ)
    (hbound : ∀ z : ℂ, b < z.re → ∃ C : ℝ,
      ∀ n i, ‖T z n i‖ ≤ C / ‖w i‖ ^ 2)
    (hlim : ∀ z : ℂ, b < z.re → ∀ i,
      Tendsto (fun n => T z n i) atTop (𝓝 (((z - w i)⁻¹)^2)))
    (hvanish : ∀ z : ℂ, b < z.re → ∀ n, (∑' i, m i * T z n i) = 0) :
    ∀ i, m i = 0 := by
  apply square_resolvent_weights_zero_of_halfPlane w m hinj hfinite hweight b
  intro z hz
  obtain ⟨C, hC⟩ := hbound z hz
  exact square_resolvent_zero_of_test_limits w m (T z) hweight z C hC
    (hlim z hz) (hvanish z hz)

end ConditionalGRHReviewD



namespace ConditionalGRHReviewD
open Filter Topology

/-- D7.SUBTRACT.FINITE: bounded-height strip sums are finite from local
finiteness of the locations. No infinite-series convergence is assumed here. -/
theorem strip_height_support_finite {ι : Type*} (w f : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite) (b H : ℝ) :
    (Function.support (fun i =>
      if |(w i).re| < b ∧ |(w i).im| ≤ H then f i else 0)).Finite := by
  classical
  refine (hfinite (|b| + |H| + 1)).subset ?_
  intro i hi
  have hc : |(w i).re| < b ∧ |(w i).im| ≤ H := by
    by_contra hn
    simp [Function.mem_support, hn] at hi
  change ‖w i‖ < |b| + |H| + 1
  have hn := Complex.norm_le_abs_re_add_abs_im (w i)
  have hb := le_abs_self b
  have hH := le_abs_self H
  linarith [hc.1, hc.2]

/-- D7.SUBTRACT: subtraction at finite height gives the half-open annulus,
including its inner boundary. This is the spectral algebra needed when the
same arithmetic trace is available at two widths. -/
theorem strip_height_difference {ι : Type*} (w f : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (a b H : ℝ) (hab : a ≤ b) :
    (∑' i, if a ≤ |(w i).re| ∧ |(w i).re| < b ∧ |(w i).im| ≤ H
      then f i else 0) =
    (∑' i, if |(w i).re| < b ∧ |(w i).im| ≤ H then f i else 0) -
    (∑' i, if |(w i).re| < a ∧ |(w i).im| ≤ H then f i else 0) := by
  classical
  have hb : Summable (fun i => if |(w i).re| < b ∧ |(w i).im| ≤ H then f i else 0) :=
    summable_of_finite_support (strip_height_support_finite w f hfinite b H)
  have ha : Summable (fun i => if |(w i).re| < a ∧ |(w i).im| ≤ H then f i else 0) :=
    summable_of_finite_support (strip_height_support_finite w f hfinite a H)
  rw [← hb.tsum_sub ha]
  apply tsum_congr
  intro i
  by_cases hx : |(w i).re| < a
  · have hy : |(w i).re| < b := lt_of_lt_of_le hx hab
    have hn : ¬a ≤ |(w i).re| := not_le.mpr hx
    simp [hx, hy, hn]
  · have hy : a ≤ |(w i).re| := le_of_not_gt hx
    simp [hx, hy]

/-- D7.RAW: identical raw height limits at two widths imply annular raw
vanishing, before any absolute convergence or cutoff limit is used. The
common value is to be the actual polar-minus-arithmetic term. -/
theorem annular_height_zero_of_two_strip_limits {ι : Type*} (w f : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (a b : ℝ) (hab : a ≤ b) (L : ℂ)
    (ha : Tendsto (fun H : ℝ => ∑' i,
      if |(w i).re| < a ∧ |(w i).im| ≤ H then f i else 0) atTop (𝓝 L))
    (hb : Tendsto (fun H : ℝ => ∑' i,
      if |(w i).re| < b ∧ |(w i).im| ≤ H then f i else 0) atTop (𝓝 L)) :
    Tendsto (fun H : ℝ => ∑' i,
      if a ≤ |(w i).re| ∧ |(w i).re| < b ∧ |(w i).im| ≤ H
      then f i else 0) atTop (𝓝 0) := by
  simpa only [strip_height_difference w f hfinite a b _ hab, sub_self] using hb.sub ha

/-- D7.ABSOLUTE: identifies the vanishing annular raw limit with its absolute
sum. Summability on the annulus remains an explicit analytic obligation. -/
theorem annular_sum_zero_of_two_strip_limits {ι : Type*} (w f : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (a b : ℝ) (hab : a ≤ b) (L : ℂ)
    (ha : Tendsto (fun H : ℝ => ∑' i,
      if |(w i).re| < a ∧ |(w i).im| ≤ H then f i else 0) atTop (𝓝 L))
    (hb : Tendsto (fun H : ℝ => ∑' i,
      if |(w i).re| < b ∧ |(w i).im| ≤ H then f i else 0) atTop (𝓝 L))
    (hs : Summable (fun i => ‖if a ≤ |(w i).re| ∧ |(w i).re| < b
      then f i else 0‖)) :
    (∑' i, if a ≤ |(w i).re| ∧ |(w i).re| < b then f i else 0) = 0 := by
  classical
  have ht : Tendsto (fun H : ℝ => ∑' i,
      if a ≤ |(w i).re| ∧ |(w i).re| < b ∧ |(w i).im| ≤ H
      then f i else 0) atTop
      (𝓝 (∑' i, if a ≤ |(w i).re| ∧ |(w i).re| < b then f i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hs ?_ ?_
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop |(w i).im|] with H hH
      simp [hH]
    · exact Eventually.of_forall fun H i => by
        by_cases h1 : a ≤ |(w i).re| <;>
        by_cases h2 : |(w i).re| < b <;>
        by_cases h3 : |(w i).im| ≤ H <;> simp [h1, h2, h3]
  exact tendsto_nhds_unique ht
    (annular_height_zero_of_two_strip_limits w f hfinite a b hab L ha hb)

end ConditionalGRHReviewD


namespace ConditionalGRHReviewD
open Filter Topology
/-- D7--D9.ANNULAR: two raw strip identities, plus the separately stated
counting and transform estimates, force every coefficient in the half-open
annulus to vanish. This is an analytic reduction, not an arithmetic trace
hypothesis or an assertion that the indexed locations are Hecke zeros. -/
theorem annular_coefficients_zero_of_strip_limits
    {ι : Type*} (w m : ι → ℂ) (hinj : Function.Injective w)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2))
    (a b : ℝ) (hab : a ≤ b) (T : ℂ → ℕ → ι → ℂ)
    (hbound : ∀ z : ℂ, b < z.re → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n i, a ≤ |(w i).re| ∧ |(w i).re| < b → ‖T z n i‖ ≤ C / ‖w i‖ ^ 2)
    (hlim : ∀ z : ℂ, b < z.re → ∀ i,
      a ≤ |(w i).re| ∧ |(w i).re| < b →
      Tendsto (fun n => T z n i) atTop (𝓝 (((z - w i)⁻¹)^2)))
    (hraw : ∀ z : ℂ, b < z.re → ∀ n, ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i,
        if |(w i).re| < a ∧ |(w i).im| ≤ H then m i * T z n i else 0)
        atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i,
        if |(w i).re| < b ∧ |(w i).im| ≤ H then m i * T z n i else 0)
        atTop (𝓝 L)) :
    ∀ i, a ≤ |(w i).re| ∧ |(w i).re| < b → m i = 0 := by
  classical
  let J := {i : ι // a ≤ |(w i).re| ∧ |(w i).re| < b}
  have hj : Function.Injective (fun i : J => w i.val) :=
    hinj.comp Subtype.val_injective
  have hf : ∀ R : ℝ, {i : J | ‖w i.val‖ < R}.Finite := fun R =>
    (hfinite R).preimage Subtype.val_injective.injOn
  have hz := weights_zero_of_test_limits
    (fun i : J => w i.val) (fun i : J => m i.val) hj hf (hweight.subtype _) b
    (fun z n i => T z n i.val) ?_ ?_ ?_
  · intro i hi
    exact hz ⟨i, hi⟩
  · intro z hz
    obtain ⟨C, _, hC⟩ := hbound z hz
    exact ⟨C, fun n i => hC n i.val i.property⟩
  · intro z hz i
    exact hlim z hz i.val i.property
  · intro z hz n
    obtain ⟨C, hC0, hC⟩ := hbound z hz
    obtain ⟨L, ha, hb⟩ := hraw z hz n
    have hs : Summable (fun i => ‖if a ≤ |(w i).re| ∧ |(w i).re| < b
        then m i * T z n i else 0‖) := by
      apply (hweight.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) 
      intro i
      by_cases hi : a ≤ |(w i).re| ∧ |(w i).re| < b
      · simp only [if_pos hi, norm_mul]
        calc
          ‖m i‖ * ‖T z n i‖ ≤ ‖m i‖ * (C / ‖w i‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hC n i hi) (norm_nonneg _)
          _ = C * (‖m i‖ / ‖w i‖ ^ 2) := by ring
      · simp only [if_neg hi, norm_zero]
        exact mul_nonneg hC0 (div_nonneg (norm_nonneg _) (sq_nonneg _))
    have he := annular_sum_zero_of_two_strip_limits w (fun i => m i * T z n i)
      hfinite a b hab L ha hb hs
    have heq := tsum_subtype {i : ι | a ≤ |(w i).re| ∧ |(w i).re| < b}
      (fun i => m i * T z n i)
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, he] using heq

end ConditionalGRHReviewD


open Filter Topology
namespace ConditionalGRHReviewD

/-- D4.DYADIC: discharges weighted inverse-power summability from an
independently established weighted counting bound. This does not assume or
prove the counting bound for genuine Hecke zeros. Adapted from the supplied
alpo dyadic argument, generalized to real counting exponent and weights. -/
theorem summable_weight_mul_rpow_neg_of_count
    {ι : Type*} (h μ : ι → ℝ) (h1 : ∀ i, 1 ≤ h i)
    (hμ : ∀ i, 0 ≤ μ i) (C c s : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hs : c < s)
    (hcount : ∀ T : ℝ, 1 ≤ T → ∀ u : Finset ι,
      (∀ i ∈ u, h i ≤ T) → ∑ i ∈ u, μ i ≤ C * T ^ c) :
    Summable (fun i => μ i * h i ^ (-s)) := by
  classical
  let r : ℝ := 2 ^ (c - s)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable (fun k : ℕ => C * 2 ^ c * r ^ k) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  let K : ι → ℕ := fun i => ⌊Real.logb 2 (h i)⌋₊
  have hlow : ∀ i, (2 : ℝ) ^ (K i : ℝ) ≤ h i := by
    intro i
    have hp : 0 < h i := lt_of_lt_of_le one_pos (h1 i)
    have hl : 0 ≤ Real.logb 2 (h i) := Real.logb_nonneg (by norm_num) (h1 i)
    calc
      (2 : ℝ) ^ (K i : ℝ) ≤ 2 ^ Real.logb 2 (h i) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hl)
      _ = h i := Real.rpow_logb (by norm_num) (by norm_num) hp
  have hupp : ∀ i, h i ≤ (2 : ℝ) ^ (K i + 1) := by
    intro i
    have hp : 0 < h i := lt_of_lt_of_le one_pos (h1 i)
    have hl : Real.logb 2 (h i) ≤ ((K i + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc
      h i = (2 : ℝ) ^ Real.logb 2 (h i) :=
        (Real.rpow_logb (by norm_num) (by norm_num) hp).symm
      _ ≤ 2 ^ ((K i + 1 : ℕ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hl
      _ = (2 : ℝ) ^ (K i + 1) := Real.rpow_natCast _ _
  have hfib : ∀ (u : Finset ι) (k : ℕ),
      ∑ i ∈ u with K i = k, μ i * h i ^ (-s) ≤ C * 2 ^ c * r ^ k := by
    intro u k
    have hT : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hcnt := hcount _ hT (u.filter fun i => K i = k) (by
      intro i hi
      have he : K i = k := (Finset.mem_filter.mp hi).2
      simpa only [he] using hupp i)
    have hterm : ∀ i ∈ u.filter (fun i => K i = k),
        μ i * h i ^ (-s) ≤ μ i * ((2 : ℝ) ^ (k : ℝ)) ^ (-s) := by
      intro i hi
      have he : K i = k := (Finset.mem_filter.mp hi).2
      apply mul_le_mul_of_nonneg_left _ (hμ i)
      apply Real.rpow_le_rpow_of_nonpos (by positivity)
      · simpa only [he] using hlow i
      · linarith
    calc
      (∑ i ∈ u with K i = k, μ i * h i ^ (-s))
          ≤ ∑ i ∈ u with K i = k, μ i * ((2 : ℝ) ^ (k : ℝ)) ^ (-s) :=
        Finset.sum_le_sum hterm
      _ = (∑ i ∈ u with K i = k, μ i) * ((2 : ℝ) ^ (k : ℝ)) ^ (-s) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (C * ((2 : ℝ) ^ (k + 1)) ^ c) * ((2 : ℝ) ^ (k : ℝ)) ^ (-s) :=
        mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = C * 2 ^ c * r ^ k := by
        have e1 : ((2 : ℝ) ^ (k + 1)) ^ c =
            2 ^ c * ((2 : ℝ) ^ (k : ℝ)) ^ c := by
          rw [Real.rpow_natCast, pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
          ring
        have e2 : r ^ k = ((2 : ℝ) ^ (k : ℝ)) ^ c *
            ((2 : ℝ) ^ (k : ℝ)) ^ (-s) := by
          rw [← Real.rpow_add (by positivity)]
          dsimp [r]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
        rw [e1, e2]
        ring
  refine summable_of_sum_le (c := ∑' k : ℕ, C * 2 ^ c * r ^ k)
    (fun i => mul_nonneg (hμ i) (Real.rpow_nonneg (by linarith [h1 i]) _)) ?_
  intro u
  calc
    (∑ i ∈ u, μ i * h i ^ (-s)) =
        ∑ k ∈ u.image K, ∑ i ∈ u with K i = k, μ i * h i ^ (-s) :=
      (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem K hi) _).symm
    _ ≤ ∑ k ∈ u.image K, C * 2 ^ c * r ^ k := Finset.sum_le_sum fun k _ => hfib u k
    _ ≤ ∑' k : ℕ, C * 2 ^ c * r ^ k := hg.sum_le_tsum _ (fun k _ => by positivity)

end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
/-- D4.COUNT_TO_SUM: the standard weighted T(1+log T) counting estimate
implies the inverse-square majorant used in D7.LIMIT and D9.ASSEMBLY. -/
theorem summable_weight_div_sq_of_log_count
    {ι : Type*} (h μ : ι → ℝ) (h1 : ∀ i, 1 ≤ h i)
    (hμ : ∀ i, 0 ≤ μ i) (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ T : ℝ, 1 ≤ T → ∀ u : Finset ι,
      (∀ i ∈ u, h i ≤ T) → ∑ i ∈ u, μ i ≤ C * T * (1 + Real.log T)) :
    Summable (fun i => μ i / h i ^ 2) := by
  have hpoly : ∀ T : ℝ, 1 ≤ T → ∀ u : Finset ι,
      (∀ i ∈ u, h i ≤ T) → ∑ i ∈ u, μ i ≤ (3 * C) * T ^ (3 / 2 : ℝ) := by
    intro T hT u hu
    have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
    have hl := Real.log_le_rpow_div hT0.le (show (0 : ℝ) < 1 / 2 by norm_num)
    have hpow : 1 ≤ T ^ (1 / 2 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_le hT (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    have he : T ^ (3 / 2 : ℝ) = T * T ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hT0, Real.rpow_one]
    calc
      (∑ i ∈ u, μ i) ≤ C * T * (1 + Real.log T) := hcount T hT u hu
      _ ≤ C * T * (3 * T ^ (1 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hT0.le)
        linarith
      _ = (3 * C) * T ^ (3 / 2 : ℝ) := by rw [he]; ring
  have hh := summable_weight_mul_rpow_neg_of_count h μ h1 hμ (3 * C)
    (3 / 2) 2 (by positivity) (by norm_num) (by norm_num) hpoly
  apply hh.congr
  intro i
  rw [Real.rpow_neg (by linarith [h1 i]), Real.rpow_two, div_eq_mul_inv]

/-- D4.HEAD_TAIL: finite bounded preimages handle small spectral locations;
weighted logarithmic counting handles the tail. No zero enumeration or
multiplicity bound is assumed implicitly. -/
theorem inverse_square_summable_of_log_count
    {ι : Type*} (w m : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ T : ℝ, 1 ≤ T → ∀ u : Finset ι,
      (∀ i ∈ u, 1 ≤ ‖w i‖ ∧ ‖w i‖ ≤ T) →
      ∑ i ∈ u, ‖m i‖ ≤ C * T * (1 + Real.log T)) :
    Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2) := by
  classical
  let J := {i : ι // 1 ≤ ‖w i‖}
  have ht : Summable (fun i : J => ‖m i.val‖ / ‖w i.val‖ ^ 2) := by
    apply summable_weight_div_sq_of_log_count
      (fun i : J => ‖w i.val‖) (fun i : J => ‖m i.val‖)
      (fun i => i.property) (fun i => norm_nonneg _) C hC
    intro T hT u hu
    have hh := hcount T hT (u.image Subtype.val) (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      exact ⟨j.property, hu j hj⟩)
    simpa only [Finset.sum_image Subtype.val_injective.injOn] using hh
  have hh : Summable (fun i : {i : ι // ¬1 ≤ ‖w i‖} => ‖m i.val‖ / ‖w i.val‖ ^ 2) := by
    have hf : {i : ι | ¬1 ≤ ‖w i‖}.Finite := by
      simpa only [not_le] using hfinite 1
    letI : Fintype {i : ι // ¬1 ≤ ‖w i‖} := hf.fintype
    exact (hasSum_fintype _).summable
  exact (summable_subtype_and_compl (s := {i : ι | 1 ≤ ‖w i‖})).mp ⟨ht, hh⟩

end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
open Filter Topology
/-- D4 through D9: this analytic reduction replaces the summability premise
by the separate weighted logarithmic count. The raw strip limits and scalar
bounds must still be obtained from actual admissible arithmetic tests. -/
theorem annular_coefficients_zero_of_log_count_and_strip_limits
    {ι : Type*} (w m : ι → ℂ) (hinj : Function.Injective w)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset ι,
      (∀ i ∈ u, 1 ≤ ‖w i‖ ∧ ‖w i‖ ≤ R) →
      ∑ i ∈ u, ‖m i‖ ≤ C * R * (1 + Real.log R))
    (a b : ℝ) (hab : a ≤ b) (T : ℂ → ℕ → ι → ℂ)
    (hbound : ∀ z : ℂ, b < z.re → ∃ B : ℝ, 0 ≤ B ∧
      ∀ n i, a ≤ |(w i).re| ∧ |(w i).re| < b → ‖T z n i‖ ≤ B / ‖w i‖ ^ 2)
    (hlim : ∀ z : ℂ, b < z.re → ∀ i,
      a ≤ |(w i).re| ∧ |(w i).re| < b →
      Tendsto (fun n => T z n i) atTop (𝓝 (((z - w i)⁻¹)^2)))
    (hraw : ∀ z : ℂ, b < z.re → ∀ n, ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i,
        if |(w i).re| < a ∧ |(w i).im| ≤ H then m i * T z n i else 0)
        atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i,
        if |(w i).re| < b ∧ |(w i).im| ≤ H then m i * T z n i else 0)
        atTop (𝓝 L)) :
    ∀ i, a ≤ |(w i).re| ∧ |(w i).re| < b → m i = 0 := by
  exact annular_coefficients_zero_of_strip_limits w m hinj hfinite
    (inverse_square_summable_of_log_count w m hfinite C hC hcount)
    a b hab T hbound hlim hraw

end ConditionalGRHReviewD


namespace ConditionalGRHReviewD
open Filter Topology Set

/-- D4.LOCAL_FINITE: compact zero sets of a nonzero entire function are finite.
This discharges local finiteness after the genuine pole-cleared Hecke function
has been constructed and proved entire and non-identically-zero. -/
theorem finite_entire_zeros_in_closedBall {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ) (R : ℝ) :
    ({z | f z = 0} ∩ Metric.closedBall c R).Finite := by
  by_contra h
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact
    h (isCompact_closedBall c R) Set.inter_subset_right
  have hfreq : ∃ᶠ y in 𝓝[≠] z, f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono fun _ hy => hy.1
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  exact hx (ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ z) hfreq (Set.mem_univ x))

/-- D4.FINITE_ORDER: the identity theorem excludes infinite analytic order
at every point of the same nonzero entire function. -/
theorem entire_analyticOrder_ne_top {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  exact hx (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) htop (Set.mem_univ x))

/-- D4.POSITIVE_ORDER: the coefficients used at actual zeros are their
strictly positive analytic multiplicities, not arbitrary positive weights. -/
theorem entire_zero_order_pos {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) {z : ℂ} (hz : f z = 0) :
    0 < analyticOrderNatAt f z := by
  apply Nat.pos_of_ne_zero
  intro hn
  have hfin := entire_analyticOrder_ne_top hf hx z
  have he : analyticOrderAt f z = 0 := by
    rw [← Nat.cast_analyticOrderNatAt hfin, hn]
    rfl
  exact ((hf.analyticAt z).analyticOrderAt_eq_zero.mp he) hz

/-- D4.SHIFTED_FINITE: the genuine zero subtype remains locally finite after
translation by the critical-line center. No enumeration is postulated. -/
theorem shifted_entire_zeros_locally_finite {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ) (R : ℝ) :
    {z : {z : ℂ // f z = 0} | ‖z.val - c‖ < R}.Finite := by
  have hbig := (finite_entire_zeros_in_closedBall hf hx c R).preimage
    (f := fun z : {z : ℂ // f z = 0} => z.val) Subtype.val_injective.injOn
  apply hbig.subset
  intro z hz
  exact ⟨z.property, Metric.mem_closedBall.mpr (by
    simpa only [dist_eq_norm] using hz.le)⟩

/-- D4.GENUINE_DIVISOR_REDUCTION: local finiteness and inverse-square
summability for the actual zero subtype with actual analytic multiplicities.
The logarithmic count remains an explicit independent premise. Applying this
to the genuine completed Hecke function still requires its analytic bridge. -/
theorem entire_zero_order_inverse_square_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - c‖ ∧ ‖z.val - c‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R)) :
    Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ)‖ / ‖z.val - c‖ ^ 2) := by
  exact inverse_square_summable_of_log_count
    (fun z : {z : ℂ // f z = 0} => z.val - c)
    (fun z => (analyticOrderNatAt f z.val : ℂ))
    (shifted_entire_zeros_locally_finite hf hx c) C hC hcount

end ConditionalGRHReviewD

namespace ConditionalGRHReviewD
open Filter Topology

/-- D10.ANALYTIC_ONLY: all actual zeros of a nonzero entire function lie
on the critical line when the separately stated counting, transform and
raw-strip premises hold. This is not named an arithmetic TraceFormulaHypothesis:
the genuine Hecke continuation and all displayed analytic premises remain
obligations at the intended arithmetic instantiation. -/
theorem entire_zeros_on_critical_line_of_analytic_inputs {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (htests : ∀ a b : ℝ, 0 < a → a < b →
      ∃ T : ℂ → ℕ → {z : ℂ // f z = 0} → ℂ,
      (∀ z : ℂ, b < z.re → ∃ B : ℝ, 0 ≤ B ∧
        ∀ n i, a ≤ |(i.val - (1/2:ℂ)).re| ∧ |(i.val - (1/2:ℂ)).re| < b →
          ‖T z n i‖ ≤ B / ‖i.val - (1/2:ℂ)‖ ^ 2) ∧
      (∀ z : ℂ, b < z.re → ∀ i,
        a ≤ |(i.val - (1/2:ℂ)).re| ∧ |(i.val - (1/2:ℂ)).re| < b →
        Tendsto (fun n => T z n i) atTop (𝓝 (((z - (i.val - (1/2:ℂ)))⁻¹)^2))) ∧
      (∀ z : ℂ, b < z.re → ∀ n, ∃ L : ℂ,
        Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
          if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
          then (analyticOrderNatAt f i.val : ℂ) * T z n i else 0) atTop (𝓝 L) ∧
        Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
          if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
          then (analyticOrderNatAt f i.val : ℂ) * T z n i else 0) atTop (𝓝 L))) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  intro z hz
  by_contra hn
  have hp : 0 < |(z - (1/2:ℂ)).re| := by
    have he : (z - (1/2:ℂ)).re = z.re - 1/2 := by norm_num
    rw [he]
    exact abs_pos.mpr (sub_ne_zero.mpr hn)
  obtain ⟨T, hb, hl, hr⟩ := htests (|(z - (1/2:ℂ)).re| / 2)
    (|(z - (1/2:ℂ)).re| + 1) (by linarith) (by linarith)
  have hm := annular_coefficients_zero_of_log_count_and_strip_limits
    (fun i : {z : ℂ // f z = 0} => i.val - (1/2:ℂ))
    (fun i => (analyticOrderNatAt f i.val : ℂ))
    (by intro i j hij; apply Subtype.ext; exact sub_left_injective hij)
    (shifted_entire_zeros_locally_finite hf hx (1/2:ℂ)) C hC hcount
    (|(z - (1/2:ℂ)).re| / 2) (|(z - (1/2:ℂ)).re| + 1)
    (by linarith) T hb hl hr ⟨z, hz⟩ ⟨by change |(z - (1/2:ℂ)).re| / 2 ≤ |(z - (1/2:ℂ)).re|; linarith,
      by change |(z - (1/2:ℂ)).re| < |(z - (1/2:ℂ)).re| + 1; linarith⟩
  have hm' : (analyticOrderNatAt f z : ℂ) = 0 := hm
  have hm0 : analyticOrderNatAt f z = 0 := by exact_mod_cast hm'
  exact (Nat.ne_of_gt (entire_zero_order_pos hf hx hz)) hm0

end ConditionalGRHReviewD

namespace ConditionalReviewC
open Filter Topology MeasureTheory
open MasulloGRH.ConditionalMoment

/-- C.END_TO_END.ANALYTIC: the scalar bounds and limits are now discharged.
The entire function, its nonzero value, genuine weighted count, and raw strip
agreement remain explicit independent premises, not an arithmetic trace axiom.
Attaching these to the genuine Hecke completion is still required. -/
theorem entire_zeros_on_line_from_concrete_strip_limits {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (hraw : ∀ a b : ℝ, 0 < a → a < b → ∀ z : ℂ, b < z.re → ∀ n : ℕ,
      ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L)) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  apply ConditionalGRHReviewD.entire_zeros_on_critical_line_of_analytic_inputs hf hx C hC hcount
  intro a b ha hab
  refine ⟨fun z n i => concreteTransform z n (i.val-(1/2:ℂ)), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨B, hB, hbound⟩ := cutoffMoment_uniform_spectral_decay b z hz
    refine ⟨B, hB, fun n i hi => ?_⟩
    have hn : i.val - (1/2:ℂ) ≠ 0 := by
      intro he
      have h0 : a ≤ 0 := by simpa only [he, Complex.zero_re, abs_zero] using hi.1
      linarith
    exact hbound ((n : ℝ)+2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) _ hn
      (le_trans (le_abs_self _) hi.2.le)
  · intro z hz i hi
    exact concreteTransform_limit z _ (lt_trans (lt_of_le_of_lt (le_abs_self _) hi.2) hz)
  · exact hraw a b ha hab

end ConditionalReviewC


/- The genuine zero subtype and true analytic orders are retained.
The good-width and raw arithmetic premises remain explicit. -/
namespace ConditionalGRHReviewD
open Filter Topology
theorem entire_zeros_on_critical_line_of_bracketing_widths {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (good : Set ℝ)
    (hbracket : ∀ r : ℝ, 0 < r → ∃ a ∈ good, ∃ b ∈ good, 0 < a ∧ a < r ∧ r < b)
    (htests : ∀ a b : ℝ, a ∈ good → b ∈ good → 0 < a → a < b →
      ∃ T : ℂ → ℕ → {z : ℂ // f z = 0} → ℂ,
      (∀ z : ℂ, b < z.re → ∃ B : ℝ, 0 ≤ B ∧
        ∀ n i, a ≤ |(i.val - (1/2:ℂ)).re| ∧ |(i.val - (1/2:ℂ)).re| < b →
          ‖T z n i‖ ≤ B / ‖i.val - (1/2:ℂ)‖ ^ 2) ∧
      (∀ z : ℂ, b < z.re → ∀ i,
        a ≤ |(i.val - (1/2:ℂ)).re| ∧ |(i.val - (1/2:ℂ)).re| < b →
        Tendsto (fun n => T z n i) atTop (𝓝 (((z - (i.val - (1/2:ℂ)))⁻¹)^2))) ∧
      (∀ z : ℂ, b < z.re → ∀ n, ∃ L : ℂ,
        Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
          if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
          then (analyticOrderNatAt f i.val : ℂ) * T z n i else 0) atTop (𝓝 L) ∧
        Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
          if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
          then (analyticOrderNatAt f i.val : ℂ) * T z n i else 0) atTop (𝓝 L))) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  intro z hz
  by_contra hn
  have hp : 0 < |(z - (1/2:ℂ)).re| := by
    have he : (z - (1/2:ℂ)).re = z.re - 1/2 := by norm_num
    rw [he]
    exact abs_pos.mpr (sub_ne_zero.mpr hn)
  obtain ⟨a, hag, b, hbg, ha, har, hrb⟩ := hbracket _ hp
  obtain ⟨T, hb, hl, hr⟩ := htests a b hag hbg ha (lt_trans har hrb)
  have hm := annular_coefficients_zero_of_log_count_and_strip_limits
    (fun i : {z : ℂ // f z = 0} => i.val - (1/2:ℂ))
    (fun i => (analyticOrderNatAt f i.val : ℂ))
    (by intro i j hij; apply Subtype.ext; exact sub_left_injective hij)
    (shifted_entire_zeros_locally_finite hf hx (1/2:ℂ)) C hC hcount
    a b (le_of_lt (lt_trans har hrb)) T hb hl hr ⟨z, hz⟩ ⟨har.le, hrb⟩
  have hm' : (analyticOrderNatAt f z : ℂ) = 0 := hm
  have hm0 : analyticOrderNatAt f z = 0 := by exact_mod_cast hm'
  exact (Nat.ne_of_gt (entire_zero_order_pos hf hx hz)) hm0

end ConditionalGRHReviewD

namespace ConditionalReviewC
open Filter Topology MeasureTheory
open MasulloGRH.ConditionalMoment
theorem entire_zeros_on_line_from_good_width_concrete_limits {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (good : Set ℝ)
    (hbracket : ∀ r : ℝ, 0 < r → ∃ a ∈ good, ∃ b ∈ good, 0 < a ∧ a < r ∧ r < b)
    (hraw : ∀ a b : ℝ, a ∈ good → b ∈ good → 0 < a → a < b → ∀ z : ℂ, b < z.re → ∀ n : ℕ,
      ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L)) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  apply ConditionalGRHReviewD.entire_zeros_on_critical_line_of_bracketing_widths hf hx C hC hcount good hbracket
  intro a b hag hbg ha hab
  refine ⟨fun z n i => concreteTransform z n (i.val-(1/2:ℂ)), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨B, hB, hbound⟩ := cutoffMoment_uniform_spectral_decay b z hz
    refine ⟨B, hB, fun n i hi => ?_⟩
    have hn : i.val - (1/2:ℂ) ≠ 0 := by
      intro he
      have h0 : a ≤ 0 := by simpa only [he, Complex.zero_re, abs_zero] using hi.1
      linarith
    exact hbound ((n : ℝ)+2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) _ hn
      (le_trans (le_abs_self _) hi.2.le)
  · intro z hz i hi
    exact concreteTransform_limit z _ (lt_trans (lt_of_le_of_lt (le_abs_self _) hi.2) hz)
  · exact hraw a b hag hbg ha hab

end ConditionalReviewC

/- Countability and bracketing repair integrated from conditional_D. -/

namespace BoundaryFreeRepairD
open Filter Topology Set

/-- The actual zero set, not a supplied enumeration, is countable. -/
theorem entire_zero_set_countable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) :
    {z : ℂ | f z = 0}.Countable := by
  have hc : (⋃ n : ℕ, {z : ℂ | f z = 0} ∩ Metric.closedBall 0 (n : ℝ)).Countable :=
    Set.countable_iUnion fun n =>
      (ConditionalGRHReviewD.finite_entire_zeros_in_closedBall hf hx 0 (n : ℝ)).countable
  apply Set.Countable.mono (s₂ := ⋃ n : ℕ,
    {z : ℂ | f z = 0} ∩ Metric.closedBall 0 (n : ℝ)) _ hc
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  apply Set.mem_iUnion.mpr
  refine ⟨n, hz, ?_⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le

/-- A width is free precisely when neither vertical boundary contains a zero. -/
def boundaryFreeWidths (f : ℂ → ℂ) (c : ℂ) : Set ℝ :=
  ((fun z : ℂ => |(z - c).re|) '' {z : ℂ | f z = 0})ᶜ

theorem boundaryFreeWidths_dense {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ) :
    Dense (boundaryFreeWidths f c) := by
  exact Set.Countable.dense_compl ℝ
    ((entire_zero_set_countable hf hx).image (fun z : ℂ => |(z - c).re|))

/-- Every possible positive off-line distance has a pair of free widths.
No moving-width limit or uniform nuclear estimate is needed for this choice. -/
theorem boundaryFreeWidths_bracket {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    {r : ℝ} (hr : 0 < r) :
    ∃ a ∈ boundaryFreeWidths f c, ∃ b ∈ boundaryFreeWidths f c,
      0 < a ∧ a < r ∧ r < b := by
  obtain ⟨a, ha, ha0, har⟩ := (boundaryFreeWidths_dense hf hx c).exists_between hr
  obtain ⟨b, hb, hrb, _⟩ := (boundaryFreeWidths_dense hf hx c).exists_between
    (show r < r + 1 by linarith)
  exact ⟨a, ha, b, hb, ha0, har, hrb⟩


end BoundaryFreeRepairD

namespace ConditionalReviewC
open Filter Topology
theorem entire_zeros_on_line_from_boundary_free_concrete_limits {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (hraw : ∀ a b : ℝ, a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) →
      b ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) → 0 < a → a < b → ∀ z : ℂ, b < z.re → ∀ n : ℕ,
      ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L)) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  exact entire_zeros_on_line_from_good_width_concrete_limits hf hx C hC hcount
    (BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ))
    (fun r hr => BoundaryFreeRepairD.boundaryFreeWidths_bracket hf hx (1/2:ℂ) hr) hraw

end ConditionalReviewC

open scoped BigOperators
namespace ActualZeroCorrection
noncomputable def admittedJets (n : ℕ) (s : ℝ) : ℕ :=
  ((Finset.range n).filter (fun m : ℕ => 2 * (m : ℝ) + 1 < s)).card

theorem admittedJets_le (n : ℕ) (s : ℝ) : admittedJets n s ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

noncomputable def nativeMultiplicity (f : ℂ → ℂ) (c a s : ℝ)
    (z : {z : ℂ // f z = 0}) : ℕ :=
  if |z.val.re - c| < a then analyticOrderNatAt f z.val
  else if |z.val.re - c| = a then admittedJets (analyticOrderNatAt f z.val) s
  else 0

theorem nativeMultiplicity_le (f : ℂ → ℂ) (c a s : ℝ)
    (z : {z : ℂ // f z = 0}) :
    nativeMultiplicity f c a s z ≤ analyticOrderNatAt f z.val := by
  unfold nativeMultiplicity
  split_ifs
  · exact le_rfl
  · exact admittedJets_le _ _
  · exact Nat.zero_le _

/-- Actual finite zero divisor; the missing coefficient is derived, not postulated. -/
theorem finite_actual_correction (f : ℂ → ℂ) (c a s : ℝ)
    (u : Finset {z : ℂ // f z = 0}) (T : {z : ℂ // f z = 0} → ℂ) :
    (∑ z ∈ u, (analyticOrderNatAt f z.val : ℂ) * T z) =
      (∑ z ∈ u, (nativeMultiplicity f c a s z : ℂ) * T z) +
      ∑ z ∈ u, ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Nat.cast_sub (nativeMultiplicity_le f c a s z)]
  ring

/-- Strict boundary admission persists at a zero-width window, counted only once. -/
theorem zero_width_native (f : ℂ → ℂ) (c s : ℝ)
    (z : {z : ℂ // f z = 0}) (hz : z.val.re = c) :
    nativeMultiplicity f c 0 s z = admittedJets (analyticOrderNatAt f z.val) s := by
  simp [nativeMultiplicity, hz]

/-- Boundary-free widths retain the entire exterior multiplicity. -/
theorem exterior_omitted (f : ℂ → ℂ) (c a s : ℝ)
    (z : {z : ℂ // f z = 0}) (hz : a < |z.val.re - c|) :
    analyticOrderNatAt f z.val - nativeMultiplicity f c a s z = analyticOrderNatAt f z.val := by
  unfold nativeMultiplicity
  rw [if_neg (not_lt_of_ge hz.le), if_neg (ne_of_gt hz), Nat.sub_zero]

theorem native_norm_le (f : ℂ → ℂ) (c a s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ) (z : {z : ℂ // f z = 0}) :
    ‖(nativeMultiplicity f c a s z : ℂ) * T z‖ ≤
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖ := by
  simp only [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast nativeMultiplicity_le f c a s z)
    (norm_nonneg _)

/-- Absolute convergence of the genuine full divisor yields the native and
omitted series with no assumption that either correction vanishes. -/
theorem actual_tsum_correction (f : ℂ → ℂ) (c a s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ)
    (habs : Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖)) :
    (∑' z : {z : ℂ // f z = 0}, (analyticOrderNatAt f z.val : ℂ) * T z) =
      (∑' z : {z : ℂ // f z = 0}, (nativeMultiplicity f c a s z : ℂ) * T z) +
      ∑' z : {z : ℂ // f z = 0},
        ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z := by
  have hn : Summable (fun z : {z : ℂ // f z = 0} =>
      (nativeMultiplicity f c a s z : ℂ) * T z) :=
    Summable.of_norm_bounded habs (native_norm_le f c a s T)
  have hf : Summable (fun z : {z : ℂ // f z = 0} =>
      (analyticOrderNatAt f z.val : ℂ) * T z) := habs.of_norm
  have he : (fun z : {z : ℂ // f z = 0} =>
      ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z) =
      fun z => (analyticOrderNatAt f z.val : ℂ) * T z -
        (nativeMultiplicity f c a s z : ℂ) * T z := by
    funext z
    rw [Nat.cast_sub (nativeMultiplicity_le f c a s z)]
    ring
  rw [he, hf.tsum_sub hn]
  abel

/-- Exact arithmetic correction after matching the genuine full-divisor formula.
This is conditional on that formula; it does not prove it or cancel its remainder. -/
theorem corrected_arithmetic (f : ℂ → ℂ) (c a s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ)
    (habs : Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖))
    (G poles : ℂ)
    (hfull : G = poles - ∑' z : {z : ℂ // f z = 0},
      (analyticOrderNatAt f z.val : ℂ) * T z) :
    G = poles - (∑' z : {z : ℂ // f z = 0},
        (nativeMultiplicity f c a s z : ℂ) * T z) -
      ∑' z : {z : ℂ // f z = 0},
        ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z := by
  rw [hfull, actual_tsum_correction f c a s T habs]
  ring

/-- Comparing widths preserves the correction difference instead of assuming
strip independence. The center and boundary regularity are unrestricted. -/
theorem native_width_difference (f : ℂ → ℂ) (c a b s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ)
    (habs : Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖)) :
    (∑' z : {z : ℂ // f z = 0}, (nativeMultiplicity f c b s z : ℂ) * T z) -
      (∑' z : {z : ℂ // f z = 0}, (nativeMultiplicity f c a s z : ℂ) * T z) =
    (∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z) -
    ∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - nativeMultiplicity f c b s z : ℕ) : ℂ) * T z := by
  have ha := actual_tsum_correction f c a s T habs
  have hb := actual_tsum_correction f c b s T habs
  linear_combination ha - hb

end ActualZeroCorrection


namespace FiniteHeightRepairE
open Filter Topology
theorem finite_entire_zeros_in_closedBall {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ) (R : ℝ) :
    ({z | f z = 0} ∩ Metric.closedBall c R).Finite := by
  by_contra h
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact
    h (isCompact_closedBall c R) Set.inter_subset_right
  have hfreq : ∃ᶠ y in 𝓝[≠] z, f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono fun _ hy => hy.1
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  exact hx (ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ z) hfreq (Set.mem_univ x))


/-- Height truncations of a genuine entire zero divisor are finite when the
zero set is confined to a horizontal strip. No infinite divisor sum is assumed. -/
theorem height_zero_set_finite {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W) :
    {z : {z : ℂ // f z = 0} | |z.val.im| ≤ H}.Finite := by
  have hbig := (finite_entire_zeros_in_closedBall hf hx (c : ℂ) (|W| + |H|)).preimage
    (f := fun z : {z : ℂ // f z = 0} => z.val) Subtype.val_injective.injOn
  apply hbig.subset
  intro z hz
  refine ⟨z.property, Metric.mem_closedBall.mpr ?_⟩
  rw [dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (z.val - (c : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
    Complex.ofReal_im, sub_zero] at hn
  have hs := hstrip z.val z.property
  have hW := le_abs_self W
  have hH := le_abs_self H
  change |z.val.im| ≤ H at hz
  linarith

theorem height_weight_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * (if |z.val.im| ≤ H then T z else 0)‖) := by
  apply summable_of_finite_support
  apply (height_zero_set_finite hf hx c W H hstrip).subset
  intro z hz
  by_contra hn
  change ¬ |z.val.im| ≤ H at hn
  simp [Function.mem_support, hn] at hz

/-- Exact finite-height native/full correction, with true multiplicities and
strict admitted boundary jets. Applicable to either actual transform T. -/
theorem actual_height_correction {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H a s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    (∑' z : {z : ℂ // f z = 0}, (analyticOrderNatAt f z.val : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) =
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) +
    ∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c a s z : ℕ) : ℂ) *
        (if |z.val.im| ≤ H then T z else 0) := by
  exact ActualZeroCorrection.actual_tsum_correction f c a s
    (fun z => if |z.val.im| ≤ H then T z else 0)
    (height_weight_summable hf hx c W H hstrip T)

/-- The exact native correction difference is already valid at finite height;
no assertion of equal raw strip limits is used. -/
theorem actual_height_width_difference {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H a b s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c b s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) -
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) =
    (∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c a s z : ℕ) : ℂ) *
        (if |z.val.im| ≤ H then T z else 0)) -
    ∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c b s z : ℕ) : ℂ) *
        (if |z.val.im| ≤ H then T z else 0) := by
  exact ActualZeroCorrection.native_width_difference f c a b s
    (fun z => if |z.val.im| ≤ H then T z else 0)
    (height_weight_summable hf hx c W H hstrip T)

/-- Free boundaries identify the native finite-height sum with the original
strict raw strip sum. The exterior correction is not set to zero. -/
theorem boundary_free_native_height (f : ℂ → ℂ) (c a s H : ℝ)
    (hfree : ∀ z : ℂ, f z = 0 → |z.re - c| ≠ a)
    (T : {z : ℂ // f z = 0} → ℂ) :
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) =
    ∑' z : {z : ℂ // f z = 0},
      if |z.val.re - c| < a ∧ |z.val.im| ≤ H
      then (analyticOrderNatAt f z.val : ℂ) * T z else 0 := by
  apply tsum_congr
  intro z
  by_cases hi : |z.val.re - c| < a <;>
    by_cases ht : |z.val.im| ≤ H <;>
    simp [ActualZeroCorrection.nativeMultiplicity, hi, ht, hfree z.val z.property]


noncomputable def fullHeight (f : ℂ → ℂ) (H : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ) : ℂ :=
  ∑' z, (analyticOrderNatAt f z.val : ℂ) * (if |z.val.im| ≤ H then T z else 0)
noncomputable def nativeHeight (f : ℂ → ℂ) (c a s H : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ) : ℂ :=
  ∑' z, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
    (if |z.val.im| ≤ H then T z else 0)
noncomputable def omittedHeight (f : ℂ → ℂ) (c a s H : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ) : ℂ :=
  ∑' z, ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c a s z : ℕ) : ℂ) *
    (if |z.val.im| ≤ H then T z else 0)

/-- The strongest passage to infinite height needs a matched full-height
limit, not absolute convergence or an unproved vanishing correction. -/
theorem native_limit_iff_omitted_limit {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W a s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) (F N : ℂ)
    (hfull : Tendsto (fun H => fullHeight f H T) atTop (𝓝 F)) :
    Tendsto (fun H => nativeHeight f c a s H T) atTop (𝓝 N) ↔
      Tendsto (fun H => omittedHeight f c a s H T) atTop (𝓝 (F-N)) := by
  have hb (H : ℝ) : fullHeight f H T =
      nativeHeight f c a s H T + omittedHeight f c a s H T :=
    actual_height_correction hf hx c W H a s hstrip T
  have ho : (fun H => omittedHeight f c a s H T) =
      (fun H => fullHeight f H T - nativeHeight f c a s H T) := by
    funext H
    rw [hb H]
    abel
  have hn : (fun H => nativeHeight f c a s H T) =
      (fun H => fullHeight f H T - omittedHeight f c a s H T) := by
    funext H
    rw [hb H]
    abel
  constructor
  · intro h
    rw [ho]
    exact hfull.sub h
  · intro h
    rw [hn]
    have he : F - (F-N) = N := by ring
    simpa only [he] using hfull.sub h

end FiniteHeightRepairE

namespace FiniteHeightRepairE
open Filter Topology

/-- Actual raw-strip limits follow from the full height limit and the limit of
the actual omitted analytic-order deficit. No absolute-convergence premise. -/
theorem raw_limit_of_full_and_omitted {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W a s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-c| ≤ W)
    (hfree : ∀ z : ℂ, f z = 0 → |z.re-c| ≠ a)
    (T : {z : ℂ // f z = 0} → ℂ) (F R : ℂ)
    (hfull : Tendsto (fun H => fullHeight f H T) atTop (𝓝 F))
    (homit : Tendsto (fun H => omittedHeight f c a s H T) atTop (𝓝 R)) :
    Tendsto (fun H : ℝ => ∑' z : {z : ℂ // f z = 0},
      if |z.val.re-c| < a ∧ |z.val.im| ≤ H
      then (analyticOrderNatAt f z.val : ℂ) * T z else 0) atTop (𝓝 (F-R)) := by
  have hn := (native_limit_iff_omitted_limit hf hx c W a s hstrip T F (F-R) hfull).mpr
    (by simpa only [sub_sub_cancel] using homit)
  have he : (fun H => nativeHeight f c a s H T) =
      (fun H : ℝ => ∑' z : {z : ℂ // f z = 0},
        if |z.val.re-c| < a ∧ |z.val.im| ≤ H
        then (analyticOrderNatAt f z.val : ℂ) * T z else 0) := by
    funext H
    exact boundary_free_native_height f c a s H hfree T
  rw [he] at hn
  exact hn

/-- Conditional endpoint with genuine zeros, true multiplicities and the
actual finite-height omitted divisor. Equality of omitted limits remains an
arithmetic obligation; this theorem does not assume or prove its vanishing. -/
theorem critical_line_of_actual_omitted_height_limits {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (W s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-(1/2:ℝ)| ≤ W)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val-(1/2:ℂ)‖ ∧ ‖z.val-(1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (hlimits : ∀ a b : ℝ,
      a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) →
      b ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) →
      0 < a → a < b → ∀ z : ℂ, b < z.re → ∀ n : ℕ, ∃ F R : ℂ,
      Tendsto (fun H => fullHeight f H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)))) atTop (𝓝 F) ∧
      Tendsto (fun H => omittedHeight f (1/2) a s H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)))) atTop (𝓝 R) ∧
      Tendsto (fun H => omittedHeight f (1/2) b s H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)))) atTop (𝓝 R)) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  apply ConditionalReviewC.entire_zeros_on_line_from_boundary_free_concrete_limits
    hf hx C hC hcount
  intro a b hag hbg ha hab z hz n
  have hfree (a : ℝ) (hag : a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ)) :
      ∀ r : ℂ, f r = 0 → |r.re-(1/2:ℝ)| ≠ a := by
    intro r hr he
    apply hag
    refine ⟨r, hr, ?_⟩
    simpa using he
  obtain ⟨F, R, hF, hRa, hRb⟩ := hlimits a b hag hbg ha hab z hz n
  refine ⟨F-R, ?_, ?_⟩
  · simpa using raw_limit_of_full_and_omitted hf hx (1/2) W a s hstrip
      (hfree a hag) (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))) F R hF hRa
  · simpa using raw_limit_of_full_and_omitted hf hx (1/2) W b s hstrip
      (hfree b hbg) (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))) F R hF hRb

end FiniteHeightRepairE

namespace FiniteHeightRepairE
open Filter Topology

/-- A raw strict-strip sum with the SAME genuine divisor and height cutoff. -/
noncomputable def rawHeight (f : ℂ → ℂ) (c a H : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ) : ℂ :=
  ∑' z, if |z.val.re-c| < a ∧ |z.val.im| ≤ H
    then (analyticOrderNatAt f z.val : ℂ) * T z else 0

/-- Native and omitted differences agree before taking ANY infinite-height
limit. Neither a full-divisor limit nor absolute convergence is assumed. -/
theorem native_difference_eq_omitted_difference {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W a b s H : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    nativeHeight f c b s H T - nativeHeight f c a s H T =
      omittedHeight f c a s H T - omittedHeight f c b s H T :=
  actual_height_width_difference hf hx c W H a b s hstrip T

/-- This equivalence locates the exact surviving arithmetic obligation:
free-boundary raw-strip agreement is agreement of actual omitted deficits.
It does not assert either side. -/
theorem raw_difference_limit_iff_omitted_difference_limit {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W a b s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-c| ≤ W)
    (hfa : ∀ z : ℂ, f z = 0 → |z.re-c| ≠ a)
    (hfb : ∀ z : ℂ, f z = 0 → |z.re-c| ≠ b)
    (T : {z : ℂ // f z = 0} → ℂ) (D : ℂ) :
    Tendsto (fun H => rawHeight f c b H T - rawHeight f c a H T) atTop (𝓝 D) ↔
    Tendsto (fun H => omittedHeight f c a s H T - omittedHeight f c b s H T)
      atTop (𝓝 D) := by
  have he (H : ℝ) : rawHeight f c b H T - rawHeight f c a H T =
      omittedHeight f c a s H T - omittedHeight f c b s H T := by
    unfold rawHeight
    rw [← boundary_free_native_height f c b s H hfb T,
      ← boundary_free_native_height f c a s H hfa T]
    exact native_difference_eq_omitted_difference hf hx c W a b s H hstrip T
  simp_rw [he]

/-- Individual native/omitted limits, if supplied, have precisely the same
width-independence obstruction. No common full-height limit is needed. -/
theorem native_limits_equal_iff_omitted_limits_equal {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W a b s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) (Na Nb Ra Rb : ℂ)
    (hna : Tendsto (fun H => nativeHeight f c a s H T) atTop (𝓝 Na))
    (hnb : Tendsto (fun H => nativeHeight f c b s H T) atTop (𝓝 Nb))
    (hra : Tendsto (fun H => omittedHeight f c a s H T) atTop (𝓝 Ra))
    (hrb : Tendsto (fun H => omittedHeight f c b s H T) atTop (𝓝 Rb)) :
    Na = Nb ↔ Ra = Rb := by
  have he : (fun H => nativeHeight f c b s H T - nativeHeight f c a s H T) =
      (fun H => omittedHeight f c a s H T - omittedHeight f c b s H T) := by
    funext H
    exact native_difference_eq_omitted_difference hf hx c W a b s H hstrip T
  have hh := hnb.sub hna
  rw [he] at hh
  have hv : Nb - Na = Ra - Rb := tendsto_nhds_unique hh (hra.sub hrb)
  constructor
  · intro h
    have hz : Ra - Rb = 0 := by rw [← hv, h, sub_self]
    exact sub_eq_zero.mp hz
  · intro h
    have hz : Nb - Na = 0 := by rw [hv, h, sub_self]
    exact (sub_eq_zero.mp hz).symm

#print axioms native_difference_eq_omitted_difference
#print axioms raw_difference_limit_iff_omitted_difference_limit
#print axioms native_limits_equal_iff_omitted_limits_equal
end FiniteHeightRepairE

#print axioms FiniteHeightRepairE.critical_line_of_actual_omitted_height_limits

namespace ConditionalGRHReviewD
open Filter Topology
theorem annular_coefficients_zero_of_strip_limits_far
    {ι : Type*} (w m : ι → ℂ) (hinj : Function.Injective w)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2))
    (a b B : ℝ) (hab : a ≤ b) (T : ℂ → ℕ → ι → ℂ)
    (hbound : ∀ z : ℂ, B < z.re → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n i, a ≤ |(w i).re| ∧ |(w i).re| < b → ‖T z n i‖ ≤ C / ‖w i‖ ^ 2)
    (hlim : ∀ z : ℂ, B < z.re → ∀ i,
      a ≤ |(w i).re| ∧ |(w i).re| < b →
      Tendsto (fun n => T z n i) atTop (𝓝 (((z - w i)⁻¹)^2)))
    (hraw : ∀ z : ℂ, B < z.re → ∀ n, ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i,
        if |(w i).re| < a ∧ |(w i).im| ≤ H then m i * T z n i else 0)
        atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i,
        if |(w i).re| < b ∧ |(w i).im| ≤ H then m i * T z n i else 0)
        atTop (𝓝 L)) :
    ∀ i, a ≤ |(w i).re| ∧ |(w i).re| < b → m i = 0 := by
  classical
  let J := {i : ι // a ≤ |(w i).re| ∧ |(w i).re| < b}
  have hj : Function.Injective (fun i : J => w i.val) :=
    hinj.comp Subtype.val_injective
  have hf : ∀ R : ℝ, {i : J | ‖w i.val‖ < R}.Finite := fun R =>
    (hfinite R).preimage Subtype.val_injective.injOn
  have hz := weights_zero_of_test_limits
    (fun i : J => w i.val) (fun i : J => m i.val) hj hf (hweight.subtype _) B
    (fun z n i => T z n i.val) ?_ ?_ ?_
  · intro i hi
    exact hz ⟨i, hi⟩
  · intro z hz
    obtain ⟨C, _, hC⟩ := hbound z hz
    exact ⟨C, fun n i => hC n i.val i.property⟩
  · intro z hz i
    exact hlim z hz i.val i.property
  · intro z hz n
    obtain ⟨C, hC0, hC⟩ := hbound z hz
    obtain ⟨L, ha, hb⟩ := hraw z hz n
    have hs : Summable (fun i => ‖if a ≤ |(w i).re| ∧ |(w i).re| < b
        then m i * T z n i else 0‖) := by
      apply (hweight.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) 
      intro i
      by_cases hi : a ≤ |(w i).re| ∧ |(w i).re| < b
      · simp only [if_pos hi, norm_mul]
        calc
          ‖m i‖ * ‖T z n i‖ ≤ ‖m i‖ * (C / ‖w i‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (hC n i hi) (norm_nonneg _)
          _ = C * (‖m i‖ / ‖w i‖ ^ 2) := by ring
      · simp only [if_neg hi, norm_zero]
        exact mul_nonneg hC0 (div_nonneg (norm_nonneg _) (sq_nonneg _))
    have he := annular_sum_zero_of_two_strip_limits w (fun i => m i * T z n i)
      hfinite a b hab L ha hb hs
    have heq := tsum_subtype {i : ι | a ≤ |(w i).re| ∧ |(w i).re| < b}
      (fun i => m i * T z n i)
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, he] using heq

theorem entire_zeros_on_critical_line_of_bracketing_widths_far {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (good : Set ℝ) (B : ℝ)
    (hbracket : ∀ r : ℝ, 0 < r → ∃ a ∈ good, ∃ b ∈ good, 0 < a ∧ a < r ∧ r < b)
    (htests : ∀ a b : ℝ, a ∈ good → b ∈ good → 0 < a → a < b →
      ∃ T : ℂ → ℕ → {z : ℂ // f z = 0} → ℂ,
      (∀ z : ℂ, max b B < z.re → ∃ B : ℝ, 0 ≤ B ∧
        ∀ n i, a ≤ |(i.val - (1/2:ℂ)).re| ∧ |(i.val - (1/2:ℂ)).re| < b →
          ‖T z n i‖ ≤ B / ‖i.val - (1/2:ℂ)‖ ^ 2) ∧
      (∀ z : ℂ, max b B < z.re → ∀ i,
        a ≤ |(i.val - (1/2:ℂ)).re| ∧ |(i.val - (1/2:ℂ)).re| < b →
        Tendsto (fun n => T z n i) atTop (𝓝 (((z - (i.val - (1/2:ℂ)))⁻¹)^2))) ∧
      (∀ z : ℂ, max b B < z.re → ∀ n, ∃ L : ℂ,
        Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
          if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
          then (analyticOrderNatAt f i.val : ℂ) * T z n i else 0) atTop (𝓝 L) ∧
        Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
          if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
          then (analyticOrderNatAt f i.val : ℂ) * T z n i else 0) atTop (𝓝 L))) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  intro z hz
  by_contra hn
  have hp : 0 < |(z - (1/2:ℂ)).re| := by
    have he : (z - (1/2:ℂ)).re = z.re - 1/2 := by norm_num
    rw [he]
    exact abs_pos.mpr (sub_ne_zero.mpr hn)
  obtain ⟨a, hag, b, hbg, ha, har, hrb⟩ := hbracket _ hp
  obtain ⟨T, hb, hl, hr⟩ := htests a b hag hbg ha (lt_trans har hrb)
  have hm := annular_coefficients_zero_of_strip_limits_far
    (fun i : {z : ℂ // f z = 0} => i.val - (1/2:ℂ))
    (fun i => (analyticOrderNatAt f i.val : ℂ))
    (by intro i j hij; apply Subtype.ext; exact sub_left_injective hij)
    (shifted_entire_zeros_locally_finite hf hx (1/2:ℂ))
    (entire_zero_order_inverse_square_summable hf hx (1/2:ℂ) C hC hcount)
    a b (max b B) (le_of_lt (lt_trans har hrb)) T hb hl hr ⟨z, hz⟩ ⟨har.le, hrb⟩
  have hm' : (analyticOrderNatAt f z : ℂ) = 0 := hm
  have hm0 : analyticOrderNatAt f z = 0 := by exact_mod_cast hm'
  exact (Nat.ne_of_gt (entire_zero_order_pos hf hx hz)) hm0

end ConditionalGRHReviewD
namespace ConditionalReviewC
open Filter Topology MeasureTheory
open MasulloGRH.ConditionalMoment
theorem entire_zeros_on_line_from_good_width_concrete_limits_far {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val - (1/2:ℂ)‖ ∧ ‖z.val - (1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C * R * (1 + Real.log R))
    (good : Set ℝ) (B : ℝ)
    (hbracket : ∀ r : ℝ, 0 < r → ∃ a ∈ good, ∃ b ∈ good, 0 < a ∧ a < r ∧ r < b)
    (hraw : ∀ a b : ℝ, a ∈ good → b ∈ good → 0 < a → a < b → ∀ z : ℂ, max b B < z.re → ∀ n : ℕ,
      ∃ L : ℂ,
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L) ∧
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 L)) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  apply ConditionalGRHReviewD.entire_zeros_on_critical_line_of_bracketing_widths_far hf hx C hC hcount good B hbracket
  intro a b hag hbg ha hab
  refine ⟨fun z n i => concreteTransform z n (i.val-(1/2:ℂ)), ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨B, hB, hbound⟩ := cutoffMoment_uniform_spectral_decay b z (lt_of_le_of_lt (le_max_left b B) hz)
    refine ⟨B, hB, fun n i hi => ?_⟩
    have hn : i.val - (1/2:ℂ) ≠ 0 := by
      intro he
      have h0 : a ≤ 0 := by simpa only [he, Complex.zero_re, abs_zero] using hi.1
      linarith
    exact hbound ((n : ℝ)+2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) _ hn
      (le_trans (le_abs_self _) hi.2.le)
  · intro z hz i hi
    exact concreteTransform_limit z _ (lt_trans (lt_of_le_of_lt (le_abs_self _) hi.2) (lt_of_le_of_lt (le_max_left b B) hz))
  · exact hraw a b hag hbg ha hab

end ConditionalReviewC
namespace FiniteHeightRepairE
open Filter Topology
theorem critical_line_of_actual_omitted_height_limits_far {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (W s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-(1/2:ℝ)| ≤ W)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {z : ℂ // f z = 0},
      (∀ z ∈ u, 1 ≤ ‖z.val-(1/2:ℂ)‖ ∧ ‖z.val-(1/2:ℂ)‖ ≤ R) →
      ∑ z ∈ u, ‖(analyticOrderNatAt f z.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (hlimits : ∀ a b : ℝ,
      a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) →
      b ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) →
      0 < a → a < b → ∀ z : ℂ, max b W < z.re → ∀ n : ℕ, ∃ F R : ℂ,
      Tendsto (fun H => fullHeight f H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)))) atTop (𝓝 F) ∧
      Tendsto (fun H => omittedHeight f (1/2) a s H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)))) atTop (𝓝 R) ∧
      Tendsto (fun H => omittedHeight f (1/2) b s H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)))) atTop (𝓝 R)) :
    ∀ z : ℂ, f z = 0 → z.re = 1/2 := by
  apply ConditionalReviewC.entire_zeros_on_line_from_good_width_concrete_limits_far
    hf hx C hC hcount (BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ)) W
    (fun r hr => BoundaryFreeRepairD.boundaryFreeWidths_bracket hf hx (1/2:ℂ) hr)
  intro a b hag hbg ha hab z hz n
  have hfree (a : ℝ) (hag : a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ)) :
      ∀ r : ℂ, f r = 0 → |r.re-(1/2:ℝ)| ≠ a := by
    intro r hr he
    apply hag
    refine ⟨r, hr, ?_⟩
    simpa using he
  obtain ⟨F, R, hF, hRa, hRb⟩ := hlimits a b hag hbg ha hab z hz n
  refine ⟨F-R, ?_, ?_⟩
  · simpa using raw_limit_of_full_and_omitted hf hx (1/2) W a s hstrip
      (hfree a hag) (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))) F R hF hRa
  · simpa using raw_limit_of_full_and_omitted hf hx (1/2) W b s hstrip
      (hfree b hbg) (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))) F R hF hRb

#print axioms raw_limit_of_full_and_omitted
#print axioms critical_line_of_actual_omitted_height_limits_far
end FiniteHeightRepairE

namespace FiniteHeightRepairE
open Filter Topology

/-- Exact annular compensation from the actual omitted height difference.
No full-divisor limit or separate native/omitted limits are required. -/
theorem actual_annular_sum_of_omitted_difference_limit {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (c W a b s : ℝ) (hab : a ≤ b)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re-c| ≤ W)
    (hfa : ∀ z : ℂ, f z = 0 → |z.re-c| ≠ a)
    (hfb : ∀ z : ℂ, f z = 0 → |z.re-c| ≠ b)
    (T : {z : ℂ // f z = 0} → ℂ) (D : ℂ)
    (hs : Summable (fun i : {z : ℂ // f z = 0} =>
      ‖if a ≤ |i.val.re-c| ∧ |i.val.re-c| < b
        then (analyticOrderNatAt f i.val : ℂ) * T i else 0‖))
    (hd : Tendsto (fun H => omittedHeight f c a s H T - omittedHeight f c b s H T)
      atTop (𝓝 D)) :
    (∑' i : {z : ℂ // f z = 0}, if a ≤ |i.val.re-c| ∧ |i.val.re-c| < b
      then (analyticOrderNatAt f i.val : ℂ) * T i else 0) = D := by
  have he (H : ℝ) :
      (∑' i : {z : ℂ // f z = 0},
        if a ≤ |i.val.re-c| ∧ |i.val.re-c| < b ∧ |i.val.im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) * T i else 0) =
      omittedHeight f c a s H T - omittedHeight f c b s H T := by
    have hr := ConditionalGRHReviewD.strip_height_difference
      (fun i : {z : ℂ // f z = 0} => i.val - (c : ℂ))
      (fun i => (analyticOrderNatAt f i.val : ℂ) * T i)
      (ConditionalGRHReviewD.shifted_entire_zeros_locally_finite hf hx (c : ℂ))
      a b H hab
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero] at hr
    rw [hr, ← boundary_free_native_height f c b s H hfb T,
      ← boundary_free_native_height f c a s H hfa T]
    exact native_difference_eq_omitted_difference hf hx c W a b s H hstrip T
  have ht : Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
      if a ≤ |i.val.re-c| ∧ |i.val.re-c| < b ∧ |i.val.im| ≤ H
      then (analyticOrderNatAt f i.val : ℂ) * T i else 0) atTop
      (𝓝 (∑' i : {z : ℂ // f z = 0},
      if a ≤ |i.val.re-c| ∧ |i.val.re-c| < b
      then (analyticOrderNatAt f i.val : ℂ) * T i else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hs ?_ ?_
    · intro i
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop |i.val.im|] with H hH
      simp [hH]
    · exact Eventually.of_forall fun H i => by
        by_cases h1 : a ≤ |i.val.re-c| <;>
        by_cases h2 : |i.val.re-c| < b <;>
        by_cases h3 : |i.val.im| ≤ H <;> simp [h1, h2, h3]
        exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  simp_rw [he] at ht
  exact tendsto_nhds_unique ht hd

#print axioms actual_annular_sum_of_omitted_difference_limit
end FiniteHeightRepairE

namespace FiniteHeightRepairE
open Filter Topology
/-- Concrete logged Mellin-cutoff specialization. The annular domination is
proved from the true-order logarithmic count, rather than assumed. -/
theorem concrete_annular_compensation {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (W a b s : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hstrip : ∀ r : ℂ, f r = 0 → |r.re-(1/2:ℝ)| ≤ W)
    (hfa : ∀ r : ℂ, f r = 0 → |r.re-(1/2:ℝ)| ≠ a)
    (hfb : ∀ r : ℂ, f r = 0 → |r.re-(1/2:ℝ)| ≠ b)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-(1/2:ℂ)‖ ∧ ‖r.val-(1/2:ℂ)‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (z : ℂ) (hz : b < z.re) (n : ℕ) (D : ℂ)
    (hd : Tendsto (fun H =>
      omittedHeight f (1/2) a s H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))) -
      omittedHeight f (1/2) b s H
        (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))))
      atTop (𝓝 D)) :
    (∑' i : {r : ℂ // f r = 0},
      if a ≤ |i.val.re-(1/2:ℝ)| ∧ |i.val.re-(1/2:ℝ)| < b
      then (analyticOrderNatAt f i.val : ℂ) *
        ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)) else 0) = D := by
  apply actual_annular_sum_of_omitted_difference_limit hf hx (1/2) W a b s hab
    hstrip hfa hfb (fun i => ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))) D ?_ hd
  have hw := ConditionalGRHReviewD.entire_zero_order_inverse_square_summable
    hf hx (1/2:ℂ) C hC hcount
  obtain ⟨B, hB, hb⟩ := MasulloGRH.ConditionalMoment.cutoffMoment_uniform_spectral_decay b z hz
  apply (hw.mul_left B).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro i
  by_cases hi : a ≤ |i.val.re-(1/2:ℝ)| ∧ |i.val.re-(1/2:ℝ)| < b
  · have he : (i.val-(1/2:ℂ)).re = i.val.re-(1/2:ℝ) := by norm_num
    have hn : i.val-(1/2:ℂ) ≠ 0 := by
      intro hn
      have h0 : a ≤ 0 := by simpa only [← he, hn, Complex.zero_re, abs_zero] using hi.1
      linarith
    have hb' := hb ((n:ℝ)+2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      (i.val-(1/2:ℂ)) hn (by rw [he]; exact (le_abs_self _).trans hi.2.le)
    simp only [if_pos hi, norm_mul]
    calc
      _ ≤ ‖(analyticOrderNatAt f i.val : ℂ)‖ * (B / ‖i.val-(1/2:ℂ)‖^2) :=
        mul_le_mul_of_nonneg_left hb' (norm_nonneg _)
      _ = B * (‖(analyticOrderNatAt f i.val : ℂ)‖ / ‖i.val-(1/2:ℂ)‖^2) := by ring
  · simp only [if_neg hi, norm_zero]
    exact mul_nonneg hB (div_nonneg (norm_nonneg _) (sq_nonneg _))

#print axioms concrete_annular_compensation
end FiniteHeightRepairE
