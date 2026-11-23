import Mathlib
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

#check positiveCutoff_uniform_plateau
#print axioms positiveCutoff_uniform_plateau
#check momentTest_smooth
#print axioms momentTest_smooth
#check momentTest_compact
#print axioms momentTest_compact

#check positiveCutoff_smooth
#print axioms positiveCutoff_smooth
#check positiveCutoff_bounds
#print axioms positiveCutoff_bounds
#check positiveCutoff_eq_one
#print axioms positiveCutoff_eq_one
#check positiveCutoff_support
#print axioms positiveCutoff_support
#check positiveCutoff_compact
#print axioms positiveCutoff_compact
#check positiveCutoff_tsupport_positive
#print axioms positiveCutoff_tsupport_positive
#check positiveCutoff_eventually_one
#print axioms positiveCutoff_eventually_one
#check positiveCutoff_tendsto
#print axioms positiveCutoff_tendsto
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

#check transition_deriv_zero_left
#print axioms transition_deriv_zero_left
#check transition_deriv_zero_right
#print axioms transition_deriv_zero_right
#check transition_deriv_support
#print axioms transition_deriv_support
#check transition_second_support
#print axioms transition_second_support
#check transition_two_derivatives_bounded
#print axioms transition_two_derivatives_bounded
#check positiveCutoff_deriv
#print axioms positiveCutoff_deriv
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

#check positiveCutoff_deriv_support
#print axioms positiveCutoff_deriv_support
#check positiveCutoff_second_support
#print axioms positiveCutoff_second_support
#check positiveCutoff_cross_zero
#print axioms positiveCutoff_cross_zero
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

#check positiveCutoff_second_deriv
#print axioms positiveCutoff_second_deriv
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

#check dilation_weighted_second_mass
#print axioms dilation_weighted_second_mass
#check dilation_first_mass
#print axioms dilation_first_mass
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

#check weighted_dilation_integrable
#print axioms weighted_dilation_integrable
#check lower_second_profile_integrable
#print axioms lower_second_profile_integrable
#check upper_second_profile_integrable
#print axioms upper_second_profile_integrable
#check lower_transition_uniform_weighted_mass
#print axioms lower_transition_uniform_weighted_mass
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

#check positiveCutoff_uniform_second_mass
#print axioms positiveCutoff_uniform_second_mass
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

#check lower_first_profile_integrable
#print axioms lower_first_profile_integrable
#check upper_first_profile_integrable
#print axioms upper_first_profile_integrable
#check positiveCutoff_uniform_first_mass
#print axioms positiveCutoff_uniform_first_mass
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

#check cutoffMoment_second_deriv
#print axioms cutoffMoment_second_deriv
#check cutoffMoment_uniform_second_mass
#print axioms cutoffMoment_uniform_second_mass
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

#check laplace_twice_ibp
#print axioms laplace_twice_ibp
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

#check laplace_square_norm_bound
#print axioms laplace_square_norm_bound
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

#check realCast_second_deriv
#print axioms realCast_second_deriv
#check cutoffMoment_uniform_laplace_decay
#print axioms cutoffMoment_uniform_laplace_decay
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

#check cutoffMoment_uniform_spectral_decay
#print axioms cutoffMoment_uniform_spectral_decay
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

#check concreteTransform_limit
#print axioms concreteTransform_limit
end ConditionalReviewC


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

#check summable_weight_mul_rpow_neg_of_count
#print axioms summable_weight_mul_rpow_neg_of_count
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

#check summable_weight_div_sq_of_log_count
#print axioms summable_weight_div_sq_of_log_count
#check inverse_square_summable_of_log_count
#print axioms inverse_square_summable_of_log_count
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

#check finite_entire_zeros_in_closedBall
#print axioms finite_entire_zeros_in_closedBall
#check entire_analyticOrder_ne_top
#print axioms entire_analyticOrder_ne_top
#check entire_zero_order_pos
#print axioms entire_zero_order_pos
#check shifted_entire_zeros_locally_finite
#print axioms shifted_entire_zeros_locally_finite
#check entire_zero_order_inverse_square_summable
#print axioms entire_zero_order_inverse_square_summable
end ConditionalGRHReviewD

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

#print axioms corrected_arithmetic
#print axioms native_width_difference
#print axioms finite_actual_correction
#print axioms zero_width_native
#print axioms exterior_omitted
#print axioms actual_tsum_correction
end ActualZeroCorrection


namespace ConcreteZeroCorrection
open ConditionalReviewC ConditionalGRHReviewD MasulloGRH.ConditionalMoment
open scoped BigOperators

/-- Genuine multiplicities times the manuscript's logarithmic cutoff transform
are absolutely summable. A central zero is a finite head, never excluded. -/
theorem concrete_zero_divisor_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (n : ℕ) :
    Summable (fun r : {r : ℂ // f r = 0} =>
      ‖(analyticOrderNatAt f r.val : ℂ) * concreteTransform z n (r.val-c)‖) := by
  classical
  have hw := entire_zero_order_inverse_square_summable hf hx c C hC hcount
  obtain ⟨B, hB, hb⟩ := cutoffMoment_uniform_spectral_decay b z hz
  let P : Set {r : ℂ // f r = 0} := {r | r.val-c ≠ 0}
  have ht : Summable (fun r : P =>
      ‖(analyticOrderNatAt f r.val.val : ℂ) * concreteTransform z n (r.val.val-c)‖) := by
    apply Summable.of_nonneg_of_le (fun r => norm_nonneg _) _ ((hw.subtype P).mul_left B)
    intro r
    rw [norm_mul]
    calc
      _ ≤ ‖(analyticOrderNatAt f r.val.val : ℂ)‖ * (B / ‖r.val.val-c‖^2) :=
        mul_le_mul_of_nonneg_left
          (hb ((n:ℝ)+2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) _ r.property (hstrip r.val)) (norm_nonneg _)
      _ = B * (‖(analyticOrderNatAt f r.val.val : ℂ)‖ / ‖r.val.val-c‖^2) := by ring
  have hfin : {r : {r : ℂ // f r = 0} | r ∉ P}.Finite := by
    apply (shifted_entire_zeros_locally_finite hf hx c 1).subset
    intro r hr
    have he : r.val-c = 0 := by simpa [P] using hr
    simp [he]
  letI : Fintype {r : {r : ℂ // f r = 0} | r ∉ P} := hfin.fintype
  have hh : Summable (fun r : {r : {r : ℂ // f r = 0} | r ∉ P} =>
      ‖(analyticOrderNatAt f r.val.val : ℂ) * concreteTransform z n (r.val.val-c)‖) :=
    (hasSum_fintype _).summable
  exact (summable_subtype_and_compl (s := P)).mp ⟨ht, hh⟩

/-- Exact full/native/correction equality for the concrete logged test;
absolute convergence is derived from the count, not postulated as a zero sum. -/
theorem concrete_actual_correction {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (n : ℕ) (a s : ℝ) :
    (∑' r : {r : ℂ // f r = 0},
      (analyticOrderNatAt f r.val : ℂ) * concreteTransform z n (r.val-c)) =
    (∑' r : {r : ℂ // f r = 0},
      (ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℂ) *
        concreteTransform z n (r.val-c)) +
    ∑' r : {r : ℂ // f r = 0},
      ((analyticOrderNatAt f r.val - ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℕ) : ℂ) *
        concreteTransform z n (r.val-c) := by
  exact ActualZeroCorrection.actual_tsum_correction f c.re a s _
    (concrete_zero_divisor_summable hf hx c C hC hcount b hstrip z hz n)

#print axioms concrete_zero_divisor_summable
#print axioms concrete_actual_correction
end ConcreteZeroCorrection

namespace ConcreteZeroCorrection
open ConditionalReviewC ConditionalGRHReviewD MasulloGRH.ConditionalMoment
open Filter Topology
open scoped BigOperators

/-- The positive-width omitted true divisor has an explicit logged-test limit.
The central zero has zero omitted multiplicity; exterior zeros are retained. -/
theorem concrete_omitted_limit {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (a s : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ => ∑' r : {r : ℂ // f r = 0},
      ((analyticOrderNatAt f r.val - ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℕ) : ℂ) *
        concreteTransform z n (r.val-c)) atTop
      (𝓝 (∑' r : {r : ℂ // f r = 0},
        ((analyticOrderNatAt f r.val - ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℕ) : ℂ) *
          ((z-(r.val-c))⁻¹)^2)) := by
  have hw := entire_zero_order_inverse_square_summable hf hx c C hC hcount
  obtain ⟨B, hB, hb⟩ := cutoffMoment_uniform_spectral_decay b z hz
  refine tendsto_tsum_of_dominated_convergence (hw.mul_left B) ?_ ?_
  · intro r
    exact (concreteTransform_limit z (r.val-c) (lt_of_le_of_lt (hstrip r) hz)).const_mul _
  · apply Eventually.of_forall
    intro n r
    by_cases hr : r.val-c = 0
    · have he : r.val = c := sub_eq_zero.mp hr
      have hm : ActualZeroCorrection.nativeMultiplicity f c.re a s r =
          analyticOrderNatAt f r.val := by
        simp [ActualZeroCorrection.nativeMultiplicity, he, ha]
      simp [hm, hr]
    · rw [norm_mul]
      have hm : ‖((analyticOrderNatAt f r.val -
          ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℕ) : ℂ)‖ ≤
          ‖(analyticOrderNatAt f r.val : ℂ)‖ := by
        simp only [Complex.norm_natCast]
        exact_mod_cast Nat.sub_le (analyticOrderNatAt f r.val) _
      calc
        _ ≤ ‖(analyticOrderNatAt f r.val : ℂ)‖ * ‖concreteTransform z n (r.val-c)‖ :=
          mul_le_mul_of_nonneg_right hm (norm_nonneg _)
        _ ≤ ‖(analyticOrderNatAt f r.val : ℂ)‖ * (B / ‖r.val-c‖^2) :=
          mul_le_mul_of_nonneg_left
            (hb ((n:ℝ)+2) (by have := Nat.cast_nonneg (α := ℝ) n; linarith) _ hr (hstrip r))
            (norm_nonneg _)
        _ = B * (‖(analyticOrderNatAt f r.val : ℂ)‖ / ‖r.val-c‖^2) := by ring

#print axioms concrete_omitted_limit
end ConcreteZeroCorrection

namespace ConcreteZeroCorrection
open ConditionalReviewC ConditionalGRHReviewD MasulloGRH.ConditionalMoment
open Filter Topology
open scoped BigOperators

/-- Width subtraction converges to the DIFFERENCE of actual corrections.
No equality of native strip sums or cancellation is inserted. -/
theorem concrete_native_width_limit {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (a d s : ℝ) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (fun n : ℕ =>
      (∑' r : {r : ℂ // f r = 0},
        (ActualZeroCorrection.nativeMultiplicity f c.re d s r : ℂ) * concreteTransform z n (r.val-c)) -
      ∑' r : {r : ℂ // f r = 0},
        (ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℂ) * concreteTransform z n (r.val-c)) atTop
      (𝓝 ((∑' r : {r : ℂ // f r = 0},
        ((analyticOrderNatAt f r.val - ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℕ) : ℂ) *
          ((z-(r.val-c))⁻¹)^2) -
       ∑' r : {r : ℂ // f r = 0},
        ((analyticOrderNatAt f r.val - ActualZeroCorrection.nativeMultiplicity f c.re d s r : ℕ) : ℂ) *
          ((z-(r.val-c))⁻¹)^2)) := by
  have hl := (concrete_omitted_limit hf hx c C hC hcount b hstrip z hz a s ha).sub
    (concrete_omitted_limit hf hx c C hC hcount b hstrip z hz d s hd)
  have he (n : ℕ) := ActualZeroCorrection.native_width_difference f c.re a d s
    (fun r => concreteTransform z n (r.val-c))
    (concrete_zero_divisor_summable hf hx c C hC hcount b hstrip z hz n)
  simpa only [he] using hl

#print axioms concrete_native_width_limit
end ConcreteZeroCorrection

namespace ConcreteZeroCorrection
open ConditionalReviewC ConditionalGRHReviewD MasulloGRH.ConditionalMoment
open Filter Topology
open scoped BigOperators

/-- Concrete omitted squared-resolvent divisor, with true zero orders and
strict native boundary admission. This is not assumed to vanish. -/
noncomputable def omittedResolvent (f : ℂ → ℂ) (c z : ℂ) (a s : ℝ) : ℂ :=
  ∑' r : {r : ℂ // f r = 0},
    ((analyticOrderNatAt f r.val - ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℕ) : ℂ) *
      ((z-(r.val-c))⁻¹)^2

noncomputable def nativeLoggedSum (f : ℂ → ℂ) (c z : ℂ) (a s : ℝ) (n : ℕ) : ℂ :=
  ∑' r : {r : ℂ // f r = 0},
    (ActualZeroCorrection.nativeMultiplicity f c.re a s r : ℂ) * concreteTransform z n (r.val-c)

/-- The exact remaining arithmetic criterion for the actual logged sums.
Equal native limits require equality of the two explicit omitted divisors. -/
theorem concrete_native_equal_limit_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (a d s : ℝ) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (fun n : ℕ => nativeLoggedSum f c z d s n - nativeLoggedSum f c z a s n)
      atTop (𝓝 0) ↔ omittedResolvent f c z a s = omittedResolvent f c z d s := by
  have hl := concrete_native_width_limit hf hx c C hC hcount b hstrip z hz a d s ha hd
  change Tendsto (fun n : ℕ => nativeLoggedSum f c z d s n - nativeLoggedSum f c z a s n)
    atTop (𝓝 (omittedResolvent f c z a s - omittedResolvent f c z d s)) at hl
  constructor
  · intro hzero
    exact sub_eq_zero.mp (tendsto_nhds_unique hl hzero)
  · intro heq
    simpa only [heq, sub_self] using hl

theorem concrete_native_limit_values_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (a d s : ℝ) (ha : 0 < a) (hd : 0 < d)
    (La Ld : ℂ)
    (hla : Tendsto (nativeLoggedSum f c z a s) atTop (𝓝 La))
    (hld : Tendsto (nativeLoggedSum f c z d s) atTop (𝓝 Ld)) :
    La = Ld ↔ omittedResolvent f c z a s = omittedResolvent f c z d s := by
  have hl := concrete_native_width_limit hf hx c C hC hcount b hstrip z hz a d s ha hd
  change Tendsto (fun n : ℕ => nativeLoggedSum f c z d s n - nativeLoggedSum f c z a s n)
    atTop (𝓝 (omittedResolvent f c z a s - omittedResolvent f c z d s)) at hl
  have he := tendsto_nhds_unique (hld.sub hla) hl
  constructor
  · intro heq
    apply sub_eq_zero.mp
    rw [← he, heq, sub_self]
  · intro heq
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [he, heq, sub_self]

theorem concrete_corrected_native_limit {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ R : ℝ, 1 ≤ R → ∀ u : Finset {r : ℂ // f r = 0},
      (∀ r ∈ u, 1 ≤ ‖r.val-c‖ ∧ ‖r.val-c‖ ≤ R) →
      ∑ r ∈ u, ‖(analyticOrderNatAt f r.val : ℂ)‖ ≤ C*R*(1+Real.log R))
    (b : ℝ) (hstrip : ∀ r : {r : ℂ // f r = 0}, (r.val-c).re ≤ b)
    (z : ℂ) (hz : b < z.re) (a s : ℝ) (ha : 0 < a)
    (F : ℂ)
    (hfull : Tendsto (fun n : ℕ => ∑' r : {r : ℂ // f r = 0},
      (analyticOrderNatAt f r.val : ℂ) * concreteTransform z n (r.val-c)) atTop (𝓝 F)) :
    Tendsto (nativeLoggedSum f c z a s) atTop
      (𝓝 (F - omittedResolvent f c z a s)) := by
  have hl := hfull.sub (concrete_omitted_limit hf hx c C hC hcount b hstrip z hz a s ha)
  have he (n : ℕ) := concrete_actual_correction hf hx c C hC hcount b hstrip z hz n a s
  convert hl using 1
  funext n
  dsimp [nativeLoggedSum]
  rw [he n]
  ring

#print axioms concrete_native_equal_limit_iff
#print axioms concrete_native_limit_values_iff
#print axioms concrete_corrected_native_limit
end ConcreteZeroCorrection
