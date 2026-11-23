import Mathlib

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

set_option maxHeartbeats 800000
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace MasulloGRH.ConditionalMoment
/-- B.TEST.MAJORANT: absolute integrability for the logarithmic Mellin test
on t>1; this is the scalar domination needed by compact-cutoff limits. -/
theorem mellin_log_norm_integrable (σ : ℝ) (h : 1 < σ) :
    IntegrableOn (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) (Ioi 1) := by
  set ε : ℝ := (σ - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hi : IntegrableOn (fun x : ℝ => x ^ (ε - σ) / ε) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by rw [hε]; linarith) one_pos).div_const ε
  refine hi.mono' ?_ ?_
  · have : Measurable (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) := by fun_prop
    exact this.aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0:ℝ) < x := lt_trans one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
    have hl := Real.log_le_rpow_div hx0.le hε0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have e1 : x * Real.log x * x ^ (-σ - 1) = Real.log x * x ^ (-σ) := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    rw [e1, Real.rpow_sub hx0, Real.rpow_neg hx0.le]
    calc Real.log x * (x ^ σ)⁻¹ ≤ x ^ ε / ε * (x ^ σ)⁻¹ :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ = x ^ ε / x ^ σ / ε := by ring

/-- B.TEST.TRANSFORM: evaluates the first-moment Mellin transform that
becomes the annular squared resolvent. Compact-cutoff admissibility and uniform
spectral domination remain separate obligations. Adapted from the pinned alpo
MellinElem source, with only Mathlib imported here. -/
theorem mellin_firstMoment (s : ℂ) (h : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - 1) ^ 2 := by
  set w : ℂ := 1 - s with hw
  have hw0 : w ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hw] at this
    linarith
  have hwre : w.re < 0 := by simp [hw]; linarith
  have e : EqOn (fun x : ℝ => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (lt_trans one_pos hx).ne'
    simp only
    rw [cpow_sub _ _ hx0, cpow_one]
    push_cast
    field_simp
  have hderiv : ∀ x ∈ Ici (1:ℝ), HasDerivAt
      (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
      ((Real.log x : ℂ) * (x : ℂ) ^ (-s)) x := by
    intro x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    have hx0c : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
    have h1 := hasDerivAt_ofReal_cpow_const hx0.ne' hw0
    have h2 : HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
      (Real.hasDerivAt_log hx0.ne').ofReal_comp
    have h3 := h1.mul ((h2.div_const w).sub_const (1 / w ^ 2))
    have h4 : HasDerivAt (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
        (w * (x : ℂ) ^ (w - 1) * ((Real.log x : ℂ) / w - 1 / w ^ 2) + (x : ℂ) ^ w * (((x⁻¹ : ℝ) : ℂ) / w)) x := h3
    refine h4.congr_deriv ?_
    have ea : (x : ℂ) ^ (w - 1) = (x : ℂ) ^ (-s) := by congr 1; rw [hw]; ring
    have eb : (x : ℂ) ^ w = x * (x : ℂ) ^ (-s) := by
      rw [show w = 1 + -s by rw [hw]; ring, cpow_add _ _ hx0c, cpow_one]
    rw [ea, eb]
    push_cast
    field_simp
    ring
  have hint : IntegrableOn (fun x : ℝ => (Real.log x : ℂ) * (x : ℂ) ^ (-s)) (Ioi 1) := by
    refine (mellin_log_norm_integrable s.re h).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      exact ((continuous_ofReal.continuousAt.comp (Real.continuousAt_log hx0.ne')).mul
        (continuousAt_ofReal_cpow_const x (-s) (Or.inr hx0.ne'))).continuousWithinAt
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx => ?_)
      have hx0 : (0:ℝ) < x := lt_trans one_pos hx
      have hlog : 0 ≤ Real.log x := Real.log_nonneg (le_of_lt hx)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
        norm_cpow_eq_rpow_re_of_pos hx0, abs_of_nonneg (by positivity),
        Real.rpow_sub_one hx0.ne']
      simp only [neg_re]
      apply le_of_eq
      field_simp
  have hlim : Tendsto (fun x : ℝ => (x : ℂ) ^ w * ((Real.log x : ℂ) / w - 1 / w ^ 2))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, w.re = -r := ⟨-w.re, by ring⟩
    have hr0 : 0 < r := by linarith
    have hA : Tendsto (fun x : ℝ => x ^ (-r)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hr0
    have hB : Tendsto (fun x : ℝ => Real.log x * x ^ (-r)) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop hr0).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.rpow_neg hx.le, div_eq_mul_inv]
    have hg := (hB.div_const ‖w‖).add (hA.div_const (‖w‖ ^ 2))
    simp only [zero_div, add_zero] at hg
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hg
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx0, hr]
    calc x ^ (-r) * ‖(Real.log x : ℂ) / w - 1 / w ^ 2‖
        ≤ x ^ (-r) * (Real.log x / ‖w‖ + 1 / ‖w‖ ^ 2) := by
          gcongr
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog,
            norm_one, norm_pow]
      _ = Real.log x * x ^ (-r) / ‖w‖ + x ^ (-r) / ‖w‖ ^ 2 := by ring
  rw [setIntegral_congr_fun measurableSet_Ioi e,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_div, zero_sub, one_mul]
  rw [hw]
  field_simp
  ring


#check mellin_log_norm_integrable
#print axioms mellin_log_norm_integrable
#check mellin_firstMoment
#print axioms mellin_firstMoment
/-- B.TEST.CUTOFF.LIMIT: derives the scalar cutoff limit from measurable
unit-bounded cutoffs tending to one. Constructing smooth compact arithmetic
cutoffs and a uniform spectral majorant remains a separate obligation. -/
theorem mellin_firstMoment_cutoff_limit (s : ℂ) (hs : 1 < s.re)
    (θ : ℕ → ℝ → ℂ)
    (hθ : ∀ n, AEStronglyMeasurable (θ n) (volume.restrict (Ioi 1)))
    (hbound : ∀ n x, 1 < x → ‖θ n x‖ ≤ 1)
    (hlim : ∀ x, 1 < x → Tendsto (fun n => θ n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x in Ioi (1 : ℝ),
      θ n x * (((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)))
      atTop (𝓝 (1 / (s - 1)^2)) := by
  let f : ℝ → ℂ := fun x => ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)
  have hne : s - 1 ≠ 0 := by
    intro h
    have he := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [Complex.one_re] at he
    linarith
  have hf : Integrable f (volume.restrict (Ioi 1)) := by
    apply Integrable.of_integral_ne_zero
    change (∫ x in Ioi (1 : ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) ≠ 0
    rw [mellin_firstMoment s hs]
    exact one_div_ne_zero (pow_ne_zero 2 hne)
  have ht : Tendsto (fun n => ∫ x in Ioi (1 : ℝ), θ n x * f x)
      atTop (𝓝 (∫ x in Ioi (1 : ℝ), f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      (fun n => (hθ n).mul hf.aestronglyMeasurable) hf.norm (fun n => ?_) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hbound n x hx)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [one_mul] using (hlim x hx).mul_const (f x)
  simpa only [f, mellin_firstMoment s hs] using ht

#check mellin_firstMoment_cutoff_limit
#print axioms mellin_firstMoment_cutoff_limit
end MasulloGRH.ConditionalMoment


namespace MasulloGRH.ConditionalMoment
/-- D6.POINTWISE.EXPLICIT: discharges the measurable-cutoff, unit-bound and
pointwise-limit premises of the scalar Mellin limit using the explicit smooth
compact logarithmic cutoff. Idelic admissibility, exponent/Haar identification,
and the cutoff-uniform inverse-square spectral bound remain separate. -/
theorem explicit_mellin_firstMoment_cutoff_limit (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (1 : ℝ),
      (positiveCutoff ((n : ℝ) + 1) (Real.log x) : ℂ) *
        (((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)))
      atTop (𝓝 (1 / (s - 1)^2)) := by
  apply mellin_firstMoment_cutoff_limit s hs
  · intro n
    have hm : Measurable (fun x : ℝ =>
        (positiveCutoff ((n : ℝ) + 1) (Real.log x) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((positiveCutoff_smooth _).continuous.measurable.comp Real.measurable_log)
    exact hm.aestronglyMeasurable
  · intro n x hx
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (positiveCutoff_bounds _ _).1]
    exact (positiveCutoff_bounds _ _).2
  · intro x hx
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp
      (positiveCutoff_tendsto (Real.log x) (Real.log_pos hx))

#check explicit_mellin_firstMoment_cutoff_limit
#print axioms explicit_mellin_firstMoment_cutoff_limit
end MasulloGRH.ConditionalMoment
