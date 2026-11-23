import Mathlib

/-! Insert after FPhysicalFilter. The single smoothing parameter below
satisfies both error regimes of manuscript (12.4.1.28). -/
namespace LCutoffRegime
open Filter
open scoped Topology
noncomputable section

/-- A common smoothing width for independently growing left/right cutoffs. -/
def sharedSmoothing (Lambda Lambda' delta : ℝ) : ℝ := delta / (Lambda+Lambda')

theorem sharedSmoothing_bounds (Lambda Lambda' delta : ℝ)
    (hL : 0 < Lambda) (hL' : 0 < Lambda') (hd : 0 ≤ delta) :
    (0 ≤ sharedSmoothing Lambda Lambda' delta * Lambda ∧
      sharedSmoothing Lambda Lambda' delta * Lambda ≤ delta) ∧
    (0 ≤ sharedSmoothing Lambda Lambda' delta * Lambda' ∧
      sharedSmoothing Lambda Lambda' delta * Lambda' ≤ delta) := by
  have hsum : 0 < Lambda+Lambda' := add_pos hL hL'
  have he : 0 ≤ sharedSmoothing Lambda Lambda' delta := div_nonneg hd hsum.le
  have heq : sharedSmoothing Lambda Lambda' delta * (Lambda+Lambda') = delta := by
    exact div_mul_cancel₀ _ (ne_of_gt hsum)
  constructor
  · refine ⟨mul_nonneg he hL.le, ?_⟩
    calc
      _ ≤ sharedSmoothing Lambda Lambda' delta * (Lambda+Lambda') :=
        mul_le_mul_of_nonneg_left (by linarith) he
      _ = delta := heq
  · refine ⟨mul_nonneg he hL'.le, ?_⟩
    calc
      _ ≤ sharedSmoothing Lambda Lambda' delta * (Lambda+Lambda') :=
        mul_le_mul_of_nonneg_left (by linarith) he
      _ = delta := heq

/-- Both local error conditions hold with one common epsilon and no
comparison between the independent cutoff growth rates. -/
theorem sharedSmoothing_products {ι : Type*} (f : Filter ι)
    (Lambda Lambda' delta : ι → ℝ)
    (hL : Tendsto Lambda f atTop) (hL' : Tendsto Lambda' f atTop)
    (hdnonneg : ∀ᶠ i in f, 0 ≤ delta i) (hd : Tendsto delta f (𝓝 0)) :
    Tendsto (fun i => sharedSmoothing (Lambda i) (Lambda' i) (delta i) * Lambda i)
      f (𝓝 0) ∧
    Tendsto (fun i => sharedSmoothing (Lambda i) (Lambda' i) (delta i) * Lambda' i)
      f (𝓝 0) := by
  have hb := (hL.eventually (eventually_gt_atTop (0 : ℝ))).and
    ((hL'.eventually (eventually_gt_atTop (0 : ℝ))).and hdnonneg)
  have hbound := hb.mono (fun i hi =>
    sharedSmoothing_bounds (Lambda i) (Lambda' i) (delta i) hi.1 hi.2.1 hi.2.2)
  exact ⟨squeeze_zero' (hbound.mono (fun i hi => hi.1.1))
      (hbound.mono (fun i hi => hi.1.2)) hd,
    squeeze_zero' (hbound.mono (fun i hi => hi.2.1))
      (hbound.mono (fun i hi => hi.2.2)) hd⟩

/-- The two cutoffs and their common positive smoothing approach independently. -/
def localRegime : Filter ((ℝ × ℝ) × ℝ) :=
  ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) ×ˢ (𝓝[>] (0 : ℝ))

instance localRegime_neBot : localRegime.NeBot := by
  unfold localRegime
  infer_instance

instance localRegime_countablyGenerated : localRegime.IsCountablyGenerated := by
  unfold localRegime
  infer_instance

theorem localRegime_first :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => p.1.1) localRegime atTop :=
  tendsto_fst.comp tendsto_fst

theorem localRegime_second :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => p.1.2) localRegime atTop :=
  tendsto_snd.comp tendsto_fst

theorem localRegime_delta :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2) localRegime (𝓝 (0 : ℝ)) :=
  (tendsto_snd : Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2) localRegime
    (𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds

theorem localRegime_delta_pos :
    ∀ᶠ p : (ℝ × ℝ) × ℝ in localRegime, 0 < p.2 :=
  (tendsto_snd : Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2) localRegime
    (𝓝[>] (0 : ℝ))).eventually self_mem_nhdsWithin

/-- Precisely the two o(1) smoothing products printed in (12.4.1.28). -/
theorem localRegime_products :
    Tendsto (fun p : (ℝ × ℝ) × ℝ =>
      sharedSmoothing p.1.1 p.1.2 p.2 * p.1.1) localRegime (𝓝 (0 : ℝ)) ∧
    Tendsto (fun p : (ℝ × ℝ) × ℝ =>
      sharedSmoothing p.1.1 p.1.2 p.2 * p.1.2) localRegime (𝓝 (0 : ℝ)) :=
  sharedSmoothing_products localRegime _ _ _ localRegime_first localRegime_second
    (localRegime_delta_pos.mono (fun _p hp => hp.le)) localRegime_delta

end
end LCutoffRegime


/-! The max-log correction explicitly called for in footnote 2 to the proof
of Theorem 12.4.1.1. These scalar identities retain the lower-endpoint term;
they do not postulate a local orbital integral or its limiting estimate. -/
namespace LCutoffRegime
noncomputable section

/-- Independent lower cutoff contribution in logarithmic radial coordinates. -/
def lowerCutoffBoundary (w Lambda' Lambda'' : ℝ) : ℝ :=
  max 0 (Real.log (Lambda' / (w*Lambda'')))

theorem lowerCutoffBoundary_nonneg (w Lambda' Lambda'' : ℝ) :
    0 ≤ lowerCutoffBoundary w Lambda' Lambda'' := le_max_left _ _

/-- The truncated lower limit is the old lower limit plus the retained
nonnegative boundary term. All three radial parameters are positive. -/
theorem log_max_lowerCutoff (w Lambda' Lambda'' : ℝ)
    (hw : 0 < w) (hL' : 0 < Lambda') (hL'' : 0 < Lambda'') :
    Real.log (max (w/Lambda') (1/Lambda'')) =
      Real.log (w/Lambda') + lowerCutoffBoundary w Lambda' Lambda'' := by
  have hx : 0 < w/Lambda' := div_pos hw hL'
  have hy : 0 < 1/Lambda'' := div_pos zero_lt_one hL''
  have hr : Real.log (Lambda'/(w*Lambda'')) =
      Real.log (1/Lambda'') - Real.log (w/Lambda') := by
    rw [Real.log_div (ne_of_gt hL') (ne_of_gt (mul_pos hw hL'')),
      Real.log_mul (ne_of_gt hw) (ne_of_gt hL''),
      Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hL''),
      Real.log_div (ne_of_gt hw) (ne_of_gt hL'), Real.log_one]
    ring
  unfold lowerCutoffBoundary
  rw [hr]
  rcases le_total (w/Lambda') (1/Lambda'') with h | h
  · rw [max_eq_right h]
    have hh := Real.log_le_log hx h
    rw [max_eq_right (sub_nonneg.mpr hh)]
    ring
  · rw [max_eq_left h]
    have hh := Real.log_le_log hy h
    rw [max_eq_left (sub_nonpos.mpr hh), add_zero]

/-- Exact logarithmic interval length before any limit is taken. The
untruncated local volume has the boundary correction subtracted. -/
theorem logarithmic_cutoff_length (w Lambda Lambda' Lambda'' : ℝ)
    (hw : 0 < w) (hL : 0 < Lambda) (hL' : 0 < Lambda') (hL'' : 0 < Lambda'') :
    Real.log Lambda - Real.log (max (w/Lambda') (1/Lambda'')) =
      Real.log (Lambda*Lambda') - Real.log w - lowerCutoffBoundary w Lambda' Lambda'' := by
  rw [log_max_lowerCutoff w Lambda' Lambda'' hw hL' hL'',
    Real.log_div (ne_of_gt hw) (ne_of_gt hL'),
    Real.log_mul (ne_of_gt hL) (ne_of_gt hL')]
  ring

/-- The correction vanishes when the source radial lower limit already
lies above the independent physical lower cutoff. -/
theorem lowerCutoffBoundary_eq_zero (w Lambda' Lambda'' : ℝ)
    (hw : 0 < w) (hL' : 0 < Lambda') (hL'' : 0 < Lambda'')
    (h : Lambda' ≤ w*Lambda'') :
    lowerCutoffBoundary w Lambda' Lambda'' = 0 := by
  unfold lowerCutoffBoundary
  apply max_eq_left
  apply Real.log_nonpos
  · exact le_of_lt (div_pos hL' (mul_pos hw hL''))
  · exact (div_le_one (mul_pos hw hL'')).mpr h

end
end LCutoffRegime


/-! Insert after LTwoCutoff.fragment and LLowerCutoffBoundary.fragment.
Exact lower-endpoint control for the scalar factor in (12.4.1.24).
The integrated Fourier/orbital application has its own logarithmic majorant. -/
namespace LCutoffRegime
open Filter
open scoped Topology
noncomputable section

/-- The lower-endpoint correction has the precise negative-log majorant
once the independent lower cutoff is at least the source cutoff. -/
theorem lowerCutoffBoundary_le_negative_log (w Lambda' Lambda'' : ℝ)
    (hw : 0 < w) (hL' : 0 < Lambda') (hL'' : 0 < Lambda'')
    (hscale : Lambda' ≤ Lambda'') :
    lowerCutoffBoundary w Lambda' Lambda'' ≤ max 0 (-Real.log w) := by
  unfold lowerCutoffBoundary
  apply max_le_max le_rfl
  rw [Real.log_div (ne_of_gt hL') (ne_of_gt (mul_pos hw hL'')),
    Real.log_mul (ne_of_gt hw) (ne_of_gt hL'')]
  have hh := Real.log_le_log hL' hscale
  linarith

/-- Equal lower/source scales retain exactly this nonnegative boundary term. -/
theorem lowerCutoffBoundary_equal_scales (w Lambda' : ℝ)
    (hw : 0 < w) (hL' : 0 < Lambda') :
    lowerCutoffBoundary w Lambda' Lambda' = max 0 (-Real.log w) := by
  unfold lowerCutoffBoundary
  rw [Real.log_div (ne_of_gt hL') (ne_of_gt (mul_pos hw hL')),
    Real.log_mul (ne_of_gt hw) (ne_of_gt hL')]
  congr 1
  ring

/-- Removing the lower physical endpoint first gives eventual pointwise
equality with the untruncated logarithmic length. -/
theorem lowerCutoffBoundary_eventually_zero (w Lambda' : ℝ)
    (hw : 0 < w) (hL' : 0 < Lambda') :
    ∀ᶠ Lambda'' : ℝ in atTop, lowerCutoffBoundary w Lambda' Lambda'' = 0 := by
  filter_upwards [eventually_ge_atTop (max 1 (Lambda'/w))] with L hL
  have hpos : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
  have hbound : Lambda' ≤ w*L := by
    have h := (div_le_iff₀ hw).mp ((le_max_right _ _).trans hL)
    nlinarith
  exact lowerCutoffBoundary_eq_zero w Lambda' L hw hL' hpos hbound

/-- A concrete growing lower cutoff, independent of the upper physical
cutoff, eventually removes the boundary at every fixed positive radius. -/
theorem lowerCutoffBoundary_quadratic_eventually_zero (w : ℝ) (hw : 0 < w) :
    ∀ᶠ Lambda' : ℝ in atTop,
      lowerCutoffBoundary w Lambda' (Lambda'^2) = 0 := by
  filter_upwards [eventually_ge_atTop (max 1 (1/w))] with L hL
  have hpos : 0 < L := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hL)
  have hone : 1 ≤ w*L := by
    have h := (div_le_iff₀ hw).mp ((le_max_right _ _).trans hL)
    nlinarith
  have hbound : L ≤ w*(L^2) := by
    calc
      L = 1*L := by ring
      _ ≤ (w*L)*L := mul_le_mul_of_nonneg_right hone hpos.le
      _ = w*(L^2) := by ring
  exact lowerCutoffBoundary_eq_zero w L (L^2) hw hpos (sq_pos_of_pos hpos) hbound

/-- This explicit cofinal choice is compatible with the same independently
growing upper/source cutoffs and both checked smoothing-product limits. -/
theorem localRegime_lowerBoundary_tendsto (w : ℝ) (hw : 0 < w) :
    Tendsto (fun p : (ℝ × ℝ) × ℝ =>
      lowerCutoffBoundary w p.1.2 (p.1.2^2)) localRegime (𝓝 0) := by
  have hz := localRegime_second.eventually (lowerCutoffBoundary_quadratic_eventually_zero w hw)
  exact tendsto_const_nhds.congr' (hz.mono (fun _p hp => hp.symm))

end
end LCutoffRegime
#check LCutoffRegime.localRegime_lowerBoundary_tendsto
#print axioms LCutoffRegime.localRegime_lowerBoundary_tendsto
