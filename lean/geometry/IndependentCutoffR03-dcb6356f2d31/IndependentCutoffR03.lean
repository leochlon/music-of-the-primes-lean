import Mathlib

/- The actual three-cutoff volume of manuscript (12.4.1.23), with independent
upper and lower endpoints. Analytic S-unit instantiation is in
SMOOTH_UNIT_CUTOFF_R03.md. No projected trace identity is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ActualIndependentCutoff

def clip (lo hi t : ℝ) : ℝ := max lo (min hi t)

theorem clip_eq (lo hi t : ℝ) (hl : lo ≤ t) (hh : t ≤ hi) :
    clip lo hi t = t := by simp [clip, min_eq_right hh, max_eq_right hl]

theorem clip_difference (lo hi x y : ℝ) :
    |clip lo hi x - clip lo hi y| ≤ |x-y| := by
  simp only [clip, max_def, min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;>
    linarith [le_abs_self (x-y), neg_le_abs (x-y)]

theorem clip_zero (lo hi : ℝ) (hl : lo ≤ 0) (hh : 0 ≤ hi) :
    clip lo hi 0 = 0 := clip_eq lo hi 0 hl hh

theorem abs_clip_le (lo hi t : ℝ) (hl : lo ≤ 0) (hh : 0 ≤ hi) :
    |clip lo hi t| ≤ |t| := by
  simpa only [clip_zero lo hi hl hh, sub_zero] using clip_difference lo hi t 0

/-- The radial integration performed after w=xu, with log lambda=a,
log lambda'=b, log lambda''=c. -/
theorem actual_volume (a b c t : ℝ) (hac : -c ≤ a) :
    max 0 (a - max (-c) (t-b)) = a+b-clip (b-c) (a+b) t := by
  simp only [clip, max_def, min_def]
  split_ifs <;> linarith

/-- Log-coordinate smoothing of the spatial and Fourier cutoffs shifts the
same scalar profile by the SUM of their two shifts. -/
theorem smoothed_volume_integrand (a b c t r s : ℝ) (hac : -c ≤ a) :
    max 0 (a - max (-c) (t-r-s-b)) =
      a+b-clip (b-c) (a+b) (t-r-s) := by
  exact actual_volume a b c (t-r-s) hac

theorem shifted_clip_bound (lo hi t r s : ℝ) (hl : lo ≤ 0) (hh : 0 ≤ hi) :
    |clip lo hi (t-r-s)| ≤ |t| + |r| + |s| := by
  calc
    |clip lo hi (t-r-s)| ≤ |t-r-s| := abs_clip_le lo hi _ hl hh
    _ ≤ |t-r| + |s| := abs_sub _ _
    _ ≤ |t| + |r| + |s| := by linarith [abs_sub t r]

theorem clip_eventually_eq (lo hi : ℕ → ℝ)
    (hl : Tendsto lo atTop atBot) (hh : Tendsto hi atTop atTop) (t : ℝ) :
    ∀ᶠ n in atTop, clip (lo n) (hi n) t = t := by
  filter_upwards [hl.eventually (eventually_le_atBot t),
    hh.eventually (eventually_ge_atTop t)] with n hn hm
  exact clip_eq _ _ _ hn hm

theorem independent_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ell : X → ℝ) (F : X → ℂ)
    (lo hi : ℕ → ℝ) (hl0 : ∀ n, lo n ≤ 0) (hh0 : ∀ n, 0 ≤ hi n)
    (hl : Tendsto lo atTop atBot) (hh : Tendsto hi atTop atTop)
    (hell : AEStronglyMeasurable ell μ) (hF : AEStronglyMeasurable F μ)
    (hb : Integrable (fun x => |ell x| * ‖F x‖) μ) :
    Tendsto (fun n => ∫ x, (clip (lo n) (hi n) (ell x) : ℂ) * F x ∂μ)
      atTop (𝓝 (∫ x, (ell x : ℂ) * F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |ell x| * ‖F x‖)
  · intro n
    have hc : Continuous (fun t : ℝ => (clip (lo n) (hi n) t : ℂ)) := by
      unfold clip
      fun_prop
    exact (hc.comp_aestronglyMeasurable hell).mul hF
  · exact hb
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_clip_le _ _ _ (hl0 n) (hh0 n)) (norm_nonneg _)
  · apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [clip_eventually_eq lo hi hl hh (ell x)] with n hn
    rw [hn]

end ActualIndependentCutoff
#print axioms ActualIndependentCutoff.actual_volume
#print axioms ActualIndependentCutoff.smoothed_volume_integrand
#print axioms ActualIndependentCutoff.independent_integral_limit
