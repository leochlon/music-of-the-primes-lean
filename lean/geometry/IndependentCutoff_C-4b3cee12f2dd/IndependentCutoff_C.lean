import Mathlib

set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GeometricTraceC

/-- Logarithmic length of the actual x-window in (12.4.1.23),
with lambda = lambda' = exp n and lambda'' = exp (2*n). -/
def orbitalWindow (n t : ℝ) : ℝ := max (n - max (t - n) (-2*n)) 0

theorem orbitalWindow_split (n t : ℝ) (hn : 0 ≤ n) :
    orbitalWindow n t = max (2*n-t) 0 - max (-n-t) 0 := by
  unfold orbitalWindow
  rcases le_total t (-n) with h | h
  · rw [max_eq_right (by linarith : t-n ≤ -2*n),
      max_eq_left (by linarith : 0 ≤ n-(-2*n)),
      max_eq_left (by linarith : 0 ≤ 2*n-t),
      max_eq_left (by linarith : 0 ≤ -n-t)]
    ring
  · rw [max_eq_left (by linarith : -2*n ≤ t-n),
      max_eq_right (by linarith : -n-t ≤ 0), sub_zero]
    congr 1
    ring

theorem orbitalWindow_centered_bound (n t : ℝ) (hn : 0 ≤ n) :
    |orbitalWindow n t - 2*n| ≤ |t| := by
  rw [orbitalWindow_split n t hn]
  rcases le_total t (-n) with h | h
  · rw [max_eq_left (by linarith : 0 ≤ 2*n-t),
      max_eq_left (by linarith : 0 ≤ -n-t)]
    rw [show 2*n-t-(-n-t)-2*n = n by ring, abs_of_nonneg hn,
      abs_of_nonpos (by linarith : t ≤ 0)]
    linarith
  · rw [max_eq_right (by linarith : -n-t ≤ 0), sub_zero]
    rcases le_total t (2*n) with h' | h'
    · rw [max_eq_left (by linarith : 0 ≤ 2*n-t)]
      simpa using (le_refl |t|)
    · rw [max_eq_right (by linarith : 2*n-t ≤ 0), zero_sub,
        abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2*n),
        abs_of_nonneg (by linarith : 0 ≤ t)]
      exact h'

theorem orbitalWindow_centered_eq (n t : ℝ) (hn : |t| ≤ n) :
    orbitalWindow n t - 2*n = -t := by
  have hn0 : 0 ≤ n := (abs_nonneg t).trans hn
  rw [orbitalWindow_split n t hn0,
    max_eq_left (by have := le_abs_self t; linarith : 0 ≤ 2*n-t),
    max_eq_right (by have := neg_abs_le t; linarith : -n-t ≤ 0)]
  ring

theorem orbitalWindow_centered_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => orbitalWindow n t - 2*n) atTop (𝓝 (-t)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop.eventually_ge_atTop |t|)] with n hn
  exact (orbitalWindow_centered_eq n t hn).symm

/-- The logarithmic orbital integral converges along an explicit admissible
three-cutoff family, using precisely the absolute log moment of its Fourier input. -/
theorem orbital_integral_limit {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (t : X → ℝ) (f : X → ℂ)
    (ht : AEStronglyMeasurable t μ) (hf : AEStronglyMeasurable f μ)
    (hlog : Integrable (fun x => |t x| * ‖f x‖) μ) :
    Tendsto (fun n : ℕ => ∫ x, (orbitalWindow n (t x) - 2*n) • f x ∂μ)
      atTop (𝓝 (∫ x, (-t x) • f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |t x| * ‖f x‖)
  · intro n
    have hc : Continuous (fun u : ℝ => orbitalWindow n u - 2*n) := by
      unfold orbitalWindow
      fun_prop
    exact (hc.comp_aestronglyMeasurable ht).smul hf
  · exact hlog
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (orbitalWindow_centered_bound n (t x) (Nat.cast_nonneg n)) (norm_nonneg _)
  · exact Filter.Eventually.of_forall fun x =>
      (orbitalWindow_centered_tendsto (t x)).smul tendsto_const_nhds

/-- General independent lower cutoff: its residual depends on M-N. -/
theorem orbitalWindow_general (L M N t : ℝ) (hLN : 0 ≤ L+N) :
    max (L - max (t-M) (-N)) 0 =
      max (L+M-t) 0 - max (M-N-t) 0 := by
  rcases le_total t (M-N) with h | h
  · rw [max_eq_right (by linarith : t-M ≤ -N),
      max_eq_left (by linarith : 0 ≤ L-(-N)),
      max_eq_left (by linarith : 0 ≤ L+M-t),
      max_eq_left (by linarith : 0 ≤ M-N-t)]
    ring
  · rw [max_eq_left (by linarith : -N ≤ t-M),
      max_eq_right (by linarith : M-N-t ≤ 0), sub_zero]
    congr 1
    ring

end GeometricTraceC
#print axioms GeometricTraceC.orbitalWindow_centered_tendsto

#print axioms GeometricTraceC.orbital_integral_limit
#print axioms GeometricTraceC.orbitalWindow_general
