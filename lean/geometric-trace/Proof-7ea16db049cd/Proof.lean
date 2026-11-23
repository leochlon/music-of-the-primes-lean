import Mathlib

/-! D19: the exact lower-cutoff logarithm in manuscript (12.4.1.23--24).
This scalar auxiliary discharges the cutoff-path algebra in the footnote at
manuscript.txt:31174--31178. It does not identify an arithmetic operator or
assume a zero sum. Put r=|w|_{F,S}, p=lambda', q=lambda''.
The actual annular volume, when the interval is nonempty, is
log lambda - log(max(r/p,1/q)); its renormalized weight is defined below.
The genuine Fourier kernel and its integrability remain separate obligations. -/
namespace Geometric19D
open Filter MeasureTheory

noncomputable def lowerCutoffWeight (p q r : ℝ) : ℝ :=
  Real.log (max (r / p) (1 / q)) + Real.log p

/-- Exact comparison required by the lower-cutoff footnote of §12.4. -/
theorem lowerCutoffWeight_eq (p q r : ℝ) (hp : 0 < p) (hq : 0 < q)
    (hr : 0 < r) :
    lowerCutoffWeight p q r = Real.log (max r (p / q)) := by
  unfold lowerCutoffWeight
  by_cases h : p / q ≤ r
  · have h' : 1 / q ≤ r / p := by
      apply (div_le_div_iff₀ hq hp).2
      have hh := (div_le_iff₀ hq).1 h
      nlinarith
    rw [max_eq_left h', max_eq_left h]
    rw [Real.log_div (ne_of_gt hr) (ne_of_gt hp)]
    ring
  · have hle : r ≤ p / q := le_of_lt (lt_of_not_ge h)
    have h' : r / p ≤ 1 / q := by
      apply (div_le_div_iff₀ hp hq).2
      have hh := (le_div_iff₀ hq).1 hle
      nlinarith
    rw [max_eq_right h', max_eq_right hle]
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hq),
      Real.log_div (ne_of_gt hp) (ne_of_gt hq), Real.log_one]
    ring

/-- A ratio bound makes the desired coefficient exact, before taking a limit. -/
theorem lowerCutoffWeight_exact_of_ratio_le (p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (h : p / q ≤ r) :
    lowerCutoffWeight p q r = Real.log r := by
  rw [lowerCutoffWeight_eq p q r hp hq hr, max_eq_left h]

/-- The required ratio-to-zero path gives the manuscript's logarithm. -/
theorem lowerCutoffWeight_tendsto (p q : ℕ → ℝ)
    (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n)
    (hpath : Tendsto (fun n => p n / q n) atTop (nhds 0))
    (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => lowerCutoffWeight (p n) (q n) r) atTop
      (nhds (Real.log r)) := by
  have he : ∀ᶠ n in atTop, lowerCutoffWeight (p n) (q n) r = Real.log r := by
    filter_upwards [hpath.eventually (gt_mem_nhds hr)] with n hn
    exact lowerCutoffWeight_exact_of_ratio_le _ _ _ (hp n) (hq n) hr (le_of_lt hn)
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

/-- Uniform majorant for the logarithmic Fourier integral, once p/q<=1. -/
theorem abs_log_max_le (r t : ℝ) (hr : 0 < r) (ht : t ≤ 1) :
    |Real.log (max r t)| ≤ |Real.log r| := by
  by_cases h : t ≤ r
  · rw [max_eq_left h]
  · have hrt : r ≤ t := le_of_lt (lt_of_not_ge h)
    have htp : 0 < t := lt_of_lt_of_le hr hrt
    rw [max_eq_right hrt, abs_of_nonpos (Real.log_nonpos htp.le ht),
      abs_of_nonpos (Real.log_nonpos hr.le (hrt.trans ht))]
    exact neg_le_neg (Real.log_le_log hr hrt)

/-- A synchronized lower/Fourier cutoff retains a nonzero pointwise correction
on 0<|w|<1, independently of how large the common cutoff is. -/
theorem synchronized_cutoff_correction (p r : ℝ) (hp : 0 < p)
    (hr : 0 < r) (hr1 : r < 1) :
    lowerCutoffWeight p p r - Real.log r = -Real.log r ∧
    0 < lowerCutoffWeight p p r - Real.log r := by
  have hw : lowerCutoffWeight p p r = 0 := by
    rw [lowerCutoffWeight_eq p p r hp hp hr, div_self (ne_of_gt hp),
      max_eq_right hr1.le, Real.log_one]
  rw [hw, zero_sub]
  exact ⟨rfl, neg_pos.mpr (Real.log_neg hr hr1)⟩

#check lowerCutoffWeight_eq
#print axioms lowerCutoffWeight_eq
#check lowerCutoffWeight_tendsto
#print axioms lowerCutoffWeight_tendsto
#check abs_log_max_le
#print axioms abs_log_max_le
#check synchronized_cutoff_correction
#print axioms synchronized_cutoff_correction

/-- The exact two-cutoff logarithmic integral limit needed in (12.4.1.23).
For the arithmetic application X is A_{F,S}, f is the actual Fourier transform
of eta_xi, and r is the genuine product norm. Its log-integrability and kernel
attachment are explicit unresolved inputs, not an assumed trace formula. -/
theorem annular_log_integral_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (r : X → ℝ)
    (p q R : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n)
    (hratio : ∀ n, p n / q n ≤ 1)
    (hpath : Tendsto (fun n => p n / q n) atTop (nhds 0))
    (hR : Tendsto R atTop atTop) (hr : ∀ᵐ x ∂μ, 0 < r x)
    (hmajor : Integrable (fun x => ‖f x‖ * |Real.log (r x)|) μ)
    (hmeas : ∀ n, AEStronglyMeasurable (fun x =>
      if r x ≤ R n then f x * (lowerCutoffWeight (p n) (q n) (r x) : ℂ)
      else 0) μ) :
    Tendsto (fun n => ∫ x, (if r x ≤ R n then
      f x * (lowerCutoffWeight (p n) (q n) (r x) : ℂ) else 0) ∂μ)
      atTop (nhds (∫ x, f x * (Real.log (r x) : ℂ) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖f x‖ * |Real.log (r x)|) hmeas hmajor
  · intro n
    filter_upwards [hr] with x hx
    split_ifs with h
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        lowerCutoffWeight_eq _ _ _ (hp n) (hq n) hx]
      exact mul_le_mul_of_nonneg_left
        (abs_log_max_le _ _ hx (hratio n)) (norm_nonneg _)
    · simp only [norm_zero]
      positivity
  · filter_upwards [hr] with x hx
    have he : ∀ᶠ n in atTop,
        (if r x ≤ R n then f x * (lowerCutoffWeight (p n) (q n) (r x) : ℂ)
        else 0) = f x * (Real.log (r x) : ℂ) := by
      filter_upwards [hR.eventually (eventually_ge_atTop (r x)),
        hpath.eventually (gt_mem_nhds hx)] with n hn hq'
      rw [if_pos hn, lowerCutoffWeight_exact_of_ratio_le _ _ _
        (hp n) (hq n) hx hq'.le]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

#check annular_log_integral_tendsto
#print axioms annular_log_integral_tendsto

end Geometric19D

namespace Geometric20D
open Filter MeasureTheory Geometric19D

/-- Discharges the logarithmic-majorant premise in (12.4.1.23) from
half-power moments; it does not assume any zero sum or trace identity. -/
theorem abs_log_le_half_moments (r : ℝ) (hr : 0 < r) :
    |Real.log r| ≤ 2 * (Real.sqrt r + 1 / Real.sqrt r) := by
  have ht : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hupper := Real.log_le_sub_one_of_pos ht
  have hlower := Real.log_le_sub_one_of_pos (one_div_pos.mpr ht)
  rw [Real.log_div one_ne_zero (ne_of_gt ht), Real.log_one] at hlower
  have habs : |Real.log (Real.sqrt r)| ≤ Real.sqrt r + 1 / Real.sqrt r := by
    apply abs_le.2
    constructor <;> linarith [one_div_pos.mpr ht]
  have he : Real.log r = 2 * Real.log (Real.sqrt r) := by
    have h := Real.log_mul (ne_of_gt ht) (ne_of_gt ht)
    rw [Real.mul_self_sqrt hr.le] at h
    linarith
  rw [he, abs_mul]
  rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  linarith

/-- The precise missing domination input of D19 follows from two independent
power-weighted L1 estimates. In the intended application f=Fourier(eta_xi),
r=|w|_(F,S), and mu is additive Haar. Those estimates still need an arithmetic
proof for eta_xi and control of its unit-index sum. -/
theorem log_integrable_of_half_moments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (r : X → ℝ)
    (hr : ∀ᵐ x ∂μ, 0 < r x)
    (hmeas : AEStronglyMeasurable (fun x => ‖f x‖ * |Real.log (r x)|) μ)
    (hplus : Integrable (fun x => ‖f x‖ * Real.sqrt (r x)) μ)
    (hminus : Integrable (fun x => ‖f x‖ * (1 / Real.sqrt (r x))) μ) :
    Integrable (fun x => ‖f x‖ * |Real.log (r x)|) μ := by
  apply ((hplus.add hminus).const_mul 2).mono' hmeas
  filter_upwards [hr] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _))]
  have h := mul_le_mul_of_nonneg_left (abs_log_le_half_moments (r x) hx)
    (norm_nonneg (f x))
  dsimp only [Pi.add_apply]
  nlinarith

/-- Integrated next step toward 12.4.1.23: replace its unproved logarithmic
majorant by explicit half-power moments, and retain the required cutoff path.
No actual-kernel, diagonal-trace or selected-window identity is asserted. -/
theorem annular_limit_of_half_moments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℂ) (r : X → ℝ)
    (p q R : ℕ → ℝ) (hp : ∀ n, 0 < p n) (hq : ∀ n, 0 < q n)
    (hratio : ∀ n, p n / q n ≤ 1)
    (hpath : Tendsto (fun n => p n / q n) atTop (nhds 0))
    (hR : Tendsto R atTop atTop) (hr : ∀ᵐ x ∂μ, 0 < r x)
    (hlogmeas : AEStronglyMeasurable (fun x => ‖f x‖ * |Real.log (r x)|) μ)
    (hplus : Integrable (fun x => ‖f x‖ * Real.sqrt (r x)) μ)
    (hminus : Integrable (fun x => ‖f x‖ * (1 / Real.sqrt (r x))) μ)
    (hmeas : ∀ n, AEStronglyMeasurable (fun x =>
      if r x ≤ R n then f x * (lowerCutoffWeight (p n) (q n) (r x) : ℂ)
      else 0) μ) :
    Tendsto (fun n => ∫ x, (if r x ≤ R n then
      f x * (lowerCutoffWeight (p n) (q n) (r x) : ℂ) else 0) ∂μ)
      atTop (nhds (∫ x, f x * (Real.log (r x) : ℂ) ∂μ)) := by
  exact annular_log_integral_tendsto μ f r p q R hp hq hratio hpath hR hr
    (log_integrable_of_half_moments μ f r hr hlogmeas hplus hminus) hmeas

end Geometric20D
#check Geometric20D.abs_log_le_half_moments
#print axioms Geometric20D.abs_log_le_half_moments
#check Geometric20D.log_integrable_of_half_moments
#print axioms Geometric20D.log_integrable_of_half_moments
#check Geometric20D.annular_limit_of_half_moments
#print axioms Geometric20D.annular_limit_of_half_moments
