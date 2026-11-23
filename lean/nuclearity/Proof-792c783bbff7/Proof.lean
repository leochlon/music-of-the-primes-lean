import Mathlib

/-!
Round 1, participant H. Supporting results only; no full Hecke GRH claim.
The vertical translation below records the effect expected from a unitary norm
twist. Its equality with the genuine Hecke L-function remains to be constructed.
-/
namespace MasulloGRH

def normTwistShift (t : ℝ) (s : ℂ) : ℂ := s + (t : ℂ) * Complex.I

theorem normTwistShift_re (t : ℝ) (s : ℂ) :
    (normTwistShift t s).re = s.re := by
  simp [normTwistShift, Complex.mul_re]

theorem normTwist_criticalLine_iff (t : ℝ) (s : ℂ) :
    (normTwistShift t s).re = (1 / 2 : ℝ) ↔ s.re = (1 / 2 : ℝ) := by
  rw [normTwistShift_re]

theorem jetFactor_ne_zero {c z : ℂ} (m : ℕ) (h : z ≠ c) :
    (z - c) ^ m ≠ 0 := by
  exact pow_ne_zero _ (sub_ne_zero.mpr h)

/- The positive-real branch of the Archimedean integrand at z = 3/2,
apart from its positive normalization factor, is this rational function. -/
noncomputable def archimedeanKernel (t : ℝ) : ℝ := 1 / (t ^ 2 * (t - 1))

theorem archimedeanKernel_split (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    archimedeanKernel t = 1 / (t - 1) - 1 / t - 1 / t ^ 2 := by
  unfold archimedeanKernel
  field_simp [h0, sub_ne_zero.mpr h1]
  ring

theorem log_cutoff_unbounded (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ A < -Real.log δ := by
  refine ⟨Real.exp (-(|A| + 1)), Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have := abs_nonneg A
    linarith
  · rw [Real.log_exp]
    have := le_abs_self A
    linarith

/- A constructive repair of the local singularity: subtracting the same
kernel at two parameters cancels the 1/(t-1) term. At parameters 3/2 and
5/2 the difference is simply t^(-3), hence regular at t = 1. -/
theorem archimedeanKernel_difference (t : ℝ) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    1 / (t ^ 2 * (t - 1)) - 1 / (t ^ 3 * (t - 1)) = 1 / t ^ 3 := by
  field_simp [h0, sub_ne_zero.mpr h1]

theorem archimedeanKernel_lower (t : ℝ) (ht : 1 < t) (h2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ archimedeanKernel t := by
  have hp : 0 < t - 1 := by linarith
  have ht0 : 0 < t := by linarith
  have hs : t ^ 2 ≤ 4 := by nlinarith
  unfold archimedeanKernel
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_right hs hp.le]

theorem cutoff_lower_bound_forces_unbounded (f : ℝ → ℝ)
    (h : ∀ δ, 0 < δ → δ < 1 → -Real.log δ / 8 ≤ f δ) (A : ℝ) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ A < f δ := by
  obtain ⟨δ, hd, hd1, hlog⟩ := log_cutoff_unbounded (8 * A)
  refine ⟨δ, hd, hd1, ?_⟩
  have := h δ hd hd1
  linarith

theorem reciprocal_cutoff_integral_eq_log {δ : ℝ} (hd : 0 < δ) (hd1 : δ < 1) :
    (∫ u : ℝ in δ..1, 1 / u) = -Real.log δ := by
  have hz : (0 : ℝ) ∉ Set.uIcc δ 1 := by
    rw [Set.uIcc_of_le hd1.le]
    intro h
    have := h.1
    linarith
  rw [integral_one_div hz, one_div, Real.log_inv]

theorem reciprocal_cutoff_integral_unbounded (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ A < ∫ u : ℝ in δ..1, 1 / u := by
  obtain ⟨δ, hd, hd1, ha⟩ := log_cutoff_unbounded A
  refine ⟨δ, hd, hd1, ?_⟩
  rwa [reciprocal_cutoff_integral_eq_log hd hd1]

#check reciprocal_cutoff_integral_eq_log
#print axioms reciprocal_cutoff_integral_eq_log
#check reciprocal_cutoff_integral_unbounded
#print axioms reciprocal_cutoff_integral_unbounded

theorem archimedean_cutoff_integral_lower {δ : ℝ} (hd : 0 < δ) (hd1 : δ < 1) :
    -Real.log δ / 4 ≤ ∫ u : ℝ in δ..1, archimedeanKernel (1 + u) := by
  have hxpos : ∀ x ∈ Set.uIcc δ 1, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hd1.le] at hx
    exact lt_of_lt_of_le hd hx.1
  have hf : ContinuousOn (fun x : ℝ => 1 / x) (Set.uIcc δ 1) := by
    apply continuousOn_const.div continuousOn_id
    intro x hx
    exact ne_of_gt (hxpos x hx)
  have hg : ContinuousOn (fun x : ℝ => archimedeanKernel (1 + x))
      (Set.uIcc δ 1) := by
    unfold archimedeanKernel
    apply continuousOn_const.div (by fun_prop)
    intro x hx
    have hp := hxpos x hx
    have he : 1 + x - 1 = x := by ring
    have h : 0 < (1 + x) ^ 2 * (1 + x - 1) := by
      rw [he]
      positivity
    exact ne_of_gt h
  have hcmp := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hd1.le
    (continuousOn_const.mul hf).intervalIntegrable hg.intervalIntegrable
    (fun x hx => show (1 / 4 : ℝ) * (1 / x) ≤ archimedeanKernel (1 + x) from by
      have hl : 1 < 1 + x := by linarith [hx.1]
      have hu : 1 + x ≤ 2 := by linarith [hx.2]
      have hh := archimedeanKernel_lower (1 + x) hl hu
      simpa [div_eq_mul_inv, mul_comm] using hh)
  rw [intervalIntegral.integral_const_mul, reciprocal_cutoff_integral_eq_log hd hd1] at hcmp
  linarith

#check archimedean_cutoff_integral_lower
#print axioms archimedean_cutoff_integral_lower

#check archimedeanKernel_lower
#print axioms archimedeanKernel_lower
#check cutoff_lower_bound_forces_unbounded
#print axioms cutoff_lower_bound_forces_unbounded

#check archimedeanKernel_split
#print axioms archimedeanKernel_split
#check log_cutoff_unbounded
#print axioms log_cutoff_unbounded
#check archimedeanKernel_difference
#print axioms archimedeanKernel_difference

#check normTwistShift_re
#print axioms normTwistShift_re
#check normTwist_criticalLine_iff
#print axioms normTwist_criticalLine_iff
#check jetFactor_ne_zero
#print axioms jetFactor_ne_zero

end MasulloGRH
