import Mathlib

/-!
Participant G, round 1, proof phase. Supporting results only.
The genuine all-number-field Hecke GRH construction and proof remain open here.
No declaration below is asserted to prove that target.
-/

namespace MasulloGRH

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
end MasulloGRH
