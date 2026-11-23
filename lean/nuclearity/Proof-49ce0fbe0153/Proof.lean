import Mathlib

/-!
Round 89 / A: concrete envelope for the coefficient norms on the genuine
weighted idele-class space after the checked logarithmic Haar reduction.
This is a direct analytic component, NOT a global nuclear-bound theorem.
-/

namespace GlobalNuclearBound

/-- Exact log-coordinate squared modulus of the unshifted spectral coefficient,
including the reciprocal strip weight. The compact character has modulus one. -/
noncomputable def coefficientDensity (alpha b s : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (2 * b * u - 2 * alpha * |u|) * u ^ (2 * m) /
    (1 + u ^ 2) ^ (s / 2)

/-- Interior strip decay retains the distance to the boundary explicitly. -/
theorem interior_exponent_bound (alpha b delta u : ℝ)
    (hgap : |b| + delta ≤ alpha) :
    2 * b * u - 2 * alpha * |u| ≤ -(2 * delta) * |u| := by
  have hb : b * u ≤ |b| * |u| := by
    calc
      b * u ≤ |b * u| := le_abs_self _
      _ = |b| * |u| := abs_mul _ _
  have hd := mul_le_mul_of_nonneg_right hgap (abs_nonneg u)
  nlinarith

#check interior_exponent_bound
#print axioms interior_exponent_bound

/-- The coefficient-density upper bound is uniform in character and ordinate,
but explicitly loses uniformity as delta tends to zero or jet order grows. -/
theorem coefficientDensity_le (alpha b delta s : ℝ) (m : ℕ) (u : ℝ)
    (hgap : |b| + delta ≤ alpha) (hs : 0 ≤ s) :
    coefficientDensity alpha b s m u ≤
      Real.exp (-(2 * delta) * |u|) * u ^ (2 * m) := by
  have hp : 0 ≤ u ^ (2 * m) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg u) m
  have hw : 1 ≤ (1 + u ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg u]) (by positivity)
  unfold coefficientDensity
  calc
    _ ≤ Real.exp (2 * b * u - 2 * alpha * |u|) * u ^ (2 * m) :=
      div_le_self (mul_nonneg (Real.exp_pos _).le hp) hw
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (interior_exponent_bound alpha b delta u hgap)) hp

#check coefficientDensity_le
#print axioms coefficientDensity_le


open MeasureTheory Set

/-- The explicit majorant is integrable for every finite jet order. -/
theorem halfLineMoment_integrable (delta : ℝ) (m : ℕ) (hd : 0 < delta) :
    IntegrableOn (fun u : ℝ => u ^ (2 * m) * Real.exp (-(2 * delta) * u))
      (Ioi 0) := by
  simpa only [Real.rpow_natCast, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := ((2 * m : ℕ) : ℝ)) (p := 1) (b := 2 * delta)
      (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
      (by norm_num) (by positivity))

/-- Exact half-line moment, exposing factorial growth in the jet order. -/
theorem halfLineMoment_integral (delta : ℝ) (m : ℕ) (hd : 0 < delta) :
    (∫ u : ℝ in Ioi 0, u ^ (2 * m) * Real.exp (-(2 * delta) * u)) =
      (1 / (2 * delta)) ^ (2 * m + 1) * ((2 * m).factorial : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((2 * m : ℕ) : ℝ) + 1) (r := 2 * delta)
    (by positivity) (by positivity)
  have he : ((2 * m : ℕ) : ℝ) + 1 = ((2 * m + 1 : ℕ) : ℝ) := by
    push_cast
    rfl
  simp only [add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial] at h
  rw [he, Real.rpow_natCast] at h
  simpa only [neg_mul] using h

#check halfLineMoment_integrable
#print axioms halfLineMoment_integrable
#check halfLineMoment_integral
#print axioms halfLineMoment_integral


/-- The two logarithmic half-lines retain the same explicit majorant. -/
theorem coefficientDensity_pair_le (alpha b delta s : ℝ) (m : ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hgap : |b| + delta ≤ alpha) (hs : 0 ≤ s) :
    coefficientDensity alpha b s m u + coefficientDensity alpha b s m (-u) ≤
      2 * (u ^ (2 * m) * Real.exp (-(2 * delta) * u)) := by
  have h₁ := coefficientDensity_le alpha b delta s m u hgap hs
  have h₂ := coefficientDensity_le alpha b delta s m (-u) hgap hs
  have hp : (-u) ^ (2 * m) = u ^ (2 * m) := by
    rw [pow_mul, pow_mul]
    simp
  rw [abs_neg, abs_of_nonneg hu, hp] at h₂
  rw [abs_of_nonneg hu] at h₁
  nlinarith

#check coefficientDensity_pair_le
#print axioms coefficientDensity_pair_le


theorem coefficientDensity_nonneg (alpha b s : ℝ) (m : ℕ) (u : ℝ) :
    0 ≤ coefficientDensity alpha b s m u := by
  have hp : 0 ≤ u ^ (2 * m) := by
    rw [pow_mul]
    positivity
  unfold coefficientDensity
  positivity

theorem coefficientDensity_continuous (alpha b s : ℝ) (m : ℕ) (hs : 0 ≤ s) :
    Continuous (coefficientDensity alpha b s m) := by
  unfold coefficientDensity
  apply Continuous.div
  · fun_prop
  · fun_prop (disch := positivity)
  · intro u
    positivity

/-- An integrated, explicit bound for both logarithmic half-lines. -/
theorem coefficientDensity_pair_integrable (alpha b delta s : ℝ) (m : ℕ)
    (hd : 0 < delta) (hgap : |b| + delta ≤ alpha) (hs : 0 ≤ s) :
    IntegrableOn (fun u : ℝ => coefficientDensity alpha b s m u +
      coefficientDensity alpha b s m (-u)) (Ioi 0) := by
  apply ((halfLineMoment_integrable delta m hd).const_mul 2).mono'
  · exact ((coefficientDensity_continuous alpha b s m hs).add
      ((coefficientDensity_continuous alpha b s m hs).comp continuous_neg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg
      (coefficientDensity_nonneg alpha b s m u)
      (coefficientDensity_nonneg alpha b s m (-u)))]
    exact coefficientDensity_pair_le alpha b delta s m u hu.le hgap hs

theorem coefficientDensity_pair_integral_le (alpha b delta s : ℝ) (m : ℕ)
    (hd : 0 < delta) (hgap : |b| + delta ≤ alpha) (hs : 0 ≤ s) :
    (∫ u : ℝ in Ioi 0, coefficientDensity alpha b s m u +
      coefficientDensity alpha b s m (-u)) ≤
      2 * ((1 / (2 * delta)) ^ (2 * m + 1) * ((2 * m).factorial : ℝ)) := by
  calc
    _ ≤ ∫ u : ℝ in Ioi 0, 2 * (u ^ (2 * m) * Real.exp (-(2 * delta) * u)) := by
      apply integral_mono_ae (coefficientDensity_pair_integrable alpha b delta s m hd hgap hs)
        ((halfLineMoment_integrable delta m hd).const_mul 2)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact coefficientDensity_pair_le alpha b delta s m u hu.le hgap hs
    _ = _ := by rw [integral_const_mul, halfLineMoment_integral delta m hd]

#check coefficientDensity_pair_integrable
#print axioms coefficientDensity_pair_integrable
#check coefficientDensity_pair_integral_le
#print axioms coefficientDensity_pair_integral_le

end GlobalNuclearBound


