import Mathlib

/-!
Round 88 F: direct control of the manuscript's actual weight in logarithmic
idele-norm coordinates, for I = [-alpha,alpha] and s = 2*d.
This is a pointwise analytic component, NOT a nuclear bound or a construction
of the actual global operator. No summability, lift bound, or nuclearity is assumed.
-/
namespace Round88F

noncomputable def logWeight (alpha : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (1 + u ^ 2) ^ d

 theorem logWeight_pos (alpha : ℝ) (d : ℕ) (u : ℝ) :
    0 < logWeight alpha d u := by
  unfold logWeight
  positivity

 theorem logWeight_neg (alpha : ℝ) (d : ℕ) (u : ℝ) :
    logWeight alpha d (-u) = logWeight alpha d u := by
  simp [logWeight]

 theorem polynomial_shear_bound (u v : ℝ) :
    1 + (u + v) ^ 2 ≤ 2 * (1 + u ^ 2) * (1 + v ^ 2) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (u * v)]

 theorem actual_logWeight_shear_bound (alpha : ℝ) (ha : 0 ≤ alpha)
    (d : ℕ) (u v : ℝ) :
    logWeight alpha d (u + v) ≤
      (2 : ℝ) ^ d * logWeight alpha d u * logWeight alpha d v := by
  have he : Real.exp (2 * alpha * |u + v|) ≤
      Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_add_le u v]
  have hp : (1 + (u + v) ^ 2) ^ d ≤
      (2 * (1 + u ^ 2) * (1 + v ^ 2)) ^ d := by
    gcongr
    exact polynomial_shear_bound u v
  unfold logWeight
  calc
    _ ≤ (Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|)) *
        (2 * (1 + u ^ 2) * (1 + v ^ 2)) ^ d :=
      mul_le_mul he hp (by positivity) (by positivity)
    _ = _ := by simp only [mul_pow]; ring

/-- This controls exactly the weight ratio appearing in (10.4.2.28).
The cost depends on the translating logarithmic norm, alpha and d, but contains
no spectral-frequency decay. -/
 theorem actual_logWeight_shear_ratio (alpha : ℝ) (ha : 0 ≤ alpha)
    (d : ℕ) (u x y : ℝ) :
    logWeight alpha d (u + x) / logWeight alpha d (u + y) ≤
      ((2 : ℝ) ^ d * logWeight alpha d u) ^ 2 *
        (logWeight alpha d x / logWeight alpha d y) := by
  have hx := actual_logWeight_shear_bound alpha ha d u x
  have hy := actual_logWeight_shear_bound alpha ha d (-u) (u + y)
  rw [logWeight_neg] at hy
  have hcancel : -u + (u + y) = y := by ring
  rw [hcancel] at hy
  have hpos := logWeight_pos alpha d (u + y)
  have hypos := logWeight_pos alpha d y
  apply (div_le_iff₀ hpos).2
  have hc : 0 ≤ (2 : ℝ) ^ d * logWeight alpha d u := by
    exact mul_nonneg (by positivity) (le_of_lt (logWeight_pos alpha d u))
  have hright : 0 ≤ (2 : ℝ) ^ d * logWeight alpha d u * logWeight alpha d x :=
    mul_nonneg hc (le_of_lt (logWeight_pos alpha d x))
  have hmul := mul_le_mul hx hy (le_of_lt hypos) hright
  have hcross : logWeight alpha d (u + x) * logWeight alpha d y ≤
      ((2 : ℝ) ^ d * logWeight alpha d u) ^ 2 *
        logWeight alpha d x * logWeight alpha d (u + y) := by
    convert hmul using 1
    ring
  calc
    _ ≤ (((2 : ℝ) ^ d * logWeight alpha d u) ^ 2 *
        logWeight alpha d x * logWeight alpha d (u + y)) /
          logWeight alpha d y := (le_div_iff₀ hypos).2 hcross
    _ = _ := by ring


/-- Direct squared weighted-norm control, specialized to the genuine idele class
by taking q(x)=log|x|_F and then using Haar invariance for translation.
Integrability hypotheses specify the domain of the displayed real integrals;
no nuclear or summability estimate is assumed. -/
theorem actual_weighted_translation_integral
    {X : Type*} [MeasurableSpace X] (mu : MeasureTheory.Measure X)
    (alpha : ℝ) (ha : 0 ≤ alpha) (d : ℕ) (u : ℝ)
    (q : X → ℝ) (f : X → ℂ)
    (hf : MeasureTheory.Integrable
      (fun x => ‖f x‖ ^ 2 * logWeight alpha d (q x)) mu)
    (hs : MeasureTheory.Integrable
      (fun x => ‖f x‖ ^ 2 * logWeight alpha d (u + q x)) mu) :
    (∫ x, ‖f x‖ ^ 2 * logWeight alpha d (u + q x) ∂mu) ≤
      ((2 : ℝ) ^ d * logWeight alpha d u) *
        (∫ x, ‖f x‖ ^ 2 * logWeight alpha d (q x) ∂mu) := by
  have h := MeasureTheory.integral_mono hs
    (hf.const_mul ((2 : ℝ) ^ d * logWeight alpha d u)) (fun x => by
      calc
        _ ≤ ‖f x‖ ^ 2 *
            ((2 : ℝ) ^ d * logWeight alpha d u * logWeight alpha d (q x)) :=
          mul_le_mul_of_nonneg_left
            (actual_logWeight_shear_bound alpha ha d u (q x)) (sq_nonneg _)
        _ = _ := by ring)
  simpa only [MeasureTheory.integral_const_mul] using h

/-- At the identity, the printed bound (9.3.1.6), specialized to s=2,
cannot bound the norm of the identity on a nonzero space. -/
 theorem printed_translation_bound_fails_at_identity (C alpha : ℝ) :
    ¬ (1 : ℝ) ≤ C * max (Real.rpow 1 alpha) (Real.rpow 1 (-alpha)) *
      |Real.log 1| := by
  simp

end Round88F

#check Round88F.actual_logWeight_shear_bound
#check Round88F.actual_logWeight_shear_ratio
#check Round88F.printed_translation_bound_fails_at_identity
#print axioms Round88F.actual_logWeight_shear_bound
#print axioms Round88F.actual_logWeight_shear_ratio
#print axioms Round88F.printed_translation_bound_fails_at_identity

#check Round88F.actual_weighted_translation_integral
#print axioms Round88F.actual_weighted_translation_integral

namespace Round88F
/-- Explicit jet growth on a fixed log-norm slab. This explains why a uniform
coefficient bound cannot be inferred merely from compactness in the strip. -/
theorem actual_jet_slab_lower_bound (alpha : ℝ) (ha : 0 ≤ alpha)
    (d m : ℕ) (u : ℝ) (hu : 2 ≤ u) (hu' : u ≤ 3) :
    (4 : ℝ) ^ m / (Real.exp (6 * alpha) * (10 : ℝ) ^ d) ≤
      u ^ (2 * m) / logWeight alpha d u := by
  have hn : (4 : ℝ) ^ m ≤ u ^ (2 * m) := by
    rw [pow_mul]
    gcongr
    nlinarith
  have hb : logWeight alpha d u ≤ Real.exp (6 * alpha) * (10 : ℝ) ^ d := by
    unfold logWeight
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg (by linarith : 0 ≤ u)]
      nlinarith
    · gcongr
      nlinarith
    · positivity
    · positivity
  exact div_le_div₀ (by positivity) hn (logWeight_pos alpha d u) hb
end Round88F
#check Round88F.actual_jet_slab_lower_bound
#print axioms Round88F.actual_jet_slab_lower_bound
