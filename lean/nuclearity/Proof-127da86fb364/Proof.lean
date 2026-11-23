import Mathlib

/-! Round 194 H: actual native weight transport. This is an input to the
native translation-group realization feeding C191's integrated seed-domain
lemma. It is not a theorem of global nuclearity. -/
noncomputable section
open MeasureTheory
namespace Round194H

def nativeWeight (u v s x : ℝ) : ℝ :=
  max (Real.exp (2*u*x)) (Real.exp (2*v*x)) * (1+x^2)^(s/2)

def translationCost (u v s t : ℝ) : ℝ :=
  Real.exp (2 * max |u| |v| * |t|) * ((1+|t|)^2)^(s/2)

theorem polynomial_native_shift (x t : ℝ) :
    1+(x+t)^2 ≤ (1+|t|)^2*(1+x^2) := by
  have hxt : x*t ≤ |x| *|t| := by simpa [abs_mul] using le_abs_self (x*t)
  have hx : 2*|x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
  have ht := abs_nonneg t
  have hp := mul_le_mul_of_nonneg_right hx ht
  nlinarith [sq_abs t, sq_nonneg (x*t)]

theorem native_weight_translation (u v s x t : ℝ) (hs : 0 ≤ s) :
    nativeWeight u v s (x+t) ≤ translationCost u v s t * nativeWeight u v s x := by
  let r := max |u| |v|
  have hu : u*t ≤ r*|t| := by
    calc
      u*t ≤ |u*t| := le_abs_self _
      _ = |u| *|t| := abs_mul _ _
      _ ≤ r*|t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have hv : v*t ≤ r*|t| := by
    calc
      v*t ≤ |v*t| := le_abs_self _
      _ = |v| *|t| := abs_mul _ _
      _ ≤ r*|t| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  have he (b : ℝ) (hb : b*t ≤ r*|t|) :
      Real.exp (2*b*(x+t)) ≤ Real.exp (2*r*|t|)*Real.exp (2*b*x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hem : max (Real.exp (2*u*(x+t))) (Real.exp (2*v*(x+t))) ≤
      Real.exp (2*r*|t|) * max (Real.exp (2*u*x)) (Real.exp (2*v*x)) := by
    apply max_le
    · exact (he u hu).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le)
    · exact (he v hv).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le)
  have hp : (1+(x+t)^2)^(s/2) ≤ ((1+|t|)^2)^(s/2)*(1+x^2)^(s/2) := by
    calc
      _ ≤ ((1+|t|)^2*(1+x^2))^(s/2) :=
        Real.rpow_le_rpow (by positivity) (polynomial_native_shift x t) (by positivity)
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have h := mul_le_mul hem hp (by positivity : 0 ≤ (1+(x+t)^2)^(s/2))
    (by positivity : 0 ≤ Real.exp (2*r*|t|)*max (Real.exp (2*u*x)) (Real.exp (2*v*x)))
  dsimp [nativeWeight, translationCost]
  dsimp [r] at h
  nlinarith only [h]

theorem native_weight_pos (u v s x : ℝ) : 0 < nativeWeight u v s x := by
  unfold nativeWeight
  exact mul_pos (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _)

theorem native_dual_weight_translation (u v s x t : ℝ) (hs : 0 ≤ s) :
    1 / nativeWeight u v s (x-t) ≤ translationCost u v s t / nativeWeight u v s x := by
  rw [div_le_div_iff₀ (native_weight_pos u v s (x-t)) (native_weight_pos u v s x)]
  simpa only [sub_add_cancel, one_mul] using native_weight_translation u v s (x-t) t hs

/-- The actual weighted quadratic norm under translation, with the original
Lebesgue log-Haar measure. Applied on each compact character fiber, whose
compact Haar mass is one, this extends U(t) to the native dual completion. -/
theorem native_dual_translation_integral
    (u v s t : ℝ) (hs : 0 ≤ s) (f : ℝ → ℂ) (hc : Continuous f)
    (hf : Integrable (fun x : ℝ => ‖f x‖^2 / nativeWeight u v s x)) :
    Integrable (fun x : ℝ => ‖f (x+t)‖^2 / nativeWeight u v s x) ∧
    (∫ x : ℝ, ‖f (x+t)‖^2 / nativeWeight u v s x) ≤
      translationCost u v s t * (∫ x : ℝ, ‖f x‖^2 / nativeWeight u v s x) := by
  let g : ℝ → ℝ := fun x => ‖f x‖^2 / nativeWeight u v s (x-t)
  have hfm : Measurable f := hc.measurable
  have hgm : AEStronglyMeasurable g := by
    apply Measurable.aestronglyMeasurable
    dsimp [g, nativeWeight]
    fun_prop
  have hb (x : ℝ) : g x ≤ translationCost u v s t * (‖f x‖^2 / nativeWeight u v s x) := by
    have h := mul_le_mul_of_nonneg_left (native_dual_weight_translation u v s x t hs)
      (sq_nonneg ‖f x‖)
    dsimp [g]
    convert h using 1 <;> ring
  have hg : Integrable g := by
    apply (hf.const_mul (translationCost u v s t)).mono' hgm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; exact div_nonneg (sq_nonneg _) (native_weight_pos u v s (x-t)).le)]
    exact hb x
  constructor
  · simpa only [g, add_sub_cancel_right] using hg.comp_add_right t
  · have he : (∫ x : ℝ, ‖f (x+t)‖^2 / nativeWeight u v s x) = ∫ x : ℝ, g x := by
      simpa only [g, add_sub_cancel_right] using integral_add_right_eq_self g t
    rw [he]
    calc
      _ ≤ ∫ x : ℝ, translationCost u v s t * (‖f x‖^2 / nativeWeight u v s x) :=
        integral_mono hg (hf.const_mul _) hb
      _ = _ := integral_const_mul _ _

#check native_weight_translation
#print axioms native_weight_translation
#check native_dual_weight_translation
#print axioms native_dual_weight_translation
#check native_dual_translation_integral
#print axioms native_dual_translation_integral
end Round194H
