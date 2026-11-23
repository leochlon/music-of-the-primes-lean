import Mathlib
open MeasureTheory Set
open scoped SchwartzMap ContDiff
noncomputable section
namespace FollowupE12
/- Adapted from the mean-value argument in alpo BoundMulTranslate.lean:36-59.
Actual target: the arbitrary-test origin subtraction for (3.4.3.13-15). -/

/-- Uniform quadratic Taylor remainder for every complex Schwartz test. -/
theorem complex_schwartz_taylor_bound (f : 𝓢(ℂ, ℂ)) (a z : ℂ) :
    ‖f (a + z) - f a - fderiv ℝ (⇑f) a z‖ ≤
      SchwartzMap.seminorm ℂ 0 2 f * ‖z‖ * ‖z‖ := by
  have hF : ContDiff ℝ ∞ (⇑f) := f.smooth ⊤
  have hD : ContDiff ℝ ∞ (fderiv ℝ (⇑f)) := hF.fderiv_right (by norm_cast)
  have h2 : ∀ b, ‖fderiv ℝ (fderiv ℝ (⇑f)) b‖ ≤ SchwartzMap.seminorm ℂ 0 2 f := by
    intro b
    have h := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f 2 b
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at h
    exact h
  have h1 : ∀ b ∈ segment ℝ a (a + z),
      ‖fderiv ℝ (⇑f) b - fderiv ℝ (⇑f) a‖ ≤
        SchwartzMap.seminorm ℂ 0 2 f * ‖z‖ := by
    intro b hb
    have h := (convex_segment a (a + z)).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hD.differentiable (by simp) x) (fun x _ => h2 x)
      (left_mem_segment _ _ _) hb
    have hd : ‖b - a‖ ≤ ‖z‖ := by simpa using norm_sub_le_of_mem_segment hb
    exact h.trans (mul_le_mul_of_nonneg_left hd (apply_nonneg _ _))
  have h := (convex_segment a (a + z)).norm_image_sub_le_of_norm_fderiv_le' (𝕜 := ℝ)
    (fun x _ => hF.differentiable (by simp) x) h1
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  simpa only [add_sub_cancel_left] using h

/-- Origin subtraction uses an explicit seminorm, without a Gaussian restriction. -/
theorem complex_schwartz_origin_remainder (f : 𝓢(ℂ, ℂ)) (z : ℂ) :
    ‖f z - f 0 - fderiv ℝ (⇑f) 0 z‖ ≤
      SchwartzMap.seminorm ℂ 0 2 f * ‖z‖ ^ 2 := by
  simpa only [zero_add, pow_two, ← mul_assoc] using complex_schwartz_taylor_bound f 0 z

#print axioms complex_schwartz_taylor_bound
#print axioms complex_schwartz_origin_remainder
end FollowupE12

/- BEGIN exact reuse of followup_D ComplexAngular.lean, import Mathlib already present. -/

open MeasureTheory Complex Set
open scoped SchwartzMap

noncomputable section
namespace FollowupD639

/-- Unit circle with its probability-parameter normalization. -/
def circle (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)

def mode (m : ℤ) (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * (m : ℝ) * t : ℝ) * Complex.I)

@[simp] theorem norm_circle (t : ℝ) : ‖circle t‖ = 1 := by
  simp [circle, Complex.norm_exp, Complex.mul_re]

@[simp] theorem norm_mode (m : ℤ) (t : ℝ) : ‖mode m t‖ = 1 := by
  simp [mode, Complex.norm_exp, Complex.mul_re]

/-- Every angular mode of an arbitrary complex Schwartz test, not a Gaussian. -/
def angularAverage (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) : ℂ :=
  ∫ t in (0 : ℝ)..1, f ((r : ℂ) * circle t) * mode m t

theorem angular_integrable (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) :
    IntervalIntegrable (fun t => f ((r : ℂ) * circle t) * mode m t) volume 0 1 := by
  apply Continuous.intervalIntegrable
  exact (f.continuous.comp (by unfold circle; fun_prop)).mul (by unfold mode; fun_prop)

/-- Radius and angular-mode independent control by the actual Schwartz seminorm. -/
theorem angular_norm_le (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) :
    ‖angularAverage m r f‖ ≤ SchwartzMap.seminorm ℂ 0 0 f := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := SchwartzMap.seminorm ℂ 0 0 f)
    (f := fun t => f ((r : ℂ) * circle t) * mode m t) (by
      intro t ht
      simpa only [norm_mul, norm_mode, mul_one] using f.norm_le_seminorm ℂ ((r : ℂ) * circle t))
  simpa [angularAverage] using h

/-- Arbitrarily fast radial decay with one finite family of Schwartz seminorms,
uniform in every integer angular mode. -/
theorem angular_rapid_bound (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) (k : ℕ) :
    ‖angularAverage m r f‖ ≤
      (2 ^ k * (Finset.Iic (k, 0)).sup (fun n => SchwartzMap.seminorm ℂ n.1 n.2) f) /
        (1 + |r|) ^ k := by
  have hp : 0 < (1 + |r|) ^ k := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (C := (2 ^ k * (Finset.Iic (k, 0)).sup
      (fun n => SchwartzMap.seminorm ℂ n.1 n.2) f) / (1 + |r|) ^ k)
    (f := fun t => f ((r : ℂ) * circle t) * mode m t) (by
      intro t ht
      rw [norm_mul, norm_mode, mul_one, le_div_iff₀ hp]
      have hb := SchwartzMap.one_add_le_sup_seminorm_apply
        (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f ((r : ℂ) * circle t)
      simpa [norm_iteratedFDeriv_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_comm] using hb)
  simpa [angularAverage] using h


/-- Angular averaging first on bounded continuous functions. -/
def angularBCF (m : ℤ) (r : ℝ) : BoundedContinuousFunction ℂ ℂ →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ t in (0 : ℝ)..1, f ((r : ℂ) * circle t) * mode m t
      map_add' := by
        intro f g
        change (∫ t in (0 : ℝ)..1, (f ((r : ℂ) * circle t) +
          g ((r : ℂ) * circle t)) * mode m t) = _
        simp only [add_mul]
        apply intervalIntegral.integral_add
        · exact ((f.continuous.comp (by unfold circle; fun_prop)).mul
            (by unfold mode; fun_prop)).intervalIntegrable 0 1
        · exact ((g.continuous.comp (by unfold circle; fun_prop)).mul
            (by unfold mode; fun_prop)).intervalIntegrable 0 1
      map_smul' := by
        intro c f
        change (∫ t in (0 : ℝ)..1, (c * f ((r : ℂ) * circle t)) * mode m t) =
          c * ∫ t in (0 : ℝ)..1, f ((r : ℂ) * circle t) * mode m t
        simp only [mul_assoc, intervalIntegral.integral_const_mul] }
    1 (by
      intro f
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := 1) (C := ‖f‖)
        (f := fun t => f ((r : ℂ) * circle t) * mode m t) (by
          intro t ht
          simpa only [norm_mul, norm_mode, mul_one] using
            BoundedContinuousFunction.norm_coe_le_norm f ((r : ℂ) * circle t))
      simpa using h)

/-- A continuous linear functional on the actual Schwartz topology,
with no test-space continuity hypothesis. -/
def angularCLM (m : ℤ) (r : ℝ) : 𝓢(ℂ, ℂ) →L[ℂ] ℂ :=
  (angularBCF m r).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℂ ℂ)

@[simp] theorem angularCLM_apply (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) :
    angularCLM m r f = angularAverage m r f := rfl

theorem angular_continuous (m : ℤ) (r : ℝ) : Continuous (angularAverage m r) :=
  (angularCLM m r).continuous

#print axioms angular_rapid_bound
#print axioms angular_norm_le
#print axioms angular_continuous
end FollowupD639

namespace FollowupE12
open FollowupD639

/-- Taylor-subtracted angular mode on the same probability circle parameter as
followup_D. The missing local Mellin construction integrates this against 4πr^(2s-1). -/
def angularOriginRemainder (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (f ((r : ℂ) * circle t) - f 0 - fderiv ℝ (⇑f) 0 ((r : ℂ) * circle t)) * mode m t

theorem angular_origin_remainder_integrable (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) :
    IntervalIntegrable (fun t =>
      (f ((r : ℂ) * circle t) - f 0 - fderiv ℝ (⇑f) 0 ((r : ℂ) * circle t)) * mode m t)
      volume 0 1 := by
  apply Continuous.intervalIntegrable
  have hc : Continuous (fun t : ℝ => (r : ℂ) * circle t) := by unfold circle; fun_prop
  exact (((f.continuous.comp hc).sub continuous_const).sub
    ((fderiv ℝ (⇑f) 0).continuous.comp hc)).mul (by unfold mode; fun_prop)

/-- Every integer angular mode, every radius and every complex Schwartz test:
the actual subtracted angular integral has one uniform derivative-seminorm bound. -/
theorem angular_origin_remainder_bound (m : ℤ) (r : ℝ) (f : 𝓢(ℂ, ℂ)) :
    ‖angularOriginRemainder m r f‖ ≤ SchwartzMap.seminorm ℂ 0 2 f * r ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := SchwartzMap.seminorm ℂ 0 2 f * r ^ 2)
    (f := fun t =>
      (f ((r : ℂ) * circle t) - f 0 - fderiv ℝ (⇑f) 0 ((r : ℂ) * circle t)) * mode m t)
    (by
      intro t _
      rw [norm_mul, norm_mode, mul_one]
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
        complex_schwartz_origin_remainder f ((r : ℂ) * circle t))
  simpa [angularOriginRemainder] using h

#print axioms angular_origin_remainder_integrable
#print axioms angular_origin_remainder_bound
end FollowupE12
