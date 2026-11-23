import Mathlib

/-!
Round 1, participant A. Supporting local analytic work only.
The genuine all-number-field Hecke GRH target remains unproved.
No Hecke L-function is replaced by the elementary kernel below.
-/
namespace MasulloGRH

/-- The positive-side real-place kernel for the trivial character at z = 3/2,
up to the harmless positive Haar normalization. -/
noncomputable def realPlaceKernel (t : ℝ) : ℝ := 1 / (t ^ 2 * (t - 1))

/-- A logarithmically nonintegrable lower bound near t = 1. -/
theorem realPlaceKernel_lower (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ realPlaceKernel t := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < t ^ 2 * (t - 1) := mul_pos (sq_pos_of_pos ht0) (by linarith)
  have hb : t ^ 2 * (t - 1) ≤ 4 * (t - 1) := by
    apply mul_le_mul_of_nonneg_right
    · nlinarith
    · linarith
  exact one_div_le_one_div_of_le hp hb

/-- Subtracting a reference exponent cancels the t=1 singularity in this
concrete pair of kernels. This is not the full complex-parameter repair. -/
theorem realPlaceKernel_sub_reference (t : ℝ) (ht : 1 < t) :
    realPlaceKernel t - 1 / (t * (t - 1)) = -1 / t ^ 2 := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  unfold realPlaceKernel
  field_simp
  ring

/-- Exact logarithmic divergence of the comparison kernel. -/
theorem inverse_shift_integral (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in (1 + ε)..2, 1 / (t - 1)) = -Real.log ε := by
  have hn : (0 : ℝ) ∉ Set.uIcc ε 1 := by
    rw [Set.uIcc_of_le hε1]
    intro h
    exact (not_le_of_gt hε) h.1
  have heq : 1 + ε - 1 = ε := by ring
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) 1, heq]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  rw [integral_one_div hn, one_div, Real.log_inv]

/-- The actual local kernel has a divergent cutoff lower bound. -/
theorem realPlaceKernel_integral_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    -Real.log ε / 4 ≤ ∫ t in (1 + ε)..2, realPlaceKernel t := by
  have hab : 1 + ε ≤ 2 := by linarith
  have hpos : ∀ t ∈ Set.uIcc (1 + ε) 2, 1 < t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.uIcc (1 + ε) 2) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    change t - 1 ≠ 0
    linarith [hpos t ht]
  have hk : ContinuousOn realPlaceKernel (Set.uIcc (1 + ε) 2) := by
    unfold realPlaceKernel
    apply continuousOn_const.div ((continuousOn_id.pow 2).mul
      (continuousOn_id.sub continuousOn_const))
    intro t ht
    have h := hpos t ht
    change t ^ 2 * (t - 1) ≠ 0
    exact mul_ne_zero (pow_ne_zero 2 (by linarith)) (by linarith)
  have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hc.div_const 4).intervalIntegrable hk.intervalIntegrable
    (fun t ht => by
      have hp : 1 < t := by linarith [ht.1]
      have hl := realPlaceKernel_lower t hp ht.2
      simpa only [div_div, mul_comm] using hl)
  rw [intervalIntegral.integral_div, inverse_shift_integral ε hε hε1] at hm
  exact hm

/-- No finite common bound exists for these positive cutoff integrals. -/
theorem realPlaceKernel_integrals_unbounded (M : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      M < ∫ t in (1 + ε)..2, realPlaceKernel t := by
  let a : ℝ := 4 * (|M| + 1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : 0 < Real.exp (-a) := Real.exp_pos _
  have he1 : Real.exp (-a) ≤ 1 := by
    calc
      Real.exp (-a) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  refine ⟨Real.exp (-a), he, he1, ?_⟩
  have hb := realPlaceKernel_integral_lower (Real.exp (-a)) he he1
  rw [Real.log_exp] at hb
  have hm : M ≤ |M| := le_abs_self M
  dsimp [a] at hb
  linarith

/-- Algebraic resolvent subtraction: the numerator is independent of the zero w.
With a zero-counting estimate this supplies quadratic, instead of linear,
decay in the imaginary part of w. No spectral convergence is assumed here. -/
theorem resolvent_subtraction (z z₀ w : ℂ) (hz : z ≠ w) (hz₀ : z₀ ≠ w) :
    1 / (z - w) - 1 / (z₀ - w) =
      (z₀ - z) / ((z - w) * (z₀ - w)) := by
  have h₁ : z - w ≠ 0 := sub_ne_zero.mpr hz
  have h₂ : z₀ - w ≠ 0 := sub_ne_zero.mpr hz₀
  field_simp
  ring

/-- A quantitative bound for the subtracted resolvent, useful for normal
convergence after a genuine zero-counting theorem has been supplied. -/
theorem resolvent_subtraction_bound (z z₀ w : ℂ) (R : ℝ) (hR : 0 < R)
    (h₁ : R ≤ ‖z - w‖) (h₂ : R ≤ ‖z₀ - w‖) :
    ‖1 / (z - w) - 1 / (z₀ - w)‖ ≤ ‖z₀ - z‖ / (R * R) := by
  have hn₁ : z - w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR h₁)
  have hn₂ : z₀ - w ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR h₂)
  rw [resolvent_subtraction z z₀ w (sub_ne_zero.mp hn₁) (sub_ne_zero.mp hn₂),
    norm_div, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hR hR)
    (mul_le_mul h₁ h₂ (le_of_lt hR) (norm_nonneg _))

/-- Reference subtraction addresses vanishing at t=1, but does not by itself
satisfy the different central Mellin-moment restriction of PDF p.522. -/
theorem subtracted_resolvent_central_ne_zero (z z₀ : ℂ) (hne : z ≠ z₀) :
    1 / z - 1 / z₀ ≠ 0 := by
  intro h
  apply hne
  have hi := congrArg (fun x : ℂ => x⁻¹) (sub_eq_zero.mp h)
  simpa only [one_div, inv_inv] using hi

end MasulloGRH

#check MasulloGRH.realPlaceKernel_lower
#print axioms MasulloGRH.realPlaceKernel_lower

#check MasulloGRH.realPlaceKernel_sub_reference
#print axioms MasulloGRH.realPlaceKernel_sub_reference

#check MasulloGRH.inverse_shift_integral
#print axioms MasulloGRH.inverse_shift_integral
#check MasulloGRH.realPlaceKernel_integral_lower
#print axioms MasulloGRH.realPlaceKernel_integral_lower

#check MasulloGRH.realPlaceKernel_integrals_unbounded
#print axioms MasulloGRH.realPlaceKernel_integrals_unbounded

#check MasulloGRH.resolvent_subtraction
#print axioms MasulloGRH.resolvent_subtraction

#check MasulloGRH.resolvent_subtraction_bound
#print axioms MasulloGRH.resolvent_subtraction_bound

#check MasulloGRH.subtracted_resolvent_central_ne_zero
#print axioms MasulloGRH.subtracted_resolvent_central_ne_zero
