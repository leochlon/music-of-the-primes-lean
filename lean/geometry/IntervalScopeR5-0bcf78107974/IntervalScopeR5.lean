import Mathlib

/- Arithmetic part of the Q radial-test calculation in ROUND5_DERIVATION.md.
This file does not claim to formalize ideles, the local distributions, or Hecke zeros. -/
namespace GeometricIntervalR5

theorem positive_numerator {t : ℝ} (ht : 1 < t) (hu : t < 6 / 5) :
    0 < 1 + t - t ^ 3 := by
  have ht0 : 0 ≤ t := by linarith
  have hsq : t ^ 2 < (6 / 5 : ℝ) ^ 2 := by nlinarith
  have hc : t ^ 3 < (6 / 5 : ℝ) ^ 3 := by
    nlinarith [mul_pos (sub_pos.mpr hu) (sq_pos_of_pos (by linarith : 0 < t)),
      mul_pos (by norm_num : (0 : ℝ) < 6 / 5) (sub_pos.mpr hsq)]
  nlinarith

/-- On this interval the real local term is strictly larger than the two pole terms. -/
theorem real_local_gt_poles {t : ℝ} (ht : 1 < t) (hu : t < 6 / 5) :
    (Real.sqrt t + (Real.sqrt t)⁻¹) / t < Real.sqrt t / (t ^ 2 - 1) := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t ^ 2 - 1 := by nlinarith
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have heq : (Real.sqrt t + (Real.sqrt t)⁻¹) * Real.sqrt t = t + 1 := by
    rw [add_mul, inv_mul_cancel₀ hr.ne']
    nlinarith
  apply (div_lt_div_iff₀ ht0 hd).2
  apply (mul_lt_mul_iff_of_pos_right hr).mp
  calc
    ((Real.sqrt t + (Real.sqrt t)⁻¹) * (t ^ 2 - 1)) * Real.sqrt t
        = ((Real.sqrt t + (Real.sqrt t)⁻¹) * Real.sqrt t) * (t ^ 2 - 1) := by ring
    _ = (t + 1) * (t ^ 2 - 1) := by rw [heq]
    _ < t ^ 2 := by nlinarith [positive_numerator ht hu]
    _ = (Real.sqrt t * t) * Real.sqrt t := by
      calc t ^ 2 = t * (Real.sqrt t ^ 2) := by rw [hs]; ring
           _ = (Real.sqrt t * t) * Real.sqrt t := by ring

theorem log_multiple_positive {t : ℝ} (ht : 1 < t) : 0 < Real.log t :=
  Real.log_pos ht

end GeometricIntervalR5
#print axioms GeometricIntervalR5.real_local_gt_poles
