import Mathlib

/-! Round 184 E. Arithmetic comparison used in GLOBAL_ESTIMATE.md.
This discharges the conversion from the real completed-Hecke logarithmic
 derivative at 2 to the weighted zero count in the native resolvent bound.
It is not a nuclearity theorem; no summability or nuclearity is assumed. -/
namespace Round184E

theorem poisson_weight_domination (b t : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    1 / (1 + t ^ 2) ≤ 2 * ((2 - b) / ((2 - b) ^ 2 + t ^ 2)) := by
  have hd : 0 < 1 + t ^ 2 := by positivity
  have he : 0 < (2 - b) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have h1 : 0 ≤ (2 - b) * b := mul_nonneg (by linarith) hb0
  have h2 : 0 ≤ (3 - 2 * b) * t ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg t)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd he).2
  nlinarith

/-- The local true-multiplicity count uses the same positive kernel. -/
theorem local_zero_kernel_lower (b u : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hu : u ^ 2 ≤ 1) :
    (1 : ℝ) / 5 ≤ (2 - b) / ((2 - b) ^ 2 + u ^ 2) := by
  have he : 0 < (2 - b) ^ 2 + u ^ 2 := by nlinarith [sq_nonneg u]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) he).2
  nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]

#check poisson_weight_domination
#print axioms poisson_weight_domination
#check local_zero_kernel_lower
#print axioms local_zero_kernel_lower
end Round184E
