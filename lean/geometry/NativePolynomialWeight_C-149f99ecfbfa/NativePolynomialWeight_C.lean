import Mathlib

namespace NativePolynomialWeightC

/-- The actual polynomial weight admits a polynomial translation cost.
This is the real-variable inequality used before taking the power s/4. -/
theorem translation_polynomial (x t : ℝ) :
    1 + (x + t)^2 ≤ (1 + |t|)^2 * (1 + x^2) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    nlinarith [sq_nonneg (x * t), mul_nonneg ht (sq_nonneg (x - 1)),
      mul_nonneg ht (sq_nonneg x)]
  · have ht' : 0 ≤ -t := le_of_lt (neg_pos.mpr (lt_of_not_ge ht))
    rw [abs_of_neg (lt_of_not_ge ht)]
    nlinarith [sq_nonneg (x * t), mul_nonneg ht' (sq_nonneg (x + 1)),
      mul_nonneg ht' (sq_nonneg x)]

/-- The ratio occurs in the original dual weighted L2 translation norm. -/
theorem native_weight_ratio (x t : ℝ) :
    (1 + x^2) / (1 + (x - t)^2) ≤ (1 + |t|)^2 := by
  have hden : 0 < 1 + (x - t)^2 := by positivity
  apply (div_le_iff₀ hden).2
  have h := translation_polynomial (x - t) t
  convert h using 1
  ring

end NativePolynomialWeightC

#print axioms NativePolynomialWeightC.translation_polynomial
#print axioms NativePolynomialWeightC.native_weight_ratio
