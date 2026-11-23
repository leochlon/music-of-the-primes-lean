import Mathlib

namespace ActualLocalCutoff

/-- Exact logarithmic volume with independent upper and lower spatial cutoffs.
Here L = log (lambda * lambda'), r = log (lambda' / lambda''),
and t = log |w|. -/
theorem independent_cutoff_volume (L r t : ℝ) (hrL : r ≤ L) :
    max 0 (L - max t r) =
      L - t + max 0 (t - L) - max 0 (r - t) := by
  by_cases ht : t ≤ r
  · rw [max_eq_right ht, max_eq_left (sub_nonpos.mpr (ht.trans hrL)),
      max_eq_right (sub_nonneg.mpr ht), max_eq_right (sub_nonneg.mpr hrL)]
    ring
  · have hrt : r ≤ t := le_of_lt (lt_of_not_ge ht)
    rw [max_eq_left hrt, max_eq_left (sub_nonpos.mpr hrt)]
    by_cases htL : t ≤ L
    · rw [max_eq_right (sub_nonneg.mpr htL), max_eq_left (sub_nonpos.mpr htL)]
      ring
    · have hLt : L ≤ t := le_of_lt (lt_of_not_ge htL)
      rw [max_eq_left (sub_nonpos.mpr hLt), max_eq_right (sub_nonneg.mpr hLt)]
      ring

/-- The lower-cutoff error is supported near the zero divisor and bounded by
|log |w|| once lambda'/lambda'' <= 1. -/
theorem lower_error_bound (r t : ℝ) (hr : r ≤ 0) :
    0 ≤ max 0 (r - t) ∧ max 0 (r - t) ≤ |t| := by
  constructor
  · exact le_max_left _ _
  · apply max_le (abs_nonneg t)
    linarith [neg_le_abs t]

/-- The upper-cutoff error has the same integrable logarithmic majorant. -/
theorem upper_error_bound (L t : ℝ) (hL : 0 ≤ L) :
    0 ≤ max 0 (t - L) ∧ max 0 (t - L) ≤ |t| := by
  constructor
  · exact le_max_left _ _
  · apply max_le (abs_nonneg t)
    linarith [le_abs_self t]

end ActualLocalCutoff
#print axioms ActualLocalCutoff.independent_cutoff_volume
#print axioms ActualLocalCutoff.lower_error_bound
#print axioms ActualLocalCutoff.upper_error_bound
