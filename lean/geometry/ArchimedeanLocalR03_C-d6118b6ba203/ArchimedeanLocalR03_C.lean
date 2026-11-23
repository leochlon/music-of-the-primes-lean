import Mathlib

/-! Exact real-place angular factors and the convergent radial series used
in GLOBAL_R03.md. These are scalar kernel identities, not a formalization
of the adelic projection, Lidskii, or the global trace equality. -/
noncomputable section
open scoped BigOperators

namespace GeometricTraceC.Archimedean

theorem real_even (r a : ℝ) (hm : 1 - r ≠ 0) (hp : 1 + r ≠ 0) :
    a / 2 * (1 / (1 - r) + 1 / (1 + r)) = a / (1 - r ^ 2) := by
  have hs : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [hs]
  field_simp
  ring

theorem real_odd (r a : ℝ) (hm : 1 - r ≠ 0) (hp : 1 + r ≠ 0) :
    a / 2 * (1 / (1 - r) - 1 / (1 + r)) = a * r / (1 - r ^ 2) := by
  have hs : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [hs]
  field_simp
  ring

/-- The real gamma reciprocal series has spacing two in logarithmic norm. -/
theorem real_radial_series (r a : ℝ) (hr : ‖r ^ 2‖ < 1) :
    HasSum (fun n : ℕ => a * (r ^ 2) ^ n) (a / (1 - r ^ 2)) := by
  simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hr).mul_left a

/-- The complex gamma reciprocal series has spacing one in logarithmic norm. -/
theorem complex_radial_series (r a : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => a * r ^ n) (a / (1 - r)) := by
  simpa [div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hr).mul_left a

/-- Self-dual complex additive measure is 2 dx dy, and u=2 log r.
The two Jacobian factors leave the probability angular measure. -/
theorem complex_measure_coefficient (r : ℝ) (hr : r ≠ 0) :
    (1 / (2 * Real.pi)) * (2 / r) * (r / 2) = 1 / (2 * Real.pi) := by
  field_simp

/-- The log-sharp test multiplies the n-th finite shell by n log q. -/
theorem logged_shell (n L a : ℝ) : L * ((n * L) * a) = n * L ^ 2 * a := by
  ring

end GeometricTraceC.Archimedean

#print axioms GeometricTraceC.Archimedean.real_even
#print axioms GeometricTraceC.Archimedean.real_odd
#print axioms GeometricTraceC.Archimedean.real_radial_series
#print axioms GeometricTraceC.Archimedean.complex_radial_series
#print axioms GeometricTraceC.Archimedean.complex_measure_coefficient
#print axioms GeometricTraceC.Archimedean.logged_shell
