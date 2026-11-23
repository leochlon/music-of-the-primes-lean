import Mathlib

namespace OperatorEnergyR01

/-- Exact exponential-weight cocycle on the positive log-norm ray. -/
theorem ray_weight_ratio (β u t : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    Real.exp (2 * β * |u + t|) / Real.exp (2 * β * |u|) =
      Real.exp (2 * β * t) := by
  rw [abs_of_nonneg (add_nonneg hu ht), abs_of_nonneg hu, ← Real.exp_sub]
  congr 1
  ring

/-- This is the elementary polynomial part of the manuscript's actual weight. -/
theorem polynomial_weight_ratio (u t : ℝ) :
    1 + (u+t)^2 ≤ 2 * (1+u^2) * (1+t^2) := by
  nlinarith [sq_nonneg (u-t), sq_nonneg (u*t)]

/-- After y=exp(-t), the ambient translation envelope has this exponent. -/
theorem energy_exponent (σ β t : ℝ) :
    (Real.exp ((β - 1/2) * t))^2 * Real.exp (-(σ - 2) * t) =
      Real.exp (-(σ - 1 - 2*β) * t) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

/-- An epsilon neighborhood needed by Fermat lies outside that sufficient
    ambient-energy convergence range whenever beta is positive. -/
theorem ambient_gap (β σ : ℝ) (hβ : 0 < β) (hσ : σ < 1+β) :
    σ - 1 - 2*β < 0 := by linarith

/-- Narrowing enough to put a possible exterior zero outside the strip
    leaves its strictly positive distance from the strip. -/
theorem exterior_gap (α q : ℝ) (hα : α < q-1/2) :
    0 < q - 1/2 - α := by linarith

/-- The actual intertwiner kills its kernel, so it supplies no positive
    lower norm bound on a nonzero omitted mode. -/
theorem kernel_precludes_lower_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →L[ℂ] F) (v : E) (hv : v ≠ 0) (hJ : J v = 0)
    (c : ℝ) (hc : 0 < c) : ¬ c * ‖v‖ ≤ ‖J v‖ := by
  rw [hJ, norm_zero]
  exact not_le.mpr (mul_pos hc (norm_pos_iff.mpr hv))

end OperatorEnergyR01
#print axioms OperatorEnergyR01.ray_weight_ratio
#print axioms OperatorEnergyR01.polynomial_weight_ratio
#print axioms OperatorEnergyR01.energy_exponent
#print axioms OperatorEnergyR01.ambient_gap
#print axioms OperatorEnergyR01.exterior_gap
#print axioms OperatorEnergyR01.kernel_precludes_lower_bound
