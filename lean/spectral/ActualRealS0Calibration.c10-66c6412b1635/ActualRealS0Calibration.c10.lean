import Mathlib
open MeasureTheory
noncomputable section
namespace ActualRealS0
/-- Actual real standard Gaussian and its dilation, with additive Lebesgue Haar. -/
def g (x : ℝ) : ℝ := Real.exp (-Real.pi * x^2)
def h (x : ℝ) : ℝ := Real.exp (-(4*Real.pi) * x^2)
theorem gaussian_integrals : (∫ x, g x) = 1 ∧ (∫ x, h x) = 1/2 := by
  constructor
  · simpa [g, Real.pi_ne_zero] using integral_gaussian Real.pi
  · change (∫ x : ℝ, Real.exp (-(4*Real.pi) * x^2)) = 1/2
    rw [integral_gaussian]
    have hp : Real.pi / (4 * Real.pi) = (1/2 : ℝ)^2 := by field_simp; ring
    rw [hp, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
/-- Discharges the nonzero Fourier-at-zero calibration determinant for the
actual Gaussian pair, not for arbitrary evaluation functionals. -/
theorem actual_gaussian_calibration :
    g 0 = 1 ∧ h 0 = 1 ∧ (∫ x, h x) - (∫ x, g x) = -(1/2 : ℝ) := by
  rcases gaussian_integrals with ⟨hg, hh⟩
  refine ⟨by simp [g], by simp [h], ?_⟩
  rw [hg, hh]
  norm_num
#print axioms actual_gaussian_calibration
end ActualRealS0
