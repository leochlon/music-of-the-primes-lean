import Mathlib

/-!
Round 89 E. Direct quantitative estimate for the manuscript's actual dual
coefficient squared-norm density at b=0, after logarithmic Haar coordinates.
This is not a nuclear-bound theorem. In particular no lift bound is assumed.
-/
namespace Round89E
open MeasureTheory
noncomputable section

/-- For a unitary character, the squared dual coefficient norm is the Haar
volume of C_F^1 times the integral of this density. The height t drops out. -/
def jetDensity (alpha s : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (u ^ 2) ^ m * Real.exp (-2 * alpha * |u|) / (1 + u ^ 2) ^ (s / 2)

/-- Explicit dependence on jet order; no compactness in m is assumed. -/
theorem actual_jet_density_slab_lower (alpha s : ℝ) (m : ℕ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (u : ℝ) (hu : u ∈ Set.Icc (2:ℝ) 3) :
    (4:ℝ) ^ m * Real.exp (-6 * alpha) / 10 ^ (s / 2) ≤
      jetDensity alpha s m u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hp : (4:ℝ) ^ m ≤ (u ^ 2) ^ m := by
    gcongr
    nlinarith [hu.1]
  have he : Real.exp (-6 * alpha) ≤ Real.exp (-2 * alpha * |u|) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hu0]
    nlinarith [hu.2]
  have hw : (1 + u ^ 2) ^ (s / 2) ≤ (10:ℝ) ^ (s / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    nlinarith [hu.1, hu.2]
  unfold jetDensity
  calc
    _ ≤ (4:ℝ)^m * Real.exp (-6 * alpha) / (1 + u^2)^(s/2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hw
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hp he (by positivity) (by positivity)) (by positivity)

#check actual_jet_density_slab_lower
#print axioms actual_jet_density_slab_lower

end
end Round89E
