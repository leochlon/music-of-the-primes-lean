import Mathlib

/- The logarithmic product-formula bound used to make the S-unit sum finite
AFTER the Fourier-log distribution is restricted to its coordinate axes.
See S_UNIT_LOCAL_R02.md for the actual S-adelic instantiation. -/
namespace SUnitAxis
open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- On the S-unit logarithmic hyperplane, all coordinates except v control v. -/
theorem missing_coordinate_bound (a B : S → ℝ) (v : S)
    (hprod : ∑ w, a w = 0)
    (hbound : ∀ w, w ≠ v → |a w| ≤ B w) :
    |a v| ≤ ∑ w ∈ Finset.univ.erase v, B w := by
  have he : (∑ w ∈ Finset.univ.erase v, a w) + a v = 0 := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_univ v)]
    exact hprod
  have ha : a v = -(∑ w ∈ Finset.univ.erase v, a w) := by linarith
  rw [ha, abs_neg]
  calc
    |∑ w ∈ Finset.univ.erase v, a w| ≤
        ∑ w ∈ Finset.univ.erase v, |a w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ Finset.univ.erase v, B w := by
      apply Finset.sum_le_sum
      intro w hw
      exact hbound w (Finset.mem_erase.mp hw).1

/-- The bound needed for the missing place is independent of the axis variable.
Here a(w)=log|xi_w| and B bounds the compact support of the lifted test. -/
theorem all_coordinates_bound (a B : S → ℝ) (v : S)
    (hprod : ∑ w, a w = 0)
    (hbound : ∀ w, w ≠ v → |a w| ≤ B w) :
    ∀ w, |a w| ≤ if w = v then ∑ j ∈ Finset.univ.erase v, B j else B w := by
  intro w
  by_cases hw : w = v
  · subst w
    simp only [ite_true]
    exact missing_coordinate_bound a B v hprod hbound
  · simp only [hw, ite_false]
    exact hbound w hw

/-- A norm-one unit translate cannot restore a norm-one-vanishing lift.
This removes each individual delta-at-zero term, before summing units. -/
theorem lifted_axis_vanishes {U : Type*} [CommGroup U]
    (normS : U →* ℝ) (f : U → ℂ)
    (hf : ∀ x, normS x = 1 → f x = 0)
    (xi g : U) (hxi : normS xi = 1) (hg : normS g = 1) :
    f (xi * g⁻¹) = 0 := by
  apply hf
  rw [map_mul, map_inv, hxi, hg, inv_one, one_mul]

end SUnitAxis
#print axioms SUnitAxis.missing_coordinate_bound
#print axioms SUnitAxis.all_coordinates_bound
#print axioms SUnitAxis.lifted_axis_vanishes
