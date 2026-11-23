import Mathlib

/- Round 91 C: actual global nuclear bound remains incomplete.
The authentic operator is A(phi) composed with P_a^spec on W_I^s(C_F).
No nuclearity, lift estimate, or cutoff convergence is asserted here. -/

namespace Round91C

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem geometric_lift_obstruction (A : H →L[ℂ] H)
    (eta : H →L[ℂ] ℂ) (u v : H) :
    2 * ‖A v‖ * ‖eta‖ ≤
      ‖A (u + v)‖ * ‖eta‖ + ‖A (u - v)‖ * ‖eta‖ := by
  have heq : A (u + v) - A (u - v) = (2 : ℂ) • A v := by
    simp only [map_add, map_sub, two_smul]
    abel
  have h := norm_sub_le (A (u + v)) (A (u - v))
  rw [heq, norm_smul] at h
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo] at h
  nlinarith [norm_nonneg eta]

#check geometric_lift_obstruction
#print axioms geometric_lift_obstruction


open scoped BigOperators
open Filter

/-- The actual form of each proposed finite lifted-convolution sum. -/
noncomputable def liftedSum (A : H →L[ℂ] H) (u : ℕ → H)
    (eta : ℕ → H →L[ℂ] ℂ) (J : Finset ℕ) : H →L[ℂ] H :=
  ∑ j ∈ J, (eta j).smulRight (A (u j))

/-- A fixed lifted term leaves a persistent error against A P. -/
theorem liftedSum_error_on_basis (A P : H →L[ℂ] H)
    (u : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ) (i : ℕ) (J : Finset ℕ)
    (hi : i ∈ J) (hbio : ∀ j, eta j (u i) = if j = i then 1 else 0) :
    (liftedSum A u eta J - A.comp P) (u i) = A (u i - P (u i)) := by
  classical
  simp [liftedSum, hbio, hi, map_sub]

/-- Every such error controls the missing convolved geometric component. -/
theorem liftedSum_error_lower_bound (A P : H →L[ℂ] H)
    (u : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ) (i : ℕ) (J : Finset ℕ)
    (hi : i ∈ J) (hbio : ∀ j, eta j (u i) = if j = i then 1 else 0) :
    ‖A (u i - P (u i))‖ ≤ ‖liftedSum A u eta J - A.comp P‖ * ‖u i‖ := by
  rw [← liftedSum_error_on_basis A P u eta i J hi hbio]
  exact (liftedSum A u eta J - A.comp P).le_opNorm (u i)

/-- Operator-norm convergence to the required order forces every convolved
geometric residual to vanish. Nuclear-norm convergence would imply this.
This is a necessary condition, not an assumed global nuclear bound. -/
theorem liftedSum_convergence_forces_residual_zero (A P : H →L[ℂ] H)
    (u : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ) (i : ℕ)
    (hbio : ∀ j, eta j (u i) = if j = i then 1 else 0)
    (hconv : Tendsto (fun n => liftedSum A u eta (Finset.range n)) atTop
      (nhds (A.comp P))) :
    A (u i - P (u i)) = 0 := by
  have hnorm : Tendsto (fun n =>
      ‖liftedSum A u eta (Finset.range n) - A.comp P‖ * ‖u i‖) atTop
      (nhds (0 : ℝ)) := by
    have hd : Tendsto (fun n => liftedSum A u eta (Finset.range n) - A.comp P)
        atTop (nhds (A.comp P - A.comp P)) := hconv.sub tendsto_const_nhds
    simpa using hd.norm.mul_const ‖u i‖
  have hevent : ∀ᶠ n in atTop, ‖A (u i - P (u i))‖ ≤
      ‖liftedSum A u eta (Finset.range n) - A.comp P‖ * ‖u i‖ := by
    filter_upwards [eventually_gt_atTop i] with n hn
    exact liftedSum_error_lower_bound A P u eta i (Finset.range n)
      (Finset.mem_range.mpr hn) hbio
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hnorm hevent) (norm_nonneg _))

#check liftedSum_error_lower_bound
#print axioms liftedSum_error_lower_bound
#check liftedSum_convergence_forces_residual_zero
#print axioms liftedSum_convergence_forces_residual_zero


/-- The cost of repairing a smoothed lift by its canonical lift. No
summability or bound on the chosen lifts is assumed in this inequality. -/
theorem convolved_lift_correction_cost (A : H →L[ℂ] H)
    (eta : H →L[ℂ] ℂ) (u p : H) :
    ‖A u - A p‖ * ‖eta‖ ≤ ‖A‖ * (‖u - p‖ * ‖eta‖) := by
  rw [← map_sub]
  have h := mul_le_mul_of_nonneg_right (A.le_opNorm (u - p)) (norm_nonneg eta)
  simpa only [mul_assoc] using h

/-- A finite correction bound for precisely the rank-one costs in the
manuscript representation. It does not assume or conclude main summability. -/
theorem finite_lift_correction_cost (A : H →L[ℂ] H)
    (eta : ℕ → H →L[ℂ] ℂ) (u p : ℕ → H) (J : Finset ℕ) :
    ∑ i ∈ J, ‖A (u i) - A (p i)‖ * ‖eta i‖ ≤
      ‖A‖ * ∑ i ∈ J, ‖u i - p i‖ * ‖eta i‖ := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _hi => convolved_lift_correction_cost A (eta i) (u i) (p i)

#check convolved_lift_correction_cost
#print axioms convolved_lift_correction_cost
#check finite_lift_correction_cost
#print axioms finite_lift_correction_cost

end Round91C
