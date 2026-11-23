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

end Round91C
