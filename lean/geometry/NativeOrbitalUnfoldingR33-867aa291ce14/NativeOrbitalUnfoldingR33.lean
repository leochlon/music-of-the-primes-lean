import Mathlib

namespace NativeOrbitalUnfoldingR33

/-- Source entries retain the exact physical-cutoff commutator. -/
theorem cutoff_difference (f h g cy cx : ℂ) :
    f * h * cy * g - f * h * cx * g = f * h * (cy - cx) * g := by
  ring

/-- Finite decreasing idele shells have this orientation. -/
theorem shell_telescope (a : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (a k - a (k+1))) = a 0 - a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The logged test multiplies the SAME ordered entry by minus log norm. -/
theorem logged_entry (f h g chi t : ℂ) :
    f * (-t * h) * chi * g = -t * (f * h * chi * g) := by
  ring

/-- Width subtraction uses the original source traces with the correct sign. -/
theorem width_source_sign (ta tb ga gb : ℂ)
    (ha : ta = -ga) (hb : tb = -gb) : tb - ta = ga - gb := by
  rw [ha, hb]
  ring

#print axioms cutoff_difference
#print axioms shell_telescope
#print axioms logged_entry
#print axioms width_source_sign
end NativeOrbitalUnfoldingR33
