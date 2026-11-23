import Mathlib

namespace NativeOrderRepair

/-- The exact mixed block, with source invariance as an explicit input. -/
theorem mixed_block {R : Type*} [Ring R] (A P S : R)
    (hs : S = 1 - P) (hinv : P * A * S = 0) :
    A * P - P * A = S * A * P := by
  subst S
  have hx : P * A * P = P * A := by
    have he : P * A - P * A * P = 0 := by
      simpa only [mul_sub, mul_one] using hinv
    exact (sub_eq_zero.mp he).symm
  simp only [sub_mul, one_mul, hx]

/-- Regular coefficient after the two actual integrations by parts. -/
theorem radial_coefficient (c l lp h h1 h2 : ℝ) :
    c^2*h + 2*c*(-h1+l*h) + (h2-2*l*h1+(l^2+lp)*h)
      = (c^2*h-2*c*h1+h2) + 2*l*(c*h-h1)+(l^2+lp)*h := by
  ring

/-- The finite-rank corner term has the indicated width difference. -/
theorem corner_jump (u v : ℝ) : (-2*v)-(-2*u) = -2*(v-u) := by
  ring

end NativeOrderRepair
#print axioms NativeOrderRepair.mixed_block
#print axioms NativeOrderRepair.radial_coefficient
#print axioms NativeOrderRepair.corner_jump
