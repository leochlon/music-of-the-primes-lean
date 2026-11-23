import Mathlib

namespace NativeCutoffR02

/-- Polynomial Sobolev growth remains polynomial in the actual translation. -/
theorem weight_translation_square (u v : ℝ) :
    1 + (u + v)^2 ≤ (1 + |v|)^2 * (1 + u^2) := by
  have huv : u * v ≤ |u| * |v| := by
    simpa only [abs_mul] using le_abs_self (u * v)
  have hp := mul_nonneg (abs_nonneg v) (sq_nonneg (|u| - 1))
  have hq := mul_nonneg (sq_nonneg u) (sq_nonneg v)
  have hu := sq_abs u
  have hv := sq_abs v
  have he : (|u| - 1)^2 = u^2 - 2 * |u| + 1 := by nlinarith
  rw [he] at hp
  have hvp : |v|^2 * (1 + u^2) = v^2 * (1 + u^2) := by rw [sq_abs]
  have hr := mul_nonneg (abs_nonneg v) (show 0 ≤ 1 + u^2 by positivity)
  nlinarith

/-- The ordered inverse difference used by the actual bounded resolvent pencils.
No commutation of the geometric projection with convolution is a premise. -/
theorem inverse_difference {R : Type*} [Ring R] (A B X Y : R)
    (hAX : A * X = 1) (hYB : Y * B = 1) :
    X - Y = Y * (B - A) * X := by
  calc
    X - Y = (Y * B) * X - Y * (A * X) := by rw [hAX, hYB]; simp
    _ = Y * (B - A) * X := by noncomm_ring

/-- Square difference retains the order needed for two HS factors. -/
theorem logged_inverse_difference {R : Type*} [Ring R] (X Y : R) :
    -(X * X) + Y * Y = -(X * (X - Y) + (X - Y) * Y) := by
  noncomm_ring

end NativeCutoffR02

#print axioms NativeCutoffR02.weight_translation_square
#print axioms NativeCutoffR02.inverse_difference
#print axioms NativeCutoffR02.logged_inverse_difference
