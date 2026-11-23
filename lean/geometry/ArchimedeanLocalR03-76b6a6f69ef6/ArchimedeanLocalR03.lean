import Mathlib

/- The radial coefficients of the actual real and complex local kernels.
   See GLOBAL_ARCHIMEDEAN_R03.md for their angular and Mellin applications.
   This file makes no assertion of an adelic trace theorem. -/
namespace ArchimedeanLocalR03

theorem real_even_kernel (r v : ℝ) (hm : 1 - r ≠ 0) (hp : 1 + r ≠ 0)
    (hs : 1 - r ^ 2 ≠ 0) :
    (v / 2) * (1 / (1 - r) + 1 / (1 + r)) = v / (1 - r ^ 2) := by
  field_simp
  ring

theorem real_odd_kernel (r v : ℝ) (hm : 1 - r ≠ 0) (hp : 1 + r ≠ 0)
    (hs : 1 - r ^ 2 ≠ 0) :
    (v / 2) * (1 / (1 - r) - 1 / (1 + r)) = v * r / (1 - r ^ 2) := by
  field_simp
  ring

/-- The frequency-m diagonal of the absolutely convergent two geometric
series for the complex angular kernel.  The application takes |z| < 1. -/
theorem complex_mode_series (z : ℂ) (hz : ‖z‖ < 1) (m : ℕ) :
    HasSum (fun k : ℕ => z ^ (2 * k + m)) (z ^ m / (1 - z ^ 2)) := by
  have hz2 : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have h := (hasSum_geometric_of_norm_lt_one hz2).mul_left (z ^ m)
  convert h using 1
  · ext k
    rw [pow_add, pow_mul]
    ring

/-- Multiplying by log norm before sharp multiplies both local radial
halves by the correct, opposite signed radial parameters. -/
theorem log_sharp_local_pair (u : ℝ) (fp fm kp km : ℂ) :
    (-(u : ℂ) * fp) * kp + ((u : ℂ) * fm) * km =
      (u : ℂ) * (fm * km - fp * kp) := by ring

end ArchimedeanLocalR03

#print axioms ArchimedeanLocalR03.real_even_kernel
#print axioms ArchimedeanLocalR03.real_odd_kernel
#print axioms ArchimedeanLocalR03.complex_mode_series
#print axioms ArchimedeanLocalR03.log_sharp_local_pair
