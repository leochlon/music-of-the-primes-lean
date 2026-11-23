import Mathlib

/- Quantitative envelope for excising the norm-one hypersurface from the
actual convolution test. The two input bounds are derived by Taylor's
formula and two integrations by parts in APPLICATION_R04.md. -/
namespace GeometricTraceExcisionR04

/-- The transition derivative for h₁=-t h₀ contains the extra first derivative. -/
theorem logarithmic_second_derivative_algebra (t c f f' f'' : ℂ) :
    c^2 * (-t*f) + 2*c*(-f-t*f') + (-2*f'-t*f'') =
      -t*(c^2*f+2*c*f'+f'') - 2*(c*f+f') := by ring

/-- A single integrable frequency envelope combines the small support and
second derivative estimates; unlike a fixed Sobolev estimate, it shrinks. -/
theorem fourier_excision_envelope (eps n C x : ℝ)
    (hx0 : x ≤ C*eps^2)
    (hx2 : n^2*x ≤ C) :
    x ≤ 2*C*eps^2/(1+(eps*n)^2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1+(eps*n)^2)).2
  have hmul := mul_le_mul_of_nonneg_left hx2 (sq_nonneg eps)
  nlinarith

/-- Substituting eps=1/N gives the low-frequency part of the actual
shrinking-band estimate, with its normalization exposed. -/
theorem low_frequency_excision_bound (N : ℕ) (hN : 0 < N)
    (C : ℝ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ Finset.range N, a n ≤ C/(N:ℝ)^2) :
    (∑ n ∈ Finset.range N, a n) ≤ C/(N:ℝ) := by
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    (∑ n ∈ Finset.range N, a n) ≤
        ∑ _n ∈ Finset.range N, C/(N:ℝ)^2 := Finset.sum_le_sum ha
    _ = C/(N:ℝ) := by simp; field_simp

#print axioms logarithmic_second_derivative_algebra
#print axioms fourier_excision_envelope
#print axioms low_frequency_excision_bound
end GeometricTraceExcisionR04
