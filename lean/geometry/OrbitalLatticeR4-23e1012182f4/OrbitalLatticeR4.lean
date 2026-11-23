import Mathlib

namespace GeometricTraceR4

/-- A two-sided support gap, together with vanishing at zero, kills every
integer lattice sample. This lemma does not assume a trace formula. -/
theorem integer_lattice_vanishes (L : ℝ) (hL : 0 < L) (f : ℝ → ℂ)
    (hzero : f 0 = 0) (hsupport : ∀ u, L ≤ |u| → f u = 0) (k : ℤ) :
    f ((k : ℝ) * L) = 0 := by
  by_cases hk : k = 0
  · subst k
    simpa using hzero
  apply hsupport
  have hkbound : k ≤ -1 ∨ 1 ≤ k := by omega
  have hka : (1 : ℝ) ≤ |(k : ℝ)| := by
    rcases hkbound with hneg | hpos
    · have hn : (k : ℝ) ≤ -1 := by exact_mod_cast hneg
      have ha : -(k : ℝ) ≤ |(k : ℝ)| := neg_le_abs _
      linarith
    · have hp : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hpos
      exact hp.trans (le_abs_self _)
  rw [abs_mul, abs_of_pos hL]
  nlinarith

theorem weighted_lattice_sum_zero (L : ℝ) (hL : 0 < L) (f : ℝ → ℂ)
    (hzero : f 0 = 0) (hsupport : ∀ u, L ≤ |u| → f u = 0)
    (c : ℤ → ℂ) :
    HasSum (fun k : ℤ => c k * f ((k : ℝ) * L)) 0 := by
  have heq : (fun k : ℤ => c k * f ((k : ℝ) * L)) = fun _ => 0 := by
    funext k
    rw [integer_lattice_vanishes L hL f hzero hsupport k, mul_zero]
  rw [heq]
  exact hasSum_zero

end GeometricTraceR4

#print axioms GeometricTraceR4.integer_lattice_vanishes
#print axioms GeometricTraceR4.weighted_lattice_sum_zero
