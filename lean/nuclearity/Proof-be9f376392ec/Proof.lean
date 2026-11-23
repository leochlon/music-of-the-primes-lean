import Mathlib

/-! Round 184C. Arithmetic comparison in the global native resolvent bound.
The centered canonical-product and gamma calculations are in GLOBAL_ESTIMATE.md.
These lemmas discharge the positive-kernel comparison used there, for every
critical-strip zero and every multiplicity. They do not assume summability,
nuclearity, zero separation, or an inverse-Gram bound. -/
namespace Round184C

theorem poisson_zero_weight_domination (beta gamma : ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    1 / (1 + gamma ^ 2) ≤
      2 * ((2 - beta) / ((2 - beta) ^ 2 + gamma ^ 2)) := by
  have hg : 0 ≤ gamma ^ 2 := sq_nonneg gamma
  have ha : 1 ≤ 2 - beta := by linarith
  have hden : 0 < (2 - beta) ^ 2 + gamma ^ 2 := by nlinarith
  have hnum : (2 - beta) ^ 2 + gamma ^ 2 ≤
      (2 * (2 - beta)) * (1 + gamma ^ 2) := by
    have hb : 0 ≤ beta * (2 - beta) := mul_nonneg hb0 (by linarith)
    have ht : 0 ≤ (3 - 2 * beta) * gamma ^ 2 :=
      mul_nonneg (by linarith) hg
    nlinarith
  rw [← mul_div_assoc]
  exact (div_le_div_iff₀ (by positivity) hden).2 (by nlinarith [hnum])

theorem local_zero_poisson_mass (beta gamma height : ℝ)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hnear : |gamma - height| ≤ 1) :
    (1 : ℝ) / 5 ≤
      (2 - beta) / ((2 - beta) ^ 2 + (height - gamma) ^ 2) := by
  have ha : 1 ≤ 2 - beta := by linarith
  have hh := abs_le.mp hnear
  have hs : (height - gamma) ^ 2 ≤ 1 := by nlinarith
  have hden : 0 < (2 - beta) ^ 2 + (height - gamma) ^ 2 := by
    nlinarith [sq_nonneg (height - gamma)]
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden).2
  nlinarith [sq_nonneg beta]

#check poisson_zero_weight_domination
#print axioms poisson_zero_weight_domination
#check local_zero_poisson_mass
#print axioms local_zero_poisson_mass
end Round184C
