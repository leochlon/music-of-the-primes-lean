import Mathlib

namespace MasulloGRH
/-- For a rank-n identity matrix the squared trace norm is n^2, whereas
the squared Hilbert-Schmidt norm is n. This scalar obstruction rules out
a dimension-independent bound; operator identification is informal here. -/
theorem no_uniform_rank_norm_bound (C : ℝ) :
    ∃ n : ℕ, C^2 * (n : ℝ) < (n : ℝ)^2 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C^2 + 1)
  refine ⟨n, ?_⟩
  have hp : 0 < (n : ℝ) := by nlinarith [sq_nonneg C]
  have hdiff : 0 < (n : ℝ) - C^2 := by linarith
  have hprod := mul_pos hdiff hp
  nlinarith
end MasulloGRH
#check MasulloGRH.no_uniform_rank_norm_bound
#print axioms MasulloGRH.no_uniform_rank_norm_bound
