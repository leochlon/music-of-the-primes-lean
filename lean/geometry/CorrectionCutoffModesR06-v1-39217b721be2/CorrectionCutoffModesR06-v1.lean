import Mathlib

open Filter Topology
open scoped BigOperators

namespace CorrectionCutoffModesR06

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Finite-rank trace pairing: for R x = sum_i ell_i(x) v_i,
this is the trace of R A. The adelic identification is supplied on paper. -/
def pairing {m : ℕ} (ell : Fin m → H →L[ℂ] ℂ)
    (v : Fin m → H) (A : H →L[ℂ] H) : ℂ :=
  ∑ i, ell i (A (v i))

theorem pairing_cutoff_limit {m : ℕ} (ell : Fin m → H →L[ℂ] ℂ)
    (v : Fin m → H) (M : ℕ → H →L[ℂ] H)
    (hM : ∀ x, Tendsto (fun L => M L x) atTop (𝓝 x)) :
    Tendsto (fun L => pairing ell v (M L)) atTop
      (𝓝 (∑ i, ell i (v i))) := by
  unfold pairing
  exact tendsto_finset_sum _ fun i _ =>
    ((ell i).continuous.tendsto (v i)).comp (hM (v i))

theorem pairing_jet {m r : ℕ} (ell : Fin m → H →L[ℂ] ℂ)
    (v : Fin m → H) (A : Fin r → H →L[ℂ] H)
    (M : H →L[ℂ] H) (c : Fin r → ℂ) :
    (∑ i, ell i (M (∑ k, c k • A k (v i)))) =
      ∑ k, c k * pairing ell (fun i => A k (v i)) M := by
  simp only [map_sum, map_smul, pairing, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]

/-- Once the smoothing is identity on the entire jet space, logging
shifts the exact finite-cutoff polynomial, not merely its limiting trace. -/
theorem logged_jet {r : ℕ} (c : Fin r → ℂ) (t : ℂ) :
    t * (∑ k, c k * t ^ (k : ℕ)) =
      ∑ k, c k * t ^ ((k : ℕ) + 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

theorem surviving_constant {m : ℕ} (ell : Fin m → H →L[ℂ] ℂ)
    (v : Fin m → H) (M : ℕ → H →L[ℂ] H)
    (hM : ∀ x, Tendsto (fun L => M L x) atTop (𝓝 x))
    (hm : (∑ i, ell i (v i)) ≠ 0) :
    ∀ᶠ L in atTop, pairing ell v (M L) ≠ 0 := by
  exact (pairing_cutoff_limit ell v M hM).eventually_ne hm

/-- The reflected zero lies outside the SAME narrow witness. -/
theorem reflected_generator (q : ℂ) (alpha : ℝ)
    (h : alpha < q.re - 1/2) :
    (1-q).re - 1/2 < -alpha ∧ -(1-q-1/2) = q-1/2 := by
  constructor
  · simp only [Complex.sub_re, Complex.one_re]
    linarith
  · ring

/-- A nilpotent term can have nonzero trace after an input cutoff. -/
theorem nilpotent_cutoff_example :
    let N : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℂ := !![1/2, 1/4; 1/4, 1/2]
    N ^ 2 = 0 ∧ Matrix.trace N = 0 ∧ Matrix.trace (N * C) = 1/4 := by
  dsimp
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  · norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

end
end CorrectionCutoffModesR06

#print axioms CorrectionCutoffModesR06.pairing_cutoff_limit
#print axioms CorrectionCutoffModesR06.pairing_jet
#print axioms CorrectionCutoffModesR06.logged_jet
#print axioms CorrectionCutoffModesR06.surviving_constant
#print axioms CorrectionCutoffModesR06.reflected_generator
#print axioms CorrectionCutoffModesR06.nilpotent_cutoff_example
