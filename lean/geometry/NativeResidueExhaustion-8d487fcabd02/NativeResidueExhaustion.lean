import Mathlib

noncomputable section
open Filter Topology
namespace NativeResidueExhaustion

/-- The approximation premise is supplied by the genuine residue exhaustion
and the Riesz isometry, not by an assumed spectral trace identity. -/
theorem strong_of_dense_fixed_vectors
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (E : ℕ → H →L[ℂ] H)
    (hcontract : ∀ n x, ‖E n x‖ ≤ ‖x‖)
    (happrox : ∀ (x : H) (ε : ℝ), 0 < ε →
      ∃ y N, ‖x-y‖ < ε ∧ ∀ n ≥ N, E n y = y) :
    ∀ x, Tendsto (fun n => E n x) atTop (𝓝 x) := by
  intro x
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨y, N, hxy, hfix⟩ := happrox x (ε/2) (by linarith)
  refine ⟨N, ?_⟩
  intro n hn
  rw [dist_eq_norm]
  have hid : E n x - x = E n (x-y) - (x-y) := by
    rw [map_sub, hfix n hn]
    abel
  rw [hid]
  calc
    ‖E n (x-y) - (x-y)‖ ≤ ‖E n (x-y)‖ + ‖x-y‖ := norm_sub_le _ _
    _ ≤ ‖x-y‖ + ‖x-y‖ := by linarith [hcontract n (x-y)]
    _ < ε := by linarith

/-- Summable nuclear costs transfer the just-proved strong approximation
into the full operator's trace-norm error bound. -/
theorem nuclear_error_tends_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (E : ℕ → H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun k => ‖u k‖ * ‖v k‖))
    (herror : ∀ n x, ‖x-E n x‖ ≤ ‖x‖)
    (hstrong : ∀ x, Tendsto (fun n => E n x) atTop (𝓝 x)) :
    Tendsto (fun n => ∑' k, ‖u k‖ * ‖v k-E n (v k)‖) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun n k => ‖u k‖ * ‖v k-E n (v k)‖)
    (g := fun _ => (0 : ℝ)) (bound := fun k => ‖u k‖ * ‖v k‖) hc ?_ ?_
  · simpa using h
  · intro k
    have hv := ((tendsto_const_nhds (x := v k)).sub (hstrong (v k))).norm
    simpa using (tendsto_const_nhds (x := ‖u k‖)).mul hv
  · exact Eventually.of_forall fun n k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (herror n (v k)) (norm_nonneg _)

end NativeResidueExhaustion
#print axioms NativeResidueExhaustion.strong_of_dense_fixed_vectors
#print axioms NativeResidueExhaustion.nuclear_error_tends_zero
