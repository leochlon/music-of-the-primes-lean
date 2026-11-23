import Mathlib
open scoped InnerProductSpace
namespace Spectral19

/- T1: nuclear rank-one diagonals are absolutely summable with cost control.
This uses the existing operator's nuclear vectors; no zero list is prescribed. -/
theorem rankOne_diagonal_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : ι → H) (hb : Orthonormal ℂ b) (u v : H) :
    Summable (fun i => ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ∧
    (∑' i, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
  have key (S : Finset ι) :
      ∑ i ∈ S, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
    have hn (i : ι) : ‖⟪u, b i⟫_ℂ‖ = ‖⟪b i, u⟫_ℂ‖ := norm_inner_symm _ _
    simp only [norm_mul, hn]
    calc
      _ ≤ Real.sqrt (∑ i ∈ S, ‖⟪b i, u⟫_ℂ‖ ^ 2) *
          Real.sqrt (∑ i ∈ S, ‖⟪b i, v⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (‖u‖ ^ 2) * Real.sqrt (‖v‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt (hb.sum_inner_products_le u))
          (Real.sqrt_le_sqrt (hb.sum_inner_products_le v))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖u‖ * ‖v‖ := by simp
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) key,
    le_of_tendsto (summable_of_sum_le (fun _ => norm_nonneg _) key).hasSum
      (Filter.Eventually.of_forall key)⟩

/- T1: unconditional double-series convergence follows from the independent
nuclear representation cost, not from an assumed spectral zero sum. -/
theorem nuclear_diagonal_interchange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun p : ℕ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) ∧
    (∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) =
      ∑' n, ⟪u n, v n⟫_ℂ := by
  have hf (n : ℕ) := rankOne_diagonal_bound b b.orthonormal (u n) (v n)
  have hs : Summable (fun n => ∑' i, ‖⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ‖) :=
    Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun n => (hf n).2) hc
  have hp : Summable (fun p : ℕ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) := by
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun n => (hf n).1, hs⟩
  refine ⟨hp, ?_⟩
  calc
    _ = ∑' n, ∑' i, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ := hp.of_norm.tsum_comm
    _ = _ := tsum_congr (fun n => (b.hasSum_inner_mul_inner (u n) (v n)).tsum_eq)

#check rankOne_diagonal_bound
#print axioms rankOne_diagonal_bound
#check nuclear_diagonal_interchange
#print axioms nuclear_diagonal_interchange

/- T2's operator-expansion bridge: for a given continuous operator, a genuine
nuclear expansion identifies its basis diagonal with the convergent series. -/
theorem nuclear_operator_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' n, ⟪u n, v n⟫_ℂ := by
  have hd (i : ι) :
      (∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [inner_smul_right] using hh.tsum_eq
  calc
    _ = ∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ :=
      tsum_congr (fun i => (hd i).symm)
    _ = _ := (nuclear_diagonal_interchange b u v hc).2

#check nuclear_operator_diagonal
#print axioms nuclear_operator_diagonal
end Spectral19


set_option maxHeartbeats 400000
namespace GeometricCutoff
open Filter Topology
open scoped InnerProductSpace

/-- The actual left-cutoff operator retains the same nuclear functionals.
Both the cost and HasSum hypotheses are indispensable. -/
theorem left_cutoff_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    (∑' i, ⟪b i, M (T (b i))⟫_ℂ) = ∑' n, ⟪u n, M (v n)⟫_ℂ := by
  have hcost : Summable (fun n => ‖u n‖ * ‖M (v n)‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => ?_) (hc.mul_left ‖M‖)
    calc
      ‖u n‖ * ‖M (v n)‖ ≤ ‖u n‖ * (‖M‖ * ‖v n‖) :=
        mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
      _ = ‖M‖ * (‖u n‖ * ‖v n‖) := by ring
  apply Spectral19.nuclear_operator_diagonal b (M.comp T) u (fun n => M (v n)) hcost
  intro x
  simpa only [map_smul, ContinuousLinearMap.comp_apply] using M.hasSum (hT x)

/-- Strong cutoff convergence suffices with a uniform operator bound and the
ACTUAL nuclear expansion. Operator-norm convergence is not assumed. -/
theorem strong_left_cutoff_trace_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (T : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x))
    (M : ℕ → H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ k x, ‖M k x‖ ≤ C * ‖x‖)
    (hstrong : ∀ x, Tendsto (fun k => M k x) atTop (𝓝 x)) :
    Tendsto (fun k => ∑' i, ⟪b i, M k (T (b i))⟫_ℂ) atTop
      (𝓝 (∑' i, ⟪b i, T (b i)⟫_ℂ)) := by
  have ht : Tendsto (fun k => ∑' n, ⟪u n, M k (v n)⟫_ℂ) atTop
      (𝓝 (∑' n, ⟪u n, v n⟫_ℂ)) := by
    refine tendsto_tsum_of_dominated_convergence (hc.mul_left C) ?_ ?_
    · intro n
      exact (innerSL ℂ (u n)).continuous.continuousAt.tendsto.comp (hstrong (v n))
    · exact Eventually.of_forall fun k n => by
        calc
          ‖⟪u n, M k (v n)⟫_ℂ‖ ≤ ‖u n‖ * ‖M k (v n)‖ := norm_inner_le_norm _ _
          _ ≤ ‖u n‖ * (C * ‖v n‖) :=
            mul_le_mul_of_nonneg_left (hbound k (v n)) (norm_nonneg _)
          _ = C * (‖u n‖ * ‖v n‖) := by ring
  simpa only [left_cutoff_diagonal b T _ u v hc hT,
    Spectral19.nuclear_operator_diagonal b T u v hc hT] using ht

/-- Ordered manuscript application: first the actual convolution A, then the
GENUINE spectral projection, then the spatial cutoff. E is to be instantiated
with the original theta-closure orthogonal; no AP commutation is used. -/
theorem genuine_PA_strong_cutoff_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (A : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (E.starProjection (A x)))
    (M : ℕ → H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ k x, ‖M k x‖ ≤ C * ‖x‖)
    (hstrong : ∀ x, Tendsto (fun k => M k x) atTop (𝓝 x)) :
    Tendsto (fun k => ∑' i, ⟪b i, M k (E.starProjection (A (b i)))⟫_ℂ) atTop
      (𝓝 (∑' i, ⟪b i, E.starProjection (A (b i))⟫_ℂ)) := by
  exact strong_left_cutoff_trace_limit b (E.starProjection.comp A) u v hc hPA
    M C hbound hstrong

#print axioms left_cutoff_diagonal
#print axioms strong_left_cutoff_trace_limit
#print axioms genuine_PA_strong_cutoff_limit
end GeometricCutoff
