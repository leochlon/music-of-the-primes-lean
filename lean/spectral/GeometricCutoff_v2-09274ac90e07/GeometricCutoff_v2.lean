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

namespace Geometric30F
open scoped InnerProductSpace

/-- Transport both genuine cutoffs through the supplied PA expansion.
The original subspace E may be the orthogonal of the theta closure.
No AP expansion, commutation, or trace-norm convergence of cutoffs is assumed. -/
theorem ordered_PA_cutoff_nuclear_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A L R : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      (E.starProjection (A x))) :
    (∑' i, ⟪b i, L (E.starProjection (A (R (b i))))⟫_ℂ) =
      ∑' n, ⟪u n, R (L (v n))⟫_ℂ := by
  let U : ℕ → H := fun n => R.adjoint (u n)
  let V : ℕ → H := fun n => L (v n)
  have hcost : Summable (fun n => ‖U n‖ * ‖V n‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => ?_) (hc.mul_left (‖R.adjoint‖ * ‖L‖))
    calc
      ‖U n‖ * ‖V n‖ ≤ (‖R.adjoint‖ * ‖u n‖) * (‖L‖ * ‖v n‖) :=
        mul_le_mul (R.adjoint.le_opNorm (u n)) (L.le_opNorm (v n))
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖R.adjoint‖ * ‖L‖) * (‖u n‖ * ‖v n‖) := by ring
  have hpair (n : ℕ) (x : H) : ⟪U n, x⟫_ℂ = ⟪u n, R x⟫_ℂ :=
    R.adjoint_inner_left x (u n)
  have hexp (x : H) : HasSum (fun n => ⟪U n, x⟫_ℂ • V n)
      ((L.comp (E.starProjection.comp (A.comp R))) x) := by
    have hh := L.hasSum (hPA (R x))
    simpa only [map_smul, ContinuousLinearMap.comp_apply, hpair, V] using hh
  have ht := Spectral19.nuclear_operator_diagonal b
    (L.comp (E.starProjection.comp (A.comp R))) U V hcost hexp
  simpa only [ContinuousLinearMap.comp_apply, hpair, V] using ht

/-- Exact ordered complement correction, retaining both off-diagonal terms. -/
theorem ordered_complement_cutoff_identity
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (P A L R : H →L[ℂ] H) (x : H) :
    L (A (R x) - P (A (R x))) =
      L (A (R x - P (R x))) +
      L (A (P (R x)) - P (A (P (R x)))) -
      L (P (A (R x - P (R x)))) := by
  simp only [map_sub]
  abel

#print axioms ordered_PA_cutoff_nuclear_trace
#print axioms ordered_complement_cutoff_identity
end Geometric30F

namespace Geometric30F
open scoped InnerProductSpace
open Filter Topology

/-- A simultaneous cutoff limit needs only the composition RL on the
original nuclear vectors. The actual geometric application must establish
these bounds and limits for its multiplier/shell maps in the same H. -/
theorem ordered_PA_two_cutoff_trace_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      (E.starProjection (A x)))
    (L R : ℕ → H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ k n, ‖R k (L k (v n))‖ ≤ C * ‖v n‖)
    (hstrong : ∀ n, Tendsto (fun k => R k (L k (v n))) atTop (𝓝 (v n))) :
    Tendsto (fun k => ∑' i,
      ⟪b i, L k (E.starProjection (A (R k (b i))))⟫_ℂ) atTop
      (𝓝 (∑' n, ⟪u n, v n⟫_ℂ)) := by
  have ht : Tendsto (fun k => ∑' n, ⟪u n, R k (L k (v n))⟫_ℂ) atTop
      (𝓝 (∑' n, ⟪u n, v n⟫_ℂ)) := by
    refine tendsto_tsum_of_dominated_convergence (hc.mul_left C) ?_ ?_
    · intro n
      exact (innerSL ℂ (u n)).continuous.continuousAt.tendsto.comp (hstrong n)
    · exact Eventually.of_forall fun k n => by
        calc
          ‖⟪u n, R k (L k (v n))⟫_ℂ‖ ≤ ‖u n‖ * ‖R k (L k (v n))‖ :=
            norm_inner_le_norm _ _
          _ ≤ ‖u n‖ * (C * ‖v n‖) :=
            mul_le_mul_of_nonneg_left (hbound k n) (norm_nonneg _)
          _ = C * (‖u n‖ * ‖v n‖) := by ring
  have heq : (fun k => ∑' i,
      ⟪b i, L k (E.starProjection (A (R k (b i))))⟫_ℂ) =
      (fun k => ∑' n, ⟪u n, R k (L k (v n))⟫_ℂ) := by
    funext k
    exact ordered_PA_cutoff_nuclear_trace E b A (L k) (R k) u v hc hPA
  rw [heq]
  exact ht

#print axioms ordered_PA_two_cutoff_trace_limit
end Geometric30F
