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

namespace FollowupD30
open Filter Topology
open scoped InnerProductSpace

/-- Correctly ordered replacement for 10.4.2.20. Strong uniformly bounded
left cutoffs preserve the diagonal trace of the actual supplied PA nuclear
expansion. No commutation or nuclearity of AP is used. For the manuscript,
H is the original weighted space and M is its multiplication cutoff. -/
theorem cutoff_PA_trace_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (E : Submodule ℂ H) [CompleteSpace E] (A : H →L[ℂ] H)
    (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      (E.starProjection (A x)))
    (M : ℕ → H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ k, ‖M k‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun k => M k x) atTop (𝓝 x)) :
    Tendsto (fun k => ∑' i, ⟪b i, M k (E.starProjection (A (b i)))⟫_ℂ)
      atTop (𝓝 (∑' n, ⟪u n, v n⟫_ℂ)) := by
  have hb (k n : ℕ) : ‖u n‖ * ‖M k (v n)‖ ≤ C * (‖u n‖ * ‖v n‖) := by
    calc
      _ ≤ ‖u n‖ * (‖M k‖ * ‖v n‖) :=
        mul_le_mul_of_nonneg_left ((M k).le_opNorm (v n)) (norm_nonneg _)
      _ ≤ ‖u n‖ * (C * ‖v n‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hbound k) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hm (k : ℕ) : Summable (fun n => ‖u n‖ * ‖M k (v n)‖) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (hb k) (hc.mul_left C)
  have hexp (k : ℕ) (x : H) :
      HasSum (fun n => ⟪u n, x⟫_ℂ • M k (v n)) (M k (E.starProjection (A x))) := by
    simpa only [map_smul] using (M k).hasSum (hT x)
  have heq (k : ℕ) :
      (∑' i, ⟪b i, M k (E.starProjection (A (b i)))⟫_ℂ) =
        ∑' n, ⟪u n, M k (v n)⟫_ℂ :=
    Spectral19.nuclear_operator_diagonal b ((M k).comp (E.starProjection.comp A))
      u (fun n => M k (v n)) (hm k) (hexp k)
  simp_rw [heq]
  apply tendsto_tsum_of_dominated_convergence (hc.mul_left C)
  · intro n
    exact ((innerSL ℂ (u n)).continuous.tendsto (v n)).comp (hstrong (v n))
  · exact Filter.Eventually.of_forall (fun k n => (norm_inner_le_norm _ _).trans (hb k n))

/-- The geometric kernel complement must be formed after convolution. -/
theorem genuine_geometric_complement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] (A : H →L[ℂ] H) :
    A - E.starProjection.comp A =
      (ContinuousLinearMap.id ℂ H - E.starProjection).comp A := by
  ext x
  simp

#print axioms cutoff_PA_trace_tendsto
#print axioms genuine_geometric_complement
end FollowupD30


namespace FollowupD30
open MeasureTheory Filter Topology

/-- The actual weighted-Haar norm estimate needed for manuscript cutoffs.
The weight and Haar are unchanged. With w=w_I,s and rho from 9.3.3.1,
this is the squared norm of (M_rho - 1)f in the original space. -/
theorem weighted_cutoff_error_tendsto
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (w : X → ℝ) (f : X → ℂ) (rho : ℕ → X → ℝ)
    (hw : ∀ᵐ x ∂mu, 0 ≤ w x)
    (hf : Integrable (fun x => w x * ‖f x‖^2) mu)
    (hr : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, w x * ‖((rho n x : ℂ) - 1) * f x‖^2 ∂mu)
      atTop (𝓝 0) := by
  have he (n : ℕ) (x : X) :
      w x * ‖((rho n x : ℂ) - 1) * f x‖^2 =
        (rho n x - 1)^2 * (w x * ‖f x‖^2) := by
    rw [show ((rho n x : ℂ) - 1) = ((rho n x - 1 : ℝ) : ℂ) by push_cast; rfl]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [he]
  have hh : Tendsto (fun n => ∫ x, (rho n x - 1)^2 * (w x * ‖f x‖^2) ∂mu)
      atTop (𝓝 (∫ x, (0 : ℝ) ∂mu)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => w x * ‖f x‖^2)
      (fun n => (((hr n).sub aestronglyMeasurable_const).pow 2).mul
        hf.aestronglyMeasurable) hf (fun n => ?_) ?_
    · filter_upwards [hw, hb n] with x hx hrx
      have hp : 0 ≤ w x * ‖f x‖^2 := mul_nonneg hx (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hp)]
      exact mul_le_of_le_one_left hp (by nlinarith [hrx.1, hrx.2])
    · filter_upwards [hl] with x hx
      simpa using ((hx.sub_const 1).pow 2).mul_const (w x * ‖f x‖^2)
  simpa using hh

#print axioms weighted_cutoff_error_tendsto
end FollowupD30


namespace FollowupD30
open Filter Topology

/-- The actual Paley-Wiener projections converge to the geometric projection,
not the identity. Thus the claimed full strong limit in 11.2.1.9 requires
vanishing of the opposite off-diagonal block, even with the genuine projector. -/
theorem geometric_truncation_full_limit_forces_offDiagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E]
    (A L : H →L[ℂ] H) (R : ℕ → H →L[ℂ] H)
    (hR : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 (x - E.starProjection x)))
    (hfull : ∀ x, Tendsto
      (fun n => L (A (R n x) - E.starProjection (A (R n x)))) atTop
      (𝓝 (L (A x - E.starProjection (A x))))) :
    ∀ x, L (A (E.starProjection x) -
      E.starProjection (A (E.starProjection x))) = 0 := by
  let T : H →L[ℂ] H := L.comp
    ((ContinuousLinearMap.id ℂ H - E.starProjection).comp A)
  intro x
  have ht : Tendsto (fun n => T (R n x)) atTop (𝓝 (T (x - E.starProjection x))) :=
    (T.continuous.tendsto _).comp (hR x)
  have hf : Tendsto (fun n => T (R n x)) atTop (𝓝 (T x)) := hfull x
  have he := tendsto_nhds_unique ht hf
  rw [map_sub] at he
  have hz : T (E.starProjection x) = 0 := by
    have hzero : T x - T (E.starProjection x) - T x = 0 := sub_eq_zero.mpr he
    have hn : -(T (E.starProjection x)) = 0 := by
      calc
        _ = T x - T (E.starProjection x) - T x := by abel
        _ = 0 := hzero
    exact neg_eq_zero.mp hn
  exact hz

#print axioms geometric_truncation_full_limit_forces_offDiagonal
end FollowupD30
