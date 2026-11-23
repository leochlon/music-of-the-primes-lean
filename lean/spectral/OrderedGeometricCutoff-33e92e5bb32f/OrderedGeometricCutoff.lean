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
namespace Spectral26B
open scoped InnerProductSpace

/-- Absolute convergence is derived from the existing operator expansion.
Both summable costs and the genuine HasSum equation are indispensable. -/
theorem nuclear_diagonal_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    Summable (fun i => ‖⟪b i, T (b i)⟫_ℂ‖) := by
  let c : ℕ → ι → ℂ := fun n i => ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ
  have hp : Summable (fun p : ℕ × ι => ‖c p.1 p.2‖) :=
    (Spectral19.nuclear_diagonal_interchange b u v hc).1
  have hs : Summable (fun p : ι × ℕ => ‖c p.2 p.1‖) := hp.prod_symm
  have hr : (∀ i, Summable (fun n => ‖c n i‖)) ∧
      Summable (fun i => ∑' n, ‖c n i‖) :=
    (summable_prod_of_nonneg (fun p : ι × ℕ => norm_nonneg (c p.2 p.1))).1 hs
  have hd (i : ι) : (∑' n, c n i) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [c, inner_smul_right] using hh.tsum_eq
  have hbound (i : ι) : ‖⟪b i, T (b i)⟫_ℂ‖ ≤ ∑' n, ‖c n i‖ := by
    calc
      ‖⟪b i, T (b i)⟫_ℂ‖ = ‖∑' n, c n i‖ := congrArg norm (hd i).symm
      _ ≤ ∑' n, ‖c n i‖ := norm_tsum_le_tsum_norm (hr.1 i)
  exact Summable.of_nonneg_of_le
    (fun i => norm_nonneg (⟪b i, T (b i)⟫_ℂ)) hbound hr.2

/-- The native application sets T = P.comp (A h). The theorem does not
assume summability of a prescribed zero sum or reverse the operator order. -/
theorem nuclear_diagonal_hasSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪u n, v n⟫_ℂ) := by
  have hs := (nuclear_diagonal_summable b T u v hc hT).of_norm.hasSum
  rwa [Spectral19.nuclear_operator_diagonal b T u v hc hT] at hs

#print axioms nuclear_diagonal_summable
#print axioms nuclear_diagonal_hasSum

/-- Attach the nuclear diagonal to a finite predecessor flag for the linear
functional action. The actual application supplies the normalized native jets,
their Gram-Schmidt flag and P A, in precisely this order. -/
theorem ordered_PA_flag_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (P A : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (P (A x)))
    (lam : ι → ℂ) (lower : ι → Finset ι) (coef : ι → ι → ℂ)
    (hproper : ∀ i, i ∉ lower i)
    (hflag : ∀ i x, ⟪b i, P (A x)⟫_ℂ = lam i * ⟪b i, x⟫_ℂ +
      ∑ j ∈ lower i, coef i j * ⟪b j, x⟫_ℂ) :
    Summable (fun i => ‖lam i‖) ∧
      HasSum lam (∑' n, ⟪u n, v n⟫_ℂ) := by
  have hd (i : ι) : ⟪b i, (P.comp A) (b i)⟫_ℂ = lam i := by
    change ⟪b i, P (A (b i))⟫_ℂ = lam i
    rw [hflag]
    have hz : (∑ j ∈ lower i, coef i j * ⟪b j, b i⟫_ℂ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hji : j ≠ i := by
        intro he
        subst j
        exact hproper i hj
      rw [b.orthonormal.inner_eq_zero hji, mul_zero]
    rw [hz, add_zero]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  constructor
  · simpa only [hd] using nuclear_diagonal_summable b (P.comp A) u v hc hT
  · simpa only [hd] using nuclear_diagonal_hasSum b (P.comp A) u v hc hT

#print axioms ordered_PA_flag_trace
end Spectral26B


namespace ConditionalB26
open scoped InnerProductSpace

/-- Cutoffs and smoothing act on the supplied nuclear expansion of the genuine
PA operator in their actual order. This requires no nuclearity of A or AP.
In the manuscript E is the orthogonal of the original theta closure. -/
theorem ordered_cutoff_nuclear_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E]
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A C D : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      (E.starProjection (A x))) :
    Summable (fun n => ‖D.adjoint (u n)‖ * ‖C (v n)‖) ∧
    (∀ x, HasSum (fun n => ⟪D.adjoint (u n), x⟫_ℂ • C (v n))
      (C (E.starProjection (A (D x))))) ∧
    Summable (fun i => ‖⟪b i, C (E.starProjection (A (D (b i))))⟫_ℂ‖) ∧
    HasSum (fun i => ⟪b i, C (E.starProjection (A (D (b i))))⟫_ℂ)
      (∑' n, ⟪D.adjoint (u n), C (v n)⟫_ℂ) := by
  have hcost : Summable (fun n => ‖D.adjoint (u n)‖ * ‖C (v n)‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => ?_) (hc.mul_left (‖D.adjoint‖ * ‖C‖))
    calc
      ‖D.adjoint (u n)‖ * ‖C (v n)‖ ≤
          (‖D.adjoint‖ * ‖u n‖) * (‖C‖ * ‖v n‖) :=
        mul_le_mul (D.adjoint.le_opNorm (u n)) (C.le_opNorm (v n))
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖D.adjoint‖ * ‖C‖) * (‖u n‖ * ‖v n‖) := by ring
  have hexp (x : H) :
      HasSum (fun n => ⟪D.adjoint (u n), x⟫_ℂ • C (v n))
        (C (E.starProjection (A (D x)))) := by
    have hh := C.hasSum (hPA (D x))
    simpa only [map_smul, D.adjoint_inner_left] using hh
  let T : H →L[ℂ] H := C.comp (E.starProjection.comp (A.comp D))
  exact ⟨hcost, hexp,
    Spectral26B.nuclear_diagonal_summable b T
      (fun n => D.adjoint (u n)) (fun n => C (v n)) hcost hexp,
    Spectral26B.nuclear_diagonal_hasSum b T
      (fun n => D.adjoint (u n)) (fun n => C (v n)) hcost hexp⟩

/-- The original theta closure determines the projection; no zero list defines it.
The theorem retains the actual PA expansion as an independent supplied input. -/
theorem original_theta_ordered_cutoff_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {S0 : Type*} (theta : S0 → H)
    {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A C D : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      ((Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal.starProjection
        (A x))) :
    HasSum (fun i => ⟪b i, C
      ((Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal.starProjection
        (A (D (b i))))⟫_ℂ)
      (∑' n, ⟪D.adjoint (u n), C (v n)⟫_ℂ) := by
  exact (ordered_cutoff_nuclear_trace
    (Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal
    b A C D u v hc hPA).2.2.2

/-- The complement forced by the ordered kernel, including both cutoff slots. -/
theorem ordered_complement_with_cutoffs
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) [CompleteSpace E]
    (A C D : H →L[ℂ] H) (x : H) :
    C (A (D x) - E.starProjection (A (D x))) =
      C (A (D x)) - C (E.starProjection (A (D x))) := C.map_sub _ _

#print axioms ordered_cutoff_nuclear_trace
#print axioms original_theta_ordered_cutoff_trace
#print axioms ordered_complement_with_cutoffs
end ConditionalB26

namespace ConditionalB26
open Filter Topology MeasureTheory
open scoped InnerProductSpace

/-- A two-sided cutoff trace limit needs strong convergence of the composite
D_k C_k occurring in the nuclear diagonal, with a uniform bound. It does not
require strong convergence of the adjoints or operator-norm convergence. -/
theorem ordered_two_cutoff_trace_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] {ι : Type*} (b : HilbertBasis ι ℂ H)
    (A : H →L[ℂ] H) (C D : ℕ → H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (E.starProjection (A x)))
    (M : ℝ) (hbound : ∀ k x, ‖D k (C k x)‖ ≤ M * ‖x‖)
    (hstrong : ∀ x, Tendsto (fun k => D k (C k x)) atTop (𝓝 x)) :
    Tendsto (fun k => ∑' i, ⟪b i, C k (E.starProjection (A (D k (b i))))⟫_ℂ)
      atTop (𝓝 (∑' n, ⟪u n, v n⟫_ℂ)) := by
  have he (k : ℕ) :
      (∑' i, ⟪b i, C k (E.starProjection (A (D k (b i))))⟫_ℂ) =
        ∑' n, ⟪u n, D k (C k (v n))⟫_ℂ := by
    have ht := (ordered_cutoff_nuclear_trace E b A (C k) (D k) u v hc hPA).2.2.2
    simpa only [(D k).adjoint_inner_left] using ht.tsum_eq
  simp_rw [he]
  apply tendsto_tsum_of_dominated_convergence (hc.mul_left M)
  · intro n
    exact ((innerSL ℂ (u n)).continuous.tendsto (v n)).comp (hstrong (v n))
  · exact Eventually.of_forall fun k n => by
      calc
        ‖⟪u n, D k (C k (v n))⟫_ℂ‖ ≤ ‖u n‖ * ‖D k (C k (v n))‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖u n‖ * (M * ‖v n‖) :=
          mul_le_mul_of_nonneg_left (hbound k (v n)) (norm_nonneg _)
        _ = M * (‖u n‖ * ‖v n‖) := by ring

/-- Same-measure integral attachment in the normalized L2 model. The original
theta map fixes the subspace. In the native application X=C_K and mu is the
original quotient Haar; no compact/unitary trace theorem is invoked. -/
theorem original_theta_same_measure_cutoff_diagonal
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    {S0 : Type*} (theta : S0 → Lp ℂ 2 mu)
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 mu))
    (A C D : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ℕ → Lp ℂ 2 mu)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hPA : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      ((Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal.starProjection
        (A x))) :
    (∑' i, ∫ x, inner ℂ ((b i) x)
      ((C ((Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal.starProjection
        (A (D (b i))))) x) ∂mu) =
      ∑' n, ∫ x, inner ℂ ((D.adjoint (u n)) x) ((C (v n)) x) ∂mu := by
  simpa only [L2.inner_def] using
    (original_theta_ordered_cutoff_trace theta b A C D u v hc hPA).tsum_eq

#print axioms ordered_two_cutoff_trace_limit
#print axioms original_theta_same_measure_cutoff_diagonal
end ConditionalB26
