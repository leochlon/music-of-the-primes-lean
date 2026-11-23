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

namespace Spectral28B
open scoped InnerProductSpace
/-- The native family spans E inside H; it need not span all of H. -/
theorem orthonormal_nuclear_diagonal_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : ι → H) (hb : Orthonormal ℂ b) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    Summable (fun i => ‖⟪b i, T (b i)⟫_ℂ‖) := by
  let c : ℕ → ι → ℂ := fun n i => ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ
  have hp : Summable (fun p : ℕ × ι => ‖c p.1 p.2‖) :=
    (summable_prod_of_nonneg (fun p : ℕ × ι => norm_nonneg (c p.1 p.2))).2
      ⟨fun n => (Spectral19.rankOne_diagonal_bound b hb (u n) (v n)).1,
        Summable.of_nonneg_of_le
          (fun n => tsum_nonneg (fun i => norm_nonneg (c n i)))
          (fun n => (Spectral19.rankOne_diagonal_bound b hb (u n) (v n)).2) hc⟩
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


/-- The ambient PA diagonal on a genuine spectral-subspace basis is absolutely
summable. No assertion that this is a HilbertBasis of the ambient H is made. -/
theorem ambient_subspace_diagonal_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (E : Submodule ℂ H) {ι : Type*} (b : HilbertBasis ι ℂ E)
    (P A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (P (A x))) :
    Summable (fun i => ‖⟪(b i : H), P (A (b i : H))⟫_ℂ‖) := by
  have hb : Orthonormal ℂ (fun i => (b i : H)) :=
    E.subtypeₗᵢ.orthonormal_comp_iff.mpr b.orthonormal
  exact orthonormal_nuclear_diagonal_summable
    (fun i => (b i : H)) hb (P.comp A) u v hc hT

#print axioms orthonormal_nuclear_diagonal_summable
#print axioms ambient_subspace_diagonal_summable

/-- Exact trace on the original spectral subspace, obtained from the AMBIENT
PA expansion. Only output vectors must lie in E; the input vectors remain in H.
The adjoint of the inclusion is used for Parseval, with its actual norm bound. -/
theorem ambient_subspace_nuclear_hasSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] {ι : Type*} (b : HilbertBasis ι ℂ E)
    (P A : H →L[ℂ] H) (u : ℕ → H) (v : ℕ → E)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • (v n : H)) (P (A x))) :
    HasSum (fun i => ⟪(b i : H), P (A (b i : H))⟫_ℂ)
      (∑' n, ⟪u n, (v n : H)⟫_ℂ) := by
  let R : H →L[ℂ] E := E.subtypeL.adjoint
  let w : ℕ → E := fun n => R (u n)
  have hp (n : ℕ) (x : E) : ⟪w n, x⟫_ℂ = ⟪u n, (x : H)⟫_ℂ :=
    E.subtypeL.adjoint_inner_left x (u n)
  have hcE : Summable (fun n => ‖w n‖ * ‖v n‖) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => ?_) (hc.mul_left ‖R‖)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (R.le_opNorm (u n)) (norm_nonneg (v n))
  have hdouble := (Spectral19.nuclear_diagonal_interchange b w v hcE).2
  simp only [hp] at hdouble
  have hd (i : ι) :
      (∑' n, ⟪u n, (b i : H)⟫_ℂ * ⟪(b i : H), (v n : H)⟫_ℂ) =
        ⟪(b i : H), P (A (b i : H))⟫_ℂ := by
    have hh := (hT (b i : H)).map (innerSL ℂ (b i : H)).toAddMonoidHom
      (innerSL ℂ (b i : H)).continuous
    simpa [inner_smul_right] using hh.tsum_eq
  have he : (∑' i, ⟪(b i : H), P (A (b i : H))⟫_ℂ) =
      ∑' n, ⟪u n, (v n : H)⟫_ℂ := by
    calc
      _ = ∑' i, ∑' n, ⟪u n, (b i : H)⟫_ℂ *
          ⟪(b i : H), (v n : H)⟫_ℂ := tsum_congr (fun i => (hd i).symm)
      _ = _ := hdouble
  have hh := (ambient_subspace_diagonal_summable E b P A u
    (fun n => (v n : H)) hc hT).of_norm.hasSum
  rwa [he] at hh

#print axioms ambient_subspace_nuclear_hasSum

/-- Native predecessor flags live in E while convolution and projection remain
operators on the original ambient H. This joins their diagonal to the ambient
nuclear expansion without AP, ambient completeness of the jets, or Lidskii. -/
theorem ambient_subspace_flag_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] {ι : Type*} (b : HilbertBasis ι ℂ E)
    (P A : H →L[ℂ] H) (u : ℕ → H) (v : ℕ → E)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • (v n : H)) (P (A x)))
    (lam : ι → ℂ) (lower : ι → Finset ι) (coef : ι → ι → ℂ)
    (hproper : ∀ i, i ∉ lower i)
    (hflag : ∀ i (x : E), ⟪(b i : H), P (A (x : H))⟫_ℂ =
      lam i * ⟪b i, x⟫_ℂ + ∑ j ∈ lower i, coef i j * ⟪b j, x⟫_ℂ) :
    Summable (fun i => ‖lam i‖) ∧
      HasSum lam (∑' n, ⟪u n, (v n : H)⟫_ℂ) := by
  have hd (i : ι) : ⟪(b i : H), P (A (b i : H))⟫_ℂ = lam i := by
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
  · simpa only [hd] using ambient_subspace_diagonal_summable E b P A u
      (fun n => (v n : H)) hc hT
  · simpa only [hd] using ambient_subspace_nuclear_hasSum E b P A u v hc hT

#print axioms ambient_subspace_flag_trace
end Spectral28B

namespace Spectral29B
open scoped InnerProductSpace
/-- The genuine orthogonal projection preserves exactly the functional pairing
against the native subspace. This does not commute A with the projection. -/
theorem native_projection_pairing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] (y : E) (x : H) :
    ⟪(y : H), E.starProjection x⟫_ℂ = ⟪(y : H), x⟫_ℂ := by
  rw [E.starProjection_apply]
  change ⟪y, E.orthogonalProjection x⟫_ℂ = ⟪(y : H), x⟫_ℂ
  rw [← E.adjoint_subtypeL]
  exact E.subtypeL.adjoint_inner_right y x

/-- Attach the measured CONVOLUTION functional flag to the genuine PA trace.
The native application sets E to the original theta-closure orthogonal; the
same-Haar Mellin action is supplied for A, not for a freely chosen PA map. -/
theorem genuine_projection_convolution_flag_trace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] {ι : Type*} (b : HilbertBasis ι ℂ E)
    (A : H →L[ℂ] H) (u : ℕ → H) (v : ℕ → E)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • (v n : H))
      (E.starProjection (A x)))
    (lam : ι → ℂ) (lower : ι → Finset ι) (coef : ι → ι → ℂ)
    (hproper : ∀ i, i ∉ lower i)
    (hflag : ∀ i (x : E), ⟪(b i : H), A (x : H)⟫_ℂ =
      lam i * ⟪b i, x⟫_ℂ + ∑ j ∈ lower i, coef i j * ⟪b j, x⟫_ℂ) :
    Summable (fun i => ‖lam i‖) ∧
      HasSum lam (∑' n, ⟪u n, (v n : H)⟫_ℂ) := by
  apply Spectral28B.ambient_subspace_flag_trace E b E.starProjection A u v hc hT
    lam lower coef hproper
  intro i x
  rw [native_projection_pairing E (b i) (A (x : H))]
  exact hflag i x

#print axioms native_projection_pairing
#print axioms genuine_projection_convolution_flag_trace
end Spectral29B

namespace Spectral29B
open scoped InnerProductSpace
/-- A nuclear expansion of PA may have ambient output vectors. Project the
actual expansion continuously; do not assume every output was already in E. -/
theorem genuine_projection_trace_of_ambient_expansion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (E : Submodule ℂ H) [CompleteSpace E] {ι : Type*} (b : HilbertBasis ι ℂ E)
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n)
      (E.starProjection (A x)))
    (lam : ι → ℂ) (lower : ι → Finset ι) (coef : ι → ι → ℂ)
    (hproper : ∀ i, i ∉ lower i)
    (hflag : ∀ i (x : E), ⟪(b i : H), A (x : H)⟫_ℂ =
      lam i * ⟪b i, x⟫_ℂ + ∑ j ∈ lower i, coef i j * ⟪b j, x⟫_ℂ) :
    Summable (fun i => ‖lam i‖) ∧
      HasSum lam (∑' n, ⟪u n, E.starProjection (v n)⟫_ℂ) := by
  let R : H →L[ℂ] E := E.orthogonalProjection
  let w : ℕ → E := fun n => R (v n)
  have hcw : Summable (fun n => ‖u n‖ * ‖w n‖) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun n => ?_) (hc.mul_left ‖R‖)
    calc
      ‖u n‖ * ‖w n‖ ≤ ‖u n‖ * (‖R‖ * ‖v n‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm (v n)) (norm_nonneg _)
      _ = ‖R‖ * (‖u n‖ * ‖v n‖) := by ring
  have hTw (x : H) : HasSum (fun n => ⟪u n, x⟫_ℂ • (w n : H))
      (E.starProjection (A x)) := by
    have hh := E.starProjection.hasSum (hT x)
    simpa only [map_smul, Submodule.starProjection_apply,
      Submodule.orthogonalProjection_mem_subspace_eq_self, w, R] using hh
  simpa only [Submodule.starProjection_apply, w, R] using
    genuine_projection_convolution_flag_trace E b A u w hcw hTw
      lam lower coef hproper hflag

#print axioms genuine_projection_trace_of_ambient_expansion
end Spectral29B
