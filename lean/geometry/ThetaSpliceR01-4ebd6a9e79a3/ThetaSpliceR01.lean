import Mathlib

/- Exact finite-lattice approximation of the regularized theta columns.
The number-field majorants are instantiated in GLOBAL_REVIEW_R01.md.
No trace or arithmetic equality is assumed here. -/
open Filter
open scoped Topology

namespace ActualThetaSpliceR01

/-- ALPO TateMain's zero-point removal, copied at its exact field scope. -/
theorem tsum_units_eq_tsum_sub {K : Type*} [Field K]
    {F : K → ℂ} (hF : Summable F) :
    ∑' ξ : Kˣ, F ξ = ∑' ξ : K, F ξ - F 0 := by
  classical
  rw [hF.tsum_eq_add_tsum_ite 0, add_sub_cancel_left]
  refine (tsum_congr fun ξ : Kˣ ↦ (if_neg ξ.ne_zero).symm).trans
    (Function.Injective.tsum_eq Units.val_injective
      (f := fun ξ ↦ if ξ = 0 then 0 else F ξ) fun ξ hξ ↦ ?_)
  have h0 : ξ ≠ 0 := fun h ↦ hξ (by simp [h])
  exact ⟨Units.mk0 ξ h0, rfl⟩

/-- The nonzero theta identity retains both additive moments. -/
theorem nonzero_poisson (theta dual m0 m1 r : ℂ)
    (hp : theta + m0 = r * (dual + m1)) :
    theta = r * dual + r * m1 - m0 := by
  linear_combination hp

/-- The regularization is a splice of two convergent NONZERO lattice sums.
The actual application sets r=|x|⁻¹ and b=|x|^a. -/
theorem regularized_eq_splice (theta dual m0 m1 r b k : ℂ)
    (hp : theta + m0 = r * (dual + m1)) :
    b * theta - k * (b * r * m1 - b * m0) =
      (1-k) * b * theta + k * b * r * dual := by
  linear_combination k * b * hp

section Banach
variable {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- A summable lattice majorant gives genuine convergence in the weighted
Hilbert space, once its column norm estimate has been proved. -/
theorem summable_columns (f : ι → E) (u : ι → ℝ)
    (hu : Summable u) (hfu : ∀ i, ‖f i‖ ≤ u i) : Summable f := by
  exact (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hfu hu).of_norm

omit [CompleteSpace E] in
/-- Quantified discarded-lattice error. Used separately on the primal
and Fourier halves, never on unregularized global partial theta sums. -/
theorem tail_bound [DecidableEq ι] (f : ι → E) (u : ι → ℝ)
    (hu : Summable u) (hfu : ∀ i, ‖f i‖ ≤ u i) (s : Finset ι) :
    ‖∑' i, (if i ∈ s then 0 else f i)‖ ≤
      ∑' i, (if i ∈ s then 0 else u i) := by
  classical
  have hu0 : ∀ i, 0 ≤ u i := fun i => (norm_nonneg _).trans (hfu i)
  have hs : Summable (fun i => if i ∈ s then (0 : ℝ) else u i) := by
    apply Summable.of_nonneg_of_le _ _ hu
    · intro i
      split_ifs <;> simp_all
    · intro i
      split_ifs <;> simp_all
  have hb : ∀ i, ‖(if i ∈ s then 0 else f i)‖ ≤
      (if i ∈ s then 0 else u i) := by
    intro i
    split_ifs <;> simp_all
  have hn := Summable.of_nonneg_of_le (fun i => norm_nonneg
    (if i ∈ s then 0 else f i)) hb hs
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hs)

/-- Both true theta tails converge in the SAME space. -/
theorem splice_hasSum (f g : ι → E) (u v : ι → ℝ)
    (hu : Summable u) (hv : Summable v)
    (hf : ∀ i, ‖f i‖ ≤ u i) (hg : ∀ i, ‖g i‖ ≤ v i) :
    HasSum (fun i => f i + g i) ((∑' i, f i) + ∑' i, g i) := by
  exact (summable_columns f u hu hf).hasSum.add
    (summable_columns g v hv hg).hasSum

end Banach

end ActualThetaSpliceR01

#print axioms ActualThetaSpliceR01.tsum_units_eq_tsum_sub
#print axioms ActualThetaSpliceR01.regularized_eq_splice
#print axioms ActualThetaSpliceR01.tail_bound
#print axioms ActualThetaSpliceR01.splice_hasSum
