import Mathlib

open scoped InnerProductSpace BigOperators
namespace SpectralCycle6B

/-- Finite predecessor Gram-Schmidt preserves the measured Mellin diagonal.
The raw family may mix different zero chains. No orthogonality between distinct
zeros is assumed. This discharges the algebraic flag-diagonal premise only. -/
theorem diagonal_from_native_jet_flag
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (jet b : ℕ → H) (lam : ℕ → ℂ)
    (coef : ℕ → ℕ → ℂ)
    (hraw : ∀ k x, ⟪jet k, A x⟫_ℂ = lam k * ⟪jet k, x⟫_ℂ +
      ∑ j ∈ Finset.range k, coef k j * ⟪jet j, x⟫_ℂ)
    (hspan : ∀ i, b i ∈ Submodule.span ℂ (jet '' Set.Iic i))
    (horth : ∀ i k, k < i → ⟪jet k, b i⟫_ℂ = 0)
    (hnorm : ∀ i, ‖b i‖ = 1) :
    ∀ i, ⟪b i, A (b i)⟫_ℂ = lam i := by
  intro i
  have hgen : ∀ k, k ≤ i →
      ⟪jet k, A (b i)⟫_ℂ = lam i * ⟪jet k, b i⟫_ℂ := by
    intro k hk
    rw [hraw]
    have hz : (∑ j ∈ Finset.range k, coef k j * ⟪jet j, b i⟫_ℂ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [horth i j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk), mul_zero]
    rw [hz, add_zero]
    rcases lt_or_eq_of_le hk with hlt | heq
    · rw [horth i k hlt, mul_zero, mul_zero]
    · rw [heq]
  have heq : ∀ x ∈ Submodule.span ℂ (jet '' Set.Iic i),
      ⟪x, A (b i)⟫_ℂ = lam i * ⟪x, b i⟫_ℂ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, hk, rfl⟩ := hx
        exact hgen k hk
    | zero => simp
    | add x y hx hy hpx hpy =>
        simp only [inner_add_left, hpx, hpy, mul_add]
    | smul c x hx hpx =>
        simp only [inner_smul_left, hpx]
        ring
  have hh := heq (b i) (hspan i)
  simpa [inner_self_eq_norm_sq_to_K, hnorm] using hh

#print axioms diagonal_from_native_jet_flag
end SpectralCycle6B
