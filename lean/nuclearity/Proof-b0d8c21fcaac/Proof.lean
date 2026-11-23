import Mathlib

noncomputable section
open scoped InnerProductSpace
set_option linter.unusedSimpArgs false

/-! Round 183 F. The new quantitative step is the resolvent energy bound.
Applied to the native logarithmic derivative on an entire finite jet span,
it controls the inverse Gram conjugation collectively. Native weighted
integration by parts, arithmetic counting, and final attachment are paper
obligations recorded in GLOBAL_ESTIMATE.md, not hypotheses of nuclearity.
-/
namespace Round183F
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Real-part dissipativity bounds the squared resolvent on each vector. -/
theorem resolvent_energy
    (D R : H →L[ℂ] H) (c B : ℝ)
    (hD : ∀ y, (⟪D y, y⟫_ℂ).re ≤ B * ‖y‖ ^ 2)
    (hR : ∀ x, (c : ℂ) • R x - D (R x) = x) (x : H) :
    (c - B) * ‖R x‖ ^ 2 ≤ (⟪x, R x⟫_ℂ).re := by
  have he := congrArg (fun y : H => (⟪y, R x⟫_ℂ).re) (hR x)
  simp [inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re] at he
  have hd := hD (R x)
  nlinarith

/-- Summing over an orthonormal basis gives the Hilbert--Schmidt/trace
inequality used for the actual native finite jet windows. No bound on
individual biorthogonals or inverse Gram entries is used. -/
theorem finite_resolvent_trace_bound
    {ι : Type*} [Fintype ι]
    (D R : H →L[ℂ] H) (c B : ℝ) (hgap : B < c)
    (hD : ∀ y, (⟪D y, y⟫_ℂ).re ≤ B * ‖y‖ ^ 2)
    (hR : ∀ x, (c : ℂ) • R x - D (R x) = x)
    (b : OrthonormalBasis ι ℂ H) :
    ∑ j, ‖R (b j)‖ ^ 2 ≤
      (∑ j, (⟪b j, R (b j)⟫_ℂ).re) / (c - B) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_comm] using resolvent_energy D R c B hD hR (b j)

#check resolvent_energy
#print axioms resolvent_energy
#check finite_resolvent_trace_bound
#print axioms finite_resolvent_trace_bound
end Round183F
