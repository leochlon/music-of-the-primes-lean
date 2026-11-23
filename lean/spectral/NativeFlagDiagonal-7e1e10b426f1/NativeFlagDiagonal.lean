import Mathlib
open scoped InnerProductSpace
namespace ConditionalA27

/-- One actual Gram-Schmidt step.  The native application takes F to the
finite span of earlier Riesz jets, e the new jet, and b its normalized residual.
The action premise concerns convolution A before any orthogonal projection. -/
theorem native_flag_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (F : Submodule ℂ H)
    (e b w r : H) (c lam : ℂ)
    (hc : c ≠ 0) (he : e = c • b + w)
    (hw : w ∈ F) (hr : r ∈ F)
    (hb : ⟪b, b⟫_ℂ = 1)
    (horth : ∀ v ∈ F, ⟪v, b⟫_ℂ = 0)
    (hinv : ∀ v ∈ F, ∃ v' ∈ F, ∀ x, ⟪v, A x⟫_ℂ = ⟪v', x⟫_ℂ)
    (hjet : ∀ x, ⟪e, A x⟫_ℂ = lam * ⟪e, x⟫_ℂ + ⟪r, x⟫_ℂ) :
    ⟪b, A b⟫_ℂ = lam := by
  obtain ⟨w', hw', hwA⟩ := hinv w hw
  have hwAb : ⟪w, A b⟫_ℂ = 0 := (hwA b).trans (horth w' hw')
  have h := hjet b
  rw [he, inner_add_left, inner_smul_left, hwAb, add_zero,
    inner_add_left, inner_smul_left, hb, horth w hw, horth r hr] at h
  simp only [mul_one, add_zero] at h
  have hcn : starRingEnd ℂ c ≠ 0 := by simpa using hc
  apply mul_left_cancel₀ hcn
  simpa only [mul_comm lam] using h

#print axioms native_flag_diagonal
end ConditionalA27
