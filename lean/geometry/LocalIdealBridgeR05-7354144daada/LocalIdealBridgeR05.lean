import Mathlib

/- Two elementary bridges used in the source-based local-ideal argument.
No theta space, L-function, or trace class assertion is postulated here. -/
namespace GeometricTraceR05

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def poleFilter (D : E →ₗ[ℂ] E) (r : ℂ) (f : E) : E :=
  D (D f - r • f) - (D f - r • f)

theorem poleFilter_kills
    (D : E →ₗ[ℂ] E) (r : ℂ) (f : E) (ev vol : E →ₗ[ℂ] ℂ)
    (hev : ∀ x, ev (D x) = ev x)
    (hvol : ∀ x, vol (D x) = r * vol x) :
    ev (poleFilter D r f) = 0 ∧ vol (poleFilter D r f) = 0 := by
  constructor
  · simp [poleFilter, hev]
  · simp only [poleFilter, map_sub, map_smul, smul_eq_mul, hvol]
    ring

theorem poleFilter_mellin
    (D : E →ₗ[ℂ] E) (r z : ℂ) (f : E) (M : E →ₗ[ℂ] ℂ)
    (hM : ∀ x, M (D x) = z * M x) :
    M (poleFilter D r f) = (z - 1) * (z - r) * M f := by
  simp only [poleFilter, map_sub, map_smul, smul_eq_mul, hM]
  ring

variable {H F ι : Type*}
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A bounded map carries a total generating family into a closed subspace
only if its entire range lies in that subspace. This is the finite-window
range step; the finite dimension and arithmetic totality are separate inputs. -/
theorem range_mem_of_total
    (b : ι → H)
    (htotal : (Submodule.span ℂ (Set.range b)).topologicalClosure = ⊤)
    (T : H →L[ℂ] F) (W : Submodule ℂ F) (hW : IsClosed (W : Set F))
    (hb : ∀ i, T (b i) ∈ W) : ∀ x, T x ∈ W := by
  let C : Submodule ℂ H := W.comap T.toLinearMap
  have hC : IsClosed (C : Set H) := hW.preimage T.continuous
  have hspan : Submodule.span ℂ (Set.range b) ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  have hclosure := Submodule.topologicalClosure_minimal _ hspan hC
  rw [htotal] at hclosure
  intro x
  exact hclosure (show x ∈ (⊤ : Submodule ℂ H) from trivial)

#print axioms poleFilter_kills
#print axioms poleFilter_mellin
#print axioms range_mem_of_total
end GeometricTraceR05
