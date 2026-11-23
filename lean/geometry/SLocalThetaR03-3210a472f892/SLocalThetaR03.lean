import Mathlib

open scoped BigOperators

namespace SLocalThetaR03

/-- The ideal/S-unit bijection may be used only with the actual summability
supplied by the compact adelic theta majorant. -/
theorem ideal_unit_reindex {Gamma Ideals Units : Type*}
    (e : Gamma ≃ Ideals × Units) (f : Ideals × Units → ℂ)
    (hf : Summable f) :
    (∑' gamma, f (e gamma)) = ∑' a, ∑' u, f (a, u) := by
  rw [e.tsum_eq]
  exact hf.tsum_prod

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The orthogonality defining the genuine projection is transported,
not replaced by orthogonality for a different local measure. -/
theorem orthogonal_transport (U : E ≃ₗᵢ[ℂ] F)
    (N : Submodule ℂ E) (x : E) :
    (∀ n ∈ N, inner ℂ n x = 0) ↔
    (∀ m ∈ N.map U.toLinearEquiv.toLinearMap, inner ℂ m (U x) = 0) := by
  constructor
  · intro h m hm
    rcases hm with ⟨n, hn, rfl⟩
    change inner ℂ (U n) (U x) = 0
    rw [U.inner_map_map]
    exact h n hn
  · intro h n hn
    have hm : U n ∈ N.map U.toLinearEquiv.toLinearMap := ⟨n, hn, rfl⟩
    simpa only [U.inner_map_map] using h (U n) hm

/-- In the substituted ideal column the logarithm is shifted by +log N(A).
Here t is log|t'/y| and L is log N(A). -/
theorem logged_ideal_column (t L h w : ℂ) :
    (-(t-L)*h)*w = (-t*h)*w + L*(h*w) := by
  ring

#print axioms ideal_unit_reindex
#print axioms orthogonal_transport
#print axioms logged_ideal_column

end SLocalThetaR03
