import Mathlib

/- The quotient/orthogonal transfer premise of manuscript (10.4.2.5).
This is Hilbert-space infrastructure, not native spectral nuclearity. -/
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace
namespace Round173H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] (G : Submodule ℂ E) [G.HasOrthogonalProjection]

/-- S has the direction quotient -> genuine orthogonal complement. -/
def quotientSection : (E ⧸ G) →ₗ[ℂ] Gᗮ :=
  G.liftQ Gᗮ.orthogonalProjection.toLinearMap (by
    intro x hx
    change Gᗮ.orthogonalProjection x = 0
    apply Submodule.orthogonalProjection_eq_zero_iff.mpr
    simpa only [Submodule.orthogonal_orthogonal] using hx)

@[simp] theorem quotientSection_mk (x : E) :
    quotientSection G (G.mkQ x) = Gᗮ.orthogonalProjection x := rfl

/-- Derived from the actual quotient norm, without assuming a bound on S. -/
theorem quotientSection_contracts (q : E ⧸ G) :
    ‖quotientSection G q‖ ≤ ‖q‖ := by
  by_contra hn
  have hd : 0 < ‖quotientSection G q‖ - ‖q‖ := sub_pos.mpr (lt_of_not_ge hn)
  obtain ⟨x, hx, hsmall⟩ := Submodule.Quotient.norm_mk_lt q hd
  have hp := Gᗮ.norm_orthogonalProjection_apply_le x
  have he : quotientSection G q = Gᗮ.orthogonalProjection x := by
    rw [← hx]
    rfl
  rw [← he] at hp
  linarith

def quotientSectionCLM : (E ⧸ G) →L[ℂ] Gᗮ :=
  (quotientSection G).mkContinuous 1 (by
    intro q
    simpa only [one_mul] using quotientSection_contracts G q)

def quotientCLM : E →L[ℂ] (E ⧸ G) :=
  G.mkQ.mkContinuous 1 (by
    intro x
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le G x)

/-- Actual quotient descent, with invariance exposed as the remaining input. -/
def inducedMap (A : E →L[ℂ] E) (hA : G ≤ G.comap A.toLinearMap) :
    (E ⧸ G) →ₗ[ℂ] (E ⧸ G) := G.mapQ G A.toLinearMap hA

/-- The manuscript factorisation with convolution first and projection second.
For application: E=W_I^s(C_K), G=closed geometric image, A=A(h).
No nuclearity, finite cost, summability or commutation assumption occurs. -/
theorem projected_quotient_factorization (A : E →L[ℂ] E)
    (hA : G ≤ G.comap A.toLinearMap) (x : E) :
    Gᗮ.orthogonalProjection (A x) =
      quotientSectionCLM G (inducedMap G A hA (quotientCLM G x)) := by
  rfl

theorem quotient_transfer_map_bounds :
    ‖quotientCLM G‖ ≤ 1 ∧ ‖quotientSectionCLM G‖ ≤ 1 := by
  constructor
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le G x
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    simpa only [one_mul] using quotientSection_contracts G q

/-- The section is faithful; no replacement quotient is introduced. -/
theorem quotientSection_injective : Function.Injective (quotientSection G) := by
  apply LinearMap.ker_eq_bot.mp
  apply G.ker_liftQ_eq_bot
  intro x hx
  change Gᗮ.orthogonalProjection x = 0 at hx
  have hm := Submodule.orthogonalProjection_eq_zero_iff.mp hx
  simpa only [Submodule.orthogonal_orthogonal] using hm

/-- Q S is the identity, so S selects the genuine orthogonal representative. -/
theorem quotient_section_right_inverse (q : E ⧸ G) :
    quotientCLM G (quotientSectionCLM G q : E) = q := by
  apply quotientSection_injective G
  change Gᗮ.orthogonalProjection (quotientSection G q : E) = quotientSection G q
  exact Submodule.orthogonalProjection_mem_subspace_eq_self (quotientSection G q)

theorem quotientSection_isometry_norm (q : E ⧸ G) :
    ‖quotientSectionCLM G q‖ = ‖q‖ := by
  apply le_antisymm (quotientSection_contracts G q)
  have h := Submodule.Quotient.norm_mk_le G (quotientSectionCLM G q : E)
  change ‖quotientCLM G (quotientSectionCLM G q : E)‖ ≤ ‖quotientSectionCLM G q‖ at h
  rwa [quotient_section_right_inverse G q] at h
end Round173H
#check Round173H.projected_quotient_factorization
#print axioms Round173H.projected_quotient_factorization
#check Round173H.quotientSection_contracts
#print axioms Round173H.quotientSection_contracts
#check Round173H.quotient_transfer_map_bounds
#print axioms Round173H.quotient_transfer_map_bounds

#check Round173H.quotient_section_right_inverse
#print axioms Round173H.quotient_section_right_inverse
#check Round173H.quotientSection_isometry_norm
#print axioms Round173H.quotientSection_isometry_norm
