import Mathlib
/- Port of the supplied alpo LatticePoissonBasic summability proof.
   Only the needed summability/continuity section is reused. -/
attribute [local instance] Classical.propDecidable
namespace FollowupF639
open MeasureTheory Module Set Filter Topology NumberField NumberField.mixedEmbedding
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
section Summability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in

def decaySeminorm (g : 𝓢(E, F)) (k : ℕ) : ℝ :=
  2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g)

omit [FiniteDimensional ℝ E] in
theorem norm_le_explicit_decaySeminorm (g : 𝓢(E, F)) (k : ℕ) (x : E) :
    ‖g x‖ ≤ decaySeminorm g k * ((1 + ‖x‖) ^ k)⁻¹ := by
  have h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa [decaySeminorm] using this

/-- The summable majorant is independent of the full mixed Schwartz test. -/
theorem uniform_summable_bound_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (R : ℝ) :
    ∃ u : Λ → ℝ, Summable u ∧ (∀ ℓ, 0 ≤ u ℓ) ∧
      ∀ (g : 𝓢(E, F)) (ℓ : Λ) (x : E), ‖x‖ ≤ R →
        ‖g (x + ℓ)‖ ≤ decaySeminorm g (finrank ℤ Λ + 1) * u ℓ := by
  set k := finrank ℤ Λ + 1
  set R' := max R 0
  refine ⟨fun ℓ => (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_,
    fun ℓ => by positivity, ?_⟩
  · apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  · intro g ℓ x hx
    have hC : 0 ≤ decaySeminorm g k := by unfold decaySeminorm; positivity
    have hR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖) := by
      have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
        calc ‖(ℓ : E)‖ = ‖(x + ℓ) - x‖ := by simp
             _ ≤ ‖x + ℓ‖ + ‖x‖ := norm_sub_le _ _
      have h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖ := this
      nlinarith [norm_nonneg (x + ℓ)]
    calc ‖g (x + ℓ)‖ ≤ decaySeminorm g k * ((1 + ‖x + ℓ‖) ^ k)⁻¹ :=
          norm_le_explicit_decaySeminorm g k _
      _ = decaySeminorm g k * ((1 + R') ^ k *
          (((1 + R') * (1 + ‖x + ℓ‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k),
            mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ decaySeminorm g k * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by
          gcongr

end Summability

theorem actual_ideal_uniform_schwartz_bound
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (R : ℝ) :
    ∃ u : idealLattice K I → ℝ, Summable u ∧ (∀ ℓ, 0 ≤ u ℓ) ∧
      ∀ (g : 𝓢(mixedSpace K, ℂ)) (ℓ : idealLattice K I) (x : mixedSpace K),
        ‖x‖ ≤ R → ‖g (x + ℓ)‖ ≤
          decaySeminorm g (finrank ℤ (idealLattice K I) + 1) * u ℓ :=
  uniform_summable_bound_comp_add (idealLattice K I) R

#print axioms actual_ideal_uniform_schwartz_bound
end
end FollowupF639
