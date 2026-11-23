import Mathlib
/- Port of the supplied alpo LatticePoissonBasic summability proof.
   Only the needed summability/continuity section is reused. -/
attribute [local instance] Classical.propDecidable
namespace ConditionalB881
open MeasureTheory Module Set Filter Topology NumberField NumberField.mixedEmbedding
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
section Summability

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in

theorem exists_norm_le_inv_one_add_pow (g : 𝓢(E, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  refine ⟨2 ^ k * (SchwartzMap.seminorm ℝ 0 0 g + SchwartzMap.seminorm ℝ k 0 g), by positivity,
    fun x => ?_⟩
  have h1 : ‖g x‖ ≤ SchwartzMap.seminorm ℝ 0 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖g x‖ ≤ SchwartzMap.seminorm ℝ k 0 g := by
    simpa using g.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa using this

theorem exists_summable_bound_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (R : ℝ) :
    ∃ u : Λ → ℝ, Summable u ∧ ∀ ℓ : Λ, ∀ x : E, ‖x‖ ≤ R → ‖g (x + ℓ)‖ ≤ u ℓ := by
  set k := finrank ℤ Λ + 1
  obtain ⟨C, hC, hg⟩ := exists_norm_le_inv_one_add_pow g k
  set R' := max R 0
  refine ⟨fun ℓ => C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹, ?_, ?_⟩
  · apply Summable.mul_left
    have hs := ZLattice.summable_norm_pow_inv (L := Λ) k (by omega)
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with ℓ hℓ
    have hpos : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  · intro ℓ x hx
    have hR : ‖x‖ ≤ R' := hx.trans (le_max_left _ _)
    have hR0 : 0 ≤ R' := le_max_right _ _
    have key : 1 + ‖ℓ‖ ≤ (1 + R') * (1 + ‖x + ℓ‖) := by
      have : ‖(ℓ : E)‖ ≤ ‖x + ℓ‖ + ‖x‖ := by
        calc ‖(ℓ : E)‖ = ‖(x + ℓ) - x‖ := by simp
          _ ≤ ‖x + ℓ‖ + ‖x‖ := norm_sub_le _ _
      have h' : ‖ℓ‖ ≤ ‖x + ℓ‖ + ‖x‖ := this
      nlinarith [norm_nonneg (x + ℓ)]
    calc ‖g (x + ℓ)‖ ≤ C * ((1 + ‖x + ℓ‖) ^ k)⁻¹ := hg _
      _ = C * ((1 + R') ^ k * (((1 + R') * (1 + ‖x + ℓ‖)) ^ k)⁻¹) := by
          rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ C * ((1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹) := by
          gcongr
      _ = C * (1 + R') ^ k * ((1 + ‖ℓ‖) ^ k)⁻¹ := by ring

theorem summable_norm_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (x : E) : Summable fun ℓ : Λ => ‖g (x + ℓ)‖ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g ‖x‖
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => hb ℓ x le_rfl)

theorem continuous_tsum_comp_add [CompleteSpace F] (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] (g : 𝓢(E, F)) : Continuous fun x => ∑' ℓ : Λ, g (x + ℓ) := by
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  obtain ⟨u, hu, hb⟩ := exists_summable_bound_comp_add Λ g (‖x₀‖ + 1)
  have hc : ContinuousOn (fun x => ∑' ℓ : Λ, g (x + ℓ)) (Metric.closedBall 0 (‖x₀‖ + 1)) :=
    continuousOn_tsum (fun ℓ => (g.continuous.comp (continuous_id.add continuous_const)).continuousOn)
      hu (fun ℓ x hx => hb ℓ x (by simpa using hx))
  exact hc.continuousAt (Metric.closedBall_mem_nhds_of_mem (by simp))

end Summability

/-- Actual archimedean fractional-ideal specialization in the proof of
Lemma 2.2.2.1 and (2.2.3.8). No lattice discreteness or summability premise. -/
theorem actual_ideal_schwartz_summable
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) :
    Summable (fun x : idealLattice K I => ‖f ((x : mixedSpace K) + a)‖) := by
  simpa [add_comm] using summable_norm_comp_add (idealLattice K I) f a

/-- The same ACTUAL fractional-ideal periodization is continuous in its
archimedean additive parameter, by a locally uniform summable bound. -/
theorem actual_ideal_schwartz_continuous
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : 𝓢(mixedSpace K, ℂ)) :
    Continuous (fun a : mixedSpace K => ∑' x : idealLattice K I, f (a + x)) :=
  continuous_tsum_comp_add (idealLattice K I) f

#print axioms actual_ideal_schwartz_summable
#print axioms actual_ideal_schwartz_continuous
end
end ConditionalB881
