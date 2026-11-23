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

end
end ConditionalB881

namespace ConditionalA885
open MeasureTheory Module Set Filter Topology NumberField NumberField.mixedEmbedding
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def decaySeminorm (k : ℕ) (f : 𝓢(E, ℂ)) : ℝ :=
  2 ^ k * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f)

omit [FiniteDimensional ℝ E] in
theorem norm_le_decaySeminorm (k : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    ‖f x‖ ≤ decaySeminorm k f * ((1 + ‖x‖) ^ k)⁻¹ := by
  have h1 : ‖f x‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
    simpa using f.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖f x‖ ≤ SchwartzMap.seminorm ℝ k 0 f := by
    simpa using f.norm_pow_mul_le_seminorm ℝ k x
  simpa [decaySeminorm] using
    pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2

def latticeMajorant (Λ : Submodule ℤ E) (R : ℝ) (x : Λ) : ℝ :=
  (1 + max R 0) ^ (finrank ℤ Λ + 1) * ((1 + ‖x‖) ^ (finrank ℤ Λ + 1))⁻¹

theorem summable_latticeMajorant (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R : ℝ) :
    Summable (latticeMajorant Λ R) := by
  apply Summable.mul_left
  have hs := ZLattice.summable_norm_pow_inv (L := Λ) (finrank ℤ Λ + 1) (by omega)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : Λ)).compl_mem_cofinite] with x hx
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  gcongr
  linarith

omit [FiniteDimensional ℝ E] in
/-- Uniform in every full Schwartz test and every shift in the specified ball. -/
theorem norm_shift_le_seminorm_majorant (Λ : Submodule ℤ E) (R : ℝ)
    (f : 𝓢(E, ℂ)) (x : Λ) (a : E) (ha : ‖a‖ ≤ R) :
    ‖f (a + x)‖ ≤ decaySeminorm (finrank ℤ Λ + 1) f * latticeMajorant Λ R x := by
  set k := finrank ℤ Λ + 1
  set R' := max R 0
  have hR : ‖a‖ ≤ R' := ha.trans (le_max_left _ _)
  have hR0 : 0 ≤ R' := le_max_right _ _
  have key : 1 + ‖x‖ ≤ (1 + R') * (1 + ‖a + x‖) := by
    have ht : ‖(x : E)‖ ≤ ‖a + x‖ + ‖a‖ := by
      calc ‖(x : E)‖ = ‖(a + x) - a‖ := by simp
           _ ≤ ‖a + x‖ + ‖a‖ := norm_sub_le _ _
    have ht' : ‖x‖ ≤ ‖a + x‖ + ‖a‖ := ht
    nlinarith [norm_nonneg (a + x)]
  calc ‖f (a + x)‖ ≤ decaySeminorm k f * ((1 + ‖a + x‖) ^ k)⁻¹ :=
        norm_le_decaySeminorm k f _
    _ = decaySeminorm k f * ((1 + R') ^ k * (((1 + R') * (1 + ‖a + x‖)) ^ k)⁻¹) := by
        rw [mul_pow, mul_inv, ← mul_assoc ((1 + R') ^ k), mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ decaySeminorm k f * ((1 + R') ^ k * ((1 + ‖x‖) ^ k)⁻¹) := by
        unfold decaySeminorm
        gcongr
    _ = decaySeminorm k f * latticeMajorant Λ R x := rfl

/-- The actual ideal sum has a single test-independent constant multiplying two Schwartz seminorms. -/
theorem actual_ideal_tsum_seminorm_bound
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (R : ℝ) (f : 𝓢(mixedSpace K, ℂ)) (a : mixedSpace K) (ha : ‖a‖ ≤ R) :
    ‖∑' x : idealLattice K I, f (a + x)‖ ≤
      decaySeminorm (finrank ℤ (idealLattice K I) + 1) f *
        ∑' x : idealLattice K I, latticeMajorant (idealLattice K I) R x := by
  have hf := ConditionalB881.summable_norm_comp_add (idealLattice K I) f a
  have hu := summable_latticeMajorant (idealLattice K I) R
  calc ‖∑' x : idealLattice K I, f (a + x)‖ ≤ ∑' x : idealLattice K I, ‖f (a + x)‖ :=
        norm_tsum_le_tsum_norm hf
    _ ≤ ∑' x : idealLattice K I, decaySeminorm (finrank ℤ (idealLattice K I) + 1) f *
          latticeMajorant (idealLattice K I) R x :=
        hf.tsum_le_tsum (fun x => norm_shift_le_seminorm_majorant _ _ _ _ _ ha) (hu.mul_left _)
    _ = _ := tsum_mul_left

omit [FiniteDimensional ℝ E] in
theorem continuous_decaySeminorm (k : ℕ) : Continuous (decaySeminorm (E := E) k) := by
  exact continuous_const.mul
    (((schwartz_withSeminorms ℝ E ℂ).continuous_seminorm (0, 0)).add
      ((schwartz_withSeminorms ℝ E ℂ).continuous_seminorm (k, 0)))

/-- Continuity in the full mixed Schwartz test, for the actual ideal and every shift. -/
theorem actual_ideal_tsum_test_continuous
    (K : Type*) [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : mixedSpace K) :
    Continuous (fun f : 𝓢(mixedSpace K, ℂ) => ∑' x : idealLattice K I, f (a + x)) := by
  let T : 𝓢(mixedSpace K, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∑' x : idealLattice K I, f (a + x)
      map_add' := by
        intro f g
        change (∑' x : idealLattice K I, (f (a + x) + g (a + x))) = _
        exact (ConditionalB881.summable_norm_comp_add _ f a).of_norm.tsum_add
          (ConditionalB881.summable_norm_comp_add _ g a).of_norm
      map_smul' := by
        intro c f
        change (∑' x : idealLattice K I, c * f (a + x)) = c * _
        exact tsum_mul_left }
  change Continuous T
  apply continuous_of_continuousAt_zero T
  change Tendsto T (𝓝 0) (𝓝 (T 0))
  rw [map_zero]
  apply squeeze_zero_norm (fun f => actual_ideal_tsum_seminorm_bound K I ‖a‖ f a le_rfl)
  have h : Continuous (fun f : 𝓢(mixedSpace K, ℂ) =>
      decaySeminorm (finrank ℤ (idealLattice K I) + 1) f *
        ∑' x : idealLattice K I, latticeMajorant (idealLattice K I) ‖a‖ x) :=
    (continuous_decaySeminorm (E := mixedSpace K)
      (finrank ℤ (idealLattice K I) + 1)).mul continuous_const
  simpa [decaySeminorm] using h.tendsto (0 : 𝓢(mixedSpace K, ℂ))

#print axioms actual_ideal_tsum_seminorm_bound
#print axioms actual_ideal_tsum_test_continuous
end
end ConditionalA885
