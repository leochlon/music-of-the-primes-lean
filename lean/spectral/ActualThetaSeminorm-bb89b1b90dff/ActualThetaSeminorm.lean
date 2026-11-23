import Mathlib
attribute [local instance] Classical.propDecidable
open MeasureTheory Module Set Filter Topology NumberField NumberField.mixedEmbedding
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
namespace SpectralA909

/-- The explicit witness from alpo LatticePoissonBasic:55–66. -/
theorem schwartz_norm_le_seminorm_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(E, ℂ)) (k : ℕ) (x : E) :
    ‖f x‖ ≤ (2 ^ k * (SchwartzMap.seminorm ℝ 0 0 f +
      SchwartzMap.seminorm ℝ k 0 f)) * ((1 + ‖x‖) ^ k)⁻¹ := by
  have h1 : ‖f x‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
    simpa using f.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + k) * ‖f x‖ ≤ SchwartzMap.seminorm ℝ k 0 f := by
    simpa using f.norm_pow_mul_le_seminorm ℝ k x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa using this

/-- The majorant depends only on the actual ideal lattice, not on the test. -/
theorem actual_ideal_tail_summable
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable (fun x : idealLattice K I =>
      ((1 + ‖(x : mixedSpace K)‖) ^ (finrank ℤ (idealLattice K I) + 1))⁻¹) := by
  let k := finrank ℤ (idealLattice K I) + 1
  have hs := ZLattice.summable_norm_pow_inv (L := idealLattice K I) k (by dsimp [k]; omega)
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLattice K I)).compl_mem_cofinite] with x hx
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [Real.norm_of_nonneg (by positivity), inv_pow]
  gcongr
  change ‖(x : mixedSpace K)‖ ≤ 1 + ‖(x : mixedSpace K)‖
  linarith

/-- Uniform Schwartz-seminorm bound for the actual ideal theta functional.
The quantifier over f follows the choice of C. Full mixed Schwartz tests occur. -/
theorem actual_ideal_theta_seminorm_bound
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓢(mixedSpace K, ℂ),
      ‖∑' x : idealLattice K I, f (x : mixedSpace K)‖ ≤
        C * (SchwartzMap.seminorm ℝ 0 0 f +
          SchwartzMap.seminorm ℝ (finrank ℤ (idealLattice K I) + 1) 0 f) := by
  let k := finrank ℤ (idealLattice K I) + 1
  let u := fun x : idealLattice K I => ((1 + ‖(x : mixedSpace K)‖) ^ k)⁻¹
  have hu : Summable u := actual_ideal_tail_summable K I
  refine ⟨2 ^ k * ∑' x, u x, mul_nonneg (by positivity)
    (tsum_nonneg (fun x => by dsimp [u]; positivity)), ?_⟩
  intro f
  let A := 2 ^ k * (SchwartzMap.seminorm ℝ 0 0 f + SchwartzMap.seminorm ℝ k 0 f)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hf : ∀ x : idealLattice K I, ‖f (x : mixedSpace K)‖ ≤ A * u x :=
    fun x => schwartz_norm_le_seminorm_decay f k x
  have hg : Summable (fun x : idealLattice K I => ‖f (x : mixedSpace K)‖) :=
    (hu.mul_left A).of_nonneg_of_le (fun x => norm_nonneg _) hf
  calc
    ‖∑' x : idealLattice K I, f (x : mixedSpace K)‖ ≤
        ∑' x : idealLattice K I, ‖f (x : mixedSpace K)‖ := norm_tsum_le_tsum_norm hg
    _ ≤ ∑' x : idealLattice K I, A * u x := hg.tsum_le_tsum hf (hu.mul_left A)
    _ = (2 ^ k * ∑' x, u x) * (SchwartzMap.seminorm ℝ 0 0 f +
        SchwartzMap.seminorm ℝ k 0 f) := by rw [tsum_mul_left]; dsimp [A]; ring

#print axioms actual_ideal_theta_seminorm_bound
end SpectralA909
