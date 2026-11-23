import Mathlib
open scoped SchwartzMap
open Finset

namespace SpectralC12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual finite Schwartz-seminorm bound used inside alpo's
`exists_norm_schwartz_le_prod`, exposed uniformly in the test. -/
noncomputable def decayControl (k : ℕ) (f : 𝓢(E, ℂ)) : ℝ :=
  2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

theorem decayControl_nonneg (k : ℕ) (f : 𝓢(E, ℂ)) : 0 ≤ decayControl k f := by
  unfold decayControl
  positivity

theorem uniform_schwartz_decay (k : ℕ) (f : 𝓢(E, ℂ)) (x : E) :
    (1 + ‖x‖) ^ k * ‖f x‖ ≤ decayControl k f := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero] at h
  exact h

/-- Full mixed archimedean tests are arbitrary joint Schwartz functions.
The bound is uniform in f and does not impose a pure-tensor hypothesis. -/
theorem uniform_mixed_schwartz_decay
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (f : 𝓢((ι → ℝ) × (κ → ℂ), ℂ))
    (x : (ι → ℝ) × (κ → ℂ)) :
    ‖f x‖ * ((∏ i, (1 + ‖x.1 i‖) ^ k) * (∏ j, (1 + ‖x.2 j‖) ^ k)) ≤
      decayControl (k * (Fintype.card ι + Fintype.card κ)) f := by
  classical
  have hR (i : ι) : ‖x.1 i‖ ≤ ‖x‖ :=
    (norm_le_pi_norm x.1 i).trans (norm_fst_le x)
  have hC (j : κ) : ‖x.2 j‖ ≤ ‖x‖ :=
    (norm_le_pi_norm x.2 j).trans (norm_snd_le x)
  have hRp : (∏ i, (1 + ‖x.1 i‖) ^ k) ≤ (1 + ‖x‖) ^ (k * Fintype.card ι) := by
    calc
      _ ≤ ∏ _i : ι, (1 + ‖x‖) ^ k :=
        Finset.prod_le_prod (fun i _ => by positivity) (fun i _ =>
          pow_le_pow_left₀ (by positivity) (by linarith [hR i]) k)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hCp : (∏ j, (1 + ‖x.2 j‖) ^ k) ≤ (1 + ‖x‖) ^ (k * Fintype.card κ) := by
    calc
      _ ≤ ∏ _j : κ, (1 + ‖x‖) ^ k :=
        Finset.prod_le_prod (fun j _ => by positivity) (fun j _ =>
          pow_le_pow_left₀ (by positivity) (by linarith [hC j]) k)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hp : ((∏ i, (1 + ‖x.1 i‖) ^ k) * (∏ j, (1 + ‖x.2 j‖) ^ k)) ≤
      (1 + ‖x‖) ^ (k * (Fintype.card ι + Fintype.card κ)) := by
    calc
      _ ≤ (1 + ‖x‖) ^ (k * Fintype.card ι) *
          (1 + ‖x‖) ^ (k * Fintype.card κ) :=
        mul_le_mul hRp hCp (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, ← Nat.mul_add]
  calc
    _ ≤ ‖f x‖ * (1 + ‖x‖) ^ (k * (Fintype.card ι + Fintype.card κ)) :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = (1 + ‖x‖) ^ (k * (Fintype.card ι + Fintype.card κ)) * ‖f x‖ := mul_comm _ _
    _ ≤ _ := uniform_schwartz_decay _ f x



/-- The controlling finite seminorm varies continuously in the genuine Schwartz topology. -/
theorem continuous_decayControl (k : ℕ) : Continuous (decayControl (E := E) k) := by
  classical
  have hc (s : Finset (ℕ × ℕ)) : Continuous (fun f : 𝓢(E, ℂ) =>
      s.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) := by
    induction s using Finset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : 𝓢(E, ℂ) => (0 : ℝ)))
    | @insert a s ha ih =>
      simpa only [Finset.sup_insert, Seminorm.sup_apply] using
        ((schwartz_withSeminorms ℝ E ℂ).continuous_seminorm a).max ih
  exact continuous_const.mul (hc _)

open MeasureTheory
/-- A uniform seminorm bound for actual weighted integrals of every Schwartz test.
The remaining kernel integrability is independent of f. The measure is unchanged. -/
theorem norm_integral_mul_le_decay [MeasurableSpace E]
    (μ : Measure E) (k : ℕ) (f : 𝓢(E, ℂ)) (w : E → ℂ)
    (hw : Integrable (fun x => ‖w x‖ / (1 + ‖x‖) ^ k) μ)
    (hm : AEStronglyMeasurable (fun x => f x * w x) μ) :
    ‖∫ x, f x * w x ∂μ‖ ≤
      decayControl k f * ∫ x, ‖w x‖ / (1 + ‖x‖) ^ k ∂μ := by
  have hp (x : E) : ‖f x * w x‖ ≤ decayControl k f * (‖w x‖ / (1 + ‖x‖) ^ k) := by
    have hpos : 0 < (1 + ‖x‖) ^ k := by positivity
    have hb : ‖f x‖ ≤ decayControl k f / (1 + ‖x‖) ^ k := by
      apply (le_div_iff₀ hpos).2
      simpa only [mul_comm] using uniform_schwartz_decay k f x
    calc
      _ = ‖f x‖ * ‖w x‖ := norm_mul _ _
      _ ≤ (decayControl k f / (1 + ‖x‖) ^ k) * ‖w x‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ = _ := by ring
  have hd := hw.const_mul (decayControl k f)
  have hi : Integrable (fun x => f x * w x) μ := hd.mono' hm (Filter.Eventually.of_forall hp)
  calc
    _ ≤ ∫ x, ‖f x * w x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, decayControl k f * (‖w x‖ / (1 + ‖x‖) ^ k) ∂μ :=
      integral_mono_ae hi.norm hd (Filter.Eventually.of_forall hp)
    _ = _ := integral_const_mul _ _

#print axioms uniform_mixed_schwartz_decay
#print axioms continuous_decayControl
#print axioms norm_integral_mul_le_decay
end SpectralC12
