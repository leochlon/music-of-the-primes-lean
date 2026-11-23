import Mathlib
open NumberField NumberField.mixedEmbedding
attribute [local instance] Classical.propDecidable
open scoped SchwartzMap NumberField
noncomputable section
namespace SpectralH909
variable (K : Type*) [Field K] [NumberField K]
-- Coordinate weight lemmas reused verbatim from spectral_D/MixedSchwartzControl.lean.
-- New extension below controls every real Frechet derivative of arbitrary mixed tests.
def decayOrder (k : ℕ) : ℕ := k *
  (Fintype.card {w : InfinitePlace K // w.IsReal} +
   Fintype.card {w : InfinitePlace K // w.IsComplex})
def placeWeight (k : ℕ) (x : mixedSpace K) : ℝ :=
  (∏ w, (1 + ‖x.1 w‖) ^ k) * (∏ w, (1 + ‖x.2 w‖) ^ k)

theorem placeWeight_pos (k : ℕ) (x : mixedSpace K) : 0 < placeWeight K k x := by
  unfold placeWeight
  apply mul_pos <;> apply Finset.prod_pos <;> intros <;> positivity

theorem placeWeight_le (k : ℕ) (x : mixedSpace K) :
    placeWeight K k x ≤ (1 + ‖x‖) ^ decayOrder K k := by
  have hr : (∏ w, (1 + ‖x.1 w‖) ^ k) ≤
      ∏ _w : {w : InfinitePlace K // w.IsReal}, (1 + ‖x‖) ^ k := by
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro w _
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [le_trans (norm_le_pi_norm x.1 w) (norm_fst_le x)]) k
  have hc : (∏ w, (1 + ‖x.2 w‖) ^ k) ≤
      ∏ _w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖x‖) ^ k := by
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro w _
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [le_trans (norm_le_pi_norm x.2 w) (norm_snd_le x)]) k
  calc placeWeight K k x ≤
      (∏ _w : {w : InfinitePlace K // w.IsReal}, (1 + ‖x‖) ^ k) *
      (∏ _w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖x‖) ^ k) := by
        exact mul_le_mul hr hc (by positivity) (by positivity)
    _ = (1 + ‖x‖) ^ decayOrder K k := by
      simp only [Finset.prod_const, Finset.card_univ, ← pow_mul, ← pow_add, decayOrder]
      congr 1
      ring


def jetControl (k j : ℕ) (f : 𝓢(mixedSpace K, ℂ)) : ℝ :=
  2 ^ decayOrder K k * (Finset.Iic (decayOrder K k, j)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

theorem mixed_jet_product_bound (k j : ℕ) (f : 𝓢(mixedSpace K, ℂ))
    (x : mixedSpace K) :
    ‖iteratedFDeriv ℝ j (⇑f) x‖ ≤ jetControl K k j f * (placeWeight K k x)⁻¹ := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (decayOrder K k, j)) le_rfl le_rfl f x
  rw [← div_eq_mul_inv, le_div_iff₀ (placeWeight_pos K k x)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ j (⇑f) x‖ * (1 + ‖x‖) ^ decayOrder K k :=
      mul_le_mul_of_nonneg_left (placeWeight_le K k x) (norm_nonneg _)
    _ = (1 + ‖x‖) ^ decayOrder K k * ‖iteratedFDeriv ℝ j (⇑f) x‖ := mul_comm _ _
    _ ≤ jetControl K k j f := h

theorem continuous_jetControl (k j : ℕ) : Continuous (jetControl K k j) := by
  have hs : ∀ s : Finset (ℕ × ℕ), Continuous (fun f : 𝓢(mixedSpace K, ℂ) =>
      s.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : 𝓢(mixedSpace K, ℂ) => (0 : ℝ)))
    | @insert a s ha ih =>
      have h := (schwartz_withSeminorms ℝ (mixedSpace K) ℂ).continuous_seminorm a
      simpa only [Finset.sup_insert, Seminorm.sup_apply] using h.max ih
  exact continuous_const.mul (hs _)

#print axioms mixed_jet_product_bound
#print axioms continuous_jetControl
end SpectralH909
