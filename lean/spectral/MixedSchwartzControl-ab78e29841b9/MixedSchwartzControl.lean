import Mathlib
open NumberField NumberField.mixedEmbedding
attribute [local instance] Classical.propDecidable
open scoped SchwartzMap NumberField
noncomputable section
namespace SpectralD909
variable (K : Type*) [Field K] [NumberField K]
def decayOrder (k : ℕ) : ℕ := k *
  (Fintype.card {w : InfinitePlace K // w.IsReal} +
   Fintype.card {w : InfinitePlace K // w.IsComplex})
def testControl (k : ℕ) (f : 𝓢(mixedSpace K, ℂ)) : ℝ :=
  2 ^ decayOrder K k * (SchwartzMap.seminorm ℝ 0 0 f +
    SchwartzMap.seminorm ℝ (decayOrder K k) 0 f)
def placeWeight (k : ℕ) (x : mixedSpace K) : ℝ :=
  (∏ w, (1 + ‖x.1 w‖) ^ k) * (∏ w, (1 + ‖x.2 w‖) ^ k)

theorem norm_le_control (k : ℕ) (f : 𝓢(mixedSpace K, ℂ)) (x : mixedSpace K) :
    ‖f x‖ ≤ testControl K k f * ((1 + ‖x‖) ^ decayOrder K k)⁻¹ := by
  have h1 : ‖f x‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
    simpa using f.norm_pow_mul_le_seminorm ℝ 0 x
  have h2 : ‖x‖ ^ (0 + decayOrder K k) * ‖f x‖ ≤
      SchwartzMap.seminorm ℝ (decayOrder K k) 0 f := by
    simpa using f.norm_pow_mul_le_seminorm ℝ (decayOrder K k) x
  have := pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h1 h2
  simpa [testControl] using this

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

theorem testControl_nonneg (k : ℕ) (f : 𝓢(mixedSpace K, ℂ)) :
    0 ≤ testControl K k f := by
  unfold testControl
  exact mul_nonneg (by positivity) (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))

theorem mixed_schwartz_product_bound (k : ℕ) (f : 𝓢(mixedSpace K, ℂ))
    (x : mixedSpace K) : ‖f x‖ ≤ testControl K k f * (placeWeight K k x)⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (placeWeight_pos K k x)]
  have h := norm_le_control K k f x
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)] at h
  exact (mul_le_mul_of_nonneg_left (placeWeight_le K k x) (norm_nonneg _)).trans h

theorem continuous_testControl (k : ℕ) : Continuous (testControl K k) := by
  have h0 := (schwartz_withSeminorms ℝ (mixedSpace K) ℂ).continuous_seminorm (0, 0)
  have hk := (schwartz_withSeminorms ℝ (mixedSpace K) ℂ).continuous_seminorm
    (decayOrder K k, 0)
  exact continuous_const.mul (h0.add hk)

/-- The mixed product estimate controls test differences uniformly over all
archimedean coordinates, including nondecomposable mixed tests. -/
theorem weighted_test_difference (k : ℕ) (f g : 𝓢(mixedSpace K, ℂ))
    (x : mixedSpace K) : ‖f x - g x‖ * placeWeight K k x ≤ testControl K k (f - g) := by
  have h := mixed_schwartz_product_bound K k (f - g) x
  rw [← div_eq_mul_inv] at h
  exact (le_div_iff₀ (placeWeight_pos K k x)).mp h

#print axioms mixed_schwartz_product_bound
#print axioms continuous_testControl
#print axioms weighted_test_difference
end SpectralD909
