import Mathlib
open scoped SchwartzMap
open NumberField
noncomputable section
namespace ConditionalD885
variable {R C : Type*} [Fintype R] [Fintype C]
abbrev Mixed (R C : Type*) := (R → ℝ) × (C → ℂ)
def mixedDecayBound (k : ℕ) (φ : 𝓢(Mixed R C, ℂ)) : ℝ :=
  2 ^ (k * (Fintype.card R + Fintype.card C)) *
    (Finset.Iic (k * (Fintype.card R + Fintype.card C), 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ

theorem mixed_weighted_bound (k : ℕ) (φ : 𝓢(Mixed R C, ℂ)) (x : Mixed R C) :
    ‖φ x‖ * ((∏ r, (1 + ‖x.1 r‖) ^ k) * (∏ c, (1 + ‖x.2 c‖) ^ k)) ≤
      mixedDecayBound k φ := by
  have hr : (∏ r, (1 + ‖x.1 r‖) ^ k) ≤
      (1 + ‖x‖) ^ (k * Fintype.card R) := by
    calc
      _ ≤ ∏ _r : R, (1 + ‖x‖) ^ k :=
        Finset.prod_le_prod (fun _ _ => by positivity) fun r _ =>
          pow_le_pow_left₀ (by positivity)
            (by linarith [norm_le_pi_norm x.1 r, norm_fst_le x]) k
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hc : (∏ c, (1 + ‖x.2 c‖) ^ k) ≤
      (1 + ‖x‖) ^ (k * Fintype.card C) := by
    calc
      _ ≤ ∏ _c : C, (1 + ‖x‖) ^ k :=
        Finset.prod_le_prod (fun _ _ => by positivity) fun c _ =>
          pow_le_pow_left₀ (by positivity)
            (by linarith [norm_le_pi_norm x.2 c, norm_snd_le x]) k
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hp : (∏ r, (1 + ‖x.1 r‖) ^ k) * (∏ c, (1 + ‖x.2 c‖) ^ k) ≤
      (1 + ‖x‖) ^ (k * (Fintype.card R + Fintype.card C)) := by
    calc
      _ ≤ (1 + ‖x‖) ^ (k * Fintype.card R) *
          (1 + ‖x‖) ^ (k * Fintype.card C) :=
        mul_le_mul hr hc (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, ← Nat.mul_add]
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (k * (Fintype.card R + Fintype.card C), 0)) le_rfl le_rfl φ x
  rw [norm_iteratedFDeriv_zero] at h
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by
    simpa [mixedDecayBound, mul_comm] using h)

theorem continuous_mixedDecayBound (k : ℕ) :
    Continuous (mixedDecayBound (R := R) (C := C) k) := by
  have hs : ∀ s : Finset (ℕ × ℕ), Continuous (fun φ : 𝓢(Mixed R C, ℂ) =>
      s.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (continuous_const : Continuous (fun _ : 𝓢(Mixed R C, ℂ) => (0 : ℝ)))
    | @insert a s ha ih =>
      have h := (schwartz_withSeminorms ℝ (Mixed R C) ℂ).continuous_seminorm a
      simpa only [Finset.sup_insert, Seminorm.sup_apply] using h.max ih
  exact continuous_const.mul (hs _)

def complexDecayBound (n : ℕ) (φ : 𝓢(ℂ, ℂ)) : ℝ :=
  2 ^ n * (Finset.Iic (n, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ

/-- Uniform Schwartz control for every logarithmic Mellin weight on the complex tail.
The extra factor 2 is log of the complex normalized absolute value |z|_C=|z|². -/
theorem complex_log_mellin_tail_bound (k m : ℕ) (φ : 𝓢(ℂ, ℂ)) (z : ℂ)
    (hz : 1 ≤ ‖z‖) :
    ‖φ z‖ * ‖z‖ ^ k * (2 * Real.log ‖z‖) ^ m ≤
      (2 : ℝ) ^ m * complexDecayBound (k + m + 3) φ / (1 + ‖z‖) ^ 3 := by
  have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
  have hlog' : Real.log ‖z‖ ≤ 1 + ‖z‖ := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < ‖z‖)]
  have hk : ‖z‖ ^ k ≤ (1 + ‖z‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg z) (by linarith) k
  have hm : (2 * Real.log ‖z‖) ^ m ≤ 2 ^ m * (1 + ‖z‖) ^ m := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) m
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (k + m + 3, 0)) le_rfl le_rfl φ z
  rw [norm_iteratedFDeriv_zero] at h
  rw [le_div_iff₀ (by positivity : 0 < (1 + ‖z‖) ^ 3)]
  calc
    _ ≤ (‖φ z‖ * (1 + ‖z‖) ^ k * (2 ^ m * (1 + ‖z‖) ^ m)) *
        (1 + ‖z‖) ^ 3 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hk (norm_nonneg _)) hm
          (by positivity) (by positivity)) (by positivity)
    _ = 2 ^ m * ((1 + ‖z‖) ^ (k + m + 3) * ‖φ z‖) := by
      simp only [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

#print axioms mixed_weighted_bound
#print axioms continuous_mixedDecayBound
#print axioms complex_log_mellin_tail_bound
end ConditionalD885
