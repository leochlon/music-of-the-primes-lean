import Mathlib
/- Source-matched port: alpo ThetaSumAdmissibility.tempered_sum, then a NEW
actual fractional-ideal and arbitrary-shift specialization. -/
attribute [local instance] Classical.propDecidable
open Module Set Filter Topology NumberField NumberField.mixedEmbedding
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
namespace SpectralF909
theorem tempered_sum {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (p : X → E) (w : X → ℂ) (k : ℕ)
    (h : Summable fun x => ‖w x‖ * ((1 + ‖p x‖) ^ k)⁻¹) :
    (∀ f : 𝓢(E, ℂ), Summable fun x => ‖f (p x) * w x‖) ∧
      ∃ T : 𝓢(E, ℂ) →L[ℂ] ℂ, ∀ f : 𝓢(E, ℂ), T f = ∑' x, f (p x) * w x := by
  have hb : ∀ (f : 𝓢(E, ℂ)) (x : X), ‖f (p x) * w x‖ ≤
      (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f) * (‖w x‖ * ((1 + ‖p x‖) ^ k)⁻¹) := by
    intro f x
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f (p x)
    rw [norm_iteratedFDeriv_zero] at h1
    have hp : 0 < (1 + ‖p x‖) ^ k := by positivity
    have h2 : ‖f (p x)‖ ≤ (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f) *
        ((1 + ‖p x‖) ^ k)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact h1
    rw [norm_mul]
    calc _ ≤ (2 ^ k * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ E ℂ) f) * ((1 + ‖p x‖) ^ k)⁻¹ * ‖w x‖ := by
          gcongr
      _ = _ := by ring
  have hs : ∀ f : 𝓢(E, ℂ), Summable fun x => ‖f (p x) * w x‖ := fun f =>
    (h.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) (hb f)
  refine ⟨hs, SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => ∑' x, f (p x) * w x) ?_ ?_ ?_, fun f => rfl⟩
  · intro f g
    rw [← (hs f).of_norm.tsum_add (hs g).of_norm]
    simp [add_mul]
  · intro a f
    simp [← tsum_mul_left, mul_assoc]
  · refine ⟨Finset.Iic (k, 0), 2 ^ k * ∑' x, ‖w x‖ * ((1 + ‖p x‖) ^ k)⁻¹,
      mul_nonneg (by positivity) (tsum_nonneg fun x => by positivity), fun f => ?_⟩
    refine (tsum_of_norm_bounded (h.mul_left _).hasSum (hb f)).trans_eq ?_
    rw [tsum_mul_left]
    ring

/-- The actual ideal lattice supplies the summable weight. Neither summability
nor Schwartz-test continuity is an assumption. -/
theorem actual_ideal_shift_weight
    (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : mixedSpace K) :
    Summable (fun x : idealLattice K I =>
      ((1 + ‖a + (x : mixedSpace K)‖) ^ (finrank ℤ (idealLattice K I) + 1))⁻¹) := by
  let L := idealLattice K I
  let k := finrank ℤ L + 1
  have hs : Summable (fun x : L => ((1 + ‖x‖) ^ k)⁻¹) := by
    have h := ZLattice.summable_norm_pow_inv (L := L) k (by dsimp [k]; omega)
    refine Summable.of_norm_bounded_eventually h ?_
    filter_upwards [(Set.finite_singleton (0 : L)).compl_mem_cofinite] with x hx
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [Real.norm_of_nonneg (by positivity), inv_pow]
    gcongr
    linarith
  refine (hs.mul_left ((1 + ‖a‖) ^ k)).of_nonneg_of_le (fun x => by positivity) ?_
  intro x
  have key : 1 + ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖a + (x : mixedSpace K)‖) := by
    have hn : ‖(x : mixedSpace K)‖ ≤ ‖a + (x : mixedSpace K)‖ + ‖a‖ := by
      calc ‖(x : mixedSpace K)‖ = ‖(a + (x : mixedSpace K)) - a‖ := by simp
        _ ≤ ‖a + (x : mixedSpace K)‖ + ‖a‖ := norm_sub_le _ _
    change 1 + ‖(x : mixedSpace K)‖ ≤ _
    nlinarith [norm_nonneg (a + (x : mixedSpace K)), norm_nonneg a]
  calc
    ((1 + ‖a + (x : mixedSpace K)‖) ^ k)⁻¹ =
        (1 + ‖a‖) ^ k * (((1 + ‖a‖) * (1 + ‖a + (x : mixedSpace K)‖)) ^ k)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ ≤ (1 + ‖a‖) ^ k * ((1 + ‖x‖) ^ k)⁻¹ := by gcongr

/-- Continuous in the full mixed Schwartz TEST, for the arithmetic ideal and
any fixed additive shift. No pure archimedean tensor restriction. -/
theorem actual_ideal_theta_CLM
    (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : mixedSpace K) :
    ∃ T : 𝓢(mixedSpace K, ℂ) →L[ℂ] ℂ,
      ∀ f, T f = ∑' x : idealLattice K I, f (a + (x : mixedSpace K)) := by
  have hs := actual_ideal_shift_weight K I a
  have hw : Summable (fun x : idealLattice K I => ‖(1 : ℂ)‖ *
      ((1 + ‖a + (x : mixedSpace K)‖) ^ (finrank ℤ (idealLattice K I) + 1))⁻¹) := by
    simpa only [norm_one, one_mul] using hs
  obtain ⟨T, hT⟩ := (tempered_sum (fun x : idealLattice K I => a + (x : mixedSpace K))
    (fun _ => (1 : ℂ)) (finrank ℤ (idealLattice K I) + 1) hw).2
  exact ⟨T, fun f => by simpa only [mul_one] using hT f⟩

theorem actual_ideal_theta_continuous_test
    (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : mixedSpace K) :
    Continuous (fun f : 𝓢(mixedSpace K, ℂ) =>
      ∑' x : idealLattice K I, f (a + (x : mixedSpace K))) := by
  obtain ⟨T, hT⟩ := actual_ideal_theta_CLM K I a
  exact T.continuous.congr hT

#print axioms actual_ideal_theta_CLM
#print axioms actual_ideal_theta_continuous_test
end SpectralF909
