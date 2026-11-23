import Mathlib
attribute [local instance] Classical.propDecidable
open NumberField NumberField.mixedEmbedding Filter Topology Set
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
namespace FollowupB639
variable (K : Type*) [Field K] [NumberField K]
local instance : Fintype {w : InfinitePlace K // w.IsReal} := Fintype.ofFinite _
local instance : Fintype {w : InfinitePlace K // w.IsComplex} := Fintype.ofFinite _

/-- A uniform TEST-SEMINORM estimate for the actual nonzero ideal theta sum.
The constant and seminorm order are chosen before the arbitrary mixed Schwartz
function, and hold uniformly for all large positive diagonal dilations.
Proof-level reuse: FollowupA636.actual_ideal_dilation_decay, with the hidden
per-test constant replaced by the explicit Schwartz seminorm. -/
theorem actual_ideal_dilation_uniform
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : ℕ) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(mixedSpace K, ℂ), ∀ t : ℝ, 1 ≤ t →
      Summable (fun x : {x : idealLattice K I // x ≠ 0} =>
        ‖f (t • (x.val : mixedSpace K))‖) ∧
      (∑' x : {x : idealLattice K I // x ≠ 0},
        ‖f (t • (x.val : mixedSpace K))‖) ≤
        C * SchwartzMap.seminorm ℝ k 0 f * (t ^ N)⁻¹ := by
  let L := idealLattice K I
  let J := {x : L // x ≠ 0}
  let k := Module.finrank ℤ L + N + 1
  let b : J → ℝ := fun x => ‖(x.val : mixedSpace K)‖⁻¹ ^ k
  have hb : Summable b := by
    have h := (ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)).subtype
      {x : L | x ≠ 0}
    exact h
  refine ⟨k, ∑' x : J, b x, tsum_nonneg (fun x => by dsimp [b]; positivity), ?_⟩
  intro f t ht
  let S : ℝ := SchwartzMap.seminorm ℝ k 0 f
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hmajor (x : J) :
      ‖f (t • (x.val : mixedSpace K))‖ ≤ (S * (t ^ N)⁻¹) * b x := by
    have hx : (x.val : mixedSpace K) ≠ 0 := by
      intro h
      apply x.property
      exact Subtype.ext h
    have hnx : 0 < ‖(x.val : mixedSpace K)‖ := norm_pos_iff.mpr hx
    have hs := f.norm_pow_mul_le_seminorm ℝ k (t • (x.val : mixedSpace K))
    rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow] at hs
    have hNk : t ^ N ≤ t ^ k := pow_le_pow_right₀ ht (by dsimp [k]; omega)
    have hs' : ‖f (t • (x.val : mixedSpace K))‖ *
        (t ^ N * ‖(x.val : mixedSpace K)‖ ^ k) ≤ S := by
      calc
        _ ≤ t ^ k * ‖(x.val : mixedSpace K)‖ ^ k *
            ‖f (t • (x.val : mixedSpace K))‖ := by
          nlinarith [mul_le_mul_of_nonneg_right hNk
            (mul_nonneg (pow_nonneg hnx.le k) (norm_nonneg (f (t • (x.val : mixedSpace K)))))]
        _ ≤ S := hs
    have he : (S * (t ^ N)⁻¹) * b x =
        S / (t ^ N * ‖(x.val : mixedSpace K)‖ ^ k) := by
      simp only [b, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    rw [he]
    exact (le_div_iff₀ (mul_pos (pow_pos ht0 N) (pow_pos hnx k))).mpr hs'
  have hb' : Summable (fun x : J => (S * (t ^ N)⁻¹) * b x) :=
    hb.mul_left _
  have hf : Summable (fun x : J => ‖f (t • (x.val : mixedSpace K))‖) :=
    hb'.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' x : J, (S * (t ^ N)⁻¹) * b x := hf.tsum_le_tsum hmajor hb'
    _ = (∑' x : J, b x) * S * (t ^ N)⁻¹ := by
      rw [hb.tsum_mul_left]
      ring

/-- Arbitrarily small Schwartz tests have uniformly small rapid-decay
ideal theta tails. This is test-topology control, uniformly for every t ≥ 1. -/
theorem actual_ideal_dilation_test_control
    (K : Type*) [Field K] [NumberField K]
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : ℕ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ f : 𝓢(mixedSpace K, ℂ) in 𝓝 0,
        ∀ t : ℝ, 1 ≤ t →
          (∑' x : {x : idealLattice K I // x ≠ 0},
            ‖f (t • (x.val : mixedSpace K))‖) ≤ ε * (t ^ N)⁻¹ := by
  obtain ⟨k, C, hC, hbound⟩ := actual_ideal_dilation_uniform K I N
  have hp : Continuous (fun f : 𝓢(mixedSpace K, ℂ) =>
      C * SchwartzMap.seminorm ℝ k 0 f) :=
    continuous_const.mul ((schwartz_withSeminorms ℝ (mixedSpace K) ℂ).continuous_seminorm (k, 0))
  intro ε hε
  have hsmall : ∀ᶠ f : 𝓢(mixedSpace K, ℂ) in 𝓝 0,
      C * SchwartzMap.seminorm ℝ k 0 f < ε := by
    have h := hp.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (show C * SchwartzMap.seminorm ℝ k 0 (0 : 𝓢(mixedSpace K, ℂ)) < ε by simpa))
    exact h
  filter_upwards [hsmall] with f hf
  intro t ht
  exact (hbound f t ht).2.trans
    (mul_le_mul_of_nonneg_right hf.le (by positivity))

#print axioms actual_ideal_dilation_uniform
#print axioms actual_ideal_dilation_test_control
end FollowupB639
