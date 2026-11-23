import Mathlib
open NumberField NumberField.mixedEmbedding Filter Topology
open scoped SchwartzMap
noncomputable section
namespace SpectralB909
variable (K : Type*) [Field K] [NumberField K]
local instance : Fintype {w : InfinitePlace K // w.IsReal} := Fintype.ofFinite _
local instance : Fintype {w : InfinitePlace K // w.IsComplex} := Fintype.ofFinite _

def archCount : ℕ := Fintype.card {w : InfinitePlace K // w.IsReal} +
  Fintype.card {w : InfinitePlace K // w.IsComplex}

def control (k : ℕ) (f : 𝓢(mixedSpace K, ℂ)) : ℝ :=
  2 ^ (k * archCount K) *
    (Finset.Iic (k * archCount K, 0)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f

def placeWeight (k : ℕ) (x : mixedSpace K) : ℝ :=
  (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + ‖x.1 w‖) ^ k) *
    ∏ w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖x.2 w‖) ^ k

/-- Explicit all-test product decay on the FULL mixed archimedean Schwartz space.
The right side is one fixed finite Schwartz seminorm, not an arbitrary test-dependent constant.
Adapted from alpo GlobalZetaInfinite.exists_norm_schwartz_le_prod (150--170). -/
theorem mixed_weighted_bound (k : ℕ) (f : 𝓢(mixedSpace K, ℂ)) (x : mixedSpace K) :
    placeWeight K k x * ‖f x‖ ≤ control K k f := by
  have hr : (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + ‖x.1 w‖) ^ k) ≤
      (1 + ‖x‖) ^ (k * Fintype.card {w : InfinitePlace K // w.IsReal}) := by
    calc
      _ ≤ ∏ _w : {w : InfinitePlace K // w.IsReal}, (1 + ‖x‖) ^ k := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro w hw
        exact pow_le_pow_left₀ (by positivity)
          (by linarith [(norm_le_pi_norm x.1 w).trans (norm_fst_le x)]) k
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hc : (∏ w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖x.2 w‖) ^ k) ≤
      (1 + ‖x‖) ^ (k * Fintype.card {w : InfinitePlace K // w.IsComplex}) := by
    calc
      _ ≤ ∏ _w : {w : InfinitePlace K // w.IsComplex}, (1 + ‖x‖) ^ k := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro w hw
        exact pow_le_pow_left₀ (by positivity)
          (by linarith [(norm_le_pi_norm x.2 w).trans (norm_snd_le x)]) k
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hp : placeWeight K k x ≤ (1 + ‖x‖) ^ (k * archCount K) := by
    calc
      _ ≤ (1 + ‖x‖) ^ (k * Fintype.card {w : InfinitePlace K // w.IsReal}) *
          (1 + ‖x‖) ^ (k * Fintype.card {w : InfinitePlace K // w.IsComplex}) :=
        mul_le_mul hr hc (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, ← Nat.mul_add]; rfl
  have hs := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (k * archCount K, 0)) le_rfl le_rfl f x
  rw [norm_iteratedFDeriv_zero] at hs
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hs

/-- Continuity of the explicit controlling seminorm in the actual Schwartz topology.
The finite-sup induction reuses the current conditional_D / spectral_C source pattern. -/
theorem continuous_control (k : ℕ) : Continuous (control K k) := by
  classical
  have hc (s : Finset (ℕ × ℕ)) : Continuous (fun f : 𝓢(mixedSpace K, ℂ) =>
      s.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f) := by
    induction s using Finset.induction_on with
    | empty => simpa using (continuous_const :
        Continuous (fun _ : 𝓢(mixedSpace K, ℂ) => (0 : ℝ)))
    | @insert a s ha ih =>
      simpa only [Finset.sup_insert, Seminorm.sup_apply] using
        ((schwartz_withSeminorms ℝ (mixedSpace K) ℂ).continuous_seminorm a).max ih
  exact continuous_const.mul (hc _)

/-- Schwartz convergence controls the product-weighted difference uniformly over
ALL mixed real/complex inputs. This is the topological form needed to extend
local distribution estimates beyond pure archimedean tensors. -/
theorem uniform_weighted_difference (k : ℕ) (f : 𝓢(mixedSpace K, ℂ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ g in nhds f, ∀ x : mixedSpace K,
      placeWeight K k x * ‖g x - f x‖ < ε := by
  have hC : Continuous (fun g : 𝓢(mixedSpace K, ℂ) => control K k (g - f)) :=
    (continuous_control K k).comp (continuous_id.sub continuous_const)
  have h0 : control K k (f - f) < ε := by simpa [control] using hε
  have hN : {g : 𝓢(mixedSpace K, ℂ) | control K k (g - f) < ε} ∈ nhds f :=
    (isOpen_lt hC continuous_const).mem_nhds h0
  filter_upwards [hN] with g hg
  intro x
  exact lt_of_le_of_lt (by simpa using mixed_weighted_bound K k (g - f) x) hg

#print axioms mixed_weighted_bound
#print axioms continuous_control
#print axioms uniform_weighted_difference
end SpectralB909
