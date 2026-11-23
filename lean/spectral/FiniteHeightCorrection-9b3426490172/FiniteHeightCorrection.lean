import Mathlib
open scoped BigOperators
namespace ActualZeroCorrection
noncomputable def admittedJets (n : ℕ) (s : ℝ) : ℕ :=
  ((Finset.range n).filter (fun m : ℕ => 2 * (m : ℝ) + 1 < s)).card

theorem admittedJets_le (n : ℕ) (s : ℝ) : admittedJets n s ≤ n := by
  exact (Finset.card_filter_le _ _).trans (by simp)

noncomputable def nativeMultiplicity (f : ℂ → ℂ) (c a s : ℝ)
    (z : {z : ℂ // f z = 0}) : ℕ :=
  if |z.val.re - c| < a then analyticOrderNatAt f z.val
  else if |z.val.re - c| = a then admittedJets (analyticOrderNatAt f z.val) s
  else 0

theorem nativeMultiplicity_le (f : ℂ → ℂ) (c a s : ℝ)
    (z : {z : ℂ // f z = 0}) :
    nativeMultiplicity f c a s z ≤ analyticOrderNatAt f z.val := by
  unfold nativeMultiplicity
  split_ifs
  · exact le_rfl
  · exact admittedJets_le _ _
  · exact Nat.zero_le _

/-- Actual finite zero divisor; the missing coefficient is derived, not postulated. -/
theorem finite_actual_correction (f : ℂ → ℂ) (c a s : ℝ)
    (u : Finset {z : ℂ // f z = 0}) (T : {z : ℂ // f z = 0} → ℂ) :
    (∑ z ∈ u, (analyticOrderNatAt f z.val : ℂ) * T z) =
      (∑ z ∈ u, (nativeMultiplicity f c a s z : ℂ) * T z) +
      ∑ z ∈ u, ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Nat.cast_sub (nativeMultiplicity_le f c a s z)]
  ring

/-- Strict boundary admission persists at a zero-width window, counted only once. -/
theorem zero_width_native (f : ℂ → ℂ) (c s : ℝ)
    (z : {z : ℂ // f z = 0}) (hz : z.val.re = c) :
    nativeMultiplicity f c 0 s z = admittedJets (analyticOrderNatAt f z.val) s := by
  simp [nativeMultiplicity, hz]

/-- Boundary-free widths retain the entire exterior multiplicity. -/
theorem exterior_omitted (f : ℂ → ℂ) (c a s : ℝ)
    (z : {z : ℂ // f z = 0}) (hz : a < |z.val.re - c|) :
    analyticOrderNatAt f z.val - nativeMultiplicity f c a s z = analyticOrderNatAt f z.val := by
  unfold nativeMultiplicity
  rw [if_neg (not_lt_of_ge hz.le), if_neg (ne_of_gt hz), Nat.sub_zero]

theorem native_norm_le (f : ℂ → ℂ) (c a s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ) (z : {z : ℂ // f z = 0}) :
    ‖(nativeMultiplicity f c a s z : ℂ) * T z‖ ≤
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖ := by
  simp only [norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast nativeMultiplicity_le f c a s z)
    (norm_nonneg _)

/-- Absolute convergence of the genuine full divisor yields the native and
omitted series with no assumption that either correction vanishes. -/
theorem actual_tsum_correction (f : ℂ → ℂ) (c a s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ)
    (habs : Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖)) :
    (∑' z : {z : ℂ // f z = 0}, (analyticOrderNatAt f z.val : ℂ) * T z) =
      (∑' z : {z : ℂ // f z = 0}, (nativeMultiplicity f c a s z : ℂ) * T z) +
      ∑' z : {z : ℂ // f z = 0},
        ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z := by
  have hn : Summable (fun z : {z : ℂ // f z = 0} =>
      (nativeMultiplicity f c a s z : ℂ) * T z) :=
    Summable.of_norm_bounded habs (native_norm_le f c a s T)
  have hf : Summable (fun z : {z : ℂ // f z = 0} =>
      (analyticOrderNatAt f z.val : ℂ) * T z) := habs.of_norm
  have he : (fun z : {z : ℂ // f z = 0} =>
      ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z) =
      fun z => (analyticOrderNatAt f z.val : ℂ) * T z -
        (nativeMultiplicity f c a s z : ℂ) * T z := by
    funext z
    rw [Nat.cast_sub (nativeMultiplicity_le f c a s z)]
    ring
  rw [he, hf.tsum_sub hn]
  abel

/-- Exact arithmetic correction after matching the genuine full-divisor formula.
This is conditional on that formula; it does not prove it or cancel its remainder. -/
theorem corrected_arithmetic (f : ℂ → ℂ) (c a s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ)
    (habs : Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖))
    (G poles : ℂ)
    (hfull : G = poles - ∑' z : {z : ℂ // f z = 0},
      (analyticOrderNatAt f z.val : ℂ) * T z) :
    G = poles - (∑' z : {z : ℂ // f z = 0},
        (nativeMultiplicity f c a s z : ℂ) * T z) -
      ∑' z : {z : ℂ // f z = 0},
        ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z := by
  rw [hfull, actual_tsum_correction f c a s T habs]
  ring

/-- Comparing widths preserves the correction difference instead of assuming
strip independence. The center and boundary regularity are unrestricted. -/
theorem native_width_difference (f : ℂ → ℂ) (c a b s : ℝ)
    (T : {z : ℂ // f z = 0} → ℂ)
    (habs : Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * T z‖)) :
    (∑' z : {z : ℂ // f z = 0}, (nativeMultiplicity f c b s z : ℂ) * T z) -
      (∑' z : {z : ℂ // f z = 0}, (nativeMultiplicity f c a s z : ℂ) * T z) =
    (∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - nativeMultiplicity f c a s z : ℕ) : ℂ) * T z) -
    ∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - nativeMultiplicity f c b s z : ℕ) : ℂ) * T z := by
  have ha := actual_tsum_correction f c a s T habs
  have hb := actual_tsum_correction f c b s T habs
  linear_combination ha - hb

#print axioms corrected_arithmetic
#print axioms native_width_difference
#print axioms finite_actual_correction
#print axioms zero_width_native
#print axioms exterior_omitted
#print axioms actual_tsum_correction
end ActualZeroCorrection


namespace FiniteHeightRepairE
open Filter Topology
theorem finite_entire_zeros_in_closedBall {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c : ℂ) (R : ℝ) :
    ({z | f z = 0} ∩ Metric.closedBall c R).Finite := by
  by_contra h
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact
    h (isCompact_closedBall c R) Set.inter_subset_right
  have hfreq : ∃ᶠ y in 𝓝[≠] z, f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hacc).mono fun _ hy => hy.1
  have ha : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  exact hx (ha.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ z) hfreq (Set.mem_univ x))


/-- Height truncations of a genuine entire zero divisor are finite when the
zero set is confined to a horizontal strip. No infinite divisor sum is assumed. -/
theorem height_zero_set_finite {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W) :
    {z : {z : ℂ // f z = 0} | |z.val.im| ≤ H}.Finite := by
  have hbig := (finite_entire_zeros_in_closedBall hf hx (c : ℂ) (|W| + |H|)).preimage
    (f := fun z : {z : ℂ // f z = 0} => z.val) Subtype.val_injective.injOn
  apply hbig.subset
  intro z hz
  refine ⟨z.property, Metric.mem_closedBall.mpr ?_⟩
  rw [dist_eq_norm]
  have hn := Complex.norm_le_abs_re_add_abs_im (z.val - (c : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im,
    Complex.ofReal_im, sub_zero] at hn
  have hs := hstrip z.val z.property
  have hW := le_abs_self W
  have hH := le_abs_self H
  change |z.val.im| ≤ H at hz
  linarith

theorem height_weight_summable {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    Summable (fun z : {z : ℂ // f z = 0} =>
      ‖(analyticOrderNatAt f z.val : ℂ) * (if |z.val.im| ≤ H then T z else 0)‖) := by
  apply summable_of_finite_support
  apply (height_zero_set_finite hf hx c W H hstrip).subset
  intro z hz
  by_contra hn
  change ¬ |z.val.im| ≤ H at hn
  simp [Function.mem_support, hn] at hz

/-- Exact finite-height native/full correction, with true multiplicities and
strict admitted boundary jets. Applicable to either actual transform T. -/
theorem actual_height_correction {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H a s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    (∑' z : {z : ℂ // f z = 0}, (analyticOrderNatAt f z.val : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) =
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) +
    ∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c a s z : ℕ) : ℂ) *
        (if |z.val.im| ≤ H then T z else 0) := by
  exact ActualZeroCorrection.actual_tsum_correction f c a s
    (fun z => if |z.val.im| ≤ H then T z else 0)
    (height_weight_summable hf hx c W H hstrip T)

/-- The exact native correction difference is already valid at finite height;
no assertion of equal raw strip limits is used. -/
theorem actual_height_width_difference {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0) (c W H a b s : ℝ)
    (hstrip : ∀ z : ℂ, f z = 0 → |z.re - c| ≤ W)
    (T : {z : ℂ // f z = 0} → ℂ) :
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c b s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) -
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) =
    (∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c a s z : ℕ) : ℂ) *
        (if |z.val.im| ≤ H then T z else 0)) -
    ∑' z : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f z.val - ActualZeroCorrection.nativeMultiplicity f c b s z : ℕ) : ℂ) *
        (if |z.val.im| ≤ H then T z else 0) := by
  exact ActualZeroCorrection.native_width_difference f c a b s
    (fun z => if |z.val.im| ≤ H then T z else 0)
    (height_weight_summable hf hx c W H hstrip T)

/-- Free boundaries identify the native finite-height sum with the original
strict raw strip sum. The exterior correction is not set to zero. -/
theorem boundary_free_native_height (f : ℂ → ℂ) (c a s H : ℝ)
    (hfree : ∀ z : ℂ, f z = 0 → |z.re - c| ≠ a)
    (T : {z : ℂ // f z = 0} → ℂ) :
    (∑' z : {z : ℂ // f z = 0}, (ActualZeroCorrection.nativeMultiplicity f c a s z : ℂ) *
      (if |z.val.im| ≤ H then T z else 0)) =
    ∑' z : {z : ℂ // f z = 0},
      if |z.val.re - c| < a ∧ |z.val.im| ≤ H
      then (analyticOrderNatAt f z.val : ℂ) * T z else 0 := by
  apply tsum_congr
  intro z
  by_cases hi : |z.val.re - c| < a <;>
    by_cases ht : |z.val.im| ≤ H <;>
    simp [ActualZeroCorrection.nativeMultiplicity, hi, ht, hfree z.val z.property]

#print axioms height_zero_set_finite
#print axioms height_weight_summable
#print axioms actual_height_correction
#print axioms actual_height_width_difference
#print axioms boundary_free_native_height
end FiniteHeightRepairE
