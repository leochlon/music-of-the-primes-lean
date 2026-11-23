import Mathlib

/- Haar shell change of variables ported from Fermat's
S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq, lines 577–601.
The remaining statements calculate the precise local arithmetic weight.
They do not assert an identification with the global theta projection. -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory
open scoped Pointwise
namespace ActualLocalShell

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

theorem integral_shell (μ : Measure G) [μ.IsMulLeftInvariant]
    {U : Set G} (hU : MeasurableSet U) (g : G) (f : G → ℂ) :
    ∫ x in g • U, f x ∂μ = ∫ u in U, f (g * u) ∂μ := by
  have hgU : MeasurableSet (g • U) := hU.const_smul g
  rw [← integral_indicator hgU, ← integral_indicator hU,
    ← integral_mul_left_eq_self _ g]
  congr 1
  funext u
  have hiff : g * u ∈ g • U ↔ u ∈ U := by
    constructor
    · intro h
      obtain ⟨u', hu', h'⟩ := Set.mem_smul_set.mp h
      rw [smul_eq_mul] at h'
      rw [← mul_left_cancel h']
      exact hu'
    · intro hu
      exact Set.mem_smul_set.mpr ⟨u, hu, rfl⟩
  simp only [Set.indicator]
  by_cases hu : u ∈ U
  · rw [if_pos (hiff.mpr hu), if_pos hu]
  · rw [if_neg (mt hiff.mp hu), if_neg hu]

/-- The normalized nonarchimedean local density off the unit shell. -/
theorem local_density (t : ℝ) :
    Real.exp (t / 2) / max 1 (Real.exp t) = Real.exp (-|t| / 2) := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (Real.one_le_exp_iff.mpr ht), ← Real.exp_sub,
      abs_of_nonneg ht]
    congr 1
    ring
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    rw [max_eq_left (Real.exp_le_one_iff.mpr ht'), div_one, abs_of_nonpos ht']
    congr 1
    ring

theorem shell_weight (L : ℝ) (hL : 0 ≤ L) (n : ℤ) :
    Real.exp (-|-(n : ℝ) * L| / 2) =
      Real.exp (-|(n : ℝ)| * L / 2) := by
  rw [abs_mul, abs_neg, abs_of_nonneg hL]
  congr 1
  ring

/-- Exact weighted shell integral, retaining the given Haar measure. In the
application G=K_v^×, U=O_v^×, L=log q_v and ell=log |.|_v. -/
theorem weighted_shell (μ : Measure G) [μ.IsMulLeftInvariant]
    {U : Set G} (hU : MeasurableSet U) (π : G) (n : ℤ)
    (L : ℝ) (hL : 0 ≤ L) (ell : G → ℝ) (h : G → ℂ)
    (hell : ∀ u ∈ U, ell (π ^ n * u) = -(n : ℝ) * L) :
    (∫ x in (π ^ n) • U, (Real.exp (-|ell x| / 2) : ℂ) * h x ∂μ) =
      (Real.exp (-|(n : ℝ)| * L / 2) : ℂ) *
        ∫ u in U, h (π ^ n * u) ∂μ := by
  rw [integral_shell μ hU]
  calc
    _ = ∫ u in U, (Real.exp (-|(n : ℝ)| * L / 2) : ℂ) * h (π ^ n * u) ∂μ := by
      apply setIntegral_congr_fun hU
      intro u hu
      dsimp only
      rw [hell u hu, shell_weight L hL n]
    _ = _ := integral_const_mul _ _

/-- Applying the logarithmic test multiplies the n-th shell average by n log q.
This is the sign from (ell phi)# = -ell phi# for inversion conventions. -/
theorem logged_shell (μ : Measure G) {U : Set G} (hU : MeasurableSet U)
    (π : G) (n : ℤ) (L : ℝ) (ell : G → ℝ) (h : G → ℂ)
    (hell : ∀ u ∈ U, ell (π ^ n * u) = -(n : ℝ) * L) :
    (∫ u in U, (-(ell (π ^ n * u)) : ℂ) * h (π ^ n * u) ∂μ) =
      ((n : ℝ) * L : ℂ) * ∫ u in U, h (π ^ n * u) ∂μ := by
  calc
    _ = ∫ u in U, ((n : ℝ) * L : ℂ) * h (π ^ n * u) ∂μ := by
      apply setIntegral_congr_fun hU
      intro u hu
      dsimp only
      rw [hell u hu]
      push_cast
      ring
    _ = _ := integral_const_mul _ _

theorem local_haar_cancellation (L mass : ℂ) (hmass : mass ≠ 0) (average : ℂ) :
    (L / mass) * (mass * average) = L * average := by
  field_simp

theorem norm_one_sub {F : Type*} [NormedField F] [IsUltrametricDist F]
    (x : F) (hx : ‖x‖ ≠ 1) : ‖1 - x‖ = max 1 ‖x‖ := by
  have hu : ‖1 - x‖ ≤ max 1 ‖x‖ := by
    simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max (1 : F) (-x)
  have h1 : 1 ≤ max ‖1 - x‖ ‖x‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (1 - x) x
  have h2 : ‖x‖ ≤ max 1 ‖1 - x‖ := by
    calc
      ‖x‖ = ‖(1 : F) - (1 - x)‖ := by congr 1; ring
      _ ≤ max 1 ‖1 - x‖ := by
        rw [sub_eq_add_neg]
        simpa only [norm_one, norm_neg] using
          IsUltrametricDist.norm_add_le_max (1 : F) (-(1 - x))
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · rw [max_eq_left hlt.le] at hu ⊢
    exact le_antisymm hu (le_of_not_gt fun hz =>
      (not_lt_of_ge h1) (max_lt hz hlt))
  · rw [max_eq_right hgt.le] at hu ⊢
    exact le_antisymm hu (le_of_not_gt fun hz =>
      (not_lt_of_ge h2) (max_lt hgt hz))

theorem local_density_of_norm {F : Type*} [NormedField F] [IsUltrametricDist F]
    (x : F) (hx : x ≠ 0) (hunit : ‖x‖ ≠ 1) :
    Real.exp (Real.log ‖x‖ / 2) / ‖1 - x‖ =
      Real.exp (-|Real.log ‖x‖| / 2) := by
  rw [norm_one_sub x hunit]
  have he := local_density (Real.log ‖x‖)
  simpa [Real.exp_log (norm_pos_iff.mpr hx)] using he

#print axioms integral_shell
#print axioms local_density
#print axioms weighted_shell
#print axioms logged_shell
#print axioms local_density_of_norm
end ActualLocalShell


/- Round 6: the actual large-prime shell vanishing works on both norm sides.
The only analytic input is the exposed compact norm band of the test.
APPLICATION_R06.md attaches this to the actual trace constructed in R05. -/
namespace ActualTwoSidedTailR06
open MeasureTheory
noncomputable section
variable {G : Type*} [Group G]

theorem integer_shell_outside (R L : ℝ) (hR : 0 ≤ R) (hRL : R < L)
    (n : ℤ) (hn : n ≠ 0) : R < |-(n : ℝ) * L| := by
  have hpos : (0 : ℤ) < |n| := abs_pos.mpr hn
  have hni : (1 : ℤ) ≤ |n| := by omega
  have hnR : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hni
  have hL : 0 ≤ L := le_trans hR hRL.le
  rw [abs_mul, abs_neg, abs_of_nonneg hL]
  exact lt_of_lt_of_le hRL (by nlinarith)

theorem both_tests_vanish (ell : G → ℝ) (h : G → ℂ)
    (R L : ℝ) (hR : 0 ≤ R) (hRL : R < L)
    (hband : ∀ x, R < |ell x| → h x = 0)
    (hunit : ∀ x, ell x = 0 → h x = 0)
    (x : G) (n : ℤ) (hell : ell x = -(n : ℝ) * L) :
    h x = 0 ∧ (-(ell x) : ℂ) * h x = 0 := by
  have hz : h x = 0 := by
    by_cases hn : n = 0
    · apply hunit
      simpa [hn] using hell
    · apply hband
      rw [hell]
      exact integer_shell_outside R L hR hRL n hn
  exact ⟨hz, by rw [hz, mul_zero]⟩

variable [MeasurableSpace G]

theorem both_unit_averages_zero (μ : Measure G) (U : Set G)
    (hU : MeasurableSet U) (ell : G → ℝ) (h : G → ℂ)
    (R L : ℝ) (hR : 0 ≤ R) (hRL : R < L)
    (hband : ∀ x, R < |ell x| → h x = 0)
    (hunit : ∀ x, ell x = 0 → h x = 0)
    (π : G) (n : ℤ)
    (hell : ∀ u ∈ U, ell (π ^ n * u) = -(n : ℝ) * L) :
    (∫ u in U, h (π ^ n * u) ∂μ) = 0 ∧
    (∫ u in U, (-(ell (π ^ n * u)) : ℂ) * h (π ^ n * u) ∂μ) = 0 := by
  constructor
  · calc
      _ = ∫ _ in U, (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU
        intro u hu
        exact (both_tests_vanish ell h R L hR hRL hband hunit
          (π ^ n * u) n (hell u hu)).1
      _ = 0 := by simp
  · calc
      _ = ∫ _ in U, (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU
        intro u hu
        exact (both_tests_vanish ell h R L hR hRL hband hunit
          (π ^ n * u) n (hell u hu)).2
      _ = 0 := by simp

/-- Either one-sided Euler weights or symmetric local weights vanish termwise.
No summation/limit exchange and no positive-support premise is required. -/
theorem weighted_tail_zero (b c : ℤ → ℂ) (hb : ∀ n, b n = 0) :
    Summable (fun n => c n * b n) ∧ (∑' n, c n * b n) = 0 := by
  constructor
  · simpa only [hb, mul_zero] using (summable_zero : Summable (fun _ : ℤ => (0 : ℂ)))
  · simp [hb]

end
#print axioms integer_shell_outside
#print axioms both_tests_vanish
#print axioms both_unit_averages_zero
#print axioms weighted_tail_zero
end ActualTwoSidedTailR06
