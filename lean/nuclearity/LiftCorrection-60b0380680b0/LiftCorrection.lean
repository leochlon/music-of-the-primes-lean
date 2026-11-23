import Mathlib

open scoped BigOperators
namespace Round95E
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Density within the geometric subspace gives arbitrarily close exact
smooth lifts; no norm bound on a chosen lift is assumed. -/
theorem exact_smooth_lift_approximation
    (S M : Submodule ℂ H)
    (hdense : ∀ v ∈ M, v ∈ closure ((S : Set H) ∩ (M : Set H)))
    (p v : H) (hv : v ∈ S) (hvp : v - p ∈ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u ∈ S, u - p ∈ M ∧ ‖u - p‖ < ε := by
  obtain ⟨q, hq, hdist⟩ := Metric.mem_closure_iff.mp (hdense (v-p) hvp) ε hε
  refine ⟨v-q, S.sub_mem hv hq.1, ?_, ?_⟩
  · have heq : v-q-p = (v-p)-q := by abel
    rw [heq]
    exact M.sub_mem hvp hq.2
  · have heq : v-q-p = (v-p)-q := by abel
    rw [heq]
    simpa only [dist_eq_norm] using hdist

/-- Constructed geometric lift errors have a geometric nuclear-cost bound.
This controls the correction terms, not the main smoothed-lift series. -/
theorem smooth_lifts_geometric_correction_bound
    (S M : Submodule ℂ H)
    (hdense : ∀ v ∈ M, v ∈ closure ((S : Set H) ∩ (M : Set H)))
    (p : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ)
    (hlift : ∀ i, ∃ v ∈ S, v - p i ∈ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℕ → H, (∀ i, u i ∈ S ∧ u i - p i ∈ M) ∧
      ∀ i, ‖u i - p i‖ * ‖eta i‖ ≤ ε * (1 / 2 : ℝ) ^ i := by
  have hex : ∀ i, ∃ u ∈ S, u - p i ∈ M ∧
      ‖u - p i‖ < (ε * (1/2 : ℝ)^i) / (‖eta i‖ + 1) := by
    intro i
    obtain ⟨v, hv, hvm⟩ := hlift i
    apply exact_smooth_lift_approximation S M hdense (p i) v hv hvm
    positivity
  choose u hu hm he using hex
  refine ⟨u, fun i => ⟨hu i, hm i⟩, ?_⟩
  intro i
  have hden : 0 < ‖eta i‖ + 1 := by positivity
  have hc := (lt_div_iff₀ hden).mp (he i)
  nlinarith [norm_nonneg (u i - p i)]

/-- The convolved geometric correction has a summable nuclear majorant
bounded by 2 epsilon times the operator norm. Summability is proved. -/
theorem smooth_lifts_summable_convolved_correction
    (S M : Submodule ℂ H)
    (hdense : ∀ v ∈ M, v ∈ closure ((S : Set H) ∩ (M : Set H)))
    (p : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ)
    (hlift : ∀ i, ∃ v ∈ S, v - p i ∈ M)
    (A : H →L[ℂ] H) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℕ → H, (∀ i, u i ∈ S ∧ u i - p i ∈ M) ∧
      Summable (fun i => ‖A (u i - p i)‖ * ‖eta i‖) ∧
      (∑' i, ‖A (u i - p i)‖ * ‖eta i‖) ≤ 2 * ε * ‖A‖ := by
  obtain ⟨u, hu, he⟩ := smooth_lifts_geometric_correction_bound
    S M hdense p eta hlift ε hε
  have hq : ‖(1/2 : ℝ)‖ < 1 := by norm_num
  have hs := (summable_geometric_of_norm_lt_one hq).mul_left (‖A‖ * ε)
  have hb : ∀ i, ‖A (u i-p i)‖ * ‖eta i‖ ≤
      (‖A‖ * ε) * (1/2 : ℝ)^i := by
    intro i
    calc
      _ ≤ (‖A‖ * ‖u i-p i‖) * ‖eta i‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ * (‖u i-p i‖ * ‖eta i‖) := by ring
      _ ≤ ‖A‖ * (ε * (1/2 : ℝ)^i) :=
        mul_le_mul_of_nonneg_left (he i) (norm_nonneg A)
      _ = _ := by ring
  have hc : Summable (fun i => ‖A (u i-p i)‖ * ‖eta i‖) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hb hs
  refine ⟨u, hu, hc, ?_⟩
  calc
    _ ≤ ∑' i, (‖A‖ * ε) * (1/2 : ℝ)^i := Summable.tsum_le_tsum hb hc hs
    _ = (‖A‖ * ε) * (1 - (1/2 : ℝ))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hq]
    _ = 2 * ε * ‖A‖ := by norm_num; ring

#check smooth_lifts_summable_convolved_correction
#print axioms smooth_lifts_summable_convolved_correction
#check exact_smooth_lift_approximation
#print axioms exact_smooth_lift_approximation
#check smooth_lifts_geometric_correction_bound
#print axioms smooth_lifts_geometric_correction_bound
end Round95E
