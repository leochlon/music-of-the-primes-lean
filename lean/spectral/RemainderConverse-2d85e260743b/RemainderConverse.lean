import Mathlib
open Filter Topology Set MeasureTheory

namespace MasulloGRH.ConditionalMoment
open MasulloGRH.ConditionalMoment
noncomputable def positiveCutoff (t x : ℝ) : ℝ :=
  Real.smoothTransition (t * x - 1) * Real.smoothTransition (2 - x / t)


end MasulloGRH.ConditionalMoment

namespace ConditionalReviewC
open MasulloGRH.ConditionalMoment
noncomputable def concreteTransform (z : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(z-w) * (x : ℂ)) *
    ((x * positiveCutoff ((n : ℝ)+2) x : ℝ) : ℂ)


end ConditionalReviewC

namespace BoundaryFreeRepairD
open MasulloGRH.ConditionalMoment
def boundaryFreeWidths (f : ℂ → ℂ) (c : ℂ) : Set ℝ :=
  ((fun z : ℂ => |(z - c).re|) '' {z : ℂ | f z = 0})ᶜ


end BoundaryFreeRepairD

namespace BoundaryFreeTraceRepairD
theorem critical_line_implies_remainder_independent
    {f : ℂ → ℂ}
    (G : ℂ → ℕ → ℂ) (remainder : ℝ → ℂ → ℕ → ℂ)
    (hcorrected : ∀ a : ℝ, a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) → 0 < a → ∀ z : ℂ, a < z.re → ∀ n : ℕ,
      Tendsto (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) *
          ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ))
        else 0) atTop (𝓝 (G z n - remainder a z n)))
    (hline : ∀ z : ℂ, f z = 0 → z.re = 1/2)
    : ∀ a b : ℝ, a ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) →
      b ∈ BoundaryFreeRepairD.boundaryFreeWidths f (1/2:ℂ) → 0 < a → a < b →
      ∀ z : ℂ, b < z.re → ∀ n : ℕ, remainder a z n = remainder b z n := by
  intro a b hag hbg ha hab z hz n
  have heq :
      (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < a ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) *
          ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)) else 0) =
      (fun H : ℝ => ∑' i : {z : ℂ // f z = 0},
        if |(i.val - (1/2:ℂ)).re| < b ∧ |(i.val - (1/2:ℂ)).im| ≤ H
        then (analyticOrderNatAt f i.val : ℂ) *
          ConditionalReviewC.concreteTransform z n (i.val-(1/2:ℂ)) else 0) := by
    funext H
    apply tsum_congr
    intro i
    have hi : |(i.val - (1/2:ℂ)).re| = 0 := by
      norm_num [Complex.sub_re, hline i.val i.property]
    simp only [hi, ha, ha.trans hab, true_and]
  have hfirst := hcorrected a hag ha z (hab.trans hz) n
  have hsecond := hcorrected b hbg (ha.trans hab) z hz n
  rw [heq] at hfirst
  have he := tendsto_nhds_unique hfirst hsecond
  exact sub_right_injective he

#print axioms critical_line_implies_remainder_independent
end BoundaryFreeTraceRepairD
