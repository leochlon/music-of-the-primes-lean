import Mathlib

open MeasureTheory
open scoped BigOperators

namespace TraceRepairB

/-- The measured transpose action used in manuscript 10.4.2.29--33.
The measure is retained, and every moment needed for Bochner integration
is an explicit hypothesis.  On C_K, ell = log of the idelic norm and c
is the actual character times the chosen complex norm power. -/
theorem measured_jet_action
    {G : Type*} [Monoid G] [MeasurableSpace G]
    (mu : Measure G) (c : G →* ℂ) (ell : G → ℂ)
    (hell : ∀ g y, ell (g * y) = ell g + ell y)
    (h : G → ℂ) (m : ℕ)
    (hint : ∀ k ∈ Finset.range (m + 1),
      Integrable (fun g => h g * c g * ell g ^ k) mu) (y : G) :
    (∫ g, h g * (c (g * y) * ell (g * y) ^ m) ∂mu) =
      ∑ k ∈ Finset.range (m + 1),
        (∫ g, h g * c g * ell g ^ k ∂mu) *
          (c y * ell y ^ (m - k) * (m.choose k : ℂ)) := by
  have hp : (fun g => h g * (c (g * y) * ell (g * y) ^ m)) =
      (fun g => ∑ k ∈ Finset.range (m + 1),
        (h g * c g * ell g ^ k) *
          (c y * ell y ^ (m - k) * (m.choose k : ℂ))) := by
    funext g
    rw [map_mul, hell, add_pow]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hp, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_mul_const _ _
  · intro k hk
    exact (hint k hk).mul_const _

/-- The zeroth measured jet has the expected Mellin eigenvalue. This fixes
the sign/order convention without assuming invariance of a chosen lift. -/
theorem measured_character_action
    {G : Type*} [Monoid G] [MeasurableSpace G]
    (mu : Measure G) (c : G →* ℂ) (h : G → ℂ) (y : G) :
    (∫ g, h g * c (g * y) ∂mu) = (∫ g, h g * c g ∂mu) * c y := by
  simp only [map_mul, ← mul_assoc]
  exact integral_mul_const _ _

#print axioms measured_jet_action
#print axioms measured_character_action

end TraceRepairB
