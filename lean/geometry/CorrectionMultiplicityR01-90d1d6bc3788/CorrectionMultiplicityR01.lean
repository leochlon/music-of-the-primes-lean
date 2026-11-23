import Mathlib

/- Exact definition excerpts from review_core/Masullo/TraceFormula.lean. -/
open Complex
namespace ManuscriptRH
structure Parameters where
  width : ℝ
  weight : ℝ
  width_pos : 0 < width

def GenuineZero := {ρ : ℂ // completedRiemannZeta ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1}

noncomputable def zeroOrder (ρ : GenuineZero) : ℕ :=
  analyticOrderNatAt completedRiemannZeta ρ.val

def AdmittedJet (p : Parameters) (ρ : GenuineZero) (m : ℕ) : Prop :=
  m < zeroOrder ρ ∧
    (|ρ.val.re - 1/2| < p.width ∨
      (|ρ.val.re - 1/2| = p.width ∧ (2 : ℝ) * m + 1 < p.weight))

noncomputable def interiorMultiplicity (p : Parameters) (ρ : GenuineZero) : ℕ :=
  if |ρ.val.re - 1/2| < p.width then zeroOrder ρ else 0

noncomputable def boundaryMultiplicity (p : Parameters) (ρ : GenuineZero) : ℕ := by
  classical
  exact if |ρ.val.re - 1/2| = p.width then
    ((Finset.range (zeroOrder ρ)).filter (fun m => (2 : ℝ) * m + 1 < p.weight)).card
    else 0

/-- The coefficient of the actual omitted-minus-boundary correction. -/
theorem correction_coefficient_right (p : Parameters) (ρ : GenuineZero)
    (h : p.width < ρ.val.re - 1/2) :
    ((zeroOrder ρ - interiorMultiplicity p ρ : ℕ) : ℂ) -
      (boundaryMultiplicity p ρ : ℂ) = (zeroOrder ρ : ℂ) := by
  have ha : p.width < |ρ.val.re - 1/2| := lt_of_lt_of_le h (le_abs_self _)
  have hi : ¬ |ρ.val.re - 1/2| < p.width := not_lt.mpr ha.le
  have he : ¬ |ρ.val.re - 1/2| = p.width := ne_of_gt ha
  simp only [interiorMultiplicity, boundaryMultiplicity, if_neg hi, if_neg he,
    Nat.sub_zero, Nat.cast_zero, sub_zero]
end ManuscriptRH
#print axioms ManuscriptRH.correction_coefficient_right
