import Mathlib

namespace NativeWidthBoundary

/-- The original strict polynomial-tail condition; equality is excluded. -/
noncomputable def boundaryJets (multiplicity : ℕ) (s : ℝ) : ℕ :=
  ((Finset.range multiplicity).filter
    (fun j : ℕ => (2 : ℝ) * (j : ℝ) + 1 < s)).card

noncomputable def admitted (multiplicity : ℕ) (s radius width : ℝ) : ℕ :=
  if radius < width then multiplicity
  else if radius = width then boundaryJets multiplicity s else 0

/-- A fixed-width correction has an endpoint term invisible to weak derivatives. -/
theorem exact_deficit (multiplicity : ℕ) (s radius width : ℝ) :
    multiplicity - admitted multiplicity s radius width =
      (if width < radius then multiplicity else 0) +
      (if radius = width then multiplicity - boundaryJets multiplicity s else 0) := by
  classical
  by_cases hlt : radius < width
  · have hgt : ¬ width < radius := by linarith
    have heq : radius ≠ width := ne_of_lt hlt
    simp [admitted, hlt, hgt, heq]
  · by_cases heq : radius = width
    · simp [admitted, heq]
    · have hgt : width < radius := by
        rcases lt_trichotomy radius width with h | h | h
        · exact (hlt h).elim
        · exact (heq h).elim
        · exact h
      simp [admitted, hlt, heq, hgt]

/-- The boundary count cannot exceed the actual zero order. -/
theorem boundaryJets_le (multiplicity : ℕ) (s : ℝ) :
    boundaryJets multiplicity s ≤ multiplicity := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range multiplicity)

/-- Finite cutoff of the actual omitted-plus-boundary trace identity. -/
theorem finite_correction {ι : Type*} (S : Finset ι)
    (multiplicity : ι → ℕ) (radius : ι → ℝ) (coefficient : ι → ℂ)
    (s width : ℝ) :
    (∑ i ∈ S, ((multiplicity i - admitted (multiplicity i) s (radius i) width : ℕ) : ℂ)
      * coefficient i) =
    (∑ i ∈ S, ((if width < radius i then multiplicity i else 0 : ℕ) : ℂ)
      * coefficient i) +
    (∑ i ∈ S, ((if radius i = width then
      multiplicity i - boundaryJets (multiplicity i) s else 0 : ℕ) : ℂ)
      * coefficient i) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [exact_deficit, Nat.cast_add, add_mul]

#print axioms exact_deficit
#print axioms boundaryJets_le
#print axioms finite_correction
end NativeWidthBoundary
