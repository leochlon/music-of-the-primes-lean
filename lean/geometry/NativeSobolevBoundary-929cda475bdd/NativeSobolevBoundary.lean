import Mathlib

namespace NativeSobolevBoundary

noncomputable def jets (m : ℕ) (s : ℝ) : ℕ :=
  ((Finset.range m).filter (fun j : ℕ => (2 : ℝ) * j + 1 < s)).card

theorem jets_le (m : ℕ) (s : ℝ) : jets m s ≤ m := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range m)

theorem jets_mono (m : ℕ) {s t : ℝ} (hst : s ≤ t) :
    jets m s ≤ jets m t := by
  classical
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 hst⟩

theorem jets_exhaust (m : ℕ) (s : ℝ) (hs : 2 * (m : ℝ) ≤ s) :
    jets m s = m := by
  classical
  unfold jets
  have hf : (Finset.range m).filter (fun j : ℕ => (2 : ℝ) * j + 1 < s) =
      Finset.range m := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    have hnat : j + 1 ≤ m := Finset.mem_range.mp hj
    have hreal : (j : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnat
    linarith
  rw [hf, Finset.card_range]

theorem exact_boundary_split (m : ℕ) {s t : ℝ} (hst : s ≤ t) :
    m - jets m s = (m - jets m t) + (jets m t - jets m s) := by
  have h₁ := jets_le m t
  have h₂ := jets_mono m hst
  omega

theorem completed_boundary (m : ℕ) {s t : ℝ}
    (ht : 2 * (m : ℝ) ≤ t) :
    m - jets m s = jets m t - jets m s := by
  rw [jets_exhaust m t ht]

#print axioms jets_exhaust
#print axioms exact_boundary_split
#print axioms completed_boundary
end NativeSobolevBoundary
