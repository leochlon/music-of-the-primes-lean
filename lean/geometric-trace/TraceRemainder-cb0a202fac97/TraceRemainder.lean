import Mathlib

open scoped BigOperators
namespace Followup23B

/-- Native boundary jets use the strict integrability threshold 2j+1<s. -/
noncomputable def boundaryCount (N : ℕ) (s : ℝ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun j : ℕ => 2 * (j : ℝ) + 1 < s).card

theorem boundaryCount_le (N : ℕ) (s : ℝ) : boundaryCount N s ≤ N := by
  classical
  unfold boundaryCount
  simpa using Finset.card_le_card (Finset.filter_subset
    (fun j : ℕ => 2 * (j : ℝ) + 1 < s) (Finset.range N))

theorem boundaryCount_at_one (N : ℕ) : boundaryCount N 1 = 0 := by
  classical
  unfold boundaryCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have h := (Finset.mem_filter.mp hj).2
  have hn : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

/-- This is a count of admissible genuine zero jets, not a definition of a spectrum. -/
noncomputable def retainedCount (f : ℂ → ℂ) (a α s : ℝ) (z : ℂ) : ℕ := by
  classical
  exact if |z.re - a| < α then analyticOrderNatAt f z
    else if |z.re - a| = α then boundaryCount (analyticOrderNatAt f z) s else 0

theorem retainedCount_le (f : ℂ → ℂ) (a α s : ℝ) (z : ℂ) :
    retainedCount f a α s z ≤ analyticOrderNatAt f z := by
  classical
  unfold retainedCount
  split_ifs
  · exact le_rfl
  · exact boundaryCount_le _ _
  · exact Nat.zero_le _

/-- Full genuine divisor = native candidate count + all omitted jets, at every
finite cutoff. No arithmetic trace or vanishing remainder is assumed. -/
theorem finite_genuine_divisor_split (f : ℂ → ℂ) (a α s : ℝ)
    (u : Finset {z : ℂ // f z = 0}) (W : ℂ → ℂ) :
    (∑ z ∈ u, (analyticOrderNatAt f z.val : ℂ) * W z.val) =
      (∑ z ∈ u, (retainedCount f a α s z.val : ℂ) * W z.val) +
      ∑ z ∈ u, ((analyticOrderNatAt f z.val - retainedCount f a α s z.val : ℕ) : ℂ) * W z.val := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Nat.cast_sub (retainedCount_le f a α s z.val)]
  ring

/-- The exact infinite split under explicitly displayed convergence premises.
W must still be identified with the actual measured Mellin transform. -/
theorem genuine_divisor_remainder (f : ℂ → ℂ) (a α s : ℝ) (W : ℂ → ℂ)
    (hselected : Summable (fun z : {z : ℂ // f z = 0} =>
      (retainedCount f a α s z.val : ℂ) * W z.val))
    (homitted : Summable (fun z : {z : ℂ // f z = 0} =>
      ((analyticOrderNatAt f z.val - retainedCount f a α s z.val : ℕ) : ℂ) * W z.val)) :
    (∑' z : {z : ℂ // f z = 0}, (analyticOrderNatAt f z.val : ℂ) * W z.val) =
      (∑' z : {z : ℂ // f z = 0}, (retainedCount f a α s z.val : ℂ) * W z.val) +
      ∑' z : {z : ℂ // f z = 0},
        ((analyticOrderNatAt f z.val - retainedCount f a α s z.val : ℕ) : ℂ) * W z.val := by
  rw [← hselected.tsum_add homitted]
  apply tsum_congr
  intro z
  rw [Nat.cast_sub (retainedCount_le f a α s z.val)]
  ring

/-- A full-zero formula yields the corrected selected formula with its
remainder retained. This does not assert the missing arithmetic attachment. -/
theorem corrected_selected_formula (f : ℂ → ℂ) (a α s : ℝ) (W : ℂ → ℂ)
    (hselected : Summable (fun z : {z : ℂ // f z = 0} =>
      (retainedCount f a α s z.val : ℂ) * W z.val))
    (homitted : Summable (fun z : {z : ℂ // f z = 0} =>
      ((analyticOrderNatAt f z.val - retainedCount f a α s z.val : ℕ) : ℂ) * W z.val))
    (G P : ℂ)
    (hfull : G = P - ∑' z : {z : ℂ // f z = 0},
      (analyticOrderNatAt f z.val : ℂ) * W z.val) :
    G = P - (∑' z : {z : ℂ // f z = 0},
      (retainedCount f a α s z.val : ℂ) * W z.val) -
      ∑' z : {z : ℂ // f z = 0},
        ((analyticOrderNatAt f z.val - retainedCount f a α s z.val : ℕ) : ℂ) * W z.val := by
  rw [hfull, genuine_divisor_remainder f a α s W hselected homitted]
  ring

#print axioms boundaryCount_at_one
#print axioms retainedCount_le
#print axioms finite_genuine_divisor_split
#print axioms genuine_divisor_remainder
#print axioms corrected_selected_formula
end Followup23B
