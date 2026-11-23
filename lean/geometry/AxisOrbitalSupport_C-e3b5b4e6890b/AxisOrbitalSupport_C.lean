import Mathlib

/- The product-formula estimate used to make the limiting S-unit orbital
distribution a finite sum. The arithmetic properness input is exposed;
APPLICATION_R02.md proves it for the actual S-unit group. -/
noncomputable section
open scoped BigOperators
namespace GeometricTraceC

theorem missing_log_bound {V : Type*} [Fintype V] [DecidableEq V]
    (l B : V → ℝ) (v : V) (hzero : ∑ w, l w = 0)
    (hB : ∀ w, 0 ≤ B w) (hother : ∀ w, w ≠ v → |l w| ≤ B w) :
    |l v| ≤ ∑ w, B w := by
  have hs := Finset.sum_erase_add (Finset.univ : Finset V) l (by simp : v ∈ Finset.univ)
  have he : l v = -(∑ w ∈ Finset.univ.erase v, l w) := by
    rw [hzero] at hs
    linarith
  rw [he, abs_neg]
  calc
    _ ≤ ∑ w ∈ Finset.univ.erase v, |l w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ Finset.univ.erase v, B w := by
      apply Finset.sum_le_sum
      intro w hw
      exact hother w (Finset.mem_erase.mp hw).1
    _ ≤ ∑ w, B w := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset _ _) (fun w _ _ => hB w)

/-- An axis can meet only finitely many unit translates of a compact lift.
The log map of S-units has finite inverse images of bounded boxes. -/
theorem finite_axis_candidates {V U : Type*} [Fintype V] [DecidableEq V]
    (l : U → V → ℝ) (B : V → ℝ) (v : V)
    (hzero : ∀ u, ∑ w, l u w = 0) (hB : ∀ w, 0 ≤ B w)
    (hproper : ∀ R : ℝ, {u | ∀ w, |l u w| ≤ R}.Finite) :
    {u | ∀ w, w ≠ v → |l u w| ≤ B w}.Finite := by
  apply (hproper (∑ w, B w)).subset
  intro u hu w
  by_cases hw : w = v
  · subst w
    exact missing_log_bound (l u) B v (hzero u) hB hu
  · exact (hu w hw).trans (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_univ w))

/-- The inversion Jacobian in the local trace density; no measure scalar
is suppressed when converting the additive-axis integral to multiplicative Haar. -/
theorem local_inversion_density (r d : ℝ) (hr : 0 < r) :
    Real.sqrt (1 / r) / (d / r) = Real.sqrt r / d := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_one]
  have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  by_cases hd : d = 0
  · simp [hd]
  · field_simp
    nlinarith

#print axioms missing_log_bound
#print axioms finite_axis_candidates
#print axioms local_inversion_density
end GeometricTraceC
