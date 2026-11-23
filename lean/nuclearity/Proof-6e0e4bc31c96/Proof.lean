import Mathlib

/-!
Round 182 E. The native two-simple-root Gram cancellation used in
GLOBAL_ESTIMATE.md. This is a local conditioning calculation for the actual
weight exp(2 alpha |x|), NOT a global nuclearity theorem. The analytic Gram
integral and its identification with the native two-root compression are
proved on paper in GLOBAL_ESTIMATE.md; only the displayed algebra and the
resulting gap-independent cost are certified here.
-/
noncomputable section
namespace Round182E

def nativeOverlap (alpha gap : ℝ) : ℝ :=
  (4 * alpha ^ 2) / (4 * alpha ^ 2 + gap ^ 2)

theorem native_overlap_defect (alpha gap : ℝ) (ha : 0 < alpha) :
    1 - nativeOverlap alpha gap ^ 2 =
      gap ^ 2 * (8 * alpha ^ 2 + gap ^ 2) /
        (4 * alpha ^ 2 + gap ^ 2) ^ 2 := by
  have hp : 0 < 4 * alpha ^ 2 + gap ^ 2 := by positivity
  unfold nativeOverlap
  field_simp
  ring

/-- After the full two-root matrix is put in an orthonormal basis, its
three rank-one terms have this cost. The Mellin difference is retained
until it cancels the inverse gap. B is a measured derivative bound, not
an assumed spectral or nuclear summability hypothesis. -/
theorem native_two_root_gapfree_cost
    (alpha gap B : ℝ) (ha : 0 < alpha) (hg : gap ≠ 0) (hB : 0 ≤ B)
    (lambda₁ lambda₂ : ℂ)
    (hdiff : ‖lambda₂ - lambda₁‖ ≤ |gap| * B) :
    ‖lambda₁‖ + ‖lambda₂‖ +
      (4 * alpha ^ 2 * ‖lambda₂ - lambda₁‖) /
        (|gap| * Real.sqrt (8 * alpha ^ 2 + gap ^ 2)) ≤
      ‖lambda₁‖ + ‖lambda₂‖ + 2 * alpha * B := by
  have hp : 0 < 8 * alpha ^ 2 + gap ^ 2 := by positivity
  have hs0 := Real.sqrt_nonneg (8 * alpha ^ 2 + gap ^ 2)
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  have hs : 2 * alpha ≤ Real.sqrt (8 * alpha ^ 2 + gap ^ 2) := by
    nlinarith [sq_nonneg gap]
  have hden : 0 < |gap| * Real.sqrt (8 * alpha ^ 2 + gap ^ 2) :=
    mul_pos (abs_pos.mpr hg) (Real.sqrt_pos.2 hp)
  suffices h : (4 * alpha ^ 2 * ‖lambda₂ - lambda₁‖) /
      (|gap| * Real.sqrt (8 * alpha ^ 2 + gap ^ 2)) ≤ 2 * alpha * B by
    linarith
  apply (div_le_iff₀ hden).2
  calc
    4 * alpha ^ 2 * ‖lambda₂ - lambda₁‖ ≤
        4 * alpha ^ 2 * (|gap| * B) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = (2 * alpha * B * |gap|) * (2 * alpha) := by ring
    _ ≤ (2 * alpha * B * |gap|) * Real.sqrt (8 * alpha ^ 2 + gap ^ 2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (2 * alpha * B) * (|gap| * Real.sqrt (8 * alpha ^ 2 + gap ^ 2)) := by ring

#check native_overlap_defect
#print axioms native_overlap_defect
#check native_two_root_gapfree_cost
#print axioms native_two_root_gapfree_cost
end Round182E
