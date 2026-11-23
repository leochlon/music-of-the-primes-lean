import Mathlib

/-! Round 88 G. Structural reduction for the missing global bound.
This does not construct the genuine weighted idele-class operator and
does not assert nuclearity or summability. In application A is convolution
and P is the manuscript's spectral projection. -/

namespace NuclearBoundR88G

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem convolution_after_projection_split
    (A P : E →L[ℂ] E) :
    A.comp P = P.comp (A.comp P) +
      (ContinuousLinearMap.id ℂ E - P).comp (A.comp P) := by
  ext x
  simp

theorem lifted_vector_norm_split (A P : E →L[ℂ] E) (u : E) :
    ‖A u‖ ≤ ‖P (A u)‖ + ‖A u - P (A u)‖ := by
  calc
    ‖A u‖ = ‖P (A u) + (A u - P (A u))‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _

theorem convolution_after_projection_off_diagonal
    (A P : E →L[ℂ] E)
    (hinvariant : P.comp (A.comp (ContinuousLinearMap.id ℂ E - P)) = 0) :
    A.comp P = P.comp A +
      (ContinuousLinearMap.id ℂ E - P).comp (A.comp P) := by
  ext x
  have h := congrArg (fun T : E →L[ℂ] E => T x) hinvariant
  have hx : P (A x) = P (A (P x)) := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_sub, ContinuousLinearMap.zero_apply,
      sub_eq_zero] using h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [hx]
  abel

/- The actual manuscript weight in logarithmic norm coordinates, at s = 2d.
No number-field, character, spectral-label or cutoff constants enter this
pointwise estimate. It is a translation bound, not a nuclear bound. -/
noncomputable def logWeight (α : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ d

theorem logWeight_translate_bound (α : ℝ) (hα : 0 ≤ α) (d : ℕ) (h x : ℝ) :
    logWeight α d (h + x) ≤
      (Real.exp (2 * α * |h|) * (2 * (1 + h ^ 2)) ^ d) * logWeight α d x := by
  have hb : 1 + (h + x) ^ 2 ≤ (2 * (1 + h ^ 2)) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (h - x), sq_nonneg (h * x)]
  have hp : (1 + (h + x) ^ 2) ^ d ≤
      ((2 * (1 + h ^ 2)) * (1 + x ^ 2)) ^ d := by
    gcongr
  have he : Real.exp (2 * α * |h + x|) ≤
      Real.exp (2 * α * |h|) * Real.exp (2 * α * |x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      2 * α * |h + x| ≤ 2 * α * (|h| + |x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le h x) (by positivity)
      _ = _ := by ring
  unfold logWeight
  calc
    _ ≤ (Real.exp (2 * α * |h|) * Real.exp (2 * α * |x|)) *
        (((2 * (1 + h ^ 2)) * (1 + x ^ 2)) ^ d) :=
      mul_le_mul he hp (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

#check convolution_after_projection_split
#check lifted_vector_norm_split
#check convolution_after_projection_off_diagonal
#check logWeight_translate_bound
#print axioms convolution_after_projection_split
#print axioms lifted_vector_norm_split
#print axioms convolution_after_projection_off_diagonal
#print axioms logWeight_translate_bound

end NuclearBoundR88G
