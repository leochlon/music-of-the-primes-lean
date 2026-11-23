import Mathlib
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
namespace TranslatedCorrectionProfileR05

/-- Scalar trace of the actual translated Riesz block after its radial
normalization. The geometric identification is proved on paper separately. -/
def profile (q m : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(t : ℂ)/2) * (m * Complex.exp ((q-1/2)*(t : ℂ)))

theorem profile_eq (q m : ℂ) (t : ℝ) :
    profile q m t = m * Complex.exp ((q-1)*(t : ℂ)) := by
  unfold profile
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem logged_profile_eq (q m : ℂ) (t : ℝ) :
    Complex.exp (-(t : ℂ)/2) * (-m*(t : ℂ)*Complex.exp ((q-1/2)*(t : ℂ))) =
      -(t : ℂ) * (m * Complex.exp ((q-1)*(t : ℂ))) := by
  calc
    _ = -(t : ℂ) * profile q m t := by unfold profile; ring
    _ = _ := by rw [profile_eq]

theorem norm_sq_weight (q m : ℂ) (t σ : ℝ) :
    ‖profile q m t‖^2 * Real.exp ((2-σ)*t) =
      ‖m‖^2 * Real.exp ((2*q.re-σ)*t) := by
  rw [profile_eq, norm_mul, Complex.norm_exp, mul_pow]
  simp only [Complex.mul_re, Complex.sub_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
  congr 2
  norm_num
  ring

theorem translation_polynomial_weight (u t : ℝ) :
    1+(u+t)^2 ≤ 2*(1+u^2)*(1+t^2) := by
  nlinarith [sq_nonneg (u-t), sq_nonneg (u*t)]

end TranslatedCorrectionProfileR05
#print axioms TranslatedCorrectionProfileR05.profile_eq
#print axioms TranslatedCorrectionProfileR05.logged_profile_eq
#print axioms TranslatedCorrectionProfileR05.norm_sq_weight
#print axioms TranslatedCorrectionProfileR05.translation_polynomial_weight
