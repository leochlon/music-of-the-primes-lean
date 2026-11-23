import Mathlib

/- Exact algebra and summability used in GLOBAL_REVIEW_R03.md.
   These are the radial kernels of the actual real and complex local
   integrals. The adelic trace identification remains a paper argument. -/
noncomputable section
namespace ArchimedeanAssemblyR03

theorem real_even_kernel (r : ℝ) (hm : 1 - r ≠ 0) (hp : 1 + r ≠ 0) :
    (1 / 2 : ℝ) * (1 / (1 - r) + 1 / (1 + r)) = 1 / (1 - r ^ 2) := by
  have h : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h]
  field_simp
  ring

theorem real_odd_kernel (r : ℝ) (hm : 1 - r ≠ 0) (hp : 1 + r ≠ 0) :
    (1 / 2 : ℝ) * (1 / (1 - r) - 1 / (1 + r)) = r / (1 - r ^ 2) := by
  have h : 1 - r ^ 2 = (1 - r) * (1 + r) := by ring
  rw [h]
  field_simp
  ring

theorem radial_geometric (a r : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => a * r ^ n) (a / (1 - r)) := by
  simpa only [div_eq_mul_inv] using
    (hasSum_geometric_of_norm_lt_one hr).mul_left a

/-- The negative-log sharp test changes the same radial series by -u. -/
theorem logarithmic_radial_geometric (a r u : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (-u * a) * r ^ n) (-u * (a / (1 - r))) := by
  simpa only [mul_div_assoc] using radial_geometric (-u * a) r hr

/-- Fejer operators on a finite level must be completed on its complement
    before applying the whole-Hilbert-space strong trace limit. -/
theorem level_complement_cancels
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T E F : H →L[ℂ] H) (hTE : T.comp E = T) :
    T.comp (ContinuousLinearMap.id ℂ H - E + F) = T.comp F := by
  rw [ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_id, hTE, sub_self, zero_add]

end ArchimedeanAssemblyR03
#print axioms ArchimedeanAssemblyR03.real_even_kernel
#print axioms ArchimedeanAssemblyR03.real_odd_kernel
#print axioms ArchimedeanAssemblyR03.radial_geometric
#print axioms ArchimedeanAssemblyR03.logarithmic_radial_geometric
#print axioms ArchimedeanAssemblyR03.level_complement_cancels
