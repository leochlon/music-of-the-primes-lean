import Mathlib

/-! Round 88 B. Direct norm ingredients for the actual global convolution.
The nuclear bound and reconstruction of the orthogonal projection remain OPEN.
The scalar weight below is the manuscript weight with Sobolev degree s = 2*d.
-/
open scoped NumberField
open MeasureTheory

namespace MasulloGRH

noncomputable def stripWeight (α : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  Real.exp (2 * α * |t|) * (1 + t ^ 2) ^ d

/-- Correct translation factor; unlike manuscript (9.3.1.6), it is nonzero at 0. -/
theorem stripWeight_translate_bound (α : ℝ) (hα : 0 ≤ α) (d : ℕ) (x y : ℝ) :
    stripWeight α d (x + y) ≤
      (Real.exp (2 * α * |y|) * (2 * (1 + y ^ 2)) ^ d) * stripWeight α d x := by
  have hp : 1 + (x + y) ^ 2 ≤ (2 * (1 + y ^ 2)) * (1 + x ^ 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x * y)]
  have he : Real.exp (2 * α * |x + y|) ≤
      Real.exp (2 * α * |y|) * Real.exp (2 * α * |x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ha : |x + y| ≤ |x| + |y| := by
      simpa only [Real.norm_eq_abs] using norm_add_le x y
    nlinarith
  have hp' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (x + y) ^ 2) hp d
  unfold stripWeight
  calc
    _ ≤ (Real.exp (2 * α * |y|) * Real.exp (2 * α * |x|)) *
        ((2 * (1 + y ^ 2)) * (1 + x ^ 2)) ^ d :=
      mul_le_mul he hp' (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Squared weighted amplitude estimate for every actual lifted value. -/
theorem lifted_amplitude_translate_bound (α : ℝ) (hα : 0 ≤ α) (d : ℕ)
    (x y : ℝ) (v : ℂ) :
    ‖v‖ ^ 2 * stripWeight α d (x + y) ≤
      (Real.exp (2 * α * |y|) * (2 * (1 + y ^ 2)) ^ d) *
        (‖v‖ ^ 2 * stripWeight α d x) := by
  have h := mul_le_mul_of_nonneg_left (stripWeight_translate_bound α hα d x y)
    (sq_nonneg ‖v‖)
  calc
    _ ≤ _ := h
    _ = _ := by ring

variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)

/-- The authentic convolution formula on the genuine idele-class group. -/
noncomputable def ideleClassConvolution (μ : Measure (HeckeIdeleClasses K))
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

/-- Changing a quotient lift by h changes the actual convolved lift by A(phi)h.
This is the term that a quotient-only Mellin estimate does not control. -/
theorem genuineConvolution_lift_change
    (μ : Measure (HeckeIdeleClasses K)) (φ u h : HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K)
    (hu : Integrable (fun g => φ g * u (g⁻¹ * x)) μ)
    (hh : Integrable (fun g => φ g * h (g⁻¹ * x)) μ) :
    ideleClassConvolution K μ φ (fun y => u y + h y) x =
      ideleClassConvolution K μ φ u x + ideleClassConvolution K μ φ h x := by
  simp only [ideleClassConvolution, mul_add]
  exact integral_add hu hh

/-- Necessary lower control of a lift perturbation by both actual convolved lifts. -/
theorem genuineConvolution_lift_leakage_bound
    (μ : Measure (HeckeIdeleClasses K)) (φ u h : HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K)
    (hu : Integrable (fun g => φ g * u (g⁻¹ * x)) μ)
    (hh : Integrable (fun g => φ g * h (g⁻¹ * x)) μ) :
    ‖ideleClassConvolution K μ φ h x‖ ≤
      ‖ideleClassConvolution K μ φ (fun y => u y + h y) x‖ +
      ‖ideleClassConvolution K μ φ u x‖ := by
  rw [genuineConvolution_lift_change K μ φ u h x hu hh]
  have htri := norm_sub_le
    (ideleClassConvolution K μ φ u x + ideleClassConvolution K μ φ h x)
    (ideleClassConvolution K μ φ u x)
  simpa only [add_sub_cancel_left] using htri

#check stripWeight_translate_bound
#print axioms stripWeight_translate_bound
#check lifted_amplitude_translate_bound
#print axioms lifted_amplitude_translate_bound
#check genuineConvolution_lift_change
#print axioms genuineConvolution_lift_change
#check genuineConvolution_lift_leakage_bound
#print axioms genuineConvolution_lift_leakage_bound
end MasulloGRH
