import Mathlib

/-! Round 54 C. A concrete convolution calculation on the genuine idele-class
 group. This is an input to the spectral trace calculation, not a trace theorem.
 The Sobolev quotient, nuclearity, genuine zero divisor, and limit remain open. -/
open scoped NumberField
open MeasureTheory

namespace MasulloTrace
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev IdeleClasses := HeckeIdeles K ⧸ principalIdeles K

variable [MeasurableSpace (IdeleClasses K)]

/-- The actual left convolution formula from manuscript 10.4.2.26.
No assertion about its Sobolev domain is built into this definition. -/
noncomputable def convolution (μ : Measure (IdeleClasses K))
    (φ f : IdeleClasses K → ℂ) (x : IdeleClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

/-- Mellin transform with the manuscript's positive-character convention. -/
noncomputable def mellin (μ : Measure (IdeleClasses K))
    (φ : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ) : ℂ :=
  ∫ g, φ g * (c g : ℂ) ∂μ

/-- Convolution acts on the inverse of a genuine idele-class character with
 the positive-convention Mellin eigenvalue. This does not identify a zero. -/
theorem convolution_inverse_character
    (μ : Measure (IdeleClasses K)) (φ : IdeleClasses K → ℂ)
    (c : IdeleClasses K →* ℂˣ) (x : IdeleClasses K) :
    convolution K μ φ (fun y => (c (y⁻¹) : ℂ)) x =
      mellin K μ φ c * (c (x⁻¹) : ℂ) := by
  unfold convolution mellin
  have h (g : IdeleClasses K) :
      φ g * (c ((g⁻¹ * x)⁻¹) : ℂ) =
        (φ g * (c g : ℂ)) * (c (x⁻¹) : ℂ) := by
    have he : (g⁻¹ * x)⁻¹ = x⁻¹ * g := by
      exact (mul_inv_rev g⁻¹ x).trans (congrArg (fun z => x⁻¹ * z) (inv_inv g))
    have hc : c ((g⁻¹ * x)⁻¹) = c (x⁻¹) * c g := by
      rw [he]
      exact c.map_mul _ _
    have hv := congrArg (fun u : ℂˣ => (u : ℂ)) hc
    change (c ((g⁻¹ * x)⁻¹) : ℂ) = (c (x⁻¹) : ℂ) * (c g : ℂ) at hv
    rw [hv]
    ring
  simp_rw [h]
  exact integral_mul_const _ _

variable [MeasurableMul (IdeleClasses K)]

/-- The coefficient functional used in 10.4.2.22 transforms by the genuine
 character. Left invariance of the measure is the exact required hypothesis. -/
theorem mellin_left_translate (μ : Measure (IdeleClasses K))
    [μ.IsMulLeftInvariant] (f : IdeleClasses K → ℂ)
    (c : IdeleClasses K →* ℂˣ) (g : IdeleClasses K) :
    (∫ x, f (g⁻¹ * x) * (c x : ℂ) ∂μ) =
      (c g : ℂ) * mellin K μ f c := by
  calc
    _ = ∫ y, f (g⁻¹ * (g * y)) * (c (g * y) : ℂ) ∂μ :=
      (integral_mul_left_eq_self (fun x => f (g⁻¹ * x) * (c x : ℂ)) g).symm
    _ = ∫ y, (c g : ℂ) * (f y * (c y : ℂ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he : g⁻¹ * (g * y) = y := inv_mul_cancel_left g y
      rw [he, c.map_mul]
      change f y * ((c g : ℂ) * (c y : ℂ)) = _
      ring
    _ = _ := integral_const_mul _ _

/-- Fubini justified Mellin coefficient identity for the actual convolution.
The product integrability premise is stated, not inferred from an unproved
Sobolev or spectral estimate. -/
theorem mellin_convolution (μ : Measure (IdeleClasses K))
    [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (h : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ)) (μ.prod μ)) :
    mellin K μ (convolution K μ φ f) c =
      mellin K μ φ c * mellin K μ f c := by
  change (∫ x, (∫ g, φ g * f (g⁻¹ * x) ∂μ) * (c x : ℂ) ∂μ) = _
  calc
    _ = ∫ x, ∫ g, φ g * f (g⁻¹ * x) * (c x : ℂ) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const _ _).symm
    _ = ∫ g, ∫ x, φ g * f (g⁻¹ * x) * (c x : ℂ) ∂μ ∂μ :=
      integral_integral_swap h
    _ = ∫ g, φ g * ((c g : ℂ) * mellin K μ f c) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp_rw [mul_assoc]
      rw [integral_const_mul, mellin_left_translate K μ f c g]
    _ = mellin K μ φ c * mellin K μ f c := by
      simp_rw [← mul_assoc]
      exact integral_mul_const _ _

/-- The same Fubini premise certifies that the output Mellin integral exists;
this conclusion does not rely on the default value of a divergent integral. -/
theorem mellin_convolution_integrable (μ : Measure (IdeleClasses K))
    [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (h : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ)) (μ.prod μ)) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ)) μ ∧
    mellin K μ (convolution K μ φ f) c =
      mellin K μ φ c * mellin K μ f c := by
  constructor
  · have hi := h.integral_prod_left
    change Integrable (fun x => ∫ g, φ g * f (g⁻¹ * x) * (c x : ℂ) ∂μ) μ at hi
    simp_rw [integral_mul_const] at hi
    exact hi
  · exact mellin_convolution K μ φ f c h

#check mellin_convolution_integrable
#print axioms mellin_convolution_integrable
#check mellin_convolution
#print axioms mellin_convolution
#check mellin_left_translate
#print axioms mellin_left_translate
#check convolution_inverse_character
#print axioms convolution_inverse_character
end MasulloTrace
