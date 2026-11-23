import Mathlib

/-! Round 55 F. A conditional kernel step on the genuine idele-class quotient.
No trace, projector, zero set, or Hecke divisor is defined by the desired identity. -/
open scoped NumberField
open MeasureTheory Filter
noncomputable section
namespace MasulloTrace
variable (K : Type*) [Field K] [NumberField K]
abbrev Ideles := (NumberField.AdeleRing (𝓞 K) K)ˣ
noncomputable def principal : Kˣ →* Ideles K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom
abbrev Classes := Ideles K ⧸ (principal K).range

/-- The convolution kernel of the manuscript, using left convolution. -/
def convolutionKernel (φ : Classes K → ℂ) (x y : Classes K) : ℂ := φ (x * y⁻¹)
/-- Definition 10.4.3.7's complement, conditional on an actual spectral kernel S. -/
def geometricKernel (φ : Classes K → ℂ) (S : Classes K → Classes K → ℂ)
    (x y : Classes K) : ℂ := convolutionKernel K φ x y - S x y

/-- The exact diagonal sign; φ vanishing on norm-one classes implies this premise. -/
theorem geometric_diagonal (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ) (x : Classes K) :
    geometricKernel K φ S x x = -S x x := by
  simp [geometricKernel, convolutionKernel, hφ]

#check geometric_diagonal
#print axioms geometric_diagonal


variable [MeasurableSpace (Classes K)]

/-- Exact cutoff diagonal mass, before taking any limit. -/
theorem cutoff_diagonal_mass (μ : Measure (Classes K))
    (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ) (ρ : Classes K → ℂ) :
    (∫ x, ρ x * geometricKernel K φ S x x ∂μ) =
      -(∫ x, ρ x * S x x ∂μ) := by
  simp_rw [geometric_diagonal K φ hφ S, mul_neg]
  exact integral_neg _

/-- This discharges the dominated cutoff limit in the manuscript's complement
kernel calculation. It does not assert the spectral diagonal is integrable. -/
theorem cutoff_geometric_mass_limit (μ : Measure (Classes K))
    (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ)
    (hS : Integrable (fun x => S x x) μ)
    (ρ : ℕ → Classes K → ℂ)
    (hρmeas : ∀ n, AEStronglyMeasurable (ρ n) μ)
    (hρbound : ∀ n, ∀ᵐ x ∂μ, ‖ρ n x‖ ≤ 1)
    (hρlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρ n x) atTop (nhds 1)) :
    Tendsto (fun n => ∫ x, ρ n x * geometricKernel K φ S x x ∂μ)
      atTop (nhds (-(∫ x, S x x ∂μ))) := by
  have hlim : Tendsto (fun n => ∫ x, ρ n x * S x x ∂μ)
      atTop (nhds (∫ x, S x x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖S x x‖)
    · intro n
      exact (hρmeas n).mul hS.aestronglyMeasurable
    · exact hS.norm
    · intro n
      filter_upwards [hρbound n] with x hx
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right hx (norm_nonneg _)).trans_eq (one_mul _)
    · filter_upwards [hρlim] with x hx
      simpa using hx.mul_const (S x x)
  simpa only [cutoff_diagonal_mass K μ φ hφ S] using hlim.neg

#check cutoff_diagonal_mass
#print axioms cutoff_diagonal_mass
#check cutoff_geometric_mass_limit
#print axioms cutoff_geometric_mass_limit


/-- Convolution written in kernel coordinates. With normalized Haar measure this
is the manuscript's A(phi), after the Haar-preserving substitution. -/
def kernelConvolution (μ : Measure (Classes K)) (φ f : Classes K → ℂ)
    (x : Classes K) : ℂ := ∫ y, convolutionKernel K φ x y * f y ∂μ

/-- Explicit operator representation obligation, without asserting the existence
of the manuscript's spectral projector. If S represents A(phi)P, its complement
represents A(phi)(1-P). This fixes the convolution-after-projection order. -/
theorem geometric_action_after_projection (μ : Measure (Classes K))
    (φ f : Classes K → ℂ) (P : (Classes K → ℂ) →ₗ[ℂ] (Classes K → ℂ))
    (S : Classes K → Classes K → ℂ) (x : Classes K)
    (hf : Integrable (fun y => convolutionKernel K φ x y * f y) μ)
    (hPf : Integrable (fun y => convolutionKernel K φ x y * P f y) μ)
    (hSf : Integrable (fun y => S x y * f y) μ)
    (hrep : (∫ y, S x y * f y ∂μ) = kernelConvolution K μ φ (P f) x) :
    (∫ y, geometricKernel K φ S x y * f y ∂μ) =
      kernelConvolution K μ φ (f - P f) x := by
  simp_rw [geometricKernel, sub_mul]
  rw [integral_sub hf hSf, hrep]
  unfold kernelConvolution
  simp_rw [Pi.sub_apply, mul_sub]
  rw [integral_sub hf hPf]

/-- Under the limit theorem's hypotheses, all cutoff diagonal integrals are
ordinary absolutely integrable Bochner integrals. -/
theorem cutoff_geometric_integrable (μ : Measure (Classes K))
    (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ)
    (hS : Integrable (fun x => S x x) μ)
    (ρ : Classes K → ℂ) (hρ : AEStronglyMeasurable ρ μ)
    (hbound : ∀ᵐ x ∂μ, ‖ρ x‖ ≤ 1) :
    Integrable (fun x => ρ x * geometricKernel K φ S x x) μ := by
  simp_rw [geometric_diagonal K φ hφ S, mul_neg]
  exact (hS.bdd_mul hρ hbound).neg

#check geometric_action_after_projection
#print axioms geometric_action_after_projection
#check cutoff_geometric_integrable
#print axioms cutoff_geometric_integrable


/-- The Haar change of variables identifies the kernel operator with the actual
left convolution on the genuine idele-class group. Normalization cancels here;
it is still required separately for the local trace terms. -/
theorem kernelConvolution_eq_leftConvolution
    [MeasurableMul (Classes K)] [MeasurableInv (Classes K)]
    (μ : Measure (Classes K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (φ f : Classes K → ℂ) (x : Classes K) :
    kernelConvolution K μ φ f x = ∫ g, φ g * f (g⁻¹ * x) ∂μ := by
  unfold kernelConvolution convolutionKernel
  have h := integral_div_left_eq_self (fun g => φ g * f (g⁻¹ * x)) μ x
  have hchange (y : Classes K) : (x / y)⁻¹ * x = y :=
    inv_mul_eq_iff_eq_mul.mpr (div_mul_cancel x y).symm
  simp_rw [hchange] at h
  simpa only [div_eq_mul_inv] using h

#check kernelConvolution_eq_leftConvolution
#print axioms kernelConvolution_eq_leftConvolution

/-- The change of variables preserves absolute integrability, so the kernel
identification is not merely an identity of totalized integrals. -/
theorem kernelConvolution_integrable
    [MeasurableMul (Classes K)] [MeasurableInv (Classes K)]
    (μ : Measure (Classes K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (φ f : Classes K → ℂ) (x : Classes K)
    (hf : Integrable (fun g => φ g * f (g⁻¹ * x)) μ) :
    Integrable (fun y => convolutionKernel K φ x y * f y) μ := by
  have h := ((μ.measurePreserving_div_left x).integrable_comp
    hf.aestronglyMeasurable).mpr hf
  change Integrable (fun y => φ (x / y) * f ((x / y)⁻¹ * x)) μ at h
  have hchange (y : Classes K) : (x / y)⁻¹ * x = y :=
    inv_mul_eq_iff_eq_mul.mpr (div_mul_cancel x y).symm
  simp_rw [hchange] at h
  simpa only [convolutionKernel, div_eq_mul_inv] using h

/-- Conditional representation of the actual truncated operator
M_rho A(phi)(1-P), in the order used by (10.4.2.20) and (10.4.3.45).
The spectral representation premise is explicit and is NOT discharged here. -/
theorem truncated_geometric_left_action
    [MeasurableMul (Classes K)] [MeasurableInv (Classes K)]
    (μ : Measure (Classes K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (φ f ρ : Classes K → ℂ)
    (P : (Classes K → ℂ) →ₗ[ℂ] (Classes K → ℂ))
    (S : Classes K → Classes K → ℂ) (x : Classes K)
    (hf : Integrable (fun g => φ g * f (g⁻¹ * x)) μ)
    (hPf : Integrable (fun g => φ g * P f (g⁻¹ * x)) μ)
    (hSf : Integrable (fun y => S x y * f y) μ)
    (hrep : (∫ y, S x y * f y ∂μ) = ∫ g, φ g * P f (g⁻¹ * x) ∂μ) :
    Integrable (fun y => ρ x * (geometricKernel K φ S x y * f y)) μ ∧
    (∫ y, ρ x * (geometricKernel K φ S x y * f y) ∂μ) =
      ρ x * ∫ g, φ g * ((f - P f) (g⁻¹ * x)) ∂μ := by
  have hkf := kernelConvolution_integrable K μ φ f x hf
  have hkPf := kernelConvolution_integrable K μ φ (P f) x hPf
  have hrep' : (∫ y, S x y * f y ∂μ) = kernelConvolution K μ φ (P f) x := by
    rw [kernelConvolution_eq_leftConvolution K μ φ (P f) x]
    exact hrep
  constructor
  · simpa only [geometricKernel, sub_mul, Pi.sub_apply] using
      (hkf.sub hSf).const_mul (ρ x)
  · rw [integral_const_mul,
      geometric_action_after_projection K μ φ f P S x hkf hkPf hSf hrep',
      kernelConvolution_eq_leftConvolution K μ φ (f - P f) x]

#check kernelConvolution_integrable
#print axioms kernelConvolution_integrable
#check truncated_geometric_left_action
#print axioms truncated_geometric_left_action

/-- Conversion from the Haar kernel to the kernel acting against w*mu.
This fixes the inverse weight in (10.4.3.48); the function w still has to be
instantiated by the actual Hardy-Sobolev weight. -/
theorem weighted_geometric_kernel_action (μ : Measure (Classes K))
    (w : Classes K → NNReal) (hw : Measurable w)
    (hwpos : ∀ y, 0 < (w y : ℝ))
    (φ f : Classes K → ℂ) (S : Classes K → Classes K → ℂ) (x : Classes K) :
    (∫ y, ((w y : ℝ)⁻¹ • geometricKernel K φ S x y) * f y
      ∂μ.withDensity (fun y => (w y : ENNReal))) =
    ∫ y, geometricKernel K φ S x y * f y ∂μ := by
  rw [integral_withDensity_eq_integral_smul hw]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [NNReal.smul_def, smul_mul_assoc, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (hwpos y)), one_smul]

/-- The inverse weight in a Hilbert-space kernel cancels on its diagonal
against w*mu. No trace theorem is assumed or concluded here. -/
theorem weighted_geometric_cutoff_mass (μ : Measure (Classes K))
    (w : Classes K → NNReal) (hw : Measurable w)
    (hwpos : ∀ y, 0 < (w y : ℝ))
    (φ ρ : Classes K → ℂ) (S : Classes K → Classes K → ℂ) :
    (∫ x, ρ x * ((w x : ℝ)⁻¹ • geometricKernel K φ S x x)
      ∂μ.withDensity (fun x => (w x : ENNReal))) =
    ∫ x, ρ x * geometricKernel K φ S x x ∂μ := by
  rw [integral_withDensity_eq_integral_smul hw]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [NNReal.smul_def, mul_smul_comm, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (hwpos x)), one_smul]

#check weighted_geometric_kernel_action
#print axioms weighted_geometric_kernel_action
#check weighted_geometric_cutoff_mass
#print axioms weighted_geometric_cutoff_mass

/-- The earlier cutoff limit in precisely the weighted-kernel convention.
This is a diagonal-mass limit, not a claimed operator trace formula. -/
theorem weighted_geometric_cutoff_limit (μ : Measure (Classes K))
    (w : Classes K → NNReal) (hw : Measurable w)
    (hwpos : ∀ y, 0 < (w y : ℝ))
    (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ)
    (hS : Integrable (fun x => S x x) μ)
    (ρ : ℕ → Classes K → ℂ)
    (hρmeas : ∀ n, AEStronglyMeasurable (ρ n) μ)
    (hρbound : ∀ n, ∀ᵐ x ∂μ, ‖ρ n x‖ ≤ 1)
    (hρlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρ n x) atTop (nhds 1)) :
    Tendsto (fun n => ∫ x, ρ n x * ((w x : ℝ)⁻¹ • geometricKernel K φ S x x)
      ∂μ.withDensity (fun x => (w x : ENNReal)))
      atTop (nhds (-(∫ x, S x x ∂μ))) := by
  simp_rw [weighted_geometric_cutoff_mass K μ w hw hwpos φ]
  exact cutoff_geometric_mass_limit K μ φ hφ S hS ρ hρmeas hρbound hρlim

#check weighted_geometric_cutoff_limit
#print axioms weighted_geometric_cutoff_limit
end MasulloTrace
