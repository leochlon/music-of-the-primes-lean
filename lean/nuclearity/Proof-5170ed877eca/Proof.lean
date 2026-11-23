import Mathlib

/-! Round 56 F. A conditional kernel step on the genuine idele-class quotient.
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

/-- The weighted Hilbert-space version needed for (10.4.3.47)-(10.4.3.48).
Here w is the square root of the density defining the Hilbert norm; reciprocal
weights on the kernel cancel against weights on its input. No trace or genuine
spectral-kernel identification is assumed to follow from L2 membership. -/
theorem weighted_truncated_geometric_action
    [MeasurableMul (Classes K)] [MeasurableInv (Classes K)]
    (μ : Measure (Classes K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (φ f ρ w : Classes K → ℂ)
    (P : (Classes K → ℂ) →ₗ[ℂ] (Classes K → ℂ))
    (S : Classes K → Classes K → ℂ) (x : Classes K)
    (hw : ∀ y, w y ≠ 0)
    (hφx : MemLp (fun y => convolutionKernel K φ x y / w y) 2 μ)
    (hf : MemLp (fun y => w y * f y) 2 μ)
    (hPf : MemLp (fun y => w y * P f y) 2 μ)
    (hS : MemLp (fun y => S x y / w y) 2 μ)
    (hrep : (∫ y, S x y * f y ∂μ) = kernelConvolution K μ φ (P f) x) :
    Integrable (fun y => ρ x * (geometricKernel K φ S x y * f y)) μ ∧
    (∫ y, ρ x * (geometricKernel K φ S x y * f y) ∂μ) =
      ρ x * ∫ g, φ g * ((f - P f) (g⁻¹ * x)) ∂μ := by
  have cancel (a b : ℂ) (y : Classes K) : a / w y * (w y * b) = a * b := by
    field_simp [hw y]
  have hkf : Integrable (fun y => convolutionKernel K φ x y * f y) μ := by
    have h := hφx.integrable_mul hf
    change Integrable (fun y => convolutionKernel K φ x y / w y * (w y * f y)) μ at h
    simpa only [cancel] using h
  have hkPf : Integrable (fun y => convolutionKernel K φ x y * P f y) μ := by
    have h := hφx.integrable_mul hPf
    change Integrable (fun y => convolutionKernel K φ x y / w y * (w y * P f y)) μ at h
    simpa only [cancel] using h
  have hSf : Integrable (fun y => S x y * f y) μ := by
    have h := hS.integrable_mul hf
    change Integrable (fun y => S x y / w y * (w y * f y)) μ at h
    simpa only [cancel] using h
  constructor
  · simpa only [geometricKernel, sub_mul] using (hkf.sub hSf).const_mul (ρ x)
  · rw [integral_const_mul,
      geometric_action_after_projection K μ φ f P S x hkf hkPf hSf hrep,
      kernelConvolution_eq_leftConvolution K μ φ (f - P f) x]

#check weighted_truncated_geometric_action
#print axioms weighted_truncated_geometric_action

/-- Compact admissible tests discharge the convolution-row hypothesis in the
weighted action theorem. The spectral representation and spectral row remain
explicit premises; this theorem does not assert the trace identity. -/
theorem weighted_truncated_action_of_compact_test
    [TopologicalSpace (Classes K)] [IsTopologicalGroup (Classes K)]
    [OpensMeasurableSpace (Classes K)]
    [MeasurableMul (Classes K)] [MeasurableInv (Classes K)]
    (μ : Measure (Classes K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f ρ w : Classes K → ℂ)
    (P : (Classes K → ℂ) →ₗ[ℂ] (Classes K → ℂ))
    (S : Classes K → Classes K → ℂ) (x : Classes K)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hwc : Continuous w) (hw : ∀ y, w y ≠ 0)
    (hf : MemLp (fun y => w y * f y) 2 μ)
    (hPf : MemLp (fun y => w y * P f y) 2 μ)
    (hS : MemLp (fun y => S x y / w y) 2 μ)
    (hrep : (∫ y, S x y * f y ∂μ) = kernelConvolution K μ φ (P f) x) :
    Integrable (fun y => ρ x * (geometricKernel K φ S x y * f y)) μ ∧
    (∫ y, ρ x * (geometricKernel K φ S x y * f y) ∂μ) =
      ρ x * ∫ g, φ g * ((f - P f) (g⁻¹ * x)) ∂μ := by
  have hc : Continuous (fun y => convolutionKernel K φ x y) :=
    hφ.comp (continuous_const.mul continuous_id.inv)
  have hs : HasCompactSupport (fun y => convolutionKernel K φ x y) := by
    have h := hφc.comp_homeomorph (Homeomorph.divLeft x)
    change HasCompactSupport (fun y => φ (x / y)) at h
    simpa only [convolutionKernel, div_eq_mul_inv] using h
  have hq : HasCompactSupport (fun y => convolutionKernel K φ x y / w y) := by
    simpa only [div_eq_mul_inv] using (hs.mul_right (f' := fun y => (w y)⁻¹))
  have hrow : MemLp (fun y => convolutionKernel K φ x y / w y) 2 μ :=
    (hc.div hwc hw).memLp_of_hasCompactSupport hq
  exact weighted_truncated_geometric_action K μ φ f ρ w P S x hw hrow hf hPf hS hrep

#check weighted_truncated_action_of_compact_test
#print axioms weighted_truncated_action_of_compact_test
/-- The sum/integral interchange used at (12.5.1.4), followed by the
geometric cutoff limit. The diagonal expansion is an explicit premise on the
chosen representative, not merely equality of Hilbert-Schmidt kernels.
The actual spectral construction remains an obligation. Round 59 derives
diagonal integrability from the tensor hypotheses, rather than assuming it. -/
theorem spectral_tensor_cutoff_limit_of_summable
    (μ : Measure (Classes K)) (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ) (w : Classes K → ℂ)
    (u v : ℕ → Classes K → ℂ) (hw : ∀ x, w x ≠ 0)
    (hu : ∀ n, MemLp (fun x => u n x / w x) 2 μ)
    (hv : ∀ n, MemLp (fun x => w x * v n x) 2 μ)
    (hsum : Summable (fun n => ∫ x, ‖u n x * v n x‖ ∂μ))
    (hdiag : (fun x => S x x) =ᵐ[μ] (fun x => ∑' n, u n x * v n x))
    (ρ : ℕ → Classes K → ℂ)
    (hρmeas : ∀ n, AEStronglyMeasurable (ρ n) μ)
    (hρbound : ∀ n, ∀ᵐ x ∂μ, ‖ρ n x‖ ≤ 1)
    (hρlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρ n x) atTop (nhds 1)) :
    Integrable (fun x => S x x) μ ∧
    (∀ n, Integrable (fun x => ρ n x * geometricKernel K φ S x x) μ) ∧
    (∫ x, geometricKernel K φ S x x ∂μ) = -(∑' n, ∫ x, u n x * v n x ∂μ) ∧
    HasSum (fun n => ∫ x, u n x * v n x ∂μ) (∫ x, S x x ∂μ) ∧
    Tendsto (fun n => ∫ x, ρ n x * geometricKernel K φ S x x ∂μ)
      atTop (nhds (-(∑' n, ∫ x, u n x * v n x ∂μ))) := by
  have hterm : ∀ n, Integrable (fun x => u n x * v n x) μ := by
    intro n
    have h := (hu n).integrable_mul (hv n)
    change Integrable (fun x => u n x / w x * (w x * v n x)) μ at h
    have hc (x : Classes K) : u n x / w x * (w x * v n x) = u n x * v n x := by
      field_simp [hw x]
    simpa only [hc] using h
  have hm (n : ℕ) := (hterm n).aestronglyMeasurable.enorm
  have htotal : (∑' n, ∫⁻ x, ‖u n x * v n x‖ₑ ∂μ) < ⊤ := by
    have heq (n : ℕ) : (∫⁻ x, ‖u n x * v n x‖ₑ ∂μ) =
        ENNReal.ofReal (∫ x, ‖u n x * v n x‖ ∂μ) :=
      lintegral_coe_eq_integral (fun x => ‖u n x * v n x‖₊) (hterm n).norm
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => integral_nonneg (fun x => norm_nonneg _)) hsum]
    exact ENNReal.ofReal_lt_top
  have htonelli : (∫⁻ x, ∑' n, ‖u n x * v n x‖ₑ ∂μ) < ⊤ := by
    rw [lintegral_tsum hm]
    exact htotal
  have hae : ∀ᵐ x ∂μ, Summable (fun n => u n x * v n x) := by
    filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hm) htonelli.ne] with x hx
    exact (ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hx.ne).of_norm
  have hmeas : AEStronglyMeasurable (fun x => ∑' n, u n x * v n x) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (f := fun n x =>
      ∑ i ∈ Finset.range n, u i x * v i x) atTop
    · intro n
      exact (integrable_finset_sum (Finset.range n) (fun i hi => hterm i)).aestronglyMeasurable
    · filter_upwards [hae] with x hx
      exact hx.hasSum.tendsto_sum_nat
  have hseriesInt : Integrable (fun x => ∑' n, u n x * v n x) μ := by
    refine ⟨hmeas, ?_⟩
    exact lt_of_le_of_lt (lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)) htonelli
  have hS : Integrable (fun x => S x x) μ := hseriesInt.congr hdiag.symm
  have hi : (∫ x, S x x ∂μ) = ∫ x, ∑' n, u n x * v n x ∂μ :=
    integral_congr_ae hdiag
  have hseries : HasSum (fun n => ∫ x, u n x * v n x ∂μ) (∫ x, S x x ∂μ) := by
    rw [hi]
    exact hasSum_integral_of_summable_integral_norm hterm hsum
  refine ⟨hS, ?_, ?_, hseries, ?_⟩
  · intro n
    exact cutoff_geometric_integrable K μ φ hφ S hS (ρ n) (hρmeas n) (hρbound n)
  · simp_rw [geometric_diagonal K φ hφ S]
    rw [integral_neg, hseries.tsum_eq]
  · rw [hseries.tsum_eq]
    exact cutoff_geometric_mass_limit K μ φ hφ S hS ρ hρmeas hρbound hρlim

#check spectral_tensor_cutoff_limit_of_summable
#print axioms spectral_tensor_cutoff_limit_of_summable

/-- The missing nuclear-estimate implication in (10.4.3.43) -> (12.5.1.4).
The two moment factors are the reciprocal weighted L2 norms. Their summability
is an explicit nuclear bound on the chosen spectral tensors, not a consequence
of mere convergence of the tensor series. Actual Hecke tensors and this bound
must still be constructed. The derived absolute diagonal convergence is used
immediately in the complement-kernel equality and cutoff limit. -/
theorem spectral_tensor_cutoff_limit_of_L2_nuclear_bound
    (μ : Measure (Classes K)) (φ : Classes K → ℂ) (hφ : φ 1 = 0)
    (S : Classes K → Classes K → ℂ) (w : Classes K → ℂ)
    (u v : ℕ → Classes K → ℂ) (hw : ∀ x, w x ≠ 0)
    (hu : ∀ n, MemLp (fun x => u n x / w x) 2 μ)
    (hv : ∀ n, MemLp (fun x => w x * v n x) 2 μ)
    (hnuclear : Summable (fun n =>
      (∫ x, ‖u n x / w x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫ x, ‖w x * v n x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))))
    (hdiag : (fun x => S x x) =ᵐ[μ] (fun x => ∑' n, u n x * v n x))
    (ρ : ℕ → Classes K → ℂ)
    (hρmeas : ∀ n, AEStronglyMeasurable (ρ n) μ)
    (hρbound : ∀ n, ∀ᵐ x ∂μ, ‖ρ n x‖ ≤ 1)
    (hρlim : ∀ᵐ x ∂μ, Tendsto (fun n => ρ n x) atTop (nhds 1)) :
    Summable (fun n => ∫ x, ‖u n x * v n x‖ ∂μ) ∧
    Integrable (fun x => S x x) μ ∧
    (∀ n, Integrable (fun x => ρ n x * geometricKernel K φ S x x) μ) ∧
    (∫ x, geometricKernel K φ S x x ∂μ) = -(∑' n, ∫ x, u n x * v n x ∂μ) ∧
    HasSum (fun n => ∫ x, u n x * v n x ∂μ) (∫ x, S x x ∂μ) ∧
    Tendsto (fun n => ∫ x, ρ n x * geometricKernel K φ S x x ∂μ)
      atTop (nhds (-(∑' n, ∫ x, u n x * v n x ∂μ))) := by
  have hsum : Summable (fun n => ∫ x, ‖u n x * v n x‖ ∂μ) := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg _)) _ hnuclear
    intro n
    have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
    have hcs := integral_mul_norm_le_Lp_mul_Lq hpq
      (show MemLp (fun x => u n x / w x) (ENNReal.ofReal 2) μ by simpa using hu n)
      (show MemLp (fun x => w x * v n x) (ENNReal.ofReal 2) μ by simpa using hv n)
    have hc (x : Classes K) : u n x / w x * (w x * v n x) = u n x * v n x := by
      field_simp [hw x]
    simpa only [← norm_mul, hc] using hcs
  exact ⟨hsum, spectral_tensor_cutoff_limit_of_summable K μ φ hφ S w u v hw
    hu hv hsum hdiag ρ hρmeas hρbound hρlim⟩

#check spectral_tensor_cutoff_limit_of_L2_nuclear_bound
#print axioms spectral_tensor_cutoff_limit_of_L2_nuclear_bound
end MasulloTrace
