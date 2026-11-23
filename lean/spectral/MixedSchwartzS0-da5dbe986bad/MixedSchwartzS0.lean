import Mathlib

/- Source-matched archimedean S_0 component. Conventions are those of
alpo TracePairing.lean and TraceFourier.lean; no Gaussian restriction. -/
namespace ConditionalC885
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open scoped Classical Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedTrace : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := ∑ w, x.1 w + ∑ w, 2 * (x.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, Finset.mul_sum, mul_add]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

def mixedTraceForm : LinearMap.BilinForm ℝ (mixedSpace K) :=
  (LinearMap.mul ℝ (mixedSpace K)).compr₂ (mixedTrace K)

def selfDualMeasure : Measure (mixedSpace K) :=
  (2 ^ nrComplexPlaces K : ℝ≥0∞) • volume

instance : (selfDualMeasure K).IsAddHaarMeasure :=
  Measure.IsAddHaarMeasure.smul _ (by simp) (by simp)

def mixedFourier (f : mixedSpace K → ℂ) : mixedSpace K → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar (selfDualMeasure K) (mixedTraceForm K) f

/-- The actual origin evaluation on the full mixed Schwartz topology. -/
def originCLM : 𝓢(mixedSpace K, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => f 0)
    (fun _ _ => rfl) (fun _ _ => rfl) (by
      refine ⟨{(0, 0)}, 1, by norm_num, ?_⟩
      intro f
      simpa [schwartzSeminormFamily] using f.norm_pow_mul_le_seminorm ℂ 0 0)

/-- Same-Haar Fourier evaluation at zero, represented as a continuous integral. -/
def fourierOriginCLM : 𝓢(mixedSpace K, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.integralCLM ℂ (selfDualMeasure K)

theorem originCLM_apply (f : 𝓢(mixedSpace K, ℂ)) : originCLM K f = f 0 := rfl

theorem mixedFourier_zero (f : mixedSpace K → ℂ) :
    mixedFourier K f 0 = ∫ x, f x ∂selfDualMeasure K := by
  simp [mixedFourier, VectorFourier.fourierIntegral]

theorem fourierOriginCLM_apply (f : 𝓢(mixedSpace K, ℂ)) :
    fourierOriginCLM K f = mixedFourier K f 0 := by
  rw [mixedFourier_zero]
  exact SchwartzMap.integralCLM_apply ℂ f

/-- Both original constraints are retained; this is the archimedean stage,
not an asserted construction of the full adelic inductive limit. -/
def mixedS0 : Submodule ℂ 𝓢(mixedSpace K, ℂ) :=
  (originCLM K).ker ⊓ (fourierOriginCLM K).ker

theorem mem_mixedS0_iff (f : 𝓢(mixedSpace K, ℂ)) :
    f ∈ mixedS0 K ↔ f 0 = 0 ∧ mixedFourier K f 0 = 0 := by
  simp only [mixedS0, Submodule.mem_inf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, originCLM_apply, fourierOriginCLM_apply]

theorem isClosed_mixedS0 : IsClosed (mixedS0 K : Set 𝓢(mixedSpace K, ℂ)) :=
  (originCLM K).isClosed_ker.inter (fourierOriginCLM K).isClosed_ker

theorem continuous_original_constraints :
    Continuous (fun f : 𝓢(mixedSpace K, ℂ) => (f 0, mixedFourier K f 0)) := by
  simpa only [originCLM_apply, fourierOriginCLM_apply] using
    (originCLM K).continuous.prodMk (fourierOriginCLM K).continuous

#print axioms mixedFourier_zero
#print axioms fourierOriginCLM_apply
#print axioms mem_mixedS0_iff
#print axioms isClosed_mixedS0
#print axioms continuous_original_constraints
end
end ConditionalC885
