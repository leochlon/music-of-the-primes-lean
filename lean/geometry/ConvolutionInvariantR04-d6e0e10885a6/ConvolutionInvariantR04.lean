import Mathlib

/- Integrated invariance for a genuine orthogonal projection. The measure is
arbitrary; compactness and finite total mass are not hidden assumptions. -/
open MeasureTheory
namespace GeometricTraceR04

variable {G H : Type*} [MeasurableSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrated_preserves
    (μ : Measure G) (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (R : G → H →L[ℂ] H) (hR : ∀ g v, v ∈ V → R g v ∈ V)
    (h : G → ℂ) (A : H →L[ℂ] H)
    (hint : ∀ v, Integrable (fun g => h g • R g v) μ)
    (hA : ∀ v, A v = ∫ g, h g • R g v ∂μ) :
    ∀ v ∈ V, A v ∈ V := by
  intro v hv
  apply V.starProjection_eq_self_iff.mp
  rw [hA v, ← V.starProjection.integral_comp_comm (hint v)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun g =>
    V.starProjection_eq_self_iff.mpr (V.smul_mem (h g) (hR g v hv))

theorem integrated_projection_order
    (μ : Measure G) (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (R : G → H →L[ℂ] H) (hR : ∀ g v, v ∈ V → R g v ∈ V)
    (h : G → ℂ) (A : H →L[ℂ] H)
    (hint : ∀ v, Integrable (fun g => h g • R g v) μ)
    (hA : ∀ v, A v = ∫ g, h g • R g v ∂μ) :
    (ContinuousLinearMap.id ℂ H - V.starProjection).comp A =
      ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A).comp
        (ContinuousLinearMap.id ℂ H - V.starProjection) := by
  have hinv := integrated_preserves μ V R hR h A hint hA
  ext x
  have hm := hinv (V.starProjection x) (V.starProjection_apply_mem x)
  have hz := V.starProjection_eq_self_iff.mpr hm
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  rw [hz]
  abel

#print axioms integrated_preserves
#print axioms integrated_projection_order
end GeometricTraceR04
