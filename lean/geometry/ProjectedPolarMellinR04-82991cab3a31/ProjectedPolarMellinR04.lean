import Mathlib

/-!
Projection-after-convolution and a strong expansion in the actual spectral
subspace. Adapted from Fermat's OrthoExpand.main: use a Hilbert basis of the
closed subspace, map its projection expansion, and prove annihilation of the
complement from invariance. No nuclearity or trace assertion is assumed.
-/
noncomputable section
open scoped InnerProductSpace
namespace GeometricTraceR03

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def spectralProjection (V : Submodule ℂ H) [CompleteSpace V] : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - V.starProjection

theorem spectralProjection_eq_orthogonal (V : Submodule ℂ H) [CompleteSpace V]
    (x : H) : spectralProjection V x = Vᗮ.starProjection x := by
  change x - V.starProjection x = Vᗮ.starProjection x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (V.sub_starProjection_mem_orthogonal x)
  have hv : V.starProjection x ∈ Vᗮᗮ :=
    V.le_orthogonal_orthogonal (V.starProjection_apply_mem x)
  simpa only [sub_sub_cancel] using hv

theorem geometric_compression (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (hA : ∀ v ∈ V, A v ∈ V) :
    (spectralProjection V).comp A =
      ((spectralProjection V).comp A).comp (spectralProjection V) := by
  ext x
  have hv : A (V.starProjection x) ∈ V := hA _ (V.starProjection_apply_mem x)
  have hp : V.starProjection (A (V.starProjection x)) = A (V.starProjection x) :=
    V.starProjection_eq_self_iff.mpr hv
  simp only [spectralProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hp]
  abel

variable [CompleteSpace H]

/-- Strong vector expansion; this is not absolute summability in trace norm. -/
theorem projected_expansion (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (hA : ∀ v ∈ V, A v ∈ V)
    {ι : Type*} (b : HilbertBasis ι ℂ Vᗮ) (x : H) :
    HasSum (fun i => ⟪(b i : H), x⟫_ℂ • spectralProjection V (A (b i)))
      (spectralProjection V (A x)) := by
  let T := (spectralProjection V).comp A
  have hs := (T.comp Vᗮ.subtypeL).hasSum (b.hasSum_orthogonalProjection x)
  have hc : T x = T (spectralProjection V x) := by
    exact congrArg (fun S : H →L[ℂ] H => S x) (geometric_compression V A hA)
  rw [spectralProjection_eq_orthogonal] at hc
  simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    map_smul, ← Submodule.starProjection_apply, ← hc, T] using hs

end GeometricTraceR03

#print axioms GeometricTraceR03.geometric_compression
#print axioms GeometricTraceR03.projected_expansion


/-! The actual compact polar defect constructed in APPLICATION_R04.md.
The analytic vectors are not axiomatized in this file. -/
namespace ProjectedPolarR04
open GeometricTraceR03
open scoped InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem projection_kills_theta (V : Submodule ℂ H) [CompleteSpace V]
    {x : H} (hx : x ∈ V) : spectralProjection V x = 0 := by
  simp only [spectralProjection, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, V.starProjection_eq_self_iff.mpr hx, sub_self]

/-- Project the actual regularization identity, retaining its compact defect. -/
theorem projected_polar_action (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ V, A x ∈ V)
    (v k d : H) (c : ℂ) (hk : k ∈ V)
    (ha : A v = c • v + k + d) :
    spectralProjection V (A (spectralProjection V v)) =
      c • spectralProjection V v + spectralProjection V d := by
  have hc := congrArg (fun T : H →L[ℂ] H => T v)
    (geometric_compression V A hA)
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [← hc, ha, map_add, map_add, map_smul,
    projection_kills_theta V hk, add_zero]

/-- A norm-one dilation fixes the true projected polar vector. -/
theorem projected_polar_fixed (V : Submodule ℂ H) [CompleteSpace V]
    (R : H →L[ℂ] H) (v : H)
    (hcomm : (spectralProjection V).comp R = R.comp (spectralProjection V))
    (hv : R v - v ∈ V) : R (spectralProjection V v) = spectralProjection V v := by
  have hz := projection_kills_theta V hv
  rw [map_sub, sub_eq_zero] at hz
  have hc := congrArg (fun T : H →L[ℂ] H => T v) hcomm
  simp only [ContinuousLinearMap.comp_apply] at hc
  exact hc.symm.trans hz

/-- Coefficient form of the resonant-free Mellin defect formula. -/
theorem mellin_defect_cancellation (z b m p J : ℂ) (hs : z + b ≠ 0) :
    (m - p) * (J / (z + b)) * (z + b) = (m - p) * J := by
  field_simp

/-- The two compact corrections have opposite signs in the actual polar action. -/
theorem two_polar_actions (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ V, A x ∈ V)
    (v₀ v₁ k₀ k₁ c₀ c₁ : H) (p q : ℂ)
    (hk₀ : k₀ ∈ V) (hk₁ : k₁ ∈ V)
    (h₀ : A v₀ = p • v₀ + k₀ + c₀)
    (h₁ : A v₁ = q • v₁ + k₁ - c₁) :
    spectralProjection V (A (spectralProjection V v₀)) =
        p • spectralProjection V v₀ + spectralProjection V c₀ ∧
    spectralProjection V (A (spectralProjection V v₁)) =
        q • spectralProjection V v₁ - spectralProjection V c₁ := by
  constructor
  · exact projected_polar_action V A hA v₀ k₀ c₀ p hk₀ h₀
  · have hh : A v₁ = q • v₁ + k₁ + (-c₁) := by simpa [sub_eq_add_neg] using h₁
    simpa only [map_neg, sub_eq_add_neg] using
      projected_polar_action V A hA v₁ k₁ (-c₁) q hk₁ hh
/-- Changing kappa by delta produces this exact projected coboundary. -/
theorem projected_cutoff_coboundary (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (hA : ∀ x ∈ V, A x ∈ V) (d : H) (c : ℂ) :
    spectralProjection V (A d - c • d) =
      spectralProjection V (A (spectralProjection V d)) -
        c • spectralProjection V d := by
  rw [map_sub, map_smul]
  have hc := congrArg (fun T : H →L[ℂ] H => T d)
    (geometric_compression V A hA)
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [hc]
end
end ProjectedPolarR04
#print axioms ProjectedPolarR04.two_polar_actions
#print axioms ProjectedPolarR04.projected_polar_fixed

#print axioms ProjectedPolarR04.projected_cutoff_coboundary
