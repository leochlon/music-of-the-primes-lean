import Mathlib
noncomputable section
open MeasureTheory ContinuousLinearMap Filter
open scoped InnerProductSpace Topology ComplexConjugate
namespace GeometricTraceC
private lemma norm_toL1_inner_le_mul_norm {X : Type*} [MeasurableSpace X] {ν : Measure X} (f g : Lp ℂ 2 ν) :
    ‖(L2.integrable_inner f g).toL1 (fun x => ⟪f x, g x⟫_ℂ)‖ ≤ ‖f‖ * ‖g‖ := by
  have : ENNReal.HolderTriple 2 2 1 := ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (p := 2) (q := 2) (r := 1) (μ := ν)
    (Lp.aestronglyMeasurable f) (Lp.aestronglyMeasurable g) (fun u v : ℂ => ⟪u, v⟫_ℂ) 1
    (Filter.Eventually.of_forall fun x => by simpa using norm_inner_le_norm (𝕜 := ℂ) (f x) (g x))
  have e : ‖(L2.integrable_inner f g).toL1 (fun x => ⟪f x, g x⟫_ℂ)‖
      = (eLpNorm (fun x => ⟪f x, g x⟫_ℂ) 1 ν).toReal := by
    simp [Integrable.toL1, Lp.norm_toLp]
  rw [e, Lp.norm_def f, Lp.norm_def g, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)) ?_
  simpa using h


variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
theorem exists_diagonal {ι : Type*} {a b : ι → Lp ℂ 2 ν} (h : Summable fun j => ‖b j‖ * ‖a j‖) :
    ∃ d : X → ℂ, Integrable d ν ∧ ∀ E, HasSum (fun j => ∫ x in E, ⟪b j x, a j x⟫_ℂ ∂ν) (∫ x in E, d x ∂ν) := by
  have hI : ∀ j, Integrable (fun x => ⟪b j x, a j x⟫_ℂ) ν := fun j => L2.integrable_inner (b j) (a j)
  have hs : Summable fun j => (hI j).toL1 (fun x => ⟪b j x, a j x⟫_ℂ) :=
    Summable.of_norm_bounded h (fun j => norm_toL1_inner_le_mul_norm (b j) (a j))
  refine ⟨⇑(∑' j, (hI j).toL1 (fun x => ⟪b j x, a j x⟫_ℂ)), L1.integrable_coeFn _, fun E => ?_⟩
  let g : (X →₁[ν] ℂ) →+ ℂ :=
    { toFun := fun f => ∫ x in E, f x ∂ν
      map_zero' := by
        rw [integral_congr_ae (Lp.coeFn_zero ℂ 1 ν).restrict]
        simp
      map_add' := fun f f' => by
        rw [integral_congr_ae (Lp.coeFn_add f f').restrict]
        exact integral_add (L1.integrable_coeFn f).integrableOn (L1.integrable_coeFn f').integrableOn }
  have hg : Continuous g := continuous_setIntegral E
  have := hs.hasSum.map g hg
  convert this using 1
  · funext j
    simp only [Function.comp_apply, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact integral_congr_ae ((Integrable.coeFn_toL1 (hI j)).restrict).symm


section Algebra
variable {H QH : Type*} [AddCommGroup H] [Module ℂ H]
  [AddCommGroup QH] [Module ℂ QH]
theorem projection_after_convolution (P A : H →ₗ[ℂ] H)
    (hP : ∀ x, P (P x) = P x)
    (hInv : ∀ x, P x = 0 → P (A x) = 0) :
    P.comp (A.comp P) = P.comp A := by
  ext x
  have hker : P (x - P x) = 0 := by simp [map_sub, hP]
  have h := hInv (x - P x) hker
  simp only [map_sub] at h
  exact (sub_eq_zero.mp h).symm

theorem quotient_factorization (P A : H →ₗ[ℂ] H)
    (Q : H →ₗ[ℂ] QH) (S : QH →ₗ[ℂ] H) (B : QH →ₗ[ℂ] QH)
    (hSQ : S.comp Q = P) (hAQ : Q.comp A = B.comp Q) :
    P.comp A = S.comp (B.comp Q) := by
  rw [← hSQ, LinearMap.comp_assoc, hAQ]
end Algebra
end GeometricTraceC
#print axioms GeometricTraceC.exists_diagonal
#print axioms GeometricTraceC.projection_after_convolution
#print axioms GeometricTraceC.quotient_factorization
