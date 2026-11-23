import Mathlib

/-! Actual trace-density control used in GLOBAL_ROW_LIMIT_R06.md.
The Holder argument is copied at its exact general scope from ALPO
HilbertSchmidtKernel.lean:12-27 and checked here.  Adelic instantiation
and the trace-class diagonal construction are paper mathematics. -/
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ActualRowDensityR06

 theorem product_density_sq_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f g : X → ℂ)
    (hf : AEStronglyMeasurable f mu) (hg : AEStronglyMeasurable g mu) :
    (∫⁻ x, ‖f x * g x‖ₑ ∂mu)^2 ≤
      (∫⁻ x, ‖f x‖ₑ^2 ∂mu) * ∫⁻ x, ‖g x‖ₑ^2 ∂mu := by
  simp only [enorm_mul]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two hf.enorm hg.enorm
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂mu)^2
      ≤ ((∫⁻ x, ‖f x‖ₑ^2 ∂mu)^(1/2 : ℝ) *
          (∫⁻ x, ‖g x‖ₑ^2 ∂mu)^(1/2 : ℝ))^2 := by gcongr
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_natCast (_ ^ (1/2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

 theorem multiplier_row {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (eta : ℂ) (k v : H) :
    ⟪star eta • k, v⟫_ℂ = eta * ⟪k,v⟫_ℂ := by
  simp [mul_comm]

 theorem density_unique {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] (d e : X → ℂ)
    (hd : Integrable d mu) (he : Integrable e mu)
    (h : ∀ S : Set X, MeasurableSet S → mu S < ⊤ →
      (∫ x in S, d x ∂mu) = ∫ x in S, e x ∂mu) : d =ᵐ[mu] e := by
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hd.integrableOn) (fun _ _ _ => he.integrableOn) h

 def leftShift : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
 def rightShift : Matrix (Fin 2) (Fin 2) ℂ := !![0,0;1,0]

 /-- Cyclic trace equality cannot identify the measured diagonal. -/
 theorem cyclic_trace_not_density :
    Matrix.trace (leftShift * rightShift) =
      Matrix.trace (rightShift * leftShift) ∧
    (leftShift * rightShift) 0 0 ≠ (rightShift * leftShift) 0 0 := by
  norm_num [leftShift, rightShift, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]

end ActualRowDensityR06
#print axioms ActualRowDensityR06.product_density_sq_bound
#print axioms ActualRowDensityR06.multiplier_row
#print axioms ActualRowDensityR06.density_unique
#print axioms ActualRowDensityR06.cyclic_trace_not_density
