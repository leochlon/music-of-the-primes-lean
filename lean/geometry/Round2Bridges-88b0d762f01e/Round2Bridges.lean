import Mathlib

/-!
Independent bridges for manuscript 10.4 and 12. No target theorem is an axiom.
The integral-series argument is adapted from ALPO IntegralEqTsumFd.setIntegral_tsum_fd.
The finite trace argument is adapted from Fermat's orthonormal cutTrace proof.
-/
noncomputable section
open MeasureTheory

namespace GeometricTraceR02

section Algebra
variable {E Q : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup Q] [Module ℂ Q]

theorem quotient_factorization
    (A P : E →ₗ[ℂ] E) (q : E →ₗ[ℂ] Q) (S : Q →ₗ[ℂ] E)
    (B : Q →ₗ[ℂ] Q) (hSq : S.comp q = P) (hA : q.comp A = B.comp q) :
    P.comp A = (S.comp B).comp q := by
  rw [← hSq, LinearMap.comp_assoc, hA, ← LinearMap.comp_assoc]

theorem projection_after_convolution
    (A P : E →ₗ[ℂ] E) (hV : ∀ x, P (A (x - P x)) = 0) :
    P.comp A = (P.comp A).comp P := by
  ext x
  have h := hV x
  simp only [map_sub, sub_eq_zero] at h
  exact h

/-- The dual-action series has projection AFTER convolution. -/
theorem lifted_series_order {ι : Type*} (t : Finset ι)
    (A : E →ₗ[ℂ] E) (q : E →ₗ[ℂ] Q) (S : Q →ₗ[ℂ] E)
    (f : ι → Q →ₗ[ℂ] ℂ) (v : ι → Q) (x : E) :
    S (∑ i ∈ t, f i (q (A x)) • v i) =
      ∑ i ∈ t, f i (q (A x)) • S (v i) := by
  simp
end Algebra

/-- If k is a Haar kernel, k/w is its weighted-measure kernel. -/
theorem weighted_kernel_cancel (k w u : ℂ) (hw : w ≠ 0) :
    (k / w) * (w * u) = k * u := by
  field_simp

section Series
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]
  (μ : Measure X) (F : ι → X → ℂ)

theorem integral_tsum_of_summable_norm
    (hF : ∀ i, Integrable (F i) μ)
    (habs : Summable (fun i => ∫ x, ‖F i x‖ ∂μ)) :
    (∫ x, ∑' i, F i x ∂μ) = ∑' i, ∫ x, F i x ∂μ := by
  exact (hasSum_integral_of_summable_integral_norm hF habs).tsum_eq.symm
end Series

section FiniteTrace
variable {E ι X : Type*} [AddCommGroup E] [Module ℂ E]
  [Fintype ι] [DecidableEq ι] [MeasurableSpace X]

theorem finite_trace_of_integral_coordinates
    (b : Module.Basis ι ℂ E) (T : E →ₗ[ℂ] E)
    (μ : Measure X) (d : ι → X → ℂ)
    (hcoord : ∀ i, b.repr (T (b i)) i = ∫ x, d i x ∂μ) :
    LinearMap.trace ℂ E T = ∑ i, ∫ x, d i x ∂μ := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Matrix.diag_apply, LinearMap.toMatrix_apply] using hcoord i
end FiniteTrace

end GeometricTraceR02

#print axioms GeometricTraceR02.quotient_factorization
#print axioms GeometricTraceR02.integral_tsum_of_summable_norm
#print axioms GeometricTraceR02.finite_trace_of_integral_coordinates
