import Mathlib

open MeasureTheory Filter
open scoped BigOperators Topology

namespace NMeasuredShells

variable {X E : Type*} [MeasurableSpace X]

/-- Shell pairing always uses the original quotient Haar measure `mu`. -/
noncomputable def shell (mu : Measure X) (p : X → ℝ) (f : X → ℂ) : ℂ :=
  ∫ x, (p x : ℂ) * f x ∂mu

/-- Bounded measurable shell masks need no separate integrability assumption. -/
theorem masked_integrable (mu : Measure X) (p : X → ℝ) (f : X → ℂ)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => (p x : ℂ) * f x) mu := by
  apply hf.norm.mono'
    ((Complex.continuous_ofReal.measurable.comp hp).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
  simpa using mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg (f x))

/-- A finite set of positive descended masks may overlap. -/
theorem finite_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ)
    (hf : Integrable f mu)
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1)
    (hi : ∀ e ∈ F, Integrable (fun x => (p e x : ℂ) * f x) mu) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  calc
    _ ≤ ∑ e ∈ F, ∫ x, ‖(p e x : ℂ) * f x‖ ∂mu := by
      exact Finset.sum_le_sum (fun e he => norm_integral_le_integral_norm _)
    _ = ∫ x, ∑ e ∈ F, ‖(p e x : ℂ) * f x‖ ∂mu := by
      symm
      exact integral_finset_sum F (fun e he => (hi e he).norm)
    _ ≤ ∫ x, ‖f x‖ ∂mu := by
      apply integral_mono
        (integrable_finset_sum F (fun e he => (hi e he).norm)) hf.norm
      intro x
      calc
        (∑ e ∈ F, ‖(p e x : ℂ) * f x‖) = (∑ e ∈ F, p e x) * ‖f x‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e he
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp e he x)]
        _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hs x) (norm_nonneg _)
        _ = ‖f x‖ := one_mul _

/-- Discharges mask integrability for the positive overlapping partition. -/
theorem measurable_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ) (hf : Integrable f mu)
    (hm : ∀ e ∈ F, Measurable (p e))
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  apply finite_shell_contraction mu F p f hf hp hs
  intro e he
  apply masked_integrable mu (p e) f (hm e he) (hp e he) _ hf
  intro x
  exact (Finset.single_le_sum (fun j hj => hp j hj x) he).trans (hs x)

omit [MeasurableSpace X] in
/-- Exact finite regularizer: the narrow remainder has a PLUS sign. -/
theorem regularizer_plus (wide narrow sandwich regNarrow : X → ℂ) :
    (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) = (fun x => wide x - sandwich x) := by
  funext x
  ring

/-- The correction identity holds under every mask before any limit. -/
theorem regularized_shell_eq (mu : Measure X) (p : X → ℝ)
    (wide narrow sandwich regNarrow : X → ℂ) :
    shell mu p (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) =
      shell mu p (fun x => wide x - sandwich x) := by
  rw [regularizer_plus]

/-- A trace-zero transport has a retained masked boundary contribution. -/
theorem shell_sub (mu : Measure X) (p : X → ℝ) (f g : X → ℂ)
    (hf : Integrable (fun x => (p x : ℂ) * f x) mu)
    (hg : Integrable (fun x => (p x : ℂ) * g x) mu) :
    shell mu p (fun x => f x - g x) = shell mu p f - shell mu p g := by
  simp only [shell, mul_sub]
  exact integral_sub hf hg

/-- Original representative and incoming-mask boundaries telescope before integration. -/
theorem boundary_repairs (indicator outgoing incoming : ℂ) :
    indicator - incoming = (indicator - outgoing) + (outgoing - incoming) := by ring

/-- The omitted residue is bounded by every paid finite shell enclosure. -/
theorem finite_residue_certificate [Fintype E]
    (v w : E → ℂ) (m : ℕ) (err : ℝ)
    (hm : ∑ e, v e = (m : ℂ))
    (he : (∑ e, ‖v e - w e‖) ≤ err) :
    ‖(m : ℂ) - ∑ e, w e‖ ≤ err := by
  rw [← hm, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans he

end NMeasuredShells

#print axioms NMeasuredShells.finite_shell_contraction
#print axioms NMeasuredShells.regularizer_plus
#print axioms NMeasuredShells.boundary_repairs
#print axioms NMeasuredShells.finite_residue_certificate
