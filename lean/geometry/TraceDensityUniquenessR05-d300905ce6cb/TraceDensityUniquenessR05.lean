import Mathlib

/- The determining-measure step used in the factorization-independent
trace density construction for the actual T_h; see GLOBAL_R05.md.
This is not an assumption identifying an arithmetic kernel. -/
namespace TraceDensityUniquenessR05
open MeasureTheory

theorem density_unique {X : Type*} [MeasurableSpace X] (mu : Measure X)
    [SigmaFinite mu] (d e : X → ℂ) (hd : Integrable d mu) (he : Integrable e mu)
    (h : ∀ S : Set X, MeasurableSet S → mu S < ⊤ →
      (∫ x in S, d x ∂mu) = ∫ x in S, e x ∂mu) : d =ᵐ[mu] e := by
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hd.integrableOn) (fun _ _ _ => he.integrableOn) h

/-- Two factor-row constructions with the same localized traces determine
one a.e. density. Equality of only their total integrals is not a premise. -/
theorem density_unique_of_localized_trace {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] (d e : X → ℂ)
    (hd : Integrable d mu) (he : Integrable e mu) (tau : Set X → ℂ)
    (hdT : ∀ S : Set X, MeasurableSet S → mu S < ⊤ →
      tau S = ∫ x in S, d x ∂mu)
    (heT : ∀ S : Set X, MeasurableSet S → mu S < ⊤ →
      tau S = ∫ x in S, e x ∂mu) : d =ᵐ[mu] e := by
  apply density_unique mu d e hd he
  intro S hS hfin
  exact (hdT S hS hfin).symm.trans (heT S hS hfin)

end TraceDensityUniquenessR05
#print axioms TraceDensityUniquenessR05.density_unique_of_localized_trace
