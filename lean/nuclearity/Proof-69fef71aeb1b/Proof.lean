import Mathlib

/- Named premise of manuscript (10.4.2.5), lines 27711--27728:
   closed geometric translation invariance passes to Bochner convolution.
   No nuclearity, nuclear cost, or spectral summability is assumed here.
   Native adelic attachment remains a separate, explicitly open obligation. -/
open MeasureTheory
open scoped ENNReal
namespace Round173B
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed-subspace invariance for the actual order: convolution first. -/
theorem convolution_mem (G : Submodule ℂ H) [CompleteSpace G]
    (μ : Measure X) (T : X → H →L[ℂ] H) (h : X → ℂ)
    (hinv : ∀ t x, x ∈ G → T t x ∈ G)
    (x : H) (hx : x ∈ G)
    (hint : Integrable (fun t => h t • T t x) μ) :
    (∫ t, h t • T t x ∂μ) ∈ G := by
  let P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H -
    G.subtypeL.comp G.orthogonalProjection
  have hp : ∀ v : H, v ∈ G → P v = 0 := by
    intro v hv
    change v - (G.orthogonalProjection v : H) = 0
    have he := Submodule.orthogonalProjection_mem_subspace_eq_self (⟨v, hv⟩ : G)
    rw [he]
    exact sub_self v
  have hz : ∀ t, P (h t • T t x) = 0 := by
    intro t
    exact hp _ (G.smul_mem _ (hinv t x hx))
  have hi : P (∫ t, h t • T t x ∂μ) = 0 := by
    rw [← P.integral_comp_comm hint]
    simp only [hz, integral_zero]
  change (∫ t, h t • T t x ∂μ) -
    (G.orthogonalProjection (∫ t, h t • T t x ∂μ) : H) = 0 at hi
  rw [sub_eq_zero.mp hi]
  exact (G.orthogonalProjection _).property

/-- Construct the quotient action from invariance, rather than assuming it. -/
theorem convolution_quotient_intertwining
    (G : Submodule ℂ H) [CompleteSpace G]
    (μ : Measure X) (T : X → H →L[ℂ] H) (h : X → ℂ)
    (hinv : ∀ t x, x ∈ G → T t x ∈ G)
    (A : H →L[ℂ] H)
    (hA : ∀ x, A x = ∫ t, h t • T t x ∂μ)
    (hint : ∀ x, Integrable (fun t => h t • T t x) μ) :
    ∃ B : (H ⧸ G) →ₗ[ℂ] (H ⧸ G),
      ∀ x, B (G.mkQ x) = G.mkQ (A x) := by
  have hi : G ≤ G.comap A.toLinearMap := by
    intro x hx
    change A x ∈ G
    rw [hA]
    exact convolution_mem G μ T h hinv x hx (hint x)
  exact ⟨G.mapQ G A.toLinearMap hi, fun x => rfl⟩
/-- The genuine complement projector, with codomain the ambient Hilbert space. -/
noncomputable def spectralProjection (G : Submodule ℂ H) [CompleteSpace G] :
    H →L[ℂ] H := ContinuousLinearMap.id ℂ H - G.subtypeL.comp G.orthogonalProjection

/-- Algebraic quotient factorization (10.4.2.5), constructing both quotient maps.
    Boundedness/isometry of S and nuclearity of B are not claimed by this theorem. -/
theorem projected_convolution_factors
    (G : Submodule ℂ H) [CompleteSpace G]
    (μ : Measure X) (T : X → H →L[ℂ] H) (h : X → ℂ)
    (hinv : ∀ t x, x ∈ G → T t x ∈ G)
    (A : H →L[ℂ] H)
    (hA : ∀ x, A x = ∫ t, h t • T t x ∂μ)
    (hint : ∀ x, Integrable (fun t => h t • T t x) μ) :
    ∃ B : (H ⧸ G) →ₗ[ℂ] (H ⧸ G), ∃ S : (H ⧸ G) →ₗ[ℂ] H,
      (∀ x, B (G.mkQ x) = G.mkQ (A x)) ∧
      (∀ x, S (G.mkQ x) = spectralProjection G x) ∧
      (∀ x, spectralProjection G (A x) = S (B (G.mkQ x))) := by
  obtain ⟨B, hB⟩ := convolution_quotient_intertwining G μ T h hinv A hA hint
  have hk : G ≤ (spectralProjection G).toLinearMap.ker := by
    intro v hv
    change v - (G.orthogonalProjection v : H) = 0
    have he := Submodule.orthogonalProjection_mem_subspace_eq_self (⟨v, hv⟩ : G)
    rw [he]
    exact sub_self v
  refine ⟨B, G.liftQ (spectralProjection G).toLinearMap hk, hB, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rw [hB x]
    rfl
end Round173B
#check Round173B.convolution_mem
#print axioms Round173B.convolution_mem
#check Round173B.convolution_quotient_intertwining
#print axioms Round173B.convolution_quotient_intertwining

#check Round173B.projected_convolution_factors
#print axioms Round173B.projected_convolution_factors
