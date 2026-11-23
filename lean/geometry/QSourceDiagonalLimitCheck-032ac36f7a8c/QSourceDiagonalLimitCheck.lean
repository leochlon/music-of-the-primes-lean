import Mathlib
set_option linter.unusedSectionVars false

/-! Closure of the BOTH-moment theta image. The arithmetic theta/intertwining
supplier is explicit; no finite Mellin family is substituted for its image. -/
namespace OSourceClosure
open Filter
open scoped Topology
noncomputable section
variable {V H : Type*} [AddCommGroup V] [Module ℂ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoMomentSource (e0 eF : V →ₗ[ℂ] ℂ) : Submodule ℂ V := e0.ker ⊓ eF.ker

def restrictedAction (e0 eF : V →ₗ[ℂ] ℂ) (B : V →ₗ[ℂ] V)
    (l0 lF : ℂ) (h0 : ∀ f, e0 (B f) = l0 * e0 f)
    (hF : ∀ f, eF (B f) = lF * eF f) :
    twoMomentSource e0 eF →ₗ[ℂ] twoMomentSource e0 eF :=
  B.restrict fun f hf => by
    rcases hf with ⟨hf0, hfF⟩
    constructor
    · change e0 (B f) = 0
      rw [h0, show e0 f = 0 from hf0, mul_zero]
    · change eF (B f) = 0
      rw [hF, show eF f = 0 from hfF, mul_zero]

abbrev sourceClosure (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range Theta).topologicalClosure

/-- The actual source action supplies invariance before closure. -/
theorem theta_closure_invariant (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (A : H →L[ℂ] H)
    (B : V →ₗ[ℂ] V) (l0 lF : ℂ)
    (h0 : ∀ f, e0 (B f) = l0 * e0 f)
    (hF : ∀ f, eF (B f) = lF * eF f)
    (hint : ∀ f, A (Theta f) = Theta (restrictedAction e0 eF B l0 lF h0 hF f)) :
    ∀ x ∈ sourceClosure e0 eF Theta, A x ∈ sourceClosure e0 eF Theta := by
  have hr : ∀ x ∈ LinearMap.range Theta, A x ∈ LinearMap.range Theta := by
    rintro x ⟨f, rfl⟩
    exact ⟨restrictedAction e0 eF B l0 lF h0 hF f, (hint f).symm⟩
  intro x hx
  exact map_mem_closure A.continuous hx hr

/-- Source invariance gives PA=PAP, and the exact noncommuting AP-PA block. -/
theorem theta_convolution_first (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (A : H →L[ℂ] H)
    (B : V →ₗ[ℂ] V) (l0 lF : ℂ)
    (h0 : ∀ f, e0 (B f) = l0 * e0 f)
    (hF : ∀ f, eF (B f) = lF * eF f)
    (hint : ∀ f, A (Theta f) = Theta (restrictedAction e0 eF B l0 lF h0 hF f))
    (x : H) :
    let S := (sourceClosure e0 eF Theta).starProjection
    let P := ContinuousLinearMap.id ℂ H - S
    P (A x) = P (A (P x)) ∧ A (P x) - P (A x) = S (A (P x)) := by
  dsimp only
  have hInv := theta_closure_invariant e0 eF Theta A B l0 lF h0 hF hint
  have hS : (sourceClosure e0 eF Theta).starProjection
      (A ((sourceClosure e0 eF Theta).starProjection x)) =
      A ((sourceClosure e0 eF Theta).starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hInv _ ((sourceClosure e0 eF Theta).starProjection_apply_mem x))
  constructor <;>
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hS] <;> abel

/-- A masked geometric defect has the opposite spectral sign, before limits. -/
theorem paired_masked_order (A S M : H →L[ℂ] H) (x : H) :
    let P := ContinuousLinearMap.id ℂ H - S
    (M (A (P x)) - M (P (A x))) +
      (M (A (S x)) - M (S (A x))) = 0 := by
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub]
  abel

/-- Every finite source projection is removed on the right of the true PA.
The output factor remains on the left of convolution throughout. -/
theorem source_input_killed (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (A : H →L[ℂ] H)
    (hInv : ∀ x ∈ sourceClosure e0 eF Theta, A x ∈ sourceClosure e0 eF Theta)
    (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (hF : F ≤ sourceClosure e0 eF Theta) (x : H) :
    (ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection)
      (A (F.starProjection x)) = 0 := by
  have h := Submodule.starProjection_eq_self_iff.mpr
    (hInv _ (hF (F.starProjection_apply_mem x)))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, h, sub_self]

end
end OSourceClosure
#print axioms OSourceClosure.theta_convolution_first
#print axioms OSourceClosure.paired_masked_order
#print axioms OSourceClosure.source_input_killed

-- Reviewed projection-exhaustion source, verbatim except import.
set_option linter.unusedSectionVars false

namespace Masullo.NestedProjection
open Filter
open scoped Topology
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

/-- Nested orthogonal projections absorb the global projection on the right.
This is a projection identity, not commutation with convolution. -/
theorem nested_projection (E F : Submodule ℂ H)
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hFE : F ≤ E) (x : H) : F.starProjection (E.starProjection x) = F.starProjection x := by
  have hd := (Submodule.mem_orthogonal E _).mp
    (Submodule.sub_starProjection_mem_orthogonal (K := E) x)
  have hz : F.starProjection (x-E.starProjection x) = 0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (F.zero_mem)
    intro w hw
    simpa only [sub_zero] using inner_eq_zero_symm.mpr (hd w (hFE hw))
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- A finite-subspace approximant controls the GLOBAL projected error.
There is no common compact support restriction on x. -/
theorem projection_recovery_bound (E F : Submodule ℂ H)
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hFE : F ≤ E) (x v : H) (hv : v ∈ F) :
    ‖F.starProjection x-E.starProjection x‖ ≤ 2*‖E.starProjection x-v‖ := by
  have he := nested_projection E F hFE x
  have hvp : F.starProjection v = v := Submodule.starProjection_eq_self_iff.mpr hv
  have hid : F.starProjection x-E.starProjection x =
      F.starProjection (E.starProjection x-v) - (E.starProjection x-v) := by
    rw [map_sub, he, hvp]
    abel
  rw [hid]
  exact (norm_sub_le _ _).trans (by
    have hb := F.norm_starProjection_apply_le (E.starProjection x-v)
    linarith)

/-- Directed dense exhaustion recovers the ENTIRE orthogonal projection.
The density premise is the exact spectral completeness obligation. -/
theorem global_projection_tendsto
    {N : Type*} [Nonempty N] [SemilatticeSup N]
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (F : N → Submodule ℂ H) [∀ n, (F n).HasOrthogonalProjection]
    (hmono : Monotone F) (hFE : ∀ n, F n ≤ E)
    (hdense : (E : Set H) ⊆ closure (⋃ n, (F n : Set H))) (x : H) :
    Tendsto (fun n => (F n).starProjection x) atTop (𝓝 (E.starProjection x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp
    (hdense (E.starProjection_apply_mem x)) (ε/2) (by linarith)
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
  refine ⟨n, fun m hm => ?_⟩
  rw [dist_eq_norm] at hdist ⊢
  exact (projection_recovery_bound E (F m) (hFE m) x v (hmono hm hn)).trans_lt
    (by linarith)

/-- Both LEFT projections of either required convolution are recovered on
all native vectors. A is any already constructed bounded convolution family;
no assumption that A preserves orthogonality or is nuclear is used. -/
theorem both_convolution_first_global_limits
    {N J : Type*} [Nonempty N] [SemilatticeSup N]
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (F : N → Submodule ℂ H) [∀ n, (F n).HasOrthogonalProjection]
    (hmono : Monotone F) (hFE : ∀ n, F n ≤ E)
    (hdense : (E : Set H) ⊆ closure (⋃ n, (F n : Set H)))
    (A : J → H →L[ℂ] H) (j : J) (x : H) :
    Tendsto (fun n => ((F n).starProjection.comp (A j)) x) atTop
      (𝓝 ((E.starProjection.comp (A j)) x)) ∧
    Tendsto (fun n => (((ContinuousLinearMap.id ℂ H)-(F n).starProjection).comp (A j)) x)
      atTop (𝓝 ((((ContinuousLinearMap.id ℂ H)-E.starProjection).comp (A j)) x)) := by
  have hp := global_projection_tendsto E F hmono hFE hdense (A j x)
  exact ⟨hp, tendsto_const_nhds.sub hp⟩

/-- The union of spans of finite subsets of the ACTUAL supplied family is
its algebraic span. No enumeration, independence or Gram determinant is used. -/
theorem span_subset_finite_union (S : Set H) :
    (Submodule.span ℂ S : Set H) ⊆
      ⋃ T : Finset H, (Submodule.span ℂ ((T : Set H) ∩ S) : Set H) := by
  intro x hx
  obtain ⟨T, hT, hxT⟩ := Submodule.mem_span_finite_of_mem_span hx
  apply Set.mem_iUnion.mpr
  refine ⟨T, ?_⟩
  have hsub : (T : Set H) ⊆ (T : Set H) ∩ S := by
    intro y hy
    exact ⟨hy, hT hy⟩
  exact (Submodule.span_mono hsub) hxT

/-- Concrete finite-family exhaustion. The only infinite subspace here is
literally the closed span of S, not an invented orthogonal spectrum. -/
theorem actual_family_projection_tendsto (S : Set H) (x : H) :
    let E := (Submodule.span ℂ S).topologicalClosure
    let F := fun T : Finset H => Submodule.span ℂ ((T : Set H) ∩ S)
    ∃ p : Finset H → H,
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p T = @Submodule.starProjection ℂ H _ _ _ (F T) hp x) ∧
      Tendsto p atTop (𝓝 (E.starProjection x)) := by
  classical
  let E := (Submodule.span ℂ S).topologicalClosure
  let F := fun T : Finset H => Submodule.span ℂ ((T : Set H) ∩ S)
  letI (T : Finset H) : FiniteDimensional ℂ (F T) :=
    FiniteDimensional.span_of_finite ℂ
      (T.finite_toSet.subset (show (T : Set H) ∩ S ⊆ (T : Set H) from Set.inter_subset_left))
  have hm : Monotone F := by
    intro T U hTU
    apply Submodule.span_mono
    intro y hy
    exact ⟨hTU hy.1, hy.2⟩
  have hFE : ∀ T, F T ≤ E := by
    intro T
    exact (Submodule.span_mono Set.inter_subset_right).trans
      (Submodule.le_topologicalClosure _)
  have hd : (E : Set H) ⊆ closure (⋃ T, (F T : Set H)) :=
    closure_mono (span_subset_finite_union S)
  refine ⟨fun T => (F T).starProjection x, fun T => ⟨inferInstance, rfl⟩, ?_⟩
  exact global_projection_tendsto E F hm hFE hd x

#print axioms span_subset_finite_union
#print axioms actual_family_projection_tendsto

#print axioms nested_projection
#print axioms projection_recovery_bound
#print axioms global_projection_tendsto
#print axioms both_convolution_first_global_limits
end
end Masullo.NestedProjection

namespace OSourceClosure
open Filter
open scoped Topology
noncomputable section
variable {V H : Type*} [AddCommGroup V] [Module ℂ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source finite spans exhaust the literal theta closure. This is STRONG
convergence; no trace convergence or admitted-Mellin completeness is inferred. -/
theorem actual_source_family_exhaustion (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (A : H →L[ℂ] H) (x : H) :
    let F := fun T : Finset H => Submodule.span ℂ ((T : Set H) ∩ Set.range Theta)
    ∃ p : Finset H → H,
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p T = @Submodule.starProjection ℂ H _ _ _ (F T) hp (A x)) ∧
      Tendsto (fun T => A x - p T) atTop
        (𝓝 (A x - (sourceClosure e0 eF Theta).starProjection (A x))) := by
  have hspan : Submodule.span ℂ (Set.range Theta) = LinearMap.range Theta := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨f, rfl⟩
      exact ⟨f, rfl⟩
    · rintro _ ⟨f, rfl⟩
      exact Submodule.subset_span ⟨f, rfl⟩
  obtain ⟨p, hp, ht⟩ := Masullo.NestedProjection.actual_family_projection_tendsto
    (Set.range Theta) (A x)
  refine ⟨p, hp, ?_⟩
  simpa only [hspan, sourceClosure] using (tendsto_const_nhds (x := A x)).sub ht
end
end OSourceClosure
#print axioms OSourceClosure.actual_source_family_exhaustion

namespace HNormalizedKernel
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]

def haarKernel (b : X → ℝ) (V : ℝ) (U R : X → ℂ) (x y : X) : ℂ :=
  (U x / (b x : ℂ)) * ((b y : ℂ) * star (R y) / (V : ℂ))

theorem diagonal_formula (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : X → ℂ) (x : X) :
    haarKernel b V U R x x = (V : ℂ)⁻¹ * (U x * star (R x)) := by
  have hb0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  unfold haarKernel
  field_simp

theorem l2_inner_formula (nu : Measure X) (U R : Lp ℂ 2 nu) :
    (∫ x, U x * star (R x) ∂nu) = inner ℂ R U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [RCLike.inner_apply]

/-- Correct original-Haar diagonal density; no lower bound on b is needed. -/
theorem diagonal_integrable (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : Lp ℂ 2 nu) :
    Integrable (fun x => haarKernel b V U R x x) (ENNReal.ofReal V • nu) := by
  simp_rw [diagonal_formula b hb]
  exact (((Lp.memLp U).integrable_mul (Lp.memLp R).star).const_mul _).smul_measure
    (by simp)

/-- The Haar factor cancels exactly once in the diagonal trace coefficient. -/
theorem diagonal_integral (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu) :
    (∫ x, haarKernel b V U R x x ∂(ENNReal.ofReal V • nu)) = inner ℂ R U := by
  simp_rw [diagonal_formula b hb]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le, integral_const_mul,
    Complex.real_smul, l2_inner_formula]
  have hv0 : (V : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hV)
  rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]

/-- Full-input kernel action, not merely agreement on a theta core. -/
theorem kernel_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R F : Lp ℂ 2 nu) (x : X) :
    (b x : ℂ) * (∫ y, haarKernel b V U R x y * (F y / (b y : ℂ))
      ∂(ENNReal.ofReal V • nu)) = inner ℂ R F * U x := by
  have bx0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  have v0 : (V : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hV)
  have he (y : X) : haarKernel b V U R x y * (F y / (b y : ℂ)) =
      (U x / (b x : ℂ) / (V : ℂ)) * (F y * star (R y)) := by
    have by0 : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    unfold haarKernel
    field_simp
  simp_rw [he]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le, integral_const_mul,
    Complex.real_smul, l2_inner_formula]
  field_simp

/-- Contractive physical masks remove the cutoff from this canonical diagonal. -/
theorem diagonal_cutoff_limit (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu)
    (omega : ℕ → X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) (ENNReal.ofReal V • nu))
    (hbound : ∀ n, ∀ᵐ x ∂(ENNReal.ofReal V • nu), ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂(ENNReal.ofReal V • nu), Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, omega n x * haarKernel b V U R x x
      ∂(ENNReal.ofReal V • nu)) atTop (𝓝 (inner ℂ R U)) := by
  rw [← diagonal_integral nu b hb V hV U R]
  have hi := diagonal_integrable nu b hb V U R
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖haarKernel b V U R x x‖)
  · intro n
    exact (hm n).mul hi.aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa only [one_mul] using hx.mul
      (tendsto_const_nhds (x := haarKernel b V U R x x))

end
end HNormalizedKernel
#print axioms HNormalizedKernel.kernel_action
#print axioms HNormalizedKernel.diagonal_integral
#print axioms HNormalizedKernel.diagonal_cutoff_limit


/- Append after HNormalizedKernel and OSourceClosure.actual_source_family_exhaustion.
   The finite spans below are literally the common theta-source finite spans. -/
namespace DSourceKernel
open MeasureTheory Filter ContinuousLinearMap OSourceClosure
open scoped Topology BigOperators InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Integrability of the actual full-input rank-one kernel integrand. -/
theorem rank_integrable (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (U R F : Lp ℂ 2 nu) (x : X) :
    Integrable (fun y => HNormalizedKernel.haarKernel b 1 U R x y *
      (F y / (b y : ℂ))) nu := by
  have he (y : X) : HNormalizedKernel.haarKernel b 1 U R x y *
      (F y / (b y : ℂ)) = (U x / (b x : ℂ)) * (F y * star (R y)) := by
    have hy : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    simp only [HNormalizedKernel.haarKernel, Complex.ofReal_one, div_one]
    field_simp
  simp_rw [he]
  exact ((Lp.memLp F).integrable_mul (Lp.memLp R).star).const_mul _

/-- Finite source projection expressed with its actual orthonormal basis. -/
theorem projection_expansion (nu : Measure X)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (v : Lp ℂ 2 nu) :
    E.starProjection v = ∑ i,
      inner ℂ ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu) v •
        ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu) := by
  let e := stdOrthonormalBasis ℂ E
  let w : E := ⟨E.starProjection v, E.starProjection_apply_mem v⟩
  have hw : (w : Lp ℂ 2 nu) = ∑ i, inner ℂ (e i) w • (e i : Lp ℂ 2 nu) := by
    conv_lhs => rw [← e.sum_repr' w]
    simp
  have hi (i) : inner ℂ (e i) w = inner ℂ (e i : Lp ℂ 2 nu) v := by
    change inner ℂ (e i : Lp ℂ 2 nu) (E.starProjection v) = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (e i).property]
  simpa only [hi] using hw

/-- Every row is precomposed with A, implemented by A.adjoint. -/
def finiteKernel (nu : Measure X) (b : X → ℝ)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (x y : X) : ℂ :=
  ∑ i, HNormalizedKernel.haarKernel b 1
    ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
    (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) x y

/-- The canonical finite-source kernel acts on every completed input. -/
theorem finiteKernel_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    (fun x => (E.starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, finiteKernel nu b E A x y *
        (F y / (b y : ℂ)) ∂nu) := by
  classical
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  let c : Fin (Module.finrank ℂ E) → ℂ := fun i => inner ℂ (e i) (A F)
  have he (T : Finset (Fin (Module.finrank ℂ E))) :
      (fun x => (∑ i ∈ T, c i • e i) x) =ᵐ[nu]
      (fun x => ∑ i ∈ T, c i * e i x) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 nu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • e i) (∑ j ∈ T, c j • e j),
        Lp.coeFn_smul (c i) (e i), ih] with x hx hs ht
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, ht] using hx
  rw [projection_expansion]
  filter_upwards [he Finset.univ] with x hx
  change (∑ i, c i • e i) x = _ at hx ⊢
  rw [hx]
  unfold finiteKernel
  simp only [Finset.sum_mul]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h := HNormalizedKernel.kernel_action nu b hb 1 (by norm_num)
      (e i) (A.adjoint (e i)) F x
    rw [adjoint_inner_left] at h
    simpa only [ENNReal.ofReal_one, one_smul] using h.symm
  · intro i hi
    exact rank_integrable nu b hb _ _ F x

/-- This is a direct Haar diagonal calculation for the specified finite kernel. -/
theorem finiteKernel_diagonal (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    Integrable (fun x => finiteKernel nu b E A x x) nu ∧
    (∫ x, finiteKernel nu b E A x x ∂nu) =
      ∑ i, inner ℂ ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
        (A ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) := by
  have hi (i) : Integrable (fun x => HNormalizedKernel.haarKernel b 1
      ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
      (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) x x) nu := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      HNormalizedKernel.diagonal_integrable nu b hb 1
        ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
        (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu))
  constructor
  · exact integrable_finset_sum _ (fun i _ => hi i)
  · unfold finiteKernel
    rw [integral_finset_sum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hmem
    have h := HNormalizedKernel.diagonal_integral nu b hb 1 (by norm_num)
      ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
      (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu))
    rw [adjoint_inner_left] at h
    simpa only [ENNReal.ofReal_one, one_smul] using h

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def sourceSpan (nu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (T : Finset (Lp ℂ 2 nu)) : Submodule ℂ (Lp ℂ 2 nu) :=
  Submodule.span ℂ ((T : Set (Lp ℂ 2 nu)) ∩ Set.range Theta)

instance sourceSpan_finiteDim (nu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu) (T : Finset (Lp ℂ 2 nu)) :
    FiniteDimensional ℂ (sourceSpan nu e0 eF Theta T) :=
  FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet T).inter_of_left _)

/-- The kernels use the literal theta-source spans. Their residual operators
converge to the full source-complement projection AFTER A on every input.
This is a strong operator statement; it makes no trace-limit assertion. -/
theorem source_kernel_global_connection (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    let E := sourceSpan nu e0 eF Theta
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, finiteKernel nu b (E T) A x y *
        (F y / (b y : ℂ)) ∂nu)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - (sourceClosure e0 eF Theta).starProjection (A F))) := by
  dsimp only
  refine ⟨fun T => finiteKernel_action nu b hb _ A F, ?_⟩
  obtain ⟨p, hp, ht⟩ := actual_source_family_exhaustion e0 eF Theta A F
  have he (T) : p T = (sourceSpan nu e0 eF Theta T).starProjection (A F) := by
    obtain ⟨inst, h⟩ := hp T
    exact h
  simpa only [he] using ht

end
end DSourceKernel
#print axioms DSourceKernel.source_kernel_global_connection
#print axioms DSourceKernel.finiteKernel_diagonal

/- Append after DSourceKernel. The actual operator factorization remains explicit. -/
namespace DSourceKernel
open MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The diagonal of the actual finite projected kernel is the projected
coefficient series of any proved factorization of its completed operator.
This identifies the coefficient series, rather than merely naming it a trace. -/
theorem finiteKernel_factor_series (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hfactor : ∀ F, HasSum (fun j => ⟪u j, F⟫_ℂ • v j) (A F)) :
    HasSum (fun j => ⟪u j, E.starProjection (v j)⟫_ℂ)
      (∫ x, finiteKernel nu b E A x x ∂nu) := by
  classical
  rw [(finiteKernel_diagonal nu b hb E A).2]
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have hi (i : Fin (Module.finrank ℂ E)) :
      HasSum (fun j => ⟪u j, e i⟫_ℂ * ⟪e i, v j⟫_ℂ) ⟪e i, A (e i)⟫_ℂ := by
    have h := (innerSL ℂ (e i)).hasSum (hfactor (e i))
    simpa only [innerSL_apply_apply, inner_smul_right] using h
  have hs : HasSum (fun j => ∑ i, ⟪u j, e i⟫_ℂ * ⟪e i, v j⟫_ℂ)
      (∑ i, ⟪e i, A (e i)⟫_ℂ) := hasSum_sum (fun i _ => hi i)
  convert hs using 1
  funext j
  rw [projection_expansion]
  simp only [inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end
end DSourceKernel
#print axioms DSourceKernel.finiteKernel_factor_series

/- Append after the seed's OSourceClosure.actual_source_family_exhaustion.
   No arithmetic or source definitions from the seed are duplicated. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Dominated nuclear representation cost for any directed source flag. -/
theorem directed_source_nuclear_cost_limit
    {N : Type*} [Nonempty N] [SemilatticeSup N]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (E : N → Submodule ℂ H) [∀ n, (E n).HasOrthogonalProjection]
    (hmono : Monotone E) (hES : ∀ n, E n ≤ S)
    (hdense : (S : Set H) ⊆ closure (⋃ n, (E n : Set H)))
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun n => ∑' j, ‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖)
      atTop (𝓝 0) := by
  have hb (n : N) (j : ℕ) : ‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖ ≤
      2 * (‖u j‖ * ‖v j‖) := by
    have hp : ‖(E n).starProjection (v j)-S.starProjection (v j)‖ ≤ 2*‖v j‖ :=
      (norm_sub_le _ _).trans (by linarith [(E n).norm_starProjection_apply_le (v j),
        S.norm_starProjection_apply_le (v j)])
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring)
  have ht (j : ℕ) : Tendsto
      (fun n => ‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖) atTop (𝓝 0) := by
    have hh := (Masullo.NestedProjection.global_projection_tendsto S E hmono hES hdense (v j)).sub
      (tendsto_const_nhds (x := S.starProjection (v j)))
    simpa using hh.norm.const_mul ‖u j‖
  have he : ∀ᶠ n in atTop, ∀ j,
      ‖‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖‖ ≤
      2*(‖u j‖*‖v j‖) := by
    apply Eventually.of_forall
    intro n j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb n j
  simpa using tendsto_tsum_of_dominated_convergence (hc.mul_left 2) ht he

/-- The seed's finite spans, with a named projection instance. -/
def finiteSourceSpan (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H) : Submodule ℂ H :=
  Submodule.span ℂ ((T : Set H) ∩ Set.range Theta)

instance finiteSourceSpan_finiteDimensional (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H) :
    FiniteDimensional ℂ (finiteSourceSpan e0 eF Theta T) :=
  FiniteDimensional.span_of_finite ℂ
    (T.finite_toSet.subset (show (T : Set H) ∩ Set.range Theta ⊆ (T : Set H)
      from Set.inter_subset_left))

theorem theta_span_eq (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) :
    Submodule.span ℂ (Set.range Theta) = LinearMap.range Theta := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, rfl⟩

theorem finiteSourceSpan_monotone (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) :
    Monotone (finiteSourceSpan e0 eF Theta) := by
  intro T U hTU
  apply Submodule.span_mono
  intro y hy
  exact ⟨hTU hy.1, hy.2⟩

theorem finiteSourceSpan_le (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H) :
    finiteSourceSpan e0 eF Theta T ≤ sourceClosure e0 eF Theta := by
  have h := (Submodule.span_mono (R := ℂ)
    (show (T : Set H) ∩ Set.range Theta ⊆ Set.range Theta from Set.inter_subset_right)).trans
      (Submodule.le_topologicalClosure (Submodule.span ℂ (Set.range Theta)))
  simpa only [theta_span_eq, sourceClosure, finiteSourceSpan] using h

theorem finiteSourceSpan_dense (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) :
    (sourceClosure e0 eF Theta : Set H) ⊆
      closure (⋃ T, (finiteSourceSpan e0 eF Theta T : Set H)) := by
  have h := closure_mono (Masullo.NestedProjection.span_subset_finite_union (Set.range Theta))
  simpa only [theta_span_eq, sourceClosure, finiteSourceSpan] using h

/-- Density is proved for the actual theta image; only the nuclear factor
summability remains an analytic input. No countable source basis is imposed. -/
theorem actual_theta_nuclear_cost_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j, ‖u j‖ *
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) atTop (𝓝 0) := by
  classical
  exact directed_source_nuclear_cost_limit (sourceClosure e0 eF Theta)
    (finiteSourceSpan e0 eF Theta) (finiteSourceSpan_monotone e0 eF Theta)
    (finiteSourceSpan_le e0 eF Theta) (finiteSourceSpan_dense e0 eF Theta) u v hc

/-- A factorization of the fixed-input-mask convolution is carried through
both genuine left projections. The sign is global minus finite spectral part. -/
theorem actual_theta_factor_residual (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) (x : H) :
    HasSum (fun j => ⟪u j, x⟫_ℂ •
      ((finiteSourceSpan e0 eF Theta T).starProjection (v j) -
       (sourceClosure e0 eF Theta).starProjection (v j)))
      (((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A) (M x) -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A) (M x)) := by
  have he := (hfactor x).map (finiteSourceSpan e0 eF Theta T).starProjection.toAddMonoidHom
    (finiteSourceSpan e0 eF Theta T).starProjection.continuous
  have hs := (hfactor x).map (sourceClosure e0 eF Theta).starProjection.toAddMonoidHom
    (sourceClosure e0 eF Theta).starProjection.continuous
  change HasSum (fun j => (finiteSourceSpan e0 eF Theta T).starProjection (⟪u j, x⟫_ℂ • v j))
    ((finiteSourceSpan e0 eF Theta T).starProjection (A (M x))) at he
  change HasSum (fun j => (sourceClosure e0 eF Theta).starProjection (⟪u j, x⟫_ℂ • v j))
    ((sourceClosure e0 eF Theta).starProjection (A (M x))) at hs
  simp only [map_smul] at he hs
  convert he.sub hs using 1
  · funext j
    exact smul_sub _ _ _
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    abel

/-- Scalar coefficient series for the projected nuclear representation.
The operator-trace / diagonal identification is a separate theorem. -/
theorem actual_theta_trace_series_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j,
      ⟪u j, v j - (finiteSourceSpan e0 eF Theta T).starProjection (v j)⟫_ℂ)
      atTop (𝓝 (∑' j, ⟪u j, v j - (sourceClosure e0 eF Theta).starProjection (v j)⟫_ℂ)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence (hc.mul_left 2)
  · intro j
    have hp := Masullo.NestedProjection.global_projection_tendsto
      (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
      (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
      (finiteSourceSpan_dense e0 eF Theta) (v j)
    exact tendsto_const_nhds.inner (tendsto_const_nhds.sub hp)
  · apply Eventually.of_forall
    intro T j
    have hp : ‖v j - (finiteSourceSpan e0 eF Theta T).starProjection (v j)‖ ≤ 2 * ‖v j‖ :=
      (norm_sub_le _ _).trans (by linarith [(finiteSourceSpan e0 eF Theta T).norm_starProjection_apply_le (v j)])
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring))

end
end Q.IntegratedSourceCutoff
#print Q.IntegratedSourceCutoff.actual_theta_nuclear_cost_limit
#print axioms Q.IntegratedSourceCutoff.actual_theta_nuclear_cost_limit
#print axioms Q.IntegratedSourceCutoff.actual_theta_factor_residual
#print axioms Q.IntegratedSourceCutoff.actual_theta_trace_series_limit

/- Append after QSourceCutoffFragment and QKernelFactorFragment.
   These are the exact D finite kernels and the same genuine source projections. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The source coefficient series converges under the original nuclear factor
cost; the finite source sets are the canonical directed theta exhaustion. -/
theorem actual_theta_source_series_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j,
      inner ℂ (u j) ((finiteSourceSpan e0 eF Theta T).starProjection (v j)))
      atTop (𝓝 (∑' j, inner ℂ (u j) ((sourceClosure e0 eF Theta).starProjection (v j)))) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hc
  · intro j
    exact tendsto_const_nhds.inner
      (Masullo.NestedProjection.global_projection_tendsto
        (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
        (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
        (finiteSourceSpan_dense e0 eF Theta) (v j))
  · apply Eventually.of_forall
    intro T j
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left
        ((finiteSourceSpan e0 eF Theta T).norm_starProjection_apply_le (v j))
        (norm_nonneg _))

end
end Q.IntegratedSourceCutoff

namespace DSourceKernel
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Original-Haar diagonal integrals of the actual finite theta-source kernels
converge to the source-projected factor series. The HasSum hypothesis is an
identity for the completed operator on every input, not merely theta inputs. -/
theorem sourceKernel_diagonal_series_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) =>
      ∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu)
      atTop (𝓝 (∑' j, inner ℂ (u j)
        ((sourceClosure e0 eF Theta).starProjection (v j)))) := by
  have he (T : Finset (Lp ℂ 2 nu)) :
      (∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu) =
        ∑' j, inner ℂ (u j)
          ((finiteSourceSpan e0 eF Theta T).starProjection (v j)) :=
    (finiteKernel_factor_series nu b hb (sourceSpan nu e0 eF Theta T) A u v hfactor).tsum_eq.symm
  simp_rw [he]
  exact actual_theta_source_series_limit e0 eF Theta u v hc

/-- The source limit keeps the free diagonal term and its sign. In the actual
localized convolution application `free` is its separately proved trace. -/
theorem sourceKernel_complement_diagonal_series_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F))
    (free : ℂ) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) =>
      free - ∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu)
      atTop (𝓝 (free - ∑' j, inner ℂ (u j)
        ((sourceClosure e0 eF Theta).starProjection (v j)))) :=
  tendsto_const_nhds.sub
    (sourceKernel_diagonal_series_limit nu b hb e0 eF Theta A u v hc hfactor)

end
end DSourceKernel
#print DSourceKernel.sourceKernel_diagonal_series_limit
#print axioms DSourceKernel.sourceKernel_diagonal_series_limit
#print axioms DSourceKernel.sourceKernel_complement_diagonal_series_limit
