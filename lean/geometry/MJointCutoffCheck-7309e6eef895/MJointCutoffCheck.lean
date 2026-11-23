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

set_option linter.unusedSectionVars false
noncomputable section
open Filter
open scoped BigOperators Topology
namespace ReviewMPartition

/-- An indentation averages a positive partition; the resulting masks may overlap. -/
theorem averaged_partition {U I : Type*} (b : U → ℝ) (d : I → U → ℝ)
    (hb : ∀ u, 0 ≤ b u) (hbs : HasSum b 1)
    (hd : ∀ i u, 0 ≤ d i u) (hds : ∀ u, HasSum (fun i => d i u) 1) :
    (∀ i, Summable (fun u => b u * d i u)) ∧
    (∀ i, 0 ≤ ∑' u, b u * d i u) ∧
    HasSum (fun i => ∑' u, b u * d i u) 1 := by
  have hle (i : I) (u : U) : d i u ≤ 1 := by
    simpa only [Finset.sum_singleton, (hds u).tsum_eq] using
      (hds u).summable.sum_le_tsum {i} (fun j _ => hd j u)
  have hs (i : I) : Summable (fun u => b u * d i u) :=
    Summable.of_nonneg_of_le (fun u => mul_nonneg (hb u) (hd i u))
      (fun u => mul_le_of_le_one_right (hb u) (hle i u)) hbs.summable
  have hrow (u : U) : Summable (fun i => b u * d i u) :=
    (hds u).summable.mul_left (b u)
  have hrowval (u : U) : (∑' i, b u * d i u) = b u := by
    rw [tsum_mul_left, (hds u).tsum_eq, mul_one]
  have hall : Summable (fun ui : U × I => b ui.1 * d ui.2 ui.1) := by
    apply (summable_prod_of_nonneg (fun ui => mul_nonneg (hb ui.1) (hd ui.2 ui.1))).2
    exact ⟨hrow, by simpa only [hrowval] using hbs.summable⟩
  have hmass : (∑' i, ∑' u, b u * d i u) = 1 := by
    calc
      _ = ∑' u, ∑' i, b u * d i u := hall.tsum_comm
      _ = 1 := by simpa only [hrowval] using hbs.tsum_eq
  have houter : Summable (fun i => ∑' u, b u * d i u) := by
    exact ((summable_prod_of_nonneg (fun iu : I × U =>
      mul_nonneg (hb iu.2) (hd iu.1 iu.2))).1 hall.prod_symm).2
  exact ⟨hs, fun i => tsum_nonneg (fun u => mul_nonneg (hb u) (hd i u)),
    hmass ▸ houter.hasSum⟩

end ReviewMPartition


/-! Positive descended shells of the original Haar diagonal, M36 (36.1)-(36.3).
No disjointness assumption is used. Arithmetic identification of the density
is deliberately a separate obligation, not a new axiom. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ReviewM

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The masks are the nonnegative descended indentation weights. -/
structure PositivePartition (p : ι → X → ℝ) : Prop where
  measurable : ∀ i, Measurable (p i)
  nonneg : ∀ i x, 0 ≤ p i x
  mass : ∀ x, HasSum (fun i => p i x) 1

theorem partition_partial_le (p : ι → X → ℝ) (hp : PositivePartition p)
    (s : Finset ι) (x : X) : ∑ i ∈ s, p i x ≤ 1 := by
  simpa only [(hp.mass x).tsum_eq] using
    (hp.mass x).summable.sum_le_tsum s (fun i _ => hp.nonneg i x)

theorem partition_le_one (p : ι → X → ℝ) (hp : PositivePartition p)
    (i : ι) (x : X) : p i x ≤ 1 := by
  simpa using partition_partial_le p hp {i} x

/-- Multiplication by any descended shell preserves L1. -/
theorem shell_integrable (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (i : ι) :
    Integrable (fun x => (p i x : ℂ) * d x) μ := by
  apply hd.norm.mono' ((hp.measurable i).complex_ofReal.aestronglyMeasurable.mul
    hd.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p i x : ℂ) * d x‖ ≤ ‖d x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg i x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (partition_le_one p hp i x)

/-- Every finite family of shell integrals is bounded by the SAME L1 mass. -/
theorem finite_shell_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (s : Finset ι) :
    ∑ i ∈ s, ‖∫ x, (p i x : ℂ) * d x ∂μ‖ ≤ ∫ x, ‖d x‖ ∂μ := by
  have hi := fun i => shell_integrable μ p hp d hd i
  calc
    _ ≤ ∑ i ∈ s, ∫ x, ‖(p i x : ℂ) * d x‖ ∂μ :=
      Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ x, ∑ i ∈ s, ‖(p i x : ℂ) * d x‖ ∂μ :=
      (integral_finset_sum s (fun i _ => (hi i).norm)).symm
    _ ≤ ∫ x, ‖d x‖ ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => (hi i).norm)) hd.norm
      intro x
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp.nonneg _ x)]
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp s x)

/-- Countably many shells cost no factor equal to the number of shells. -/
theorem positive_shell_l1 (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) :
    Summable (fun i => ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ∧
    (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ≤ ∫ x, ‖d x‖ ∂μ := by
  have hs := summable_of_sum_le (fun i => norm_nonneg
    (∫ x, (p i x : ℂ) * d x ∂μ)) (finite_shell_bound μ p hp d hd)
  exact ⟨hs, le_of_tendsto hs.hasSum
    (Eventually.of_forall (finite_shell_bound μ p hp d hd))⟩

/-- The same estimate pays the entire shell-vector error. -/
theorem shell_difference_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d e : X → ℂ) (hd : Integrable d μ) (he : Integrable e μ) :
    (∑' i, ‖(∫ x, (p i x : ℂ) * d x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) ≤ ∫ x, ‖d x - e x‖ ∂μ := by
  have h := (positive_shell_l1 μ p hp (fun x => d x - e x) (hd.sub he)).2
  simpa only [mul_sub, integral_sub (shell_integrable μ p hp d hd _)
    (shell_integrable μ p hp e he _)] using h

/-- L1 convergence of the original Haar densities gives simultaneous shell convergence. -/
theorem shell_l1_limit (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : ℕ → X → ℂ) (e : X → ℂ) (hd : ∀ n, Integrable (d n) μ)
    (he : Integrable e μ)
    (hlim : Tendsto (fun n => ∫ x, ‖d n x - e x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, ‖(∫ x, (p i x : ℂ) * d n x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => tsum_nonneg (fun i => norm_nonneg _))
    (fun n => shell_difference_bound μ p hp (d n) e (hd n) he) hlim

/-- Relative to μ=V_K ν the density is w/V_K, not w. -/
def haarRankOneKernel (V : ℝ) (w : X → ℝ) (u v : X → ℂ) (x y : X) : ℂ :=
  ((w y / V : ℝ) : ℂ) * u x * star (v y)

omit [MeasurableSpace X] in
theorem haarRankOne_diagonal (V : ℝ) (w : X → ℝ) (u v : X → ℂ) (x : X) :
    haarRankOneKernel V w u v x x = ((w x / V : ℝ) : ℂ) * u x * star (v x) := rfl

/-- The manuscript's geometric kernel has the negative spectral diagonal. -/
theorem geometric_diagonal {G : Type*} [Group G] (h : G → ℂ)
    (k : G → G → ℂ) (hunit : h 1 = 0) (x : G) :
    h (x * x⁻¹) - k x x = -k x x := by simp [hunit]

/-- The finite narrow source compensator has the plus sign. -/
theorem finite_source_compensator (wide narrow sandwich regularized : ℂ) :
    wide - narrow - (sandwich - regularized) + (narrow - regularized) =
      wide - sandwich := by ring

/-- Neither the endpoint term nor the omitted-zero remainder disappears. -/
theorem retained_remainder (trace orbital boundary omitted : ℂ)
    (h : trace = orbital + boundary - omitted) :
    orbital = trace - boundary + omitted := by rw [h]; ring

end ReviewM

namespace ReviewM
variable {X ι U : Type*} [MeasurableSpace X]

/-- Apply the checked orbit-average normalization at every quotient point.
Measurability is stated for the descended functions, as required for Haar integration. -/
theorem averaged_positivePartition
    (b : X → U → ℝ) (d : ι → X → U → ℝ)
    (hb : ∀ x u, 0 ≤ b x u) (hbs : ∀ x, HasSum (b x) 1)
    (hd : ∀ i x u, 0 ≤ d i x u)
    (hds : ∀ x u, HasSum (fun i => d i x u) 1)
    (hm : ∀ i, Measurable (fun x => ∑' u, b x u * d i x u)) :
    PositivePartition (fun i x => ∑' u, b x u * d i x u) := by
  refine ⟨hm, ?_, ?_⟩
  · intro i x
    exact (ReviewMPartition.averaged_partition (b x) (fun i => d i x)
      (hb x) (hbs x) (fun i => hd i x) (hds x)).2.1 i
  · intro x
    exact (ReviewMPartition.averaged_partition (b x) (fun i => d i x)
      (hb x) (hbs x) (fun i => hd i x) (hds x)).2.2

/-- The positive descended shells reconstruct the ORIGINAL-measure diagonal.
This is B's checked reconstruction argument, using the common partition structure. -/
theorem shell_reconstruction [Countable ι] (μ : Measure X)
    (p : ι → X → ℝ) (hp : PositivePartition p)
    (f : X → ℂ) (hf : Integrable f μ) :
    HasSum (fun i => ∫ x, (p i x : ℂ) * f x ∂μ) (∫ x, f x ∂μ) := by
  classical
  have hi (i : ι) := shell_integrable μ p hp f hf i
  have hb (F : Finset ι) :
      (∑ i ∈ F, ∫ x, ‖(p i x : ℂ) * f x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
    rw [← integral_finset_sum F (fun i _ => (hi i).norm)]
    apply integral_mono (integrable_finset_sum F (fun i _ => (hi i).norm)) hf.norm
    intro x
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp.nonneg _ _)]
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp F x)
  have hs : Summable (fun i => ∫ x, ‖(p i x : ℂ) * f x‖ ∂μ) :=
    summable_of_sum_le (fun i => integral_nonneg (fun x => norm_nonneg _)) hb
  have he (x : X) : (∑' i, (p i x : ℂ) * f x) = f x := by
    have ht := ((Complex.ofRealCLM.hasSum (hp.mass x)).mul_right (f x)).tsum_eq
    simpa using ht
  simpa only [he] using hasSum_integral_of_summable_integral_norm hi hs

end ReviewM

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


/- Insert after HNormalizedKernel and ReviewM's partition fragment. -/
namespace HNormalizedKernel
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Explicit Holder cost of the two normalized L2 rows. -/
def diagonalL2Cost (nu : Measure X) (U R : Lp ℂ 2 nu) : ℝ :=
  (∫ x, ‖U x‖ ^ (2 : ℝ) ∂nu) ^ (1 / (2 : ℝ)) *
    (∫ x, ‖R x‖ ^ (2 : ℝ) ∂nu) ^ (1 / (2 : ℝ))

/-- The original-Haar volume cancels in the absolute diagonal estimate too. -/
theorem diagonal_integral_norm_le (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu) :
    (∫ x, ‖haarKernel b V U R x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      diagonalL2Cost nu U R := by
  simp_rw [diagonal_formula b hb, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hV, norm_star]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le]
  rw [integral_const_mul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hV), one_mul]
  have hU : MemLp (fun x => (U x : ℂ)) (ENNReal.ofReal (2 : ℝ)) nu := by
    simpa using Lp.memLp U
  have hR : MemLp (fun x => (R x : ℂ)) (ENNReal.ofReal (2 : ℝ)) nu := by
    simpa using Lp.memLp R
  exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hU hR

/-- The SAME Haar kernel rows have the expected diagonal coefficient series.
The summability of their explicit L2 costs is the remaining analytic input. -/
theorem diagonal_series (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => diagonalL2Cost nu (U i) (R i))) :
    HasSum (fun i => inner ℂ (R i) (U i))
      (∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu)) := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hs : Summable (fun i => ∫ x,
      ‖haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _))
      (fun i => diagonal_integral_norm_le nu b hb V hV (U i) (R i)) hcost
  simpa only [diagonal_integral nu b hb V hV] using
    hasSum_integral_of_summable_integral_norm hi hs

/-- Every descended shell may be taken through the same original-Haar series;
no factor depending on the number of shells is introduced. -/
theorem shell_diagonal_series {E : Type*} (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => diagonalL2Cost nu (U i) (R i)))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) (e : E) :
    HasSum (fun i => ∫ x, (p e x : ℂ) * haarKernel b V (U i) (R i) x x
      ∂(ENNReal.ofReal V • nu))
      (∫ x, ∑' i, (p e x : ℂ) * haarKernel b V (U i) (R i) x x
        ∂(ENNReal.ofReal V • nu)) := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hm (i : ι) := ReviewM.shell_integrable (ENNReal.ofReal V • nu) p hp
    (fun x => haarKernel b V (U i) (R i) x x) (hi i) e
  have hmajor (i : ι) : (∫ x,
      ‖(p e x : ℂ) * haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      diagonalL2Cost nu (U i) (R i) := by
    apply le_trans _ (diagonal_integral_norm_le nu b hb V hV (U i) (R i))
    apply integral_mono (hm i).norm (hi i).norm
    intro x
    change ‖(p e x : ℂ) * haarKernel b V (U i) (R i) x x‖ ≤
      ‖haarKernel b V (U i) (R i) x x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg e x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (ReviewM.partition_le_one p hp e x)
  exact hasSum_integral_of_summable_integral_norm hm
    (Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _))
      hmajor hcost)

end
end HNormalizedKernel

/- Insert after MSeriesFragment; uses H's exact original-Haar rows. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The integral Holder cost is exactly the Hilbert norm-product nuclear cost. -/
theorem diagonalL2Cost_eq_norm_mul (nu : Measure X) (U R : Lp ℂ 2 nu) :
    diagonalL2Cost nu U R = ‖U‖ * ‖R‖ := by
  have hsq (F : Lp ℂ 2 nu) :
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂nu) = ‖F‖ ^ 2 := by
    calc
      _ = ∫ x, inner ℝ (F x) (F x) ∂nu := by
        simp only [real_inner_self_eq_norm_sq, Real.rpow_two]
      _ = inner ℝ F F := (L2.inner_def F F).symm
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  unfold diagonalL2Cost
  rw [hsq U, hsq R, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg U), Real.sqrt_sq (norm_nonneg R)]

/-- Summable Hilbert factors discharge the original-Haar diagonal cost. -/
theorem diagonal_series_of_norm_cost {ι : Type*} [Countable ι]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    HasSum (fun i => inner ℂ (R i) (U i))
      (∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu)) := by
  apply diagonal_series nu b hb V hV U R
  simpa only [diagonalL2Cost_eq_norm_mul] using hcost

end
end HNormalizedKernel

/- Insert after MNormCostFragment. The series integrability proof adapts
   review_core/Masullo/Spectral/ComplexMellinMoments.lean:3654,
   itself the ALPO InterBridgeG argument, to an arbitrary countable index. -/
namespace ReviewM
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- An absolute integral row bound constructs an L1 series; pointwise
summability and integrability of the total diagonal are conclusions. -/
theorem integrable_complex_series (mu : Measure X) (F : ι → X → ℂ)
    (hi : ∀ i, Integrable (F i) mu)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂mu)) :
    Integrable (fun x => ∑' i, F i x) mu ∧
      (∫ x, ‖∑' i, F i x‖ ∂mu) ≤ ∑' i, ∫ x, ‖F i x‖ ∂mu := by
  classical
  have hm (i : ι) : AEMeasurable (fun x => ‖F i x‖ₑ) mu :=
    (hi i).aemeasurable.enorm
  have he : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) =
      ENNReal.ofReal (∑' i, ∫ x, ‖F i x‖ ∂mu) := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun x => norm_nonneg _) hs).symm
  have hlin : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) ≠ ⊤ := by rw [he]; exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ x ∂mu, ∑' i, ‖F i x‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlin
  have hsum : ∀ᵐ x ∂mu, Summable (fun i => F i x) := by
    filter_upwards [hae] with x hx
    apply Summable.of_norm
    have hn : (∑' i, (‖F i x‖₊ : ENNReal)) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)
  have htotal : Integrable (fun x => ∑' i, F i x) mu := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae
      (atTop : Filter (Finset ι)) (f := fun S x => ∑ i ∈ S, F i x)
      (fun S => Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hi i).1) ?_, ?_⟩
    · filter_upwards [hsum] with x hx
      exact hx.hasSum
    · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm)
        (lt_top_iff_ne_top.mpr hlin)
  refine ⟨htotal, ?_⟩
  have hbound : (∫⁻ x, ‖∑' i, F i x‖ₑ ∂mu) ≤
      ENNReal.ofReal (∑' i, ∫ x, ‖F i x‖ ∂mu) := by
    rw [← he]
    exact lintegral_mono fun x => enorm_tsum_le_tsum_enorm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [← ofReal_integral_norm_eq_lintegral_enorm htotal,
    ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _),
    ENNReal.toReal_ofReal (tsum_nonneg fun i => integral_nonneg fun x => norm_nonneg _)] at hreal
  exact hreal

/-- The full shell vector is continuous under L1 convergence along any filter,
including the directed finite-theta source index used in Q. -/
theorem shell_filter_limit {E J : Type*} (mu : Measure X)
    (p : E → X → ℝ) (hp : PositivePartition p)
    (d : J → X → ℂ) (e : X → ℂ) (hd : ∀ j, Integrable (d j) mu)
    (he : Integrable e mu) (L : Filter J)
    (hlim : Tendsto (fun j => ∫ x, ‖d j x - e x‖ ∂mu) L (𝓝 0)) :
    Tendsto (fun j => ∑' i, ‖(∫ x, (p i x : ℂ) * d j x ∂mu) -
      (∫ x, (p i x : ℂ) * e x ∂mu)‖) L (𝓝 0) := by
  apply squeeze_zero (fun j => tsum_nonneg (fun i => norm_nonneg _))
    (fun j => shell_difference_bound mu p hp (d j) e (hd j) he) hlim

end
end ReviewM

namespace HNormalizedKernel
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The actual original-Haar row series has an integrable diagonal with the
same total nuclear cost, without any further weight or volume factor. -/
theorem nuclear_diagonal_integrable (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    Integrable (fun x => ∑' i, haarKernel b V (U i) (R i) x x)
      (ENNReal.ofReal V • nu) ∧
    (∫ x, ‖∑' i, haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      ∑' i, ‖U i‖ * ‖R i‖ := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hmajor (i : ι) : (∫ x, ‖haarKernel b V (U i) (R i) x x‖
      ∂(ENNReal.ofReal V • nu)) ≤ ‖U i‖ * ‖R i‖ := by
    simpa only [diagonalL2Cost_eq_norm_mul] using
      diagonal_integral_norm_le nu b hb V hV (U i) (R i)
  have hs := Summable.of_nonneg_of_le
    (fun i => integral_nonneg fun x => norm_nonneg _) hmajor hc
  have h := ReviewM.integrable_complex_series (ENNReal.ofReal V • nu) _ hi hs
  exact ⟨h.1, h.2.trans (hs.tsum_le_tsum hmajor hc)⟩

/-- Reconstruct the actual L1 diagonal series by all descended shells.
Its entire shell vector is bounded by the single nuclear factor cost. -/
theorem nuclear_diagonal_shells {E : Type*} [Countable E] (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) :
    HasSum (fun e => ∫ x, (p e x : ℂ) *
      (∑' i, haarKernel b V (U i) (R i) x x) ∂(ENNReal.ofReal V • nu))
      (∑' i, inner ℂ (R i) (U i)) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) *
      (∑' i, haarKernel b V (U i) (R i) x x) ∂(ENNReal.ofReal V • nu)‖) ≤
      ∑' i, ‖U i‖ * ‖R i‖ := by
  have hd := nuclear_diagonal_integrable nu b hb V hV U R hc
  constructor
  · have h := ReviewM.shell_reconstruction (ENNReal.ofReal V • nu) p hp _ hd.1
    rw [← (diagonal_series_of_norm_cost nu b hb V hV U R hc).tsum_eq] at h
    exact h
  · exact (ReviewM.positive_shell_l1 (ENNReal.ofReal V • nu) p hp _ hd.1).2.trans hd.2

end
end HNormalizedKernel

/- Insert after MNuclearDiagonalFragment. The final source-filter application
   additionally needs QSourceCutoffFragment and the canonical OSourceClosure. -/
namespace ReviewM
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Absolute integral control also constructs pointwise summability a.e. -/
theorem complex_series_ae_summable (mu : Measure X) (F : ι → X → ℂ)
    (hi : ∀ i, Integrable (F i) mu)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂mu)) :
    ∀ᵐ x ∂mu, Summable (fun i => F i x) := by
  have hm (i : ι) : AEMeasurable (fun x => ‖F i x‖ₑ) mu :=
    (hi i).aemeasurable.enorm
  have hlin : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) ≠ ⊤ := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun x => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlin
  filter_upwards [hae] with x hx
  apply Summable.of_norm
  have hn : (∑' i, (‖F i x‖₊ : ENNReal)) ≠ ⊤ := hx.ne
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)

end
end ReviewM

namespace HNormalizedKernel
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Pointwise summability is proved for the same actual Haar rows. -/
theorem nuclear_diagonal_ae_summable (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    ∀ᵐ x ∂(ENNReal.ofReal V • nu),
      Summable (fun i => haarKernel b V (U i) (R i) x x) := by
  apply ReviewM.complex_series_ae_summable _ _
    (fun i => diagonal_integrable nu b hb V (U i) (R i))
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg fun x => norm_nonneg _) _ hc
  intro i
  simpa only [diagonalL2Cost_eq_norm_mul] using
    diagonal_integral_norm_le nu b hb V hV (U i) (R i)

/-- Subtraction of the L2 columns represents the difference of the full
original-Haar diagonals a.e.; no product-null-set restriction is used. -/
theorem nuclear_diagonal_sub_ae (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U W R : ι → Lp ℂ 2 nu)
    (hU : Summable (fun i => ‖U i‖ * ‖R i‖))
    (hW : Summable (fun i => ‖W i‖ * ‖R i‖)) :
    (fun x => (∑' i, haarKernel b V (U i) (R i) x x) -
      (∑' i, haarKernel b V (W i) (R i) x x)) =ᵐ[ENNReal.ofReal V • nu]
    (fun x => ∑' i, haarKernel b V (U i - W i : Lp ℂ 2 nu) (R i) x x) := by
  have hd (i : ι) : ∀ᵐ x ∂(ENNReal.ofReal V • nu),
      haarKernel b V (U i - W i : Lp ℂ 2 nu) (R i) x x =
        haarKernel b V (U i) (R i) x x - haarKernel b V (W i) (R i) x x := by
    filter_upwards [Measure.ae_smul_measure (Lp.coeFn_sub (U i) (W i))
      (ENNReal.ofReal V)] with x hx
    simp only [haarKernel, hx, Pi.sub_apply, sub_div, sub_mul]
  filter_upwards [nuclear_diagonal_ae_summable nu b hb V hV U R hU,
    nuclear_diagonal_ae_summable nu b hb V hV W R hW, ae_all_iff.mpr hd] with x hxU hxW hxd
  rw [← hxU.tsum_sub hxW]
  exact tsum_congr fun i => (hxd i).symm

/-- The full diagonal L1 error is controlled by the exact changing-column
nuclear cost. All series existence hypotheses are derived. -/
theorem nuclear_diagonal_difference_bound (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U W R : ι → Lp ℂ 2 nu)
    (hU : Summable (fun i => ‖U i‖ * ‖R i‖))
    (hW : Summable (fun i => ‖W i‖ * ‖R i‖)) :
    (∫ x, ‖(∑' i, haarKernel b V (U i) (R i) x x) -
      (∑' i, haarKernel b V (W i) (R i) x x)‖ ∂(ENNReal.ofReal V • nu)) ≤
    ∑' i, ‖U i-W i‖ * ‖R i‖ := by
  have hdiff : Summable (fun i => ‖U i-W i‖ * ‖R i‖) := by
    apply Summable.of_nonneg_of_le (fun i => by positivity) _ (hU.add hW)
    intro i
    exact (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)).trans_eq
      (add_mul _ _ _)
  have he := nuclear_diagonal_sub_ae nu b hb V hV U W R hU hW
  have hn := he.mono fun x hx => congrArg norm hx
  rw [integral_congr_ae hn]
  exact (nuclear_diagonal_integrable nu b hb V hV (fun i => U i-W i) R hdiff).2

/-- All shells of the actual row diagonal have the same nuclear error bound. -/
theorem nuclear_shell_difference_bound {E : Type*} (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U W R : ι → Lp ℂ 2 nu)
    (hU : Summable (fun i => ‖U i‖ * ‖R i‖))
    (hW : Summable (fun i => ‖W i‖ * ‖R i‖))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) :
    (∑' e, ‖(∫ x, (p e x : ℂ) * (∑' i, haarKernel b V (U i) (R i) x x)
      ∂(ENNReal.ofReal V • nu)) -
      (∫ x, (p e x : ℂ) * (∑' i, haarKernel b V (W i) (R i) x x)
      ∂(ENNReal.ofReal V • nu))‖) ≤ ∑' i, ‖U i-W i‖ * ‖R i‖ :=
  (ReviewM.shell_difference_bound (ENNReal.ofReal V • nu) p hp _ _
    (nuclear_diagonal_integrable nu b hb V hV U R hU).1
    (nuclear_diagonal_integrable nu b hb V hV W R hW).1).trans
      (nuclear_diagonal_difference_bound nu b hb V hV U W R hU hW)

/-- Orthogonal projection proves the summability required above; it is not
an additional premise on the finite source spans. -/
theorem projected_column_cost (nu : Measure X)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [E.HasOrthogonalProjection]
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun i => ‖E.starProjection (v i)‖ * ‖u i‖) := by
  apply Summable.of_nonneg_of_le (fun i => by positivity) _ hc
  intro i
  exact (mul_le_mul_of_nonneg_right (E.norm_starProjection_apply_le (v i))
    (norm_nonneg _)).trans_eq (mul_comm _ _)

end
end HNormalizedKernel

namespace ReviewM
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology
noncomputable section
variable {X V E : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V]

/-- Q's concrete finite theta spans now exhaust the actual row-diagonal
shell vector in l1. The original Haar and every shell are retained. -/
theorem actual_source_diagonal_shell_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (vol : ℝ) (hvol : 0 < vol)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (u v : ℕ → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (p : E → X → ℝ) (hp : PositivePartition p) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) => ∑' e,
      ‖(∫ x, (p e x : ℂ) * (∑' i, HNormalizedKernel.haarKernel b vol
        ((finiteSourceSpan e0 eF Theta T).starProjection (v i)) (u i) x x)
        ∂(ENNReal.ofReal vol • nu)) -
        (∫ x, (p e x : ℂ) * (∑' i, HNormalizedKernel.haarKernel b vol
        ((sourceClosure e0 eF Theta).starProjection (v i)) (u i) x x)
        ∂(ENNReal.ofReal vol • nu))‖) atTop (𝓝 0) := by
  classical
  apply squeeze_zero (fun T => tsum_nonneg fun e => norm_nonneg _) _
    (actual_theta_nuclear_cost_limit e0 eF Theta u v hc)
  intro T
  simpa only [mul_comm] using HNormalizedKernel.nuclear_shell_difference_bound nu b hb vol hvol
    (fun i => (finiteSourceSpan e0 eF Theta T).starProjection (v i))
    (fun i => (sourceClosure e0 eF Theta).starProjection (v i)) u
    (HNormalizedKernel.projected_column_cost nu (finiteSourceSpan e0 eF Theta T) u v hc)
    (HNormalizedKernel.projected_column_cost nu (sourceClosure e0 eF Theta) u v hc) p hp

end
end ReviewM

/- B continuation fragment. Insert after BSourceShellFragment and ReviewM.
   These are the SAME literal finite source kernels used by D and H.
   I owns their actual arithmetic/two-test/descended-partition instantiation. -/
namespace BSourceShell
open MeasureTheory ContinuousLinearMap Filter
open scoped Topology BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Contractive masks preserve the actual original-measure diagonal's L1 admission. -/
theorem masked_integrable (mu : Measure X) (d omega : X → ℂ)
    (hd : Integrable d mu) (hm : AEStronglyMeasurable omega mu)
    (hbound : ∀ᵐ x ∂mu, ‖omega x‖ ≤ 1) :
    Integrable (fun x => omega x * d x) mu := by
  apply hd.norm.mono' (hm.mul hd.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖omega x * d x‖ ≤ ‖d x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx


end
end BSourceShell
/- Insert after MSourceDiagonalFragment and BSourceCutoffShellFragment.
   The two cutoff filters are independent. No countability hypothesis is
   imposed on the directed finite-source filter. -/
namespace ReviewM
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
variable {X J R E : Type*} [MeasurableSpace X]

/-- Filter form of B's checked physical L1 passage. Only the physical filter
is countably generated; the source net below need not be. -/
theorem masked_diagonal_filter_L1 (mu : Measure X) (d : X → ℂ)
    (hd : Integrable d mu) (omega : R → X → ℂ)
    (L : Filter R) [L.IsCountablyGenerated]
    (hm : ∀ᶠ r in L, AEStronglyMeasurable (omega r) mu)
    (hb : ∀ᶠ r in L, ∀ᵐ x ∂mu, ‖omega r x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun r => omega r x) L (𝓝 1)) :
    Tendsto (fun r => ∫ x, ‖omega r x * d x-d x‖ ∂mu) L (𝓝 0) := by
  have ht : Tendsto (fun r => ∫ x, ‖omega r x*d x-d x‖ ∂mu)
      L (𝓝 (∫ _ : X, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => 2*‖d x‖)
    · exact hm.mono fun r hr =>
        ((hr.mul hd.aestronglyMeasurable).sub hd.aestronglyMeasurable).norm
    · apply hb.mono
      intro r hr
      filter_upwards [hr] with x hx
      simp only [norm_norm]
      calc
        ‖omega r x*d x-d x‖ ≤ ‖omega r x*d x‖+‖d x‖ := norm_sub_le _ _
        _ ≤ ‖d x‖+‖d x‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hx) le_rfl
        _ = 2*‖d x‖ := by ring
    · exact hd.norm.const_mul 2
    · filter_upwards [hl] with x hx
      simpa only [one_mul, sub_self, norm_zero] using
        ((hx.mul (tendsto_const_nhds (x := d x))).sub
          (tendsto_const_nhds (x := d x))).norm
  simpa only [integral_zero] using ht

/-- The source error is multiplied by a contraction. The second term is a
physical error of the fixed limiting diagonal, giving uniform control. -/
theorem masked_source_L1_bound (mu : Measure X) (d e omega : X → ℂ)
    (hd : Integrable d mu) (he : Integrable e mu)
    (hm : AEStronglyMeasurable omega mu)
    (hb : ∀ᵐ x ∂mu, ‖omega x‖ ≤ 1) :
    (∫ x, ‖omega x*d x-e x‖ ∂mu) ≤
      (∫ x, ‖d x-e x‖ ∂mu)+(∫ x, ‖omega x*e x-e x‖ ∂mu) := by
  have hmd := BSourceShell.masked_integrable mu d omega hd hm hb
  have hme := BSourceShell.masked_integrable mu e omega he hm hb
  have hi1 : Integrable (fun x => ‖d x-e x‖) mu := (hd.sub he).norm
  have hi2 : Integrable (fun x => ‖omega x*e x-e x‖) mu := (hme.sub he).norm
  rw [← integral_add hi1 hi2]
  apply integral_mono_ae (hmd.sub he).norm (hi1.add hi2)
  filter_upwards [hb] with x hx
  calc
    ‖omega x*d x-e x‖ = ‖omega x*(d x-e x)+(omega x*e x-e x)‖ := by
      congr 1
      ring
    _ ≤ ‖omega x*(d x-e x)‖+‖omega x*e x-e x‖ := norm_add_le _ _
    _ ≤ ‖d x-e x‖+‖omega x*e x-e x‖ := by
      rw [norm_mul]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hx) le_rfl

/-- Source and physical cutoffs converge jointly in original-measure L1,
without tying their rates or applying dominated convergence to the source net. -/
theorem masked_source_product_L1 (mu : Measure X) (d : J → X → ℂ) (e : X → ℂ)
    (hd : ∀ j, Integrable (d j) mu) (he : Integrable e mu)
    (omega : R → X → ℂ) (S : Filter J) (L : Filter R)
    (hm : ∀ᶠ r in L, AEStronglyMeasurable (omega r) mu)
    (hb : ∀ᶠ r in L, ∀ᵐ x ∂mu, ‖omega r x‖ ≤ 1)
    (hs : Tendsto (fun j => ∫ x, ‖d j x-e x‖ ∂mu) S (𝓝 0))
    (hl : Tendsto (fun r => ∫ x, ‖omega r x*e x-e x‖ ∂mu) L (𝓝 0)) :
    Tendsto (fun jr : J × R => ∫ x, ‖omega jr.2 x*d jr.1 x-e x‖ ∂mu)
      (S ×ˢ L) (𝓝 0) := by
  have hup := (hs.comp (tendsto_fst : Tendsto Prod.fst (S ×ˢ L) S)).add
    (hl.comp (tendsto_snd : Tendsto Prod.snd (S ×ˢ L) L))
  simp only [zero_add] at hup
  refine squeeze_zero' (Eventually.of_forall fun jr => integral_nonneg fun x => norm_nonneg _) ?_ hup
  filter_upwards [(tendsto_snd : Tendsto Prod.snd (S ×ˢ L) L).eventually hm,
    (tendsto_snd : Tendsto Prod.snd (S ×ˢ L) L).eventually hb] with jr hm' hb'
  exact masked_source_L1_bound mu (d jr.1) e (omega jr.2) (hd jr.1) he hm' hb'

/-- The entire descended shell vector has the same joint cutoff limit. -/
theorem masked_source_shell_product_limit (mu : Measure X)
    (p : E → X → ℝ) (hp : PositivePartition p)
    (d : J → X → ℂ) (e : X → ℂ)
    (hd : ∀ j, Integrable (d j) mu) (he : Integrable e mu)
    (omega : R → X → ℂ) (S : Filter J) (L : Filter R)
    (hm : ∀ᶠ r in L, AEStronglyMeasurable (omega r) mu)
    (hb : ∀ᶠ r in L, ∀ᵐ x ∂mu, ‖omega r x‖ ≤ 1)
    (hs : Tendsto (fun j => ∫ x, ‖d j x-e x‖ ∂mu) S (𝓝 0))
    (hl : Tendsto (fun r => ∫ x, ‖omega r x*e x-e x‖ ∂mu) L (𝓝 0)) :
    Tendsto (fun jr : J × R => ∑' i,
      ‖(∫ x, (p i x : ℂ)*(omega jr.2 x*d jr.1 x) ∂mu)-
        (∫ x, (p i x : ℂ)*e x ∂mu)‖) (S ×ˢ L) (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun jr => tsum_nonneg fun i => norm_nonneg _) ?_
    (masked_source_product_L1 mu d e hd he omega S L hm hb hs hl)
  filter_upwards [(tendsto_snd : Tendsto Prod.snd (S ×ˢ L) L).eventually hm,
    (tendsto_snd : Tendsto Prod.snd (S ×ˢ L) L).eventually hb] with jr hm' hb'
  exact shell_difference_bound mu p hp _ e
    (BSourceShell.masked_integrable mu (d jr.1) (omega jr.2) (hd jr.1) hm' hb') he

end
end ReviewM

namespace ReviewM
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology BigOperators
noncomputable section
variable {X V : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V]

/-- L1 source convergence is proved from Q's exact finite theta spans and
the same nuclear factor cost; no extra diagonal-limit premise is needed. -/
theorem actual_source_diagonal_L1_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (vol : ℝ) (hvol : 0 < vol)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (u v : ℕ → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖*‖v i‖)) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) => ∫ x,
      ‖(∑' i, HNormalizedKernel.haarKernel b vol
        ((finiteSourceSpan e0 eF Theta T).starProjection (v i)) (u i) x x)-
       (∑' i, HNormalizedKernel.haarKernel b vol
        ((sourceClosure e0 eF Theta).starProjection (v i)) (u i) x x)‖
      ∂(ENNReal.ofReal vol • nu)) atTop (𝓝 0) := by
  apply squeeze_zero (fun T => integral_nonneg fun x => norm_nonneg _) _
    (actual_theta_nuclear_cost_limit e0 eF Theta u v hc)
  intro T
  simpa only [mul_comm] using HNormalizedKernel.nuclear_diagonal_difference_bound nu b hb vol hvol
    (fun i => (finiteSourceSpan e0 eF Theta T).starProjection (v i))
    (fun i => (sourceClosure e0 eF Theta).starProjection (v i)) u
    (HNormalizedKernel.projected_column_cost nu (finiteSourceSpan e0 eF Theta T) u v hc)
    (HNormalizedKernel.projected_column_cost nu (sourceClosure e0 eF Theta) u v hc)

end
end ReviewM
#check ReviewM.masked_source_shell_product_limit
#print axioms ReviewM.masked_source_shell_product_limit
#check ReviewM.actual_source_diagonal_L1_limit
#print axioms ReviewM.actual_source_diagonal_L1_limit
