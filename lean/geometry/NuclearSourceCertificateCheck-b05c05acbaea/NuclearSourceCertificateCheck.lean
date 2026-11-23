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

/- E source residual estimate. Append anywhere after Mathlib.
The projection minimality argument is adapted from ALPO's
GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean:16.
Unlike a bound by 2, this gives the unit constant needed by (34.10). -/
namespace ESourceResidual
open Filter
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every genuine orthogonal complementary projection is a contraction. -/
theorem complementary_projection_bound (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : H) :
    ‖x - E.starProjection x‖ ≤ ‖x‖ := by
  calc
    ‖x - E.starProjection x‖ ≤ ‖x - ((0 : E) : H)‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (0 : E)
    _ = ‖x‖ := by simp

/-- The finite-source residual is controlled by the original input residual. -/
theorem nested_source_residual_bound (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (x : H) :
    ‖S.starProjection x - E.starProjection x‖ ≤ ‖x - E.starProjection x‖ := by
  have he : S.starProjection (E.starProjection x) = E.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (hES (E.starProjection_apply_mem x))
  calc
    ‖S.starProjection x - E.starProjection x‖ =
        ‖S.starProjection (x - E.starProjection x)‖ := by rw [map_sub, he]
    _ ≤ ‖x - E.starProjection x‖ := S.norm_starProjection_apply_le _

/-- Unit-constant whole-column bound, uniform in the finite source set. -/
theorem nested_source_residual_contraction (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (x : H) :
    ‖E.starProjection x - S.starProjection x‖ ≤ ‖x‖ := by
  rw [norm_sub_rev]
  exact (nested_source_residual_bound S E hES x).trans
    (complementary_projection_bound E x)

/-- This discharges Q's projection-dependent summability from its nuclear
factor cost. The actual operator factorization is still a separate premise. -/
theorem source_factor_cost_summable (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Summable (fun j => ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) := by
  exact Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => mul_le_mul_of_nonneg_left
      (nested_source_residual_contraction S E hES (v j)) (norm_nonneg _)) hc

/-- Whole source-factor tail is no larger than the supplied factor cost. -/
theorem source_factor_cost_le (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    (∑' j, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) ≤
      ∑' j, ‖u j‖ * ‖v j‖ := by
  apply Summable.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left
      (nested_source_residual_contraction S E hES (v j)) (norm_nonneg _))
    (source_factor_cost_summable S E hES u v hc) hc

end
end ESourceResidual

/- Append after E SourceResidualFragment and QSourceCutoffFragment.
   This applies E's unit bound to Q's exact canonical finite source sets. -/
namespace ESourceResidual
open OSourceClosure Q.IntegratedSourceCutoff
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- No inclusion/density assumption is imposed here: Q's concrete finite
source construction proves the needed inclusion in the same source closure. -/
theorem common_source_factor_cost_bound (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    (∑' j, ‖u j‖ *
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
       (sourceClosure e0 eF Theta).starProjection (v j)‖) ≤
    ∑' j, ‖u j‖ * ‖v j‖ := by
  exact source_factor_cost_le (sourceClosure e0 eF Theta)
    (finiteSourceSpan e0 eF Theta T) (finiteSourceSpan_le e0 eF Theta T) u v hc

end
end ESourceResidual

/- Append after E SourceResidualFragment and QSourceCutoffFragment.
   Quantitative form of the fixed-mask source cutoff in G32 §3/E34 (34.10).
   The explicit factorization is retained; no arithmetic nuclearity is assumed
   implicitly or concluded from strong projection convergence alone. -/
namespace ESourceResidual
open Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The source cost directly bounds the error of the actual ordered operators
on every completed input, with unit constant. -/
theorem common_source_operator_error (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) (x : H) :
    ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A) (M x) -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A) (M x)‖ ≤
      (∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) * ‖x‖ := by
  have hs := actual_theta_factor_residual e0 eF Theta A M u v hfactor T x
  have hcost := source_factor_cost_summable (sourceClosure e0 eF Theta)
    (finiteSourceSpan e0 eF Theta T) (finiteSourceSpan_le e0 eF Theta T) u v hc
  apply hs.norm_le_of_bounded (hcost.hasSum.mul_right ‖x‖)
  intro j
  rw [norm_smul]
  calc
    ‖⟪u j, x⟫_ℂ‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ ≤
      (‖u j‖ * ‖x‖) * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ :=
      mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

/-- The same estimate is uniform over the unit ball, hence an operator norm
bound, not only the strong limit already provided by the seed. -/
theorem common_source_operator_norm_error (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) :
    ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M‖ ≤
      ∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  intro x
  exact common_source_operator_error e0 eF Theta A M u v hc hfactor T x

/-- Explicit finite head plus original nuclear tail, with all cross-source
geometry remaining in the genuine projected columns. -/
theorem source_factor_head_tail_bound (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) (N : ℕ) :
    (∑' j, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) ≤
      (∑ j ∈ Finset.range N, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) +
      ∑' j, ‖u (j+N)‖ * ‖v (j+N)‖ := by
  have hs := source_factor_cost_summable S E hES u v hc
  rw [← hs.sum_add_tsum_nat_add N]
  apply add_le_add_right
  apply Summable.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left
      (nested_source_residual_contraction S E hES (v (j+N))) (norm_nonneg _))
  · exact (summable_nat_add_iff N).2 hs
  · exact (summable_nat_add_iff N).2 hc

/-- Q's proved directed density now pays the operator norm error, provided
that the actual fixed-mask factorization has separately been constructed. -/
theorem common_source_operator_norm_tendsto (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x))) :
    Tendsto (fun T : Finset H =>
      ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M‖)
      atTop (𝓝 0) := by
  classical
  exact squeeze_zero (fun _ => norm_nonneg _)
    (common_source_operator_norm_error e0 eF Theta A M u v hc hfactor)
    (actual_theta_nuclear_cost_limit e0 eF Theta u v hc)

end
end ESourceResidual

/- Insert after E SourceResidualFragment.  This is (34.10a) on the same
   genuine source and complementary subspaces, without a spectral premise. -/
namespace ESourceResidual
open Filter
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem projection_energy (E : Submodule ℂ H) [E.HasOrthogonalProjection] (x : H) :
    ‖x - E.starProjection x‖ ^ 2 = ‖x‖ ^ 2 - ‖E.starProjection x‖ ^ 2 := by
  have ho : inner ℂ (E.starProjection x) (x - E.starProjection x) = 0 :=
    (Submodule.mem_orthogonal E _).mp
      (Submodule.sub_starProjection_mem_orthogonal (K := E) x) _
      (E.starProjection_apply_mem x)
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (E.starProjection x) (x - E.starProjection x) ho
  have he : E.starProjection x + (x - E.starProjection x) = x := by abel
  rw [he] at hp
  nlinarith

theorem complementary_finite_source_zero (S E F : Submodule ℂ H)
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hES : E ≤ S) (hFS : F ≤ Sᗮ) (x : H) :
    F.starProjection (E.starProjection x) = 0 := by
  apply (F.starProjection_apply_eq_zero_iff).mpr
  apply (Submodule.mem_orthogonal F _).mpr
  intro y hy
  exact inner_eq_zero_symm.mpr ((Submodule.mem_orthogonal S _).mp (hFS hy)
    _ (hES (E.starProjection_apply_mem x)))

/-- The unknown infinite source residual is bounded by two finite projections. -/
theorem two_flag_source_residual_bound (S E F : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hES : E ≤ S) (hFS : F ≤ Sᗮ) (x : H) :
    ‖S.starProjection x - E.starProjection x‖ ≤
      ‖x - E.starProjection x - F.starProjection x‖ := by
  have he : S.starProjection (E.starProjection x) = E.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (hES (E.starProjection_apply_mem x))
  have hf : S.starProjection (F.starProjection x) = 0 :=
    (S.starProjection_apply_eq_zero_iff).mpr (hFS (F.starProjection_apply_mem x))
  calc
    _ = ‖S.starProjection (x - E.starProjection x - F.starProjection x)‖ := by
      rw [map_sub, map_sub, he, hf, sub_zero]
    _ ≤ _ := S.norm_starProjection_apply_le _

/-- All cross terms vanish by actual subspace membership; no diagonal Gram
    approximation is made. Both finite projection norms retain their full Grams. -/
theorem two_flag_residual_energy (S E F : Submodule ℂ H)
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hES : E ≤ S) (hFS : F ≤ Sᗮ) (x : H) :
    ‖x - E.starProjection x - F.starProjection x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖E.starProjection x‖ ^ 2 - ‖F.starProjection x‖ ^ 2 := by
  have hp := projection_energy F (x - E.starProjection x)
  rw [map_sub, complementary_finite_source_zero S E F hES hFS x, sub_zero,
    projection_energy E x] at hp
  exact hp

/-- Unit domination pays the same original nuclear tail for every pair of flags. -/
theorem two_flag_residual_contraction (S E F : Submodule ℂ H)
    [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hES : E ≤ S) (hFS : F ≤ Sᗮ) (x : H) :
    ‖x - E.starProjection x - F.starProjection x‖ ≤ ‖x‖ := by
  have hp := complementary_projection_bound F (x - E.starProjection x)
  rw [map_sub, complementary_finite_source_zero S E F hES hFS x, sub_zero] at hp
  exact hp.trans (complementary_projection_bound E x)

/-- A finite span of genuine complementary vectors. In the arithmetic
    application these can be H's basis of the literal full source complement. -/
def finiteComplementSpan {ι : Type*} (S : Submodule ℂ H)
    (v : ι → Sᗮ) (J : Finset ι) : Submodule ℂ H :=
  Submodule.span ℂ ((fun i => (v i : H)) '' (J : Set ι))

instance finiteComplementSpan_finiteDimensional {ι : Type*} (S : Submodule ℂ H)
    (v : ι → Sᗮ) (J : Finset ι) : FiniteDimensional ℂ (finiteComplementSpan S v J) :=
  FiniteDimensional.span_of_finite ℂ (J.finite_toSet.image (fun i => (v i : H)))

theorem finiteComplementSpan_le {ι : Type*} (S : Submodule ℂ H)
    (v : ι → Sᗮ) (J : Finset ι) : finiteComplementSpan S v J ≤ Sᗮ := by
  apply Submodule.span_le.mpr
  rintro y ⟨i, _, rfl⟩
  exact (v i).property

/-- Projection energy makes the source-error certificate a finite-Gram quantity. -/
theorem two_flag_source_residual_sq_bound (S E F : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hES : E ≤ S) (hFS : F ≤ Sᗮ) (x : H) :
    ‖E.starProjection x - S.starProjection x‖ ^ 2 ≤
      ‖x‖ ^ 2 - ‖E.starProjection x‖ ^ 2 - ‖F.starProjection x‖ ^ 2 := by
  rw [norm_sub_rev]
  have hb := pow_le_pow_left₀ (norm_nonneg _)
    (two_flag_source_residual_bound S E F hES hFS x) 2
  rwa [two_flag_residual_energy S E F hES hFS x] at hb

end
end ESourceResidual

/- Insert after SourceCertificateFragment and SourceOperatorTailFragment. -/
namespace ESourceResidual
open Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- E34 (34.10) with the actual two finite Gram projections in its head. -/
theorem source_factor_two_flag_head_tail_bound (S E F : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (hES : E ≤ S) (hFS : F ≤ Sᗮ) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) (N : ℕ) :
    (∑' j, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) ≤
      (∑ j ∈ Finset.range N, ‖u j‖ *
        ‖v j - E.starProjection (v j) - F.starProjection (v j)‖) +
      ∑' j, ‖u (j+N)‖ * ‖v (j+N)‖ := by
  apply (source_factor_head_tail_bound S E hES u v hc N).trans
  refine add_le_add ?_ le_rfl
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [norm_sub_rev]
  exact two_flag_source_residual_bound S E F hES hFS (v j)

/-- Applied to Q's exact source and mask ordering. The finite head involves
    only actual finite projections; the original factor tail stays explicit. -/
theorem common_source_operator_two_flag_bound (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (hFS : F ≤ (sourceClosure e0 eF Theta)ᗮ) (N : ℕ) :
    ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M‖ ≤
      (∑ j ∈ Finset.range N, ‖u j‖ *
        ‖v j - (finiteSourceSpan e0 eF Theta T).starProjection (v j) - F.starProjection (v j)‖) +
      ∑' j, ‖u (j+N)‖ * ‖v (j+N)‖ :=
  (common_source_operator_norm_error e0 eF Theta A M u v hc hfactor T).trans
    (source_factor_two_flag_head_tail_bound (sourceClosure e0 eF Theta)
      (finiteSourceSpan e0 eF Theta T) F (finiteSourceSpan_le e0 eF Theta T) hFS u v hc N)

end
end ESourceResidual


/- Insert after SourceCertificateFragment and QSourceCutoffFragment.
   The complementary flag is H's actual Hilbert basis, not a prescribed list
   of zeros. This proves the convergence application of E34 (34.10a). -/
namespace ESourceResidual
open Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem basis_sum_in_submodule {ι : Type*}
    (F : Submodule ℂ H) [F.HasOrthogonalProjection]
    (e : HilbertBasis ι ℂ F) (x : H) :
    HasSum (fun i => (e.repr (F.orthogonalProjection x)) i • (e i : H))
      (F.starProjection x) := by
  have h := F.subtypeL.hasSum (e.hasSum_repr (F.orthogonalProjection x))
  simpa only [map_smul, Submodule.starProjection_apply] using h

set_option maxHeartbeats 800000 in
theorem finiteComplementSpan_projection_tendsto {ι : Type*}
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (e : HilbertBasis ι ℂ Sᗮ) (x : H) :
    Tendsto (fun J : Finset ι => (finiteComplementSpan S e J).starProjection x)
      atTop (𝓝 (Sᗮ.starProjection x)) := by
  classical
  let c : ι → ℂ := fun i => (e.repr (Sᗮ.orthogonalProjection x)) i
  have hsum : HasSum (fun i => c i • (e i : H)) (Sᗮ.starProjection x) :=
    basis_sum_in_submodule Sᗮ e x
  have hm (J : Finset ι) : (∑ i ∈ J, c i • (e i : H)) ∈ finiteComplementSpan S e J := by
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, hi, rfl⟩
  change Tendsto (fun J : Finset ι => ∑ i ∈ J, c i • (e i : H))
    atTop (𝓝 (Sᗮ.starProjection x)) at hsum
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hsum (ε/2) (by linarith)
  refine ⟨J, fun U hU => ?_⟩
  have hb := Masullo.NestedProjection.projection_recovery_bound Sᗮ
    (finiteComplementSpan S e U) (finiteComplementSpan_le S e U)
    x (∑ i ∈ U, c i • (e i : H)) (hm U)
  have hd := hJ U hU
  rw [dist_eq_norm, norm_sub_rev] at hd
  rw [dist_eq_norm]
  exact hb.trans_lt (by linarith)

/-- The two independently directed finite flags recover the same whole
    Hilbert vector. Neither a Mellin density premise nor a physical limit occurs. -/
theorem common_two_flag_residual_tendsto {ι : Type*}
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (e : HilbertBasis ι ℂ (sourceClosure e0 eF Theta)ᗮ) (x : H) :
    Tendsto (fun p : Finset H × Finset ι =>
      ‖x - (finiteSourceSpan e0 eF Theta p.1).starProjection x -
        (finiteComplementSpan (sourceClosure e0 eF Theta) e p.2).starProjection x‖)
      ((atTop : Filter (Finset H)) ×ˢ (atTop : Filter (Finset ι))) (𝓝 0) := by
  classical
  have hS := Masullo.NestedProjection.global_projection_tendsto
    (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
    (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
    (finiteSourceSpan_dense e0 eF Theta) x
  have hF := finiteComplementSpan_projection_tendsto (sourceClosure e0 eF Theta) e x
  have hconst : Tendsto (fun _ : Finset H × Finset ι => x)
      ((atTop : Filter (Finset H)) ×ˢ (atTop : Filter (Finset ι))) (𝓝 x) :=
    tendsto_const_nhds
  have ht := (hconst.sub (hS.comp tendsto_fst)).sub (hF.comp tendsto_snd)
  simpa only [Submodule.starProjection_orthogonal_val, sub_self, norm_zero] using ht.norm

/-- Q's original norm-product cost also dominates the fully finite
    certificate, with constant one. Its actual factorization remains separate. -/
theorem common_two_flag_cost_tendsto {ι : Type*}
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (e : HilbertBasis ι ℂ (sourceClosure e0 eF Theta)ᗮ)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun p : Finset H × Finset ι =>
      ∑' j, ‖u j‖ * ‖v j - (finiteSourceSpan e0 eF Theta p.1).starProjection (v j) -
        (finiteComplementSpan (sourceClosure e0 eF Theta) e p.2).starProjection (v j)‖)
      ((atTop : Filter (Finset H)) ×ˢ (atTop : Filter (Finset ι))) (𝓝 0) := by
  have ht (j : ℕ) := (common_two_flag_residual_tendsto e0 eF Theta e (v j)).const_mul ‖u j‖
  have hbound : ∀ p : Finset H × Finset ι, ∀ j : ℕ,
      ‖‖u j‖ * ‖v j - (finiteSourceSpan e0 eF Theta p.1).starProjection (v j) -
        (finiteComplementSpan (sourceClosure e0 eF Theta) e p.2).starProjection (v j)‖‖ ≤
      ‖u j‖ * ‖v j‖ := by
    intro p j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact two_flag_residual_contraction (sourceClosure e0 eF Theta)
      (finiteSourceSpan e0 eF Theta p.1)
      (finiteComplementSpan (sourceClosure e0 eF Theta) e p.2)
      (finiteSourceSpan_le e0 eF Theta p.1)
      (finiteComplementSpan_le (sourceClosure e0 eF Theta) e p.2) (v j)
  simpa only [mul_zero, tsum_zero] using
    tendsto_tsum_of_dominated_convergence hc ht (Eventually.of_forall hbound)

end
end ESourceResidual
#check ESourceResidual.common_two_flag_cost_tendsto
#print axioms ESourceResidual.common_two_flag_cost_tendsto


/- Shared definitions copied from Masullo/Nuclear/TraceExhaustion.lean,
   HasNuclearCost and nuclearNorm only. Insert once; no new trace definition. -/
noncomputable section
namespace Masullo.NuclearFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

def HasNuclearCost (T : E →L[ℂ] E) (C : ℝ) : Prop :=
  ∃ (v : ι → E) (f : ι → E →L[ℂ] ℂ),
    (∀ x, HasSum (fun i => f i x • v i) (T x)) ∧
    Summable (fun i => ‖f i‖ * ‖v i‖) ∧
    (∑' i, ‖f i‖ * ‖v i‖) ≤ C

end Masullo.NuclearFactorization
namespace Masullo.NuclearFactorization
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The repository's norm from absolutely summable rank-one representations. -/
def nuclearNorm (T : H →L[ℂ] H) : ENNReal :=
  sInf {c | ∃ (κ : Type u) (C : ℝ), HasNuclearCost (ι := κ) T C ∧
    c = ENNReal.ofReal C}

theorem nuclearNorm_le_of_cost {κ : Type u} {T : H →L[ℂ] H} {C : ℝ}
    (h : HasNuclearCost (ι := κ) T C) : nuclearNorm T ≤ ENNReal.ofReal C := by
  exact sInf_le ⟨κ, C, h, rfl⟩

end Masullo.NuclearFactorization
end


/- Insert after QSourceCutoffFragment, E SourceResidualFragment, and
   QNuclearNormDefinitionsFragment. Uses exactly the existing source spans. -/
namespace Q.NuclearSourceCutoff
open Filter OSourceClosure Q.IntegratedSourceCutoff Masullo.NuclearFactorization
open scoped Topology InnerProductSpace
noncomputable section
universe w
variable {H κ : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The canonical theta-source cost works with the actual factor index,
including a Hilbert basis or a character-dependent sigma index. -/
theorem source_cost_tendsto (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : κ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j, ‖u j‖ *
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) atTop (𝓝 0) := by
  classical
  have hz : (∑' j : κ, (0 : ℝ)) = 0 := by simp
  rw [← hz]
  apply tendsto_tsum_of_dominated_convergence hc
  · intro j
    have hh := (Masullo.NestedProjection.global_projection_tendsto
      (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
      (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
      (finiteSourceSpan_dense e0 eF Theta) (v j)).sub
      (tendsto_const_nhds (x := (sourceClosure e0 eF Theta).starProjection (v j)))
    simpa using hh.norm.const_mul ‖u j‖
  · apply Eventually.of_forall
    intro T j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (ESourceResidual.nested_source_residual_contraction
        (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta T)
        (finiteSourceSpan_le e0 eF Theta T) (v j)) (norm_nonneg _)

/-- Explicit rank-one cost of global PA M minus the finite-source PA M.
The factor application concerns the actual A M on every completed input. -/
theorem source_residual_hasNuclearCost (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x)))
    (T : Finset H) :
    HasNuclearCost (ι := κ)
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M)
      (∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) := by
  refine ⟨fun j => (finiteSourceSpan e0 eF Theta T).starProjection (v j) -
      (sourceClosure e0 eF Theta).starProjection (v j),
    fun j => innerSL ℂ (u j), ?_, ?_, ?_⟩
  · intro x
    have hh := ((finiteSourceSpan e0 eF Theta T).starProjection -
      (sourceClosure e0 eF Theta).starProjection).hasSum (hfactor x)
    convert hh using 1
    · funext j
      simp only [innerSL_apply_apply, ContinuousLinearMap.sub_apply, map_smul, smul_sub]
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.one_apply]
      abel
  · simp only [innerSL_apply_norm]
    exact Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => mul_le_mul_of_nonneg_left
        (ESourceResidual.nested_source_residual_contraction
          (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta T)
          (finiteSourceSpan_le e0 eF Theta T) (v j)) (norm_nonneg _)) hc
  · simp only [innerSL_apply_norm, le_refl]

theorem source_residual_nuclearNorm_bound (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x)))
    (T : Finset H) :
    nuclearNorm
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M) ≤
      ENNReal.ofReal (∑' j, ‖u j‖ *
        ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
          (sourceClosure e0 eF Theta).starProjection (v j)‖) :=
  nuclearNorm_le_of_cost (source_residual_hasNuclearCost e0 eF Theta A M u v hc hfactor T)

/-- Source exhaustion in the repository's nuclear norm, with the actual
operator difference and convolution-first order. -/
theorem source_residual_nuclearNorm_tendsto (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x))) :
    Tendsto (fun T : Finset H => nuclearNorm
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M))
      atTop (𝓝 0) := by
  have hcost := source_cost_tendsto e0 eF Theta u v hc
  have hbound := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcost
  simp only [ENNReal.ofReal_zero] at hbound
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le _) (source_residual_nuclearNorm_bound e0 eF Theta A M u v hc hfactor)

end
end Q.NuclearSourceCutoff
#check Q.NuclearSourceCutoff.source_residual_nuclearNorm_tendsto
#print axioms Q.NuclearSourceCutoff.source_residual_nuclearNorm_tendsto


/- E34 (34.10), applied to Q's existing nuclear norm.
   Insert after QNuclearSourceCutoff and E SourceCertificateFragment.
   The actual localized factor equation and its cost remain explicit. -/
namespace ESourceResidual
open Filter OSourceClosure Q.IntegratedSourceCutoff Masullo.NuclearFactorization
open scoped Topology InnerProductSpace
noncomputable section
universe w
variable {H κ : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The finite factor packet may be any finite subset of the true factor
index. The omitted tail keeps the original norm-product cost. -/
theorem source_factor_finite_head_tail_bound
    (S E C : Submodule ℂ H) [S.HasOrthogonalProjection]
    [E.HasOrthogonalProjection] [C.HasOrthogonalProjection]
    (hES : E ≤ S) (hCS : C ≤ Sᗮ) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) (J : Finset κ) :
    (∑' j, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) ≤
      (∑ j ∈ J, ‖u j‖ * ‖v j - E.starProjection (v j) - C.starProjection (v j)‖) +
      ∑' j : {j // j ∉ J}, ‖u j.val‖ * ‖v j.val‖ := by
  classical
  have hr : Summable (fun j => ‖u j‖ *
      ‖E.starProjection (v j) - S.starProjection (v j)‖) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun j => mul_le_mul_of_nonneg_left
        (nested_source_residual_contraction S E hES (v j)) (norm_nonneg _)) hc
  rw [← hr.sum_add_tsum_subtype_compl J]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_sub_rev]
    exact two_flag_source_residual_bound S E C hES hCS (v j)
  · exact Summable.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left
        (nested_source_residual_contraction S E hES (v j.val)) (norm_nonneg _))
      (hr.subtype {j | j ∉ J}) (hc.subtype {j | j ∉ J})

/-- This is a bound in the same nuclear norm used by Q's cutoff theorem,
not merely an operator norm bound. The two finite projections retain their
full Gram matrices and convolution precedes the source projection. -/
theorem common_source_nuclearNorm_finite_certificate
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x)))
    (T : Finset H) (C : Submodule ℂ H) [C.HasOrthogonalProjection]
    (hCS : C ≤ (sourceClosure e0 eF Theta)ᗮ) (J : Finset κ) :
    nuclearNorm
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M) ≤
      ENNReal.ofReal ((∑ j ∈ J, ‖u j‖ *
        ‖v j - (finiteSourceSpan e0 eF Theta T).starProjection (v j) - C.starProjection (v j)‖) +
        ∑' j : {j // j ∉ J}, ‖u j.val‖ * ‖v j.val‖) := by
  apply (Q.NuclearSourceCutoff.source_residual_nuclearNorm_bound
    e0 eF Theta A M u v hc hfactor T).trans
  exact ENNReal.ofReal_le_ofReal (source_factor_finite_head_tail_bound
    (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta T) C
    (finiteSourceSpan_le e0 eF Theta T) hCS u v hc J)

end
end ESourceResidual
#check ESourceResidual.common_source_nuclearNorm_finite_certificate
#print axioms ESourceResidual.common_source_nuclearNorm_finite_certificate
