import Mathlib

/-! Combined live review: O source closure, P Haar scaling, C source limits, I retained compensator. -/

-- Reviewed source: inputs/exchange/O/SourceClosureCore.lean
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

-- Reviewed source: inputs/exchange/P/POriginalHaar.lean

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace POriginalHaar

/-- The scalar change from normalized quotient Haar ν to μ=Vν.
This is an equality of actual Bochner integrals, including its 1/V. -/
theorem original_haar_integral {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (V : ℝ) (hV : 0 < V) (d : X → ℂ) :
    (∫ x, (V : ℂ)⁻¹ * d x ∂(ENNReal.ofReal V • nu)) = ∫ x, d x ∂nu := by
  rw [integral_smul_measure, integral_const_mul]
  rw [ENNReal.toReal_ofReal hV.le]
  change (V : ℂ) * ((V : ℂ)⁻¹ * ∫ x, d x ∂nu) = _
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hV)), one_mul]

/-- The original-Haar rank-one density of normalized L2 columns.
For F=√w f and G=√w g this is (w/V) f conj(g). -/
theorem rank_one_original_haar {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (V : ℝ) (hV : 0 < V) (F G : Lp ℂ 2 nu) :
    (∫ x, (V : ℂ)⁻¹ * (F x * star (G x))
      ∂(ENNReal.ofReal V • nu)) = inner ℂ G F := by
  rw [original_haar_integral nu V hV, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp [RCLike.inner_apply])

/-- Weight cancellation is pointwise, so it can be used on the specified
rank-one diagonal; it does not restrict a product-a.e. representative. -/
theorem weighted_rank_one_density (r V : ℝ) (f g : ℂ) :
    (V : ℂ)⁻¹ * (((r : ℂ) * f) * star ((r : ℂ) * g)) =
      ((r*r/V : ℝ) : ℂ) * f * star g := by
  have hr : star (r : ℂ) = (r : ℂ) := by simp
  rw [star_mul, hr]
  push_cast
  ring

end POriginalHaar

#print axioms POriginalHaar.original_haar_integral
#print axioms POriginalHaar.rank_one_original_haar
#print axioms POriginalHaar.weighted_rank_one_density

-- Reviewed source: inputs/exchange/C/CFlagLimits03.lean

/-! C36: projected source flags and the order of source/physical limits.
The actual Mellin separation and trace identities are explicit hypotheses.
No finite Mellin span is defined to be the full spectral projection. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace CReview

section SourceFlag
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- Orthogonal pairing, proved from the genuine subspace projection. -/
theorem projection_pairing (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (x y : H) :
    inner ℂ (G.starProjection x) y = inner ℂ x (G.starProjection y) := by
  have h1 := Submodule.inner_right_of_mem_orthogonal
    (G.starProjection_apply_mem x) (G.sub_starProjection_mem_orthogonal y)
  rw [inner_sub_right, sub_eq_zero] at h1
  have h2 := (Submodule.mem_orthogonal' G _).1
    (G.sub_starProjection_mem_orthogonal x)
    (G.starProjection y) (G.starProjection_apply_mem y)
  rw [inner_sub_left, sub_eq_zero] at h2
  exact h1.trans h2.symm

/-- C36 (36.2): only separation on the ORIGINAL source G is needed.
Application: k j = exp(-a*u) u^j/(j! w_beta), and G is the BOTH-moment
original theta closure. Analytic/Fourier uniqueness must supply hsep. -/
theorem projected_source_flag_complete
    (G : Submodule ℂ H) [G.HasOrthogonalProjection] (k : ℕ → H)
    (hsep : ∀ f ∈ G, (∀ j, inner ℂ (k j) f = 0) → f = 0) :
    (Submodule.span ℂ (Set.range (fun j => G.starProjection (k j)))).topologicalClosure = G := by
  let F := (Submodule.span ℂ (Set.range (fun j => G.starProjection (k j)))).topologicalClosure
  have hclosed : IsClosed (G : Set H) := by
    have he : (G : Set H) = {x | G.starProjection x = x} := by
      ext x
      exact Submodule.starProjection_eq_self_iff.symm
    rw [he]
    exact isClosed_eq G.starProjection.continuous continuous_id
  have hspan : Submodule.span ℂ (Set.range (fun j => G.starProjection (k j))) ≤ G := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact G.starProjection_apply_mem _
  have hFG : F ≤ G := fun f hf => closure_minimal hspan hclosed hf
  apply le_antisymm hFG
  intro f hf
  have hr : f - F.starProjection f ∈ G :=
    G.sub_mem hf (hFG (F.starProjection_apply_mem f))
  have hz : f - F.starProjection f = 0 := by
    apply hsep _ hr
    intro j
    have hp : G.starProjection (f - F.starProjection f) = f - F.starProjection f :=
      Submodule.starProjection_eq_self_iff.mpr hr
    have hj : G.starProjection (k j) ∈ F :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, rfl⟩)
    have ho := (Submodule.mem_orthogonal F _).mp
      (F.sub_starProjection_mem_orthogonal f) _ hj
    rw [projection_pairing, hp] at ho
    exact ho
  rw [sub_eq_zero] at hz
  rw [hz]
  exact F.starProjection_apply_mem f

end SourceFlag

/-- C36 (36.6). Exact m*H return minus the actual masked trace.
The finite-rank return and compact trace norm bound remain separate inputs. -/
theorem incoming_tail_lower_bound (m : ℕ) (H masked tail : ℂ) (B : ℝ)
    (hreturn : masked + tail = (m : ℂ) * H) (hcompact : ‖masked‖ ≤ B) :
    (m : ℝ) * ‖H‖ - B ≤ ‖tail‖ := by
  have hn : ‖(m : ℂ) * H‖ = (m : ℝ) * ‖H‖ := by
    rw [norm_mul]
    simp
  have ht := norm_add_le masked tail
  rw [hreturn, hn] at ht
  linarith

/-- The incoming tail cannot have a source-rank-uniform bound when H≠0.
This does not infer that the entire omitted-zero correction is nonzero. -/
theorem no_uniform_incoming_tail (H : ℂ) (hH : H ≠ 0)
    (masked tail : ℕ → ℂ) (B : ℝ)
    (hreturn : ∀ m, masked m + tail m = (m : ℂ) * H)
    (hcompact : ∀ m, ‖masked m‖ ≤ B) :
    ∀ C : ℝ, ∃ m, C < ‖tail m‖ := by
  intro C
  have hpos : 0 < ‖H‖ := norm_pos_iff.mpr hH
  obtain ⟨m, hm⟩ := exists_nat_gt ((C+B)/‖H‖)
  have hg : C+B < (m : ℝ)*‖H‖ := (div_lt_iff₀ hpos).mp hm
  have hl := incoming_tail_lower_bound m H (masked m) (tail m) B
    (hreturn m) (hcompact m)
  exact ⟨m, by linarith⟩

/-- C36 (36.9): source approximation is paid at the FIXED physical mask. -/
theorem two_error_bound (C physical finite : ℂ) (delta epsilon : ℝ)
    (hphysical : ‖C-physical‖ ≤ delta)
    (hsource : ‖physical-finite‖ ≤ epsilon) :
    ‖C-finite‖ ≤ delta+epsilon := by
  calc
    ‖C-finite‖ = ‖(C-physical)+(physical-finite)‖ := by congr 1; ring
    _ ≤ ‖C-physical‖+‖physical-finite‖ := norm_add_le _ _
    _ ≤ delta+epsilon := add_le_add hphysical hsource

/-- The valid quantified order: first choose R, then the required source rank.
No uniformity of epsilon(R,m) in R and no exchange of limits is asserted. -/
theorem ordered_two_error_limit (C : ℂ) (physical : ℕ → ℂ)
    (finite : ℕ → ℕ → ℂ) (delta : ℕ → ℝ) (epsilon : ℕ → ℕ → ℝ)
    (hphysical : ∀ R, ‖C-physical R‖ ≤ delta R)
    (hsource : ∀ R m, ‖physical R-finite R m‖ ≤ epsilon R m)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hepsilon : ∀ R, Tendsto (epsilon R) atTop (𝓝 0)) :
    ∀ eta > 0, ∀ᶠ R in atTop, ∀ᶠ m in atTop, ‖C-finite R m‖ < eta := by
  intro eta heta
  have hd : ∀ᶠ R in atTop, delta R < eta/2 :=
    hdelta.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hd] with R hR
  have he : ∀ᶠ m in atTop, epsilon R m < eta/2 :=
    (hepsilon R).eventually (gt_mem_nhds (by linarith))
  filter_upwards [he] with m hm
  exact (two_error_bound C (physical R) (finite R m) (delta R) (epsilon R m)
    (hphysical R) (hsource R m)).trans_lt (by linarith)

/-- A finite wide-source return has a MINUS sign in the correction. -/
theorem compensated_source_identity (narrow wide boundary correction : ℂ)
    (hcorrection : correction = narrow-wide) :
    correction = -boundary + (narrow-(wide-boundary)) := by
  rw [hcorrection]
  ring

end CReview

#print axioms CReview.projected_source_flag_complete
#print axioms CReview.incoming_tail_lower_bound
#print axioms CReview.no_uniform_incoming_tail
#print axioms CReview.ordered_two_error_limit
#print axioms CReview.compensated_source_identity

-- Reviewed source: inputs/exchange/I/IShellLimits.lean

/-! I35 (35.7)-(35.9): the finite source term and narrow compensator are
retained under the SAME original-Haar mask. No arithmetic density identity
or nuclearity is asserted by this analytic lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ReviewI
variable {X : Type*} [MeasurableSpace X]

def masked (mu : Measure X) (w f : X → ℂ) : ℂ := ∫ x, w x * f x ∂mu

theorem masked_integrable (mu : Measure X) (w f : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => w x * f x) mu := by
  apply hf.norm.mono' (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖w x * f x‖ ≤ ‖f x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

theorem masked_sub (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    masked mu w (fun x => f x-g x) = masked mu w f-masked mu w g := by
  simp only [masked, mul_sub]
  exact integral_sub (masked_integrable mu w f hw hb hf)
    (masked_integrable mu w g hw hb hg)

theorem masked_error_le (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    ‖masked mu w f-masked mu w g‖ ≤ ∫ x, ‖f x-g x‖ ∂mu := by
  rw [← masked_sub mu w f g hw hb hf hg]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (masked_integrable mu w _ hw hb (hf.sub hg)).norm (hf.sub hg).norm
  filter_upwards [hb] with x hx
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- `wide=d_beta(T_beta)`, `narrow=d_alpha(T_alpha)`,
`sandwich=d_beta(S_e T_beta S_e)`, `regularized=d_alpha(R_e T_alpha R_e)`.
The source transport is `sandwich-regularized`. -/
theorem finite_source_compensator_integral
    (mu : Measure X) (w wide narrow sandwich regularized : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hsand : Integrable sandwich mu) (hreg : Integrable regularized mu) :
    masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich x-regularized x)
      +masked mu w (fun x => narrow x-regularized x) =
    masked mu w (fun x => wide x-sandwich x) := by
  rw [masked_sub mu w sandwich regularized hw hb hsand hreg,
    masked_sub mu w narrow regularized hw hb hnarrow hreg,
    masked_sub mu w wide sandwich hw hb hwide hsand]
  ring

/-- The low-energy cutoff converges to the full-input LEFT correction under
any bounded physical/shell mask. The source identity is not replaced by
its total trace; the regularization compensator is present at every n. -/
theorem regularized_source_shell_limit
    (mu : Measure X) (w wide narrow full : X → ℂ)
    (sandwich regularized : ℕ → X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hfull : Integrable full mu)
    (hsand : ∀ n, Integrable (sandwich n) mu)
    (hreg : ∀ n, Integrable (regularized n) mu)
    (hlim : Tendsto (fun n => ∫ x, ‖sandwich n x-full x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) atTop
      (𝓝 (masked mu w (fun x => wide x-full x))) := by
  have ht : Tendsto (fun n => masked mu w (sandwich n)) atTop
      (𝓝 (masked mu w full)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => masked_error_le mu w (sandwich n) full hw hb (hsand n) hfull) hlim
  have he : (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) =
      (fun n => masked mu w wide-masked mu w (sandwich n)) := by
    funext n
    rw [finite_source_compensator_integral mu w wide narrow (sandwich n)
      (regularized n) hw hb hwide hnarrow (hsand n) (hreg n),
      masked_sub mu w wide (sandwich n) hw hb hwide (hsand n)]
  rw [he, masked_sub mu w wide full hw hb hwide hfull]
  exact tendsto_const_nhds.sub ht

/-- Physical exhaustion is justified from an actual integrable Haar density. -/
theorem physical_cutoff_limit (mu : Measure X) (d : X → ℂ) (w : ℕ → X → ℂ)
    (hd : Integrable d mu) (hw : ∀ n, AEStronglyMeasurable (w n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖w n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => w n x) atTop (𝓝 1)) :
    Tendsto (fun n => masked mu (w n) d) atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · intro n
    exact (hw n).mul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    filter_upwards [hb n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa using hx.mul (tendsto_const_nhds (x := d x))

/-- The physical tail is retained as an integral before taking a limit. -/
theorem physical_tail_identity (mu : Measure X) (w d : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hd : Integrable d mu) :
    (∫ x, d x ∂mu)-masked mu w d = ∫ x, (1-w x)*d x ∂mu := by
  simp only [sub_mul, one_mul, masked]
  exact (integral_sub hd (masked_integrable mu w d hw hb hd)).symm

/-- If the full explicit formula is pole - all zeros, and the native trace
is interior + admitted edge, the correction is omitted - admitted edge. -/
theorem omitted_edge_remainder (pole geometric interior edge omitted spectral : ℂ)
    (hfull : geometric = pole-(interior+omitted))
    (hspec : spectral = interior+edge) :
    pole-geometric-spectral = omitted-edge := by
  rw [hfull, hspec]
  ring

end ReviewI
#print axioms ReviewI.finite_source_compensator_integral
#print axioms ReviewI.regularized_source_shell_limit
#print axioms ReviewI.physical_cutoff_limit
#print axioms ReviewI.omitted_edge_remainder

namespace Masullo.BoundaryJetOrders

/-- The finite set of boundary jets satisfying the STRICT numerical condition
in Proposition 9.1.2.5. This is an index set, not a spectrum or an L-function.
The unresolved analytic bridge is that these are exactly the continuous jets
of the actual weighted idele-class quotient. -/
noncomputable def boundaryJetOrders (N : ℕ) (s : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (2 : ℝ) * j + 1 < s)

/-- Discharges the finite counting premise for boundary multiplicities:
at odd integral weight 2*k+1, the strict cutoff retains min(N,k) jets. -/
theorem boundaryJetOrders_odd (N k : ℕ) :
    boundaryJetOrders N (2 * (k : ℝ) + 1) = Finset.range (min N k) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  constructor
  · intro h
    have hj : (j : ℝ) < (k : ℝ) := by linarith [h.2]
    exact ⟨h.1, by exact_mod_cast hj⟩
  · rintro ⟨hN, hk⟩
    have hj : (j : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ⟨hN, by linarith⟩

/-- Conditional finite-block trace reduction for the binomial jet action
printed at (10.3.1.17). Discharges only its finite trace calculation; the
hypothesis must be proved for the genuine quotient operator before use. -/
theorem trace_of_binomial_jet_action (n : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    Matrix.trace M = (n : ℂ) * a 0 := by
  have hd (i : Fin n) : M i i = a 0 := by simp [hM]
  simp [Matrix.trace, Matrix.diag, hd, nsmul_eq_mul]

/-- Combined exact finite-count and conditional finite-trace step toward the
correct spectral multiplicity. No assertion of analytic jet admissibility,
zero identification, completeness, nuclearity, or infinite summability. -/
theorem boundary_jet_trace_at_odd_weight (N k : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card)
      (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k ∧
      Matrix.trace M = ((min N k : ℕ) : ℂ) * a 0 := by
  have hc : (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k := by
    rw [boundaryJetOrders_odd, Finset.card_range]
  refine ⟨hc, ?_⟩
  simpa only [hc] using trace_of_binomial_jet_action _ a M hM

/-- Numerical boundary multiplicity for every real Sobolev parameter.
This discharges counting only; continuous native jet attachment is unresolved. -/
theorem boundaryJetOrders_all_real (N : ℕ) (s : ℝ) :
    boundaryJetOrders N s = Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range,
    Nat.lt_min, Nat.lt_ceil]
  constructor
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩

end Masullo.BoundaryJetOrders

namespace DCombinedReview
open MeasureTheory Filter
open scoped Topology BigOperators

/-- The printed increasing-mask shell sign, kept separate from decreasing
source-projection differences. This is finite telescoping only. -/
theorem printed_shell_sign (alpha : ℕ → ℂ) (k : ℂ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (alpha (j+1)-alpha j)*k) = (alpha n-alpha 0)*k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Zero total transport mass removes the transport only after the OUTER
physical limit; no fixed-mask integral is asserted to vanish. -/
theorem zero_mass_transport_outer_limit {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (t : X → ℂ) (w : ℕ → X → ℂ)
    (ht : Integrable t mu) (hmass : (∫ x, t x ∂mu) = 0)
    (hw : ∀ n, AEStronglyMeasurable (w n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖w n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => w n x) atTop (𝓝 1)) :
    Tendsto (fun n => ReviewI.masked mu (w n) t) atTop (𝓝 0) := by
  simpa only [hmass] using ReviewI.physical_cutoff_limit mu t w ht hw hb hl

/-- Both partners keep their own omitted-zero and admitted-edge terms.
The explicit formula and spectral identification remain application inputs. -/
theorem both_tests_retained_remainder (pole geometric interior edge omitted spectral : Fin 2 → ℂ)
    (hfull : ∀ q, geometric q = pole q-(interior q+omitted q))
    (hspec : ∀ q, spectral q = interior q+edge q) :
    ∀ q, pole q-geometric q-spectral q = omitted q-edge q := by
  intro q
  exact ReviewI.omitted_edge_remainder _ _ _ _ _ _ (hfull q) (hspec q)

#print axioms printed_shell_sign
#print axioms zero_mass_transport_outer_limit
#print axioms both_tests_retained_remainder
end DCombinedReview
