import Mathlib

/-! Assembly of reviewed exact source: core ProjectionOrder, CFlagLimits03, EIncomingMask. -/

-- SOURCE: inputs/review_core/Masullo/Geometry/ProjectionOrder.lean

namespace Masullo.CoreInvarianceExtends
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 theorem core_invariance_extends (T : H →L[ℂ] H) (C : Submodule ℂ H)
    (hC : ∀ x ∈ C, T x ∈ C) :
    ∀ x ∈ C.topologicalClosure, T x ∈ C.topologicalClosure := by
  intro x hx
  exact map_mem_closure T.continuous hx hC

/-- With G the ACTUAL geometric closure, its orthogonal complement projector
is P=1-Q. Invariance of G gives a one-sided triangular block, not commutation. -/
 theorem projection_order_defect (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    T (P x) - P (T x) = Q (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

 theorem convolution_first_compression (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let P := ContinuousLinearMap.id ℂ H - G.starProjection
    P (T x) = P (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

/-- Both complementary printed-to-convolution-first changes have opposite
signs, for the SAME cutoff. Neither individual defect is set to zero. -/
 theorem paired_cutoff_order_defects (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T M : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    (M (T (P x)) - M (P (T x)) = M (Q (T (P x)))) ∧
    (M (T (Q x)) - M (Q (T x)) = -M (Q (T (P x)))) := by
  dsimp only
  have hh := congrArg M (projection_order_defect G T hG x)
  simp only [map_sub] at hh
  constructor
  · exact hh
  · have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
      Submodule.starProjection_eq_self_iff.mpr
        (hG _ (Submodule.starProjection_apply_mem G x))
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
    abel

#print axioms core_invariance_extends
#print axioms projection_order_defect
#print axioms convolution_first_compression
#print axioms paired_cutoff_order_defects
end Masullo.CoreInvarianceExtends

-- SOURCE: inputs/exchange/C/CFlagLimits03.lean

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

-- SOURCE: inputs/exchange/E/EIncomingMask.lean

/-! E36 equations (36.4), (36.7)--(36.9): the incoming mask is on the
right of convolution, all source vectors and Gram cross terms are retained.
The finite trace formula is NOT assumed to identify arbitrary vectors with
original theta-source jets. That identification is an application obligation. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace EReview

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} [Fintype ι]

def packetTrace (u : ι → H) (A : H →L[ℂ] H) : ℂ :=
  ∑ i, inner ℂ (u i) (A (u i))

def incomingCompensation (u : ι → H) (A M : H →L[ℂ] H) : ℂ :=
  ∑ i, inner ℂ (u i) (A (u i - M (u i)))

/-- Exact finite-rank trace split, with the mask on the incoming vector. -/
theorem incomingCompensation_eq (u : ι → H) (A M : H →L[ℂ] H) :
    incomingCompensation u A M = packetTrace u A - packetTrace u (A.comp M) := by
  simp only [incomingCompensation, packetTrace, map_sub, inner_sub_right,
    Finset.sum_sub_distrib, ContinuousLinearMap.comp_apply]

/-- The actual finite family supplies a quantitative bound before a limit. -/
theorem incomingCompensation_bound (u : ι → H) (A M : H →L[ℂ] H) :
    ‖incomingCompensation u A M‖ ≤
      ∑ i, ‖u i‖ * (‖A‖ * ‖u i - M (u i)‖) := by
  unfold incomingCompensation
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _))

/-- E36 (36.7): fixed-rank Hilbert--Schmidt Cauchy--Schwarz bound. -/
theorem incomingCompensation_sqrt_bound (u : ι → H) (A M : H →L[ℂ] H)
    (hu : ∀ i, ‖u i‖ = 1) :
    ‖incomingCompensation u A M‖ ≤
      Real.sqrt (Fintype.card ι) * ‖A‖ *
        Real.sqrt (∑ i, ‖u i - M (u i)‖ ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun _ : ι => (1 : ℝ)) (fun i => ‖u i - M (u i)‖)
  have hc : (∑ i, ‖u i - M (u i)‖) ≤
      Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, ‖u i - M (u i)‖ ^ 2) := by
    simpa using hcs
  calc
    _ ≤ ∑ i, ‖u i‖ * (‖A‖ * ‖u i - M (u i)‖) :=
      incomingCompensation_bound u A M
    _ = ‖A‖ * ∑ i, ‖u i - M (u i)‖ := by simp_rw [hu, one_mul]; rw [Finset.mul_sum]
    _ ≤ ‖A‖ * (Real.sqrt (Fintype.card ι) *
        Real.sqrt (∑ i, ‖u i - M (u i)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ = _ := by ring

/-- No uniformity in the packet rank is inferred from this fixed-family limit. -/
theorem incomingCompensation_tendsto (u : ι → H) (A : H →L[ℂ] H)
    (M : ℕ → H →L[ℂ] H)
    (hM : ∀ v, Tendsto (fun n => M n v) atTop (𝓝 v)) :
    Tendsto (fun n => incomingCompensation u A (M n)) atTop (𝓝 0) := by
  have hi (i : ι) : Tendsto (fun n =>
      inner ℂ (u i) (A (u i - M n (u i)))) atTop (𝓝 0) := by
    have hv : Tendsto (fun n => u i - M n (u i)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := u i)).sub (hM (u i))
    have ha : Tendsto (fun n => A (u i - M n (u i))) atTop (𝓝 (0 : H)) := by
      simpa [Function.comp_def] using (A.continuous.tendsto 0).comp hv
    have hh := ((innerSL ℂ (u i)).continuous.tendsto (0 : H)).comp ha
    change Tendsto (fun n => inner ℂ (u i) (A (u i - M n (u i))))
      atTop (𝓝 (inner ℂ (u i) (0 : H))) at hh
    simpa only [inner_zero_right] using hh
  simpa only [incomingCompensation, Finset.sum_const_zero] using
    tendsto_finset_sum Finset.univ (fun i _ => hi i)

/-- The packet's boundary return has a NEGATIVE sign in the correction. -/
theorem compensated_correction (c narrow rest transport e atom : ℂ)
    (hc : c = narrow - rest - atom + transport + e) :
    c + atom = narrow - rest + transport + e := by rw [hc]; ring

/-- The physical cutoff is removed with the packet held fixed. -/
theorem compensated_cutoff_limit
    (c source transport e : ℕ → ℂ) (limit atom : ℂ)
    (hc : ∀ n, c n = source n - atom + transport n + e n)
    (hl : Tendsto c atTop (𝓝 limit))
    (ht : Tendsto transport atTop (𝓝 0))
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto source atTop (𝓝 (limit + atom)) := by
  have hs : source = fun n => c n + atom - transport n - e n := by
    funext n
    rw [hc n]
    ring
  rw [hs]
  simpa using ((hl.add_const atom).sub ht).sub he

section MeasuredTail
variable {X : Type*} [MeasurableSpace X]

/-- Dominated convergence for each ORIGINAL weighted Gram entry. The caller
sets d = w_beta * conjugate(r_i) * r_j, with r_j = S_beta kappa_j. -/
theorem tail_entry_tendsto (mu : Measure X) (d : X → ℂ)
    (hd : Integrable d mu) (psi : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (psi n))
    (hbound : ∀ n x, 0 ≤ psi n x ∧ psi n x ≤ 1)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => psi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (((1 - psi n x)^2 : ℝ) : ℂ) * d x ∂mu)
      atTop (𝓝 0) := by
  have hb (n : ℕ) (x : X) : |(1 - psi n x)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hp := hbound n x
    nlinarith [sq_nonneg (psi n x)]
  have ht : Tendsto (fun n => ∫ x, (((1 - psi n x)^2 : ℝ) : ℂ) * d x ∂mu)
      atTop (𝓝 (∫ _ : X, (0 : ℂ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
    · intro n
      exact (((measurable_const.sub (hm n)).pow_const 2).complex_ofReal.aestronglyMeasurable).mul hd.aestronglyMeasurable
    · exact hd.norm
    · intro n
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb n x)
    · filter_upwards [hlim] with x hx
      have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hx).pow 2
      have hhC := Complex.continuous_ofReal.continuousAt.tendsto.comp hh
      simpa using hhC.mul_const (d x)
  simpa using ht

/-- Full finite inverse-Gram contraction; off-diagonal entries are retained. -/
theorem tail_gram_contraction_tendsto {κ : Type*} [Fintype κ]
    (mu : Measure X) (Ginv : Matrix κ κ ℂ) (d : κ → κ → X → ℂ)
    (hd : ∀ i j, Integrable (d i j) mu) (psi : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (psi n))
    (hb : ∀ n x, 0 ≤ psi n x ∧ psi n x ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => psi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∑ i, ∑ j, Ginv i j *
      ∫ x, (((1 - psi n x)^2 : ℝ) : ℂ) * d j i x ∂mu)
      atTop (𝓝 0) := by
  have hi (i j : κ) := (tail_entry_tendsto mu (d j i) (hd j i) psi hm hb hl).const_mul (Ginv i j)
  have hj (i : κ) := tendsto_finset_sum Finset.univ (fun j _ => hi i j)
  simpa using tendsto_finset_sum Finset.univ (fun i _ => hj i)
end MeasuredTail

end EReview
#print axioms EReview.incomingCompensation_sqrt_bound
#print axioms EReview.incomingCompensation_tendsto
#print axioms EReview.tail_gram_contraction_tendsto
#print axioms EReview.compensated_cutoff_limit

namespace FReview.SourceAssembly
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- F36 (36.5), assembled from E's actual incoming-vector identity and C's
bound. The actual source packet trace return is an explicit premise. -/
theorem finite_source_cost (m : ℕ) (u : Fin m → H)
    (A M : H →L[ℂ] H) (Hh : ℂ) (B : ℝ)
    (hreturn : EReview.packetTrace u A = (m : ℂ)*Hh)
    (hcompact : ‖EReview.packetTrace u (A.comp M)‖ ≤ B) :
    (m : ℝ)*‖Hh‖-B ≤ ‖EReview.incomingCompensation u A M‖ := by
  apply CReview.incoming_tail_lower_bound m Hh _ _ B _ hcompact
  rw [EReview.incomingCompensation_eq, ← hreturn]
  ring

/-- The same packet is fixed during physical cutoff removal. -/
theorem finite_source_mask_limit (m : ℕ) (u : Fin m → H)
    (A : H →L[ℂ] H) (M : ℕ → H →L[ℂ] H) (Hh : ℂ)
    (hreturn : EReview.packetTrace u A = (m : ℂ)*Hh)
    (hM : ∀ v, Tendsto (fun n => M n v) atTop (𝓝 v)) :
    Tendsto (fun n => EReview.packetTrace u (A.comp (M n))) atTop
      (𝓝 ((m : ℂ)*Hh)) := by
  have he := EReview.incomingCompensation_tendsto u A M hM
  have hid (n : ℕ) : EReview.packetTrace u (A.comp (M n)) =
      EReview.packetTrace u A - EReview.incomingCompensation u A (M n) := by
    rw [EReview.incomingCompensation_eq]
    ring
  simp_rw [hid]
  simpa only [hreturn, sub_zero] using
    (tendsto_const_nhds (x := EReview.packetTrace u A)).sub he

/-- Exact negative wide-source sign with BOTH mask and width transport retained. -/
theorem retained_source_correction (C narrow rest atom mask width : ℂ)
    (h : C = narrow-rest-atom+mask+width) :
    C+atom = narrow-rest+mask+width := by rw [h]; ring

end FReview.SourceAssembly
#print axioms FReview.SourceAssembly.finite_source_cost
#print axioms FReview.SourceAssembly.finite_source_mask_limit
#print axioms FReview.SourceAssembly.retained_source_correction
