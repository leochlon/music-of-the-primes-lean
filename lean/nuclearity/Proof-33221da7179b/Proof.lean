import Mathlib

/-!
Round 173 F: completeness-to-identification component of the manuscript route.

The missing ARITHMETIC premise is that the common kernel of the permitted
continuous native Mellin jets is exactly the closed geometric image G_a.
The theorems below do not assume nuclearity or a summability estimate. They
prove the precise Hilbert-space consequences of that premise, including the
correct closed span and identification of projected operators by their jets.
H, G, and the jets are parameters: attachment to W_I^s(C_K) is NOT claimed.
-/

noncomputable section
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
namespace Round173F

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

def jetSpan (r : ι → H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range r)).topologicalClosure

theorem jet_mem_span (r : ι → H) (i : ι) : r i ∈ jetSpan r :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The corrected interval windows must exhaust this space, rather than
intersections of an increasing family of jet kernels (manuscript 25554). -/
theorem jetSpan_orthogonal_eq_commonKernel (r : ι → H) (x : H) :
    x ∈ (jetSpan r)ᗮ ↔ ∀ i, ⟪r i, x⟫_ℂ = 0 := by
  constructor
  · intro hx i
    exact (Submodule.mem_orthogonal _ _).mp hx _ (jet_mem_span r i)
  · intro hx
    have hs : Submodule.span ℂ (Set.range r) ≤ (innerSL ℂ x).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      change ⟪x, r i⟫_ℂ = 0
      exact inner_eq_zero_symm.mp (hx i)
    have hc : jetSpan r ≤ (innerSL ℂ x).ker :=
      Submodule.topologicalClosure_minimal _ hs (innerSL ℂ x).isClosed_ker
    apply (Submodule.mem_orthogonal _ _).mpr
    intro y hy
    have hxy : ⟪x, y⟫_ℂ = 0 := hc hy
    exact inner_eq_zero_symm.mp hxy

/-- Discharges the functional-analytic span implication needed at manuscript
27198--27211, conditional on the still-unproved actual native annihilator
identity. No uniform conditioning of biorthogonals is asserted. -/
theorem jetSpan_eq_geometric_orthogonal
    (G : Submodule ℂ H) (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G) :
    jetSpan r = Gᗮ := by
  have hclosed : IsClosed (jetSpan r : Set H) :=
    Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace (jetSpan r) := hclosed.completeSpace_coe
  have hv : (jetSpan r)ᗮ = G := by
    ext x
    exact (jetSpan_orthogonal_eq_commonKernel r x).trans (hkernel x)
  rw [← hv, Submodule.orthogonal_orthogonal]

/-- Exact quotient totality, without selecting an arbitrary model quotient.
This is a criterion, not a proof of its arithmetic right-hand side. -/
theorem quotient_totality_iff
    (G : Submodule ℂ H) (δ : ι → H →L[ℂ] ℂ)
    (hvanish : ∀ i, G ≤ (δ i).ker) :
    (∀ q : H ⧸ G,
      (∀ i, G.liftQ (δ i).toLinearMap (hvanish i) q = 0) → q = 0) ↔
    (∀ x : H, (∀ i, δ i x = 0) → x ∈ G) := by
  constructor
  · intro h x hx
    have hz : G.mkQ x = 0 := h (G.mkQ x) (by
      intro i
      exact hx i)
    have hm : x ∈ G.mkQ.ker := hz
    simpa only [Submodule.ker_mkQ] using hm
  · intro h q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      intro hx
      have hm : x ∈ G := h x (by intro i; exact hx i)
      have hz : x ∈ G.mkQ.ker := by simpa only [Submodule.ker_mkQ] using hm
      exact hz

/-- A candidate finite-rank limit has the same genuine projection as A once
all actual continuous jets agree and their common kernel is G. In the target
application A is convolution FIRST; projection is applied SECOND. -/
theorem projected_operator_eq_of_jet_agreement
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (δ : ι → H →L[ℂ] ℂ)
    (hkernel : ∀ x, (∀ i, δ i x = 0) → x ∈ G)
    (A T : H →L[ℂ] H)
    (hjets : ∀ i x, δ i (T x) = δ i (A x)) :
    Gᗮ.starProjection.comp T = Gᗮ.starProjection.comp A := by
  ext x
  have hg : T x - A x ∈ G := hkernel _ (by
    intro i
    rw [map_sub, hjets, sub_self])
  have hp : Gᗮ.starProjection (T x - A x) = 0 := by
    have hp' : Gᗮ.orthogonalProjection (T x - A x) = 0 :=
      Submodule.orthogonalProjection_eq_zero_iff.mpr (by
      simpa only [Submodule.orthogonal_orthogonal] using hg)
    simpa only [Submodule.starProjection_apply, Submodule.coe_zero] using
      congrArg (fun z : Gᗮ => (z : H)) hp'
  simpa only [map_sub, sub_eq_zero, ContinuousLinearMap.comp_apply] using hp

/-- The reconstruction implication used after the manuscript's S1 Cauchy
argument: pointwise convergence and eventual jet agreement suffice. The
convergence and arithmetic common-kernel premise still have to be proved
for the manuscript's actual finite blocks; neither is manufactured here. -/
theorem projected_limit_identification
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (δ : ι → H →L[ℂ] ℂ)
    (hkernel : ∀ x, (∀ i, δ i x = 0) → x ∈ G)
    {κ : Type*} (l : Filter κ) [Filter.NeBot l]
    (A T : H →L[ℂ] H) (blocks : κ → H →L[ℂ] H)
    (hlim : ∀ x, Filter.Tendsto (fun n => blocks n x) l (nhds (T x)))
    (hjets : ∀ i x, ∀ᶠ n in l, δ i (blocks n x) = δ i (A x)) :
    Gᗮ.starProjection.comp T = Gᗮ.starProjection.comp A := by
  apply projected_operator_eq_of_jet_agreement G δ hkernel A T
  intro i x
  have ht := ((δ i).continuous.tendsto (T x)).comp (hlim x)
  have ha : Filter.Tendsto (fun n => δ i (blocks n x)) l (nhds (δ i (A x))) :=
    Filter.Tendsto.congr' (Filter.EventuallyEq.symm (hjets i x)) tendsto_const_nhds
  exact tendsto_nhds_unique ht ha

#check jetSpan_orthogonal_eq_commonKernel
#print axioms jetSpan_orthogonal_eq_commonKernel
#check jetSpan_eq_geometric_orthogonal
#print axioms jetSpan_eq_geometric_orthogonal
#check quotient_totality_iff
#print axioms quotient_totality_iff
#check projected_operator_eq_of_jet_agreement
#print axioms projected_operator_eq_of_jet_agreement
#check projected_limit_identification
#print axioms projected_limit_identification
end Round173F

/-! Round 175: the finite-jet-span cutoff convergence premise of 10.2/10.3.
These are actual orthogonal projections. No nuclear cost is presumed. -/
namespace Round175F
open Filter
open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

noncomputable def window (r : ι → H) (J : Finset ι) : Submodule ℂ H :=
  (Submodule.span ℂ (r '' (J : Set ι))).topologicalClosure

instance window_complete (r : ι → H) (J : Finset ι) : CompleteSpace (window r J) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem window_mono (r : ι → H) {J K : Finset ι} (h : J ⊆ K) :
    window r J ≤ window r K := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  exact Set.image_mono h

theorem generator_mem_window (r : ι → H) {J : Finset ι} {i : ι} (hi : i ∈ J) :
    r i ∈ window r J :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem span_mem_some_window (r : ι → H) {y : H}
    (hy : y ∈ Submodule.span ℂ (Set.range r)) :
    ∃ J : Finset ι, y ∈ window r J := by
  classical
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨{i}, generator_mem_window r (by simp)⟩
  | zero => exact ⟨∅, (window r ∅).zero_mem⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨J, hJ⟩ := ihx
      obtain ⟨K, hK⟩ := ihy
      exact ⟨J ∪ K, (window r (J ∪ K)).add_mem
        (window_mono r Finset.subset_union_left hJ)
        (window_mono r Finset.subset_union_right hK)⟩
  | smul a x hx ih =>
      obtain ⟨J, hJ⟩ := ih
      exact ⟨J, (window r J).smul_mem a hJ⟩

/-- Quantitative approximation used for strong convergence. -/
theorem cutoff_error_le (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (x y : H) (hy : y ∈ U) :
    ‖U.starProjection x - x‖ ≤ 2 * ‖x - y‖ := by
  have hfix : U.starProjection y = y := Submodule.starProjection_eq_self_iff.mpr hy
  calc
    ‖U.starProjection x - x‖ = ‖U.starProjection (x-y) + (y-x)‖ := by
      rw [map_sub, hfix]
      congr 1
      abel
    _ ≤ ‖U.starProjection (x-y)‖ + ‖y-x‖ := norm_add_le _ _
    _ ≤ ‖x-y‖ + ‖y-x‖ := by
      apply add_le_add_left
      exact (U.starProjection.le_opNorm _).trans
        (by simpa using mul_le_mul_of_nonneg_right U.starProjection_norm_le (norm_nonneg (x-y)))
    _ = 2 * ‖x-y‖ := by rw [norm_sub_rev y x]; ring

/-- This proves the strong convergence assumed by the previous fixed-block
cost lemmas, on the closed spectral span, without any basis conditioning. -/
theorem finite_jet_cutoffs_tendsto (r : ι → H) (x : H)
    (hx : x ∈ Round173F.jetSpan r) :
    Tendsto (fun J : Finset ι => (window r J).starProjection x) atTop (𝓝 x) := by
  classical
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨J, hJ⟩ := span_mem_some_window r hy
  refine ⟨J, fun K hK => ?_⟩
  rw [dist_eq_norm]
  apply (cutoff_error_le (window r K) x y (window_mono r hK hJ)).trans_lt
  rw [dist_eq_norm] at hxy
  linarith

/-- Each included native Riesz jet is preserved exactly by the cutoff. -/
theorem finite_jet_cutoff_preserves (r : ι → H) (J : Finset ι)
    (i : ι) (hi : i ∈ J) (x : H) :
    ⟪r i, (window r J).starProjection x⟫_ℂ = ⟪r i, x⟫_ℂ := by
  rw [← (window r J).inner_starProjection_left_eq_right]
  rw [Submodule.starProjection_eq_self_iff.mpr (generator_mem_window r hi)]

/-- Native application criterion: the actual common-kernel theorem, still
an arithmetic obligation, identifies the strong limit with G-perp. -/
theorem finite_jet_cutoffs_tendsto_on_geometric_complement
    (G : Submodule ℂ H) (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (x : H) (hx : x ∈ Gᗮ) :
    Tendsto (fun J : Finset ι => (window r J).starProjection x) atTop (𝓝 x) := by
  apply finite_jet_cutoffs_tendsto r x
  rwa [Round173F.jetSpan_eq_geometric_orthogonal G r hkernel]


/-- The cutoff range is finite dimensional, not only topologically closed. -/
theorem window_finiteDimensional (r : ι → H) (J : Finset ι) :
    FiniteDimensional ℂ (window r J) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (r '' (J : Set ι))) :=
    FiniteDimensional.span_of_finite ℂ (J.finite_toSet.image r)
  have hc : IsClosed (Submodule.span ℂ (r '' (J : Set ι)) : Set H) :=
    (Submodule.span ℂ (r '' (J : Set ι))).closed_of_finiteDimensional
  have he : window r J = Submodule.span ℂ (r '' (J : Set ι)) := by
    apply SetLike.coe_injective
    exact hc.closure_eq
  rw [he]
  infer_instance

/-- The manuscript's fixed finite block is unchanged once all its input
jet representatives occur in the cutoff. No singular-value convergence
inference or biorthogonal norm bound is used. -/
theorem finiteBlock_cutoff_stabilizes (r v : ι → H) (J K : Finset ι)
    (hJK : J ⊆ K) :
    (∑ i ∈ J, (innerSL ℂ (r i)).smulRight (v i)).comp (window r K).starProjection =
      ∑ i ∈ J, (innerSL ℂ (r i)).smulRight (v i) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [finite_jet_cutoff_preserves r K i (hJK hi)]

#check window_finiteDimensional
#print axioms window_finiteDimensional
#check finiteBlock_cutoff_stabilizes
#print axioms finiteBlock_cutoff_stabilizes

#check cutoff_error_le
#print axioms cutoff_error_le
#check finite_jet_cutoffs_tendsto
#print axioms finite_jet_cutoffs_tendsto
#check finite_jet_cutoff_preserves
#print axioms finite_jet_cutoff_preserves
#check finite_jet_cutoffs_tendsto_on_geometric_complement
#print axioms finite_jet_cutoffs_tendsto_on_geometric_complement
end Round175F

/-! Round 176: FULL_SPACE_PROJECTED_APPROXIMATION, the operator-identification
premise at manuscript 27198--27211. The finite windows are the repaired
finite jet spans, not the decreasing kernels printed in (9.3.2.10).
No nuclearity, infinite cost bound, or summability is assumed or concluded.
The actual native common-kernel identity remains an application obligation. -/
namespace Round176F
open Filter
open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

theorem window_le_spectral_span (r : ι → H) (J : Finset ι) :
    Round175F.window r J ≤ Round173F.jetSpan r := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

/-- Each corrected cutoff ignores precisely the geometric component of
its input, provided the actual common-kernel identity has been proved. -/
theorem cutoff_after_genuine_projection
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (J : Finset ι) (x : H) :
    (Round175F.window r J).starProjection (Gᗮ.starProjection x) =
      (Round175F.window r J).starProjection x := by
  have hle : Round175F.window r J ≤ Gᗮ := by
    rw [← Round173F.jetSpan_eq_geometric_orthogonal G r hkernel]
    exact window_le_spectral_span r J
  have hz : (Round175F.window r J).orthogonalProjection
      (x - Gᗮ.starProjection x) = 0 :=
    Submodule.orthogonalProjection_eq_zero_iff.mpr
      ((Submodule.orthogonal_le hle)
        (Submodule.sub_starProjection_mem_orthogonal x))
  have hz' : (Round175F.window r J).starProjection
      (x - Gᗮ.starProjection x) = 0 := by
    simpa only [Submodule.starProjection_apply, Submodule.coe_zero] using
      congrArg (fun y : Round175F.window r J => (y : H)) hz
  exact (sub_eq_zero.mp (by simpa only [map_sub] using hz')).symm

/-- Strong approximation of the required composition, convolution FIRST
and spectral projection SECOND. A is any supplied continuous operator;
its native convolution construction is not silently asserted here. -/
theorem projected_operator_cutoffs_tendsto
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (A : H →L[ℂ] H) (x : H) :
    Tendsto (fun J : Finset ι =>
      ((Round175F.window r J).starProjection.comp A) x) atTop
      (𝓝 ((Gᗮ.starProjection.comp A) x)) := by
  have ht := Round175F.finite_jet_cutoffs_tendsto_on_geometric_complement
    G r hkernel (Gᗮ.starProjection (A x))
    (Gᗮ.starProjection_apply_mem (A x))
  simpa only [cutoff_after_genuine_projection G r hkernel,
    ContinuousLinearMap.comp_apply] using ht

/-- The approximants have an explicitly finite-dimensional containing
range. This is finite rank, not an infinite nuclear-cost estimate. -/
theorem projected_cutoff_range
    (r : ι → H) (J : Finset ι) (A : H →L[ℂ] H) :
    FiniteDimensional ℂ (Round175F.window r J) ∧
      ∀ x, ((Round175F.window r J).starProjection.comp A) x ∈
        Round175F.window r J := by
  exact ⟨Round175F.window_finiteDimensional r J,
    fun x => (Round175F.window r J).starProjection_apply_mem (A x)⟩

/-- Once any candidate block limit agrees with these cutoffs pointwise,
uniqueness identifies it with the actual projected composition. -/
theorem projected_operator_identified_by_cutoffs
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (A T : H →L[ℂ] H)
    (hlim : ∀ x, Tendsto (fun J : Finset ι =>
      ((Round175F.window r J).starProjection.comp A) x) atTop (𝓝 (T x))) :
    T = Gᗮ.starProjection.comp A := by
  ext x
  exact tendsto_nhds_unique (hlim x)
    (projected_operator_cutoffs_tendsto G r hkernel A x)

#check cutoff_after_genuine_projection
#print axioms cutoff_after_genuine_projection
#check projected_operator_cutoffs_tendsto
#print axioms projected_operator_cutoffs_tendsto
#check projected_cutoff_range
#print axioms projected_cutoff_range
#check projected_operator_identified_by_cutoffs
#print axioms projected_operator_identified_by_cutoffs
/-- Finite-window identification needs only the included jets, not the
unproved totality of every native spectral jet. This is the exact range
and interpolation criterion to check for any proposed finite block. -/
theorem finite_window_jet_unique
    (r : ι → H) (J : Finset ι) (x y : H)
    (hx : x ∈ Round175F.window r J) (hy : y ∈ Round175F.window r J)
    (hjets : ∀ i ∈ J, ⟪r i, x⟫_ℂ = ⟪r i, y⟫_ℂ) : x = y := by
  have hs : Submodule.span ℂ (r '' (J : Set ι)) ≤
      (innerSL ℂ (x - y)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change ⟪x - y, r i⟫_ℂ = 0
    apply inner_eq_zero_symm.mp
    rw [inner_sub_right, hjets i hi, sub_self]
  have hc : Round175F.window r J ≤ (innerSL ℂ (x - y)).ker :=
    Submodule.topologicalClosure_minimal _ hs (innerSL ℂ (x - y)).isClosed_ker
  have hz : ⟪x - y, x - y⟫_ℂ = 0 :=
    hc ((Round175F.window r J).sub_mem hx hy)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem finite_window_operator_identification
    (r : ι → H) (J : Finset ι) (A B : H →L[ℂ] H)
    (hrange : ∀ x, B x ∈ Round175F.window r J)
    (hjets : ∀ i ∈ J, ∀ x, ⟪r i, B x⟫_ℂ = ⟪r i, A x⟫_ℂ) :
    B = (Round175F.window r J).starProjection.comp A := by
  ext x
  apply finite_window_jet_unique r J (B x)
    ((Round175F.window r J).starProjection (A x)) (hrange x)
    ((Round175F.window r J).starProjection_apply_mem (A x))
  intro i hi
  rw [Round175F.finite_jet_cutoff_preserves r J i hi, hjets i hi x]

#check finite_window_jet_unique
#print axioms finite_window_jet_unique
#check finite_window_operator_identification
#print axioms finite_window_operator_identification
end Round176F

/-! Round 177: FINITE_SPECTRAL_COMPRESSION_IDENTIFICATION.
The finite triangular jet action in (10.3.1.12) must identify the finite
matrix with the genuine orthogonal compression before its cost can be used.
The native jet action and finite biorthogonals remain application premises;
no infinite nuclear cost, nuclearity, or summability is assumed here. -/
namespace Round177F
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

/-- Finite triangular jet action forces compression on the input too.
This does NOT assert A commutes with the projection. -/
theorem triangular_jet_action_compression
    (r : ι → H) (J : Finset ι) (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J, c i j * ⟪r j, x⟫_ℂ) :
    ((Round175F.window r J).starProjection.comp A).comp
      (Round175F.window r J).starProjection =
      (Round175F.window r J).starProjection.comp A := by
  ext x
  apply Round176F.finite_window_jet_unique r J
    ((Round175F.window r J).starProjection
      (A ((Round175F.window r J).starProjection x)))
    ((Round175F.window r J).starProjection (A x))
    ((Round175F.window r J).starProjection_apply_mem _)
    ((Round175F.window r J).starProjection_apply_mem _)
  intro i hi
  rw [Round175F.finite_jet_cutoff_preserves r J i hi,
    Round175F.finite_jet_cutoff_preserves r J i hi,
    hact i hi, hact i hi]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Round175F.finite_jet_cutoff_preserves r J j hj]

/-- Projecting finite biorthogonal representatives gives the exact output
cutoff, even if the original representatives lie outside the finite window.
Thus no unjustified identification of global biorthogonals with an
orthogonal finite spectral subspace is needed. -/
theorem projected_biorthogonal_reconstruction
    [DecidableEq ι] (r v : ι → H) (J : Finset ι) (A : H →L[ℂ] H)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0) :
    (∑ j ∈ J, ((innerSL ℂ (r j)).comp A).smulRight
      ((Round175F.window r J).starProjection (v j))) =
      (Round175F.window r J).starProjection.comp A := by
  apply Round176F.finite_window_operator_identification r J A
  · intro x
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    apply Submodule.sum_mem
    intro j hj
    exact (Round175F.window r J).smul_mem _
      ((Round175F.window r J).starProjection_apply_mem (v j))
  · intro i hi x
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_sum, inner_smul_right]
    simp_rw [Round175F.finite_jet_cutoff_preserves r J i hi]
    calc
      (∑ j ∈ J, ⟪r j, A x⟫_ℂ * ⟪r i, v j⟫_ℂ) =
          ∑ j ∈ J, ⟪r j, A x⟫_ℂ * (if i = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hdual i hi j hj]
      _ = ⟪r i, A x⟫_ℂ := by simp [hi]

/-- Exact finite rank-one matrix representation of the actual cutoff.
The two finite sums have nuclear cost
sum_i sum_j ||c i j|| ||innerSL(r j)|| ||P_J(v i)||.
No uniform bound or infinite summability of this expression is asserted. -/
theorem spectral_matrix_eq_genuine_cutoff
    [DecidableEq ι] (r v : ι → H) (J : Finset ι)
    (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J, c i j * ⟪r j, x⟫_ℂ) :
    (∑ i ∈ J, ∑ j ∈ J, (c i j • innerSL ℂ (r j)).smulRight
      ((Round175F.window r J).starProjection (v i))) =
      (Round175F.window r J).starProjection.comp A := by
  rw [← projected_biorthogonal_reconstruction r v J A hdual]
  ext x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hact i hi, Finset.sum_smul]

/-- Orthogonal projection of the output representatives cannot increase
this explicit finite nuclear representation cost. Conditioning remains
visible in the norms of the supplied biorthogonal representatives. -/
theorem finite_spectral_cost_le
    (r v : ι → H) (J : Finset ι) (c : ι → ι → ℂ) :
    (∑ i ∈ J, ∑ j ∈ J,
      ‖c i j • innerSL ℂ (r j)‖ *
        ‖(Round175F.window r J).starProjection (v i)‖) ≤
    ∑ i ∈ J, ∑ j ∈ J, ‖c i j‖ * ‖innerSL ℂ (r j)‖ * ‖v i‖ := by
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact ((Round175F.window r J).starProjection.le_opNorm _).trans
    (by simpa using mul_le_mul_of_nonneg_right (Round175F.window r J).starProjection_norm_le (norm_nonneg (v i)))

#check triangular_jet_action_compression
#print axioms triangular_jet_action_compression
#check projected_biorthogonal_reconstruction
#print axioms projected_biorthogonal_reconstruction
#check spectral_matrix_eq_genuine_cutoff
#print axioms spectral_matrix_eq_genuine_cutoff
#check finite_spectral_cost_le
#print axioms finite_spectral_cost_le
/-- Exhausting finite matrices converge to the required projected operator,
conditional on the native common-kernel and triangular-action identities.
This is strong convergence; it is explicitly not S1 convergence. -/
theorem spectral_matrices_tendsto_projected_operator
    [DecidableEq ι] (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r v : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (J : ℕ → Finset ι)
    (hcofinal : Filter.Tendsto J Filter.atTop Filter.atTop)
    (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hdual : ∀ n, ∀ i ∈ J n, ∀ j ∈ J n,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ n, ∀ i ∈ J n, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J n, c i j * ⟪r j, x⟫_ℂ)
    (x : H) :
    Filter.Tendsto (fun n =>
      (∑ i ∈ J n, ∑ j ∈ J n, (c i j • innerSL ℂ (r j)).smulRight
        ((Round175F.window r (J n)).starProjection (v i))) x)
      Filter.atTop (nhds ((Gᗮ.starProjection.comp A) x)) := by
  have he (n : ℕ) := spectral_matrix_eq_genuine_cutoff r v (J n) A c
    (hdual n) (hact n)
  simp_rw [he]
  exact (Round176F.projected_operator_cutoffs_tendsto G r hkernel A x).comp hcofinal

#check spectral_matrices_tendsto_projected_operator
#print axioms spectral_matrices_tendsto_projected_operator
end Round177F

/-!
Round 179 F. Named premise: INTRINSIC_FINITE_SPECTRAL_COST at
(10.3.1.18)--(10.3.1.22). Combine coefficient columns before taking
norms; their projected interpolants are the unique least-norm solutions.
This retains cancellations lost by an entrywise biorthogonal estimate.
No infinite nuclear bound, native attachment, or summability is assumed.
-/
namespace Round179F
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

/-- The actual finite jet data uniquely determine the projected representative.
No bound on the original biorthogonal family is needed. -/
theorem projected_interpolant_eq
    (r : ι → H) (J : Finset ι) (v w : H)
    (hjets : ∀ i ∈ J, ⟪r i, v⟫_ℂ = ⟪r i, w⟫_ℂ) :
    (Round175F.window r J).starProjection v =
      (Round175F.window r J).starProjection w := by
  apply Round176F.finite_window_jet_unique r J
    _ _ ((Round175F.window r J).starProjection_apply_mem _)
    ((Round175F.window r J).starProjection_apply_mem _)
  intro i hi
  simpa only [Round175F.finite_jet_cutoff_preserves r J i hi] using hjets i hi

/-- This is the least-norm interpolation estimate required to make the
finite spectral cost intrinsic to the jet data. It is not a uniform bound. -/
theorem projected_interpolant_minimal_norm
    (r : ι → H) (J : Finset ι) (v w : H)
    (hjets : ∀ i ∈ J, ⟪r i, v⟫_ℂ = ⟪r i, w⟫_ℂ) :
    ‖(Round175F.window r J).starProjection v‖ ≤ ‖w‖ := by
  rw [projected_interpolant_eq r J v w hjets]
  exact ((Round175F.window r J).starProjection.le_opNorm w).trans
    (by simpa using mul_le_mul_of_nonneg_right (Round175F.window r J).starProjection_norm_le (norm_nonneg w))

/-- A smaller finite nuclear certificate groups each full coefficient column
before taking its norm, preserving cancellations between close spectral jets. -/
theorem combined_columns_eq_genuine_cutoff
    [DecidableEq ι] (r v : ι → H) (J : Finset ι)
    (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J, c i j * ⟪r j, x⟫_ℂ) :
    (∑ j ∈ J, (innerSL ℂ (r j)).smulRight
      (∑ i ∈ J, c i j • (Round175F.window r J).starProjection (v i))) =
      (Round175F.window r J).starProjection.comp A := by
  rw [← Round177F.spectral_matrix_eq_genuine_cutoff r v J A c hdual hact]
  ext x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, Finset.smul_sum, smul_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Quantitative finite cost with cancellations retained. The right side is
the previous checked entrywise cost, not an assumed finite infinite sum. -/
theorem combined_column_cost_le
    (r v : ι → H) (J : Finset ι) (c : ι → ι → ℂ) :
    (∑ j ∈ J, ‖innerSL ℂ (r j)‖ *
      ‖∑ i ∈ J, c i j • (Round175F.window r J).starProjection (v i)‖) ≤
    ∑ i ∈ J, ∑ j ∈ J,
      ‖c i j • innerSL ℂ (r j)‖ *
        ‖(Round175F.window r J).starProjection (v i)‖ := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  calc
    _ ≤ ‖innerSL ℂ (r j)‖ *
        ∑ i ∈ J, ‖c i j • (Round175F.window r J).starProjection (v i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_smul]
      ring

#check projected_interpolant_eq
#print axioms projected_interpolant_eq
#check projected_interpolant_minimal_norm
#print axioms projected_interpolant_minimal_norm
#check combined_columns_eq_genuine_cutoff
#print axioms combined_columns_eq_genuine_cutoff
#check combined_column_cost_le
#print axioms combined_column_cost_le
/-- The cancellation-preserving columns are exactly convolution first and
orthogonal projection second, applied to the finite representatives. This
identifies the quantity that needs a native smoothing estimate. -/
theorem combined_column_eq_projected_action
    [DecidableEq ι] (r v : ι → H) (J : Finset ι)
    (A : H →L[ℂ] H) (c : ι → ι → ℂ)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = ∑ j ∈ J, c i j * ⟪r j, x⟫_ℂ)
    (j : ι) (hj : j ∈ J) :
    (∑ i ∈ J, c i j • (Round175F.window r J).starProjection (v i)) =
      (Round175F.window r J).starProjection (A (v j)) := by
  have he := congrArg (fun T : H →L[ℂ] H => T (v j))
    (combined_columns_eq_genuine_cutoff r v J A c hdual hact)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ContinuousLinearMap.comp_apply] at he
  have hs : (∑ k ∈ J, ⟪r k, v j⟫_ℂ •
      (∑ i ∈ J, c i k • (Round175F.window r J).starProjection (v i))) =
      ∑ i ∈ J, c i j • (Round175F.window r J).starProjection (v i) := by
    calc
      _ = ∑ k ∈ J, (if k = j then (1 : ℂ) else 0) •
          (∑ i ∈ J, c i k • (Round175F.window r J).starProjection (v i)) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hdual k hk j hj]
      _ = _ := by simp [hj]
  rw [hs] at he
  exact he

#check combined_column_eq_projected_action
#print axioms combined_column_eq_projected_action
end Round179F

/-!
Round 180 F: CLUSTER_SCALAR_CANCELLATION_COST, the finite nuclear-cost
premise (10.3.1.18)--(10.3.1.22). A common scalar part of a simple-root
cluster costs its orthogonal rank times the scalar modulus. Only the
residual uses interpolants, with the spectral difference multiplied into
the vector BEFORE its norm. This is a finite certificate; no native
conditioning or infinite nuclear bound is assumed or concluded.
-/
namespace Round180F
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι κ : Type*} [Fintype κ]

/-- The scalar cluster part has an orthonormal rank-one representation. -/
theorem orthogonal_projection_rank_one
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (b : OrthonormalBasis κ ℂ U) :
    (∑ k, (innerSL ℂ (b k : H)).smulRight (b k : H)) = U.starProjection := by
  ext x
  have hs := congrArg (fun y : U => (y : H)) (b.sum_repr (U.orthogonalProjection x))
  have hi : ∀ k, ⟪b k, U.orthogonalProjection x⟫_ℂ = ⟪(b k : H), x⟫_ℂ := by
    intro k
    change ⟪(b k : H), U.starProjection x⟫_ℂ = _
    rw [← U.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (b k).property]
  simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, Submodule.coe_sum, Submodule.coe_smul,
    OrthonormalBasis.repr_apply_apply, hi] using hs

/-- Exact genuine projected action with common scalar action separated.
For two roots take gap at the base root zero and at the other root z-w;
d is the Mellin divided difference, controlled by the actual test moment.
No inverse-separation factor appears outside the interpolation vector. -/
theorem cluster_split_genuine_projection
    [DecidableEq ι] (r v : ι → H) (J : Finset ι)
    (b : OrthonormalBasis κ ℂ (Round175F.window r J))
    (A : H →L[ℂ] H) (lam : ℂ) (d gap : ι → ℂ)
    (hdual : ∀ i ∈ J, ∀ j ∈ J,
      ⟪r i, v j⟫_ℂ = if i = j then 1 else 0)
    (hact : ∀ i ∈ J, ∀ x,
      ⟪r i, A x⟫_ℂ = (lam + d i * gap i) * ⟪r i, x⟫_ℂ) :
    (∑ k, (lam • innerSL ℂ (b k : H)).smulRight (b k : H)) +
      (∑ j ∈ J, (d j • innerSL ℂ (r j)).smulRight
        (gap j • (Round175F.window r J).starProjection (v j))) =
      (Round175F.window r J).starProjection.comp A := by
  have hp := orthogonal_projection_rank_one (Round175F.window r J) b
  have hid := Round177F.projected_biorthogonal_reconstruction r v J
    (ContinuousLinearMap.id ℂ H) hdual
  have ha := Round177F.projected_biorthogonal_reconstruction r v J A hdual
  ext x
  have hpx := congrArg (fun T : H →L[ℂ] H => T x) hp
  have hix := congrArg (fun T : H →L[ℂ] H => T x) hid
  have hax := congrArg (fun T : H →L[ℂ] H => T x) ha
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply] at hpx hix hax
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  calc
    _ = lam • (∑ k, ⟪(b k : H), x⟫_ℂ • (b k : H)) +
        ∑ j ∈ J, (d j * gap j * ⟪r j, x⟫_ℂ) •
          (Round175F.window r J).starProjection (v j) := by
      simp only [Finset.smul_sum, smul_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      ring
    _ = lam • (∑ j ∈ J, ⟪r j, x⟫_ℂ •
          (Round175F.window r J).starProjection (v j)) +
        ∑ j ∈ J, (d j * gap j * ⟪r j, x⟫_ℂ) •
          (Round175F.window r J).starProjection (v j) := by rw [hpx, ← hix]
    _ = ∑ j ∈ J, ⟪r j, A x⟫_ℂ •
          (Round175F.window r J).starProjection (v j) := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hact j hj, add_mul, add_smul, smul_smul]
    _ = _ := hax

/-- The finite representation cost retains the regularized interpolants.
It is a real finite sum, not a bound for the infinite native operator. -/
theorem cluster_split_representation_cost
    (r v : ι → H) (J : Finset ι)
    (b : OrthonormalBasis κ ℂ (Round175F.window r J))
    (lam : ℂ) (d gap : ι → ℂ) :
    (∑ k, ‖lam • innerSL ℂ (b k : H)‖ * ‖(b k : H)‖) +
      (∑ j ∈ J, ‖d j • innerSL ℂ (r j)‖ *
        ‖gap j • (Round175F.window r J).starProjection (v j)‖) =
    (Fintype.card κ : ℝ) * ‖lam‖ +
      ∑ j ∈ J, ‖d j‖ * ‖innerSL ℂ (r j)‖ *
        ‖gap j • (Round175F.window r J).starProjection (v j)‖ := by
  have hb : ∀ k, ‖(b k : H)‖ = 1 := fun k => b.orthonormal.norm_eq_one k
  simp [norm_smul, hb]

#check orthogonal_projection_rank_one
#print axioms orthogonal_projection_rank_one
#check cluster_split_genuine_projection
#print axioms cluster_split_genuine_projection
#check cluster_split_representation_cost
#print axioms cluster_split_representation_cost
end Round180F
