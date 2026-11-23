import Mathlib

/-!
Round 173 A. Structural premise of manuscript (10.4.2.5).
The closed geometric image must still be attached to the native number-field
space. No nuclearity or summability assumption is introduced here.
-/
noncomputable section
set_option linter.unusedSectionVars false
namespace Round173A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The genuine normed quotient map, not an arbitrary surrogate. -/
def Q : H →L[ℂ] H ⧸ G :=
  G.mkQ.mkContinuous 1 (by intro x; simpa using Submodule.Quotient.norm_mk_le G x)

/-- Orthogonal representative, included in the ambient space. -/
def Slinear : (H ⧸ G) →ₗ[ℂ] H :=
  G.liftQ Gᗮ.starProjection.toLinearMap (by
    intro x hx
    change Gᗮ.starProjection x = 0
    simpa only [Submodule.starProjection_apply_eq_zero_iff,
      Submodule.orthogonal_orthogonal] using hx)

@[simp] theorem Slinear_mk (x : H) :
    Slinear G (G.mkQ x) = Gᗮ.starProjection x := rfl

/-- The quotient infimum, not the open mapping theorem, gives this bound. -/
theorem Slinear_contract (x : H ⧸ G) : ‖Slinear G x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt x hε
  have hp := Submodule.norm_starProjection_apply_le Gᗮ y
  change ‖Slinear G (Submodule.Quotient.mk y)‖ ≤ ‖y‖ at hp
  rw [hy] at hp
  exact hp.trans (le_of_lt hnorm)

def S : (H ⧸ G) →L[ℂ] H :=
  (Slinear G).mkContinuous 1 (by intro x; simpa using Slinear_contract G x)

@[simp] theorem S_Q (x : H) : S G (Q G x) = Gᗮ.starProjection x := rfl

/-- Construct the induced quotient action from invariance, without assuming
an operator identity or any nuclear estimate. -/
def AbarLinear (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) :
    (H ⧸ G) →ₗ[ℂ] H ⧸ G :=
  G.mapQ G A.toLinearMap hA

@[simp] theorem AbarLinear_Q (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    AbarLinear G A hA (Q G x) = Q G (A x) := rfl

/-- Exact algebraic factorisation with the quotient and genuine projector. -/
theorem quotient_projected_factorisation (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Gᗮ.starProjection (A x) = S G (AbarLinear G A hA (Q G x)) := rfl

theorem Q_S (x : H ⧸ G) : Q G (S G x) = x := by
  refine Submodule.Quotient.induction_on G x ?_
  intro y
  have hm : y - Gᗮ.starProjection y ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal y
  have hz : G.mkQ (y - Gᗮ.starProjection y) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).2 hm
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem S_isometry (x : H ⧸ G) : ‖S G x‖ = ‖x‖ := by
  apply le_antisymm (Slinear_contract G x)
  have hn := Submodule.Quotient.norm_mk_le G (S G x)
  change ‖Q G (S G x)‖ ≤ ‖S G x‖ at hn
  simpa only [Q_S] using hn

def Abar (A : H →L[ℂ] H) : (H ⧸ G) →L[ℂ] H ⧸ G :=
  (Q G).comp (A.comp (S G))

theorem Abar_Q (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Abar G A (Q G x) = Q G (A x) := by
  have hm : x - Gᗮ.starProjection x ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal x
  have hz : G.mkQ (A (x - Gᗮ.starProjection x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).2 (hA _ hm)
  rw [map_sub, map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The bounded-composition factorisation in (10.4.2.5), with its actual
quotient maps and map costs established. Native H/G/A attachment remains. -/
theorem bounded_quotient_factorisation (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    Gᗮ.starProjection.comp A = (S G).comp ((Abar G A).comp (Q G)) ∧
    ‖Q G‖ ≤ 1 ∧ ‖S G‖ ≤ 1 ∧ (∀ x : H ⧸ G, ‖S G x‖ = ‖x‖) := by
  refine ⟨?_, ?_, ?_, S_isometry G⟩
  · ext x
    change Gᗮ.starProjection (A x) = S G (Abar G A (Q G x))
    rw [Abar_Q G A hA, S_Q]
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem S_mem (x : H ⧸ G) : S G x ∈ Gᗮ := by
  refine Submodule.Quotient.induction_on G x ?_
  intro y
  exact Gᗮ.starProjection_apply_mem y

theorem range_S : LinearMap.range (S G).toLinearMap = Gᗮ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact S_mem G x
  · intro hy
    refine ⟨Q G y, ?_⟩
    change S G (Q G y) = y
    rw [S_Q, Submodule.starProjection_eq_self_iff]
    exact hy

/-- The bounded representative formula is the induced quotient operator,
not just some operator on a space isomorphic to the quotient. -/
theorem Abar_eq_induced (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    (Abar G A).toLinearMap = AbarLinear G A hA := by
  ext x
  change Abar G A (Q G x) = AbarLinear G A hA (Q G x)
  rw [Abar_Q G A hA, AbarLinear_Q]

theorem manuscript_quotient_structure (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    Gᗮ.starProjection.comp A = (S G).comp ((Abar G A).comp (Q G)) ∧
    (Abar G A).toLinearMap = AbarLinear G A hA ∧
    LinearMap.range (S G).toLinearMap = Gᗮ ∧
    (∀ x : H ⧸ G, Q G (S G x) = x) ∧
    ‖Q G‖ ≤ 1 ∧ ‖S G‖ ≤ 1 ∧ (∀ x : H ⧸ G, ‖S G x‖ = ‖x‖) := by
  obtain ⟨hf, hq, hs, hi⟩ := bounded_quotient_factorisation G A hA
  exact ⟨hf, Abar_eq_induced G A hA, range_S G, Q_S G, hq, hs, hi⟩

end Round173A
#check Round173A.manuscript_quotient_structure
#print axioms Round173A.manuscript_quotient_structure
#check Round173A.bounded_quotient_factorisation
#print axioms Round173A.bounded_quotient_factorisation
#check Round173A.quotient_projected_factorisation
#print axioms Round173A.quotient_projected_factorisation
#check Round173A.Slinear_contract
#print axioms Round173A.Slinear_contract

/-!
Round 176 E: finite orthogonal spectral cutoffs of the actual projected
operator. This discharges the finite-rank nuclear-cost step at manuscript
(10.3.1.18)--(10.3.1.22) without an unjustified biorthogonal bound.
It does not prove a summable cost for the increasing cutoff sequence.
-/
namespace Round176E
open scoped InnerProductSpace Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Explicit finite rank-one certificate; no infinite finiteness is assumed. -/
def FiniteNuclearCost (T : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∃ (d : ℕ) (f : Fin d → H →L[ℂ] ℂ) (u : Fin d → H),
    T = ∑ i, (f i).smulRight (u i) ∧ ∑ i, ‖f i‖ * ‖u i‖ ≤ c

variable (U : Submodule ℂ H) [U.HasOrthogonalProjection]
variable {d : ℕ} (b : OrthonormalBasis (Fin d) ℂ U)

def cutoffFunctional (i : Fin d) : H →L[ℂ] ℂ :=
  (innerSL ℂ (b i)).comp U.orthogonalProjection

theorem cutoffFunctional_norm_le (i : Fin d) :
    ‖cutoffFunctional U b i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖inner ℂ (b i) (U.orthogonalProjection x)‖ ≤ 1 * ‖x‖
  calc
    _ ≤ ‖b i‖ * ‖U.orthogonalProjection x‖ := norm_inner_le_norm _ _
    _ = ‖U.starProjection x‖ := by rw [b.norm_eq_one, one_mul]; rfl
    _ ≤ 1 * ‖x‖ := by simpa using Submodule.norm_starProjection_apply_le U x

/-- Exact representation of convolution followed by projection, with an
additional finite orthogonal input cutoff. The output map L is kept literal. -/
theorem orthogonal_cutoff_representation (L : H →L[ℂ] H) :
    L.comp U.starProjection =
      ∑ i, (cutoffFunctional U b i).smulRight (L (b i : H)) := by
  ext x
  have hb := congrArg (fun u : U => L (u : H))
    (b.sum_repr (U.orthogonalProjection x))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smulRight_apply, cutoffFunctional, innerSL_apply_apply,
    OrthonormalBasis.repr_apply_apply, Submodule.coe_sum, Submodule.coe_smul,
    map_sum, map_smul, Submodule.starProjection_apply] using hb.symm

/-- The finite cost retains the actual image norms, rather than a conditioning
constant inferred from normalization of a nonorthogonal spectral system. -/
theorem orthogonal_cutoff_cost (L : H →L[ℂ] H) :
    FiniteNuclearCost (L.comp U.starProjection) (∑ i, ‖L (b i : H)‖) ∧
    (∑ i, ‖L (b i : H)‖) ≤ (d : ℝ) * ‖L‖ := by
  constructor
  · refine ⟨d, cutoffFunctional U b, fun i => L (b i : H),
      orthogonal_cutoff_representation U b L, ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simpa using mul_le_mul_of_nonneg_right
      (cutoffFunctional_norm_le U b i) (norm_nonneg (L (b i : H)))
  · calc
      _ ≤ ∑ _i : Fin d, ‖L‖ := by
        apply Finset.sum_le_sum
        intro i _
        have hi : ‖(b i : H)‖ = 1 := b.norm_eq_one i
        simpa only [hi, mul_one] using L.le_opNorm (b i : H)
      _ = (d : ℝ) * ‖L‖ := by simp

variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- A finite cutoff of the genuine leading projected operator, in its native
ambient norm. U is its lifted finite spectral space; no surrogate projector. -/
theorem leading_projected_cutoff_finite_cost (A : H →L[ℂ] H) :
    FiniteNuclearCost ((Gᗮ.starProjection.comp A).comp U.starProjection)
      (∑ i, ‖Gᗮ.starProjection (A (b i : H))‖) ∧
    (∑ i, ‖Gᗮ.starProjection (A (b i : H))‖) ≤
      (d : ℝ) * ‖Gᗮ.starProjection.comp A‖ :=
  orthogonal_cutoff_cost U b (Gᗮ.starProjection.comp A)

end Round176E
#check Round176E.leading_projected_cutoff_finite_cost
#print axioms Round176E.leading_projected_cutoff_finite_cost
#check Round176E.orthogonal_cutoff_representation
#print axioms Round176E.orthogonal_cutoff_representation

/-!
Round 177 E. INPUT_CUTOFF_LIMIT_IDENTIFICATION: the finite nuclear
certificates of Round176E concern P A P_U, so their limits must be P A.
This repairs the earlier failed input-cutoff proof, and keeps the native
spectral-totality attachment explicit. No infinite nuclear cost is assumed.
-/
namespace Round177E
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

theorem projected_right_compression (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Gᗮ.starProjection (A (Gᗮ.starProjection x)) = Gᗮ.starProjection (A x) := by
  have hm : x - Gᗮ.starProjection x ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal x
  have hz : Gᗮ.starProjection (A (x - Gᗮ.starProjection x)) = 0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff _).2
    simpa only [Submodule.orthogonal_orthogonal] using hA _ hm
  rw [map_sub, map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- Quantitative identification error for the very cutoffs whose finite
nuclear cost was constructed above, in convolution-before-projection order. -/
theorem input_cutoff_error (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (U : H →L[ℂ] H) (x : H) :
    ‖Gᗮ.starProjection (A (U x)) - Gᗮ.starProjection (A x)‖ ≤
      ‖Gᗮ.starProjection.comp A‖ * ‖U x - Gᗮ.starProjection x‖ := by
  have he : Gᗮ.starProjection (A (U x)) - Gᗮ.starProjection (A x) =
      (Gᗮ.starProjection.comp A) (U x - Gᗮ.starProjection x) := by
    simp only [ContinuousLinearMap.comp_apply, map_sub,
      projected_right_compression G A hA]
  rw [he]
  exact (Gᗮ.starProjection.comp A).le_opNorm _

/-- Strong spectral cutoff convergence and geometric invariance imply
identification with the full projected operator on every ambient input. -/
theorem leading_projected_input_cutoff_limit {J : Type*} (l : Filter J)
    (U : J → H →L[ℂ] H)
    (hstrong : ∀ x : H, Tendsto (fun j => U j x) l (nhds (Gᗮ.starProjection x)))
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Tendsto (fun j => Gᗮ.starProjection (A (U j x))) l
      (nhds (Gᗮ.starProjection (A x))) := by
  have ht := (Gᗮ.starProjection.continuous.tendsto
    (A (Gᗮ.starProjection x))).comp
      ((A.continuous.tendsto (Gᗮ.starProjection x)).comp (hstrong x))
  rw [projected_right_compression G A hA x] at ht
  exact ht

end Round177E
#check Round177E.projected_right_compression
#print axioms Round177E.projected_right_compression
#check Round177E.input_cutoff_error
#print axioms Round177E.input_cutoff_error
#check Round177E.leading_projected_input_cutoff_limit
#print axioms Round177E.leading_projected_input_cutoff_limit


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


namespace Round177E
open Filter
open scoped Topology InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {ι : Type*}

/-- Connect the finite nuclear certificates to the corrected spectral
windows and identify their full-space limit. The arithmetic common-kernel
identity remains explicit; no bound uniform in the window is presumed. -/
theorem finite_spectral_input_approximation
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (r : ι → H)
    (hkernel : ∀ x, (∀ i, ⟪r i, x⟫_ℂ = 0) ↔ x ∈ G)
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) :
    (∀ J : Finset ι, ∃ c : ℝ, 0 ≤ c ∧
      Round176E.FiniteNuclearCost
        ((Gᗮ.starProjection.comp A).comp (Round175F.window r J).starProjection) c ∧
      c ≤ (Module.finrank ℂ (Round175F.window r J) : ℝ) *
        ‖Gᗮ.starProjection.comp A‖) ∧
    (∀ x : H, Tendsto (fun J : Finset ι =>
      Gᗮ.starProjection (A ((Round175F.window r J).starProjection x)))
      atTop (𝓝 (Gᗮ.starProjection (A x)))) := by
  classical
  constructor
  · intro J
    letI := Round175F.window_finiteDimensional r J
    let b := stdOrthonormalBasis ℂ (Round175F.window r J)
    obtain ⟨hc, hb⟩ := Round176E.leading_projected_cutoff_finite_cost
      (Round175F.window r J) b G A
    exact ⟨_, Finset.sum_nonneg (fun i _ => norm_nonneg _), hc, hb⟩
  · intro x
    apply leading_projected_input_cutoff_limit G atTop
      (fun J : Finset ι => (Round175F.window r J).starProjection) _ A hA x
    intro y
    have ht := Round176F.projected_operator_cutoffs_tendsto
      G r hkernel (ContinuousLinearMap.id ℂ H) y
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using ht

end Round177E
#check Round177E.finite_spectral_input_approximation
#print axioms Round177E.finite_spectral_input_approximation
