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
Round 175 H: the nuclear-series transport step of manuscript (10.4.2.5).
The genuine quotient and orthogonal section above are reused without credit
for reproving their structure. Costs below are extended real and may be infinite.
No spectral summability or quotient nuclearity is assumed or concluded.
-/
namespace Round175H
open Round173A
open scoped ENNReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- Pullback by the canonical quotient preserves the actual functional norm. -/
theorem quotient_functional_norm (f : (H ⧸ G) →L[ℂ] ℂ) :
    ‖f.comp (Q G)‖ = ‖f‖ := by
  apply le_antisymm
  · calc
      _ ≤ ‖f‖ * ‖Q G‖ := f.opNorm_comp_le (Q G)
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) (norm_nonneg f)
      _ = _ := mul_one _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    calc
      ‖f q‖ = ‖(f.comp (Q G)) (S G q)‖ := by
        rw [ContinuousLinearMap.comp_apply, Q_S]
      _ ≤ ‖f.comp (Q G)‖ * ‖S G q‖ := (f.comp (Q G)).le_opNorm _
      _ = ‖f.comp (Q G)‖ * ‖q‖ := by rw [S_isometry]

/-- An extended representation cost; infinity is explicitly allowed. -/
def seriesCost {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℕ → E →L[ℂ] ℂ) (v : ℕ → E) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (‖f n‖ * ‖v n‖)

/-- No loss of rank-one nuclear cost through the actual quotient/section.
This does not assert that the common cost is finite. -/
theorem canonical_quotient_series_cost (f : ℕ → (H ⧸ G) →L[ℂ] ℂ)
    (v : ℕ → H ⧸ G) :
    seriesCost (fun n => (f n).comp (Q G)) (fun n => S G (v n)) =
      seriesCost f v := by
  unfold seriesCost
  apply tsum_congr
  intro n
  rw [quotient_functional_norm, S_isometry]

/-- Pointwise reconstruction in convolution-first order. The expansion
hypothesis supplies an operator identity but no finite nuclear cost. -/
theorem canonical_quotient_projected_series
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G)
    (f : ℕ → (H ⧸ G) →L[ℂ] ℂ) (v : ℕ → H ⧸ G)
    (hrep : ∀ q, HasSum (fun n => f n q • v n) (Abar G A q)) (x : H) :
    HasSum (fun n => ((f n).comp (Q G)) x • S G (v n))
      (Gᗮ.starProjection (A x)) := by
  have hh := (S G).hasSum (hrep (Q G x))
  simpa only [map_smul, Abar_Q G A hA, S_Q, ContinuousLinearMap.comp_apply] using hh

/-- Infimum of explicit countable nuclear representation costs. This extended
quantity is allowed to be infinite; no library trace-norm identification is
asserted here. A finite value must still be derived for the actual operator. -/
def nuclearRepresentationCost {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ⨅ (f : ℕ → E →L[ℂ] ℂ) (v : ℕ → E)
    (_ : ∀ x, HasSum (fun n => f n x • v n) (T x)), seriesCost f v

/-- The abstract bounded-composition cost premise of (10.4.2.5), without
assuming nuclearity, finiteness or any summability of the quotient operator.
The actual native attachment and finite right hand side remain unproved. -/
theorem canonical_projected_nuclear_cost_le
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) :
    nuclearRepresentationCost (Gᗮ.starProjection.comp A) ≤
      nuclearRepresentationCost (Abar G A) := by
  unfold nuclearRepresentationCost
  refine le_iInf fun f => le_iInf fun v => le_iInf fun hrep => ?_
  refine iInf_le_of_le (fun n => (f n).comp (Q G)) ?_
  refine iInf_le_of_le (fun n => S G (v n)) ?_
  refine iInf_le_of_le (canonical_quotient_projected_series G A hA f v hrep) ?_
  exact le_of_eq (canonical_quotient_series_cost G f v)

end Round175H
#check Round175H.quotient_functional_norm
#print axioms Round175H.quotient_functional_norm
#check Round175H.canonical_quotient_series_cost
#print axioms Round175H.canonical_quotient_series_cost

#check Round175H.canonical_quotient_projected_series
#print axioms Round175H.canonical_quotient_projected_series

#check Round175H.canonical_projected_nuclear_cost_le
#print axioms Round175H.canonical_projected_nuclear_cost_le
