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
Round 174 A review implication: the rank-one ideal-property step in
manuscript (10.4.2.5), attached to the actual normed quotient and its
constructed orthogonal representative. The source above is retained from
A173. No native arithmetic identification or finite spectral cost is assumed
or concluded. Infinite costs below remain in ENNReal and may equal infinity.
-/
open scoped ENNReal
namespace Round174A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The exact quotient representative transfers each actual rank-one term. -/
theorem quotient_rankOne_identity
    (f : (H ⧸ G) →L[ℂ] ℂ) (v : H ⧸ G) :
    (Round173A.S G).comp ((f.smulRight v).comp (Round173A.Q G)) =
      (f.comp (Round173A.Q G)).smulRight (Round173A.S G v) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    map_smul]

/-- No separately assumed bounds on Q or S: their native quotient norms
were derived in the retained source. -/
theorem quotient_rankOne_cost_le
    (f : (H ⧸ G) →L[ℂ] ℂ) (v : H ⧸ G) :
    ‖f.comp (Round173A.Q G)‖ * ‖Round173A.S G v‖ ≤ ‖f‖ * ‖v‖ := by
  have hQ : ‖Round173A.Q G‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hf : ‖f.comp (Round173A.Q G)‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖f‖ * ‖Round173A.Q G‖ := f.opNorm_comp_le _
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hQ (ContinuousLinearMap.opNorm_nonneg f)
      _ = _ := mul_one _
  rw [Round173A.S_isometry]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg v)

/-- The absolute expansion cost cannot increase under S(-)Q. This theorem
does not assert that either extended-real sum is finite. -/
theorem quotient_expansion_cost_le {ι : Type*}
    (f : ι → (H ⧸ G) →L[ℂ] ℂ) (v : ι → H ⧸ G) :
    (∑' i, ENNReal.ofReal
      (‖(f i).comp (Round173A.Q G)‖ * ‖Round173A.S G (v i)‖)) ≤
      ∑' i, ENNReal.ofReal (‖f i‖ * ‖v i‖) := by
  apply ENNReal.tsum_le_tsum
  intro i
  exact ENNReal.ofReal_le_ofReal (quotient_rankOne_cost_le G (f i) (v i))

/-- Conditional reconstruction only: if a quotient expansion has been
derived, it represents convolution FIRST and genuine projection SECOND.
No nuclear summability or finiteness hypothesis occurs. -/
theorem projected_quotient_series_transfer {ι : Type*}
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G)
    (f : ι → (H ⧸ G) →L[ℂ] ℂ) (v : ι → H ⧸ G)
    (hrep : ∀ q, HasSum (fun i => f i q • v i) (Round173A.Abar G A q)) :
    (∀ x, HasSum
      (fun i => ((f i).comp (Round173A.Q G)) x • Round173A.S G (v i))
      (Gᗮ.starProjection (A x))) ∧
    (∑' i, ENNReal.ofReal
      (‖(f i).comp (Round173A.Q G)‖ * ‖Round173A.S G (v i)‖)) ≤
      ∑' i, ENNReal.ofReal (‖f i‖ * ‖v i‖) := by
  refine ⟨?_, quotient_expansion_cost_le G f v⟩
  intro x
  have ht := (Round173A.S G).hasSum (hrep (Round173A.Q G x))
  simpa only [map_smul, ContinuousLinearMap.comp_apply,
    Round173A.Abar_Q G A hA, Round173A.S_Q] using ht

end Round174A
#check Round174A.quotient_rankOne_identity
#print axioms Round174A.quotient_rankOne_identity
#check Round174A.quotient_rankOne_cost_le
#print axioms Round174A.quotient_rankOne_cost_le
#check Round174A.quotient_expansion_cost_le
#print axioms Round174A.quotient_expansion_cost_le
#check Round174A.projected_quotient_series_transfer
#print axioms Round174A.projected_quotient_series_transfer
