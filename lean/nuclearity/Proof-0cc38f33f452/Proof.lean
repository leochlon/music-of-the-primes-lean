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
Round 175 E: the finite nuclear cost in (10.3.1.18), retaining every
biorthogonal norm. This is the finite-block estimate needed before any
infinite spectral summation, lifted through the genuine quotient maps.
No uniform conditioning, infinite summability or nuclearity is assumed.
-/
set_option maxHeartbeats 1200000
namespace Round175E
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def FiniteNuclearCost (T : H →L[ℂ] H) (c : ℝ) : Prop :=
  ∃ (d : ℕ) (f : Fin d → H →L[ℂ] ℂ) (u : Fin d → H),
    T = ∑ i, (f i).smulRight (u i) ∧ ∑ i, ‖f i‖ * ‖u i‖ ≤ c

variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

def jetBlock {d : ℕ} (c : Fin d → Fin d → ℂ)
    (δ : Fin d → (H ⧸ G) →L[ℂ] ℂ) (ψ : Fin d → H ⧸ G) :
    (H ⧸ G) →L[ℂ] H ⧸ G :=
  ∑ m, (∑ i, c m i • δ i).smulRight (ψ m)

/-- This contains the actual coordinate norms; normalization does not remove them. -/
def jetCost {d : ℕ} (c : Fin d → Fin d → ℂ)
    (δ : Fin d → (H ⧸ G) →L[ℂ] ℂ) (ψ : Fin d → H ⧸ G) : ℝ :=
  ∑ m, (∑ i, ‖c m i‖ * ‖δ i‖) * ‖ψ m‖

theorem jet_functional_norm_le {d : ℕ} (c : Fin d → ℂ)
    (δ : Fin d → (H ⧸ G) →L[ℂ] ℂ) :
    ‖∑ i, c i • δ i‖ ≤ ∑ i, ‖c i‖ * ‖δ i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg (c i)) (norm_nonneg (δ i))))
  intro x
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  calc
    ‖∑ i, c i * δ i x‖ ≤ ∑ i, ‖c i * δ i x‖ := norm_sum_le _ _
    _ ≤ ∑ i, (‖c i‖ * ‖δ i‖) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((δ i).le_opNorm x) (norm_nonneg (c i))
    _ = (∑ i, ‖c i‖ * ‖δ i‖) * ‖x‖ := (Finset.sum_mul _ _ _).symm

/-- Finite spectral blocks lifted by the literal Q and orthogonal representative
S have a derived finite nuclear representation, at the unsuppressed jet cost. -/
theorem projected_jetBlock_finite_nuclear_cost {d : ℕ}
    (c : Fin d → Fin d → ℂ)
    (δ : Fin d → (H ⧸ G) →L[ℂ] ℂ) (ψ : Fin d → H ⧸ G) :
    FiniteNuclearCost
      ((Round173A.S G).comp ((jetBlock G c δ ψ).comp (Round173A.Q G)))
      (jetCost G c δ ψ) ∧ 0 ≤ jetCost G c δ ψ := by
  have hQ : ‖Round173A.Q G‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  constructor
  · refine ⟨d, fun m => (∑ i, c m i • δ i).comp (Round173A.Q G),
      fun m => Round173A.S G (ψ m), ?_, ?_⟩
    · ext x
      simp [jetBlock, map_sum]
    · apply Finset.sum_le_sum
      intro m _
      rw [Round173A.S_isometry]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc
        ‖(∑ i, c m i • δ i).comp (Round173A.Q G)‖ ≤
            ‖∑ i, c m i • δ i‖ * ‖Round173A.Q G‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖∑ i, c m i • δ i‖ := by
          simpa using mul_le_mul_of_nonneg_left hQ (norm_nonneg (∑ i, c m i • δ i))
        _ ≤ ∑ i, ‖c m i‖ * ‖δ i‖ := jet_functional_norm_le G _ _
  · exact Finset.sum_nonneg (fun m _ => mul_nonneg
      (Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg (c m i)) (norm_nonneg (δ i))))
      (norm_nonneg (ψ m)))

#check projected_jetBlock_finite_nuclear_cost
#print axioms projected_jetBlock_finite_nuclear_cost
#check jet_functional_norm_le
#print axioms jet_functional_norm_le
end Round175E
