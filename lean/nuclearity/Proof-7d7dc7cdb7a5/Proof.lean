import Mathlib

/- Round 84 C. Arithmetic compactness of the actual norm-one idele-class
quotient, integrated into the actual logarithm Haar pushforward premise.
Reuses exact C83 compact cover and selected A76 arithmetic/logarithm proofs.
The full actual global operator / genuine Hecke-zero trace equality remains open. -/
open scoped NumberField
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
noncomputable instance classCommGroup : CommGroup (HeckeIdeleClasses K) := inferInstance
end MasulloGRH

/-! Round 79 C: the actual principal-unit action in the archimedean coordinates
needed for the compact norm-one representative construction. -/
namespace MasulloGRH
open NumberField
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineArchLog (a : HeckeIdeles K) (w : InfinitePlace K) : ℝ :=
  (w.mult : ℝ) * Real.log ‖a.val.1 w‖
noncomputable def genuineUnitIdele (u : (𝓞 K)ˣ) : HeckeIdeles K :=
  principalIdele K (Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
theorem genuineArchLog_unit (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    genuineArchLog K (genuineUnitIdele K u) w =
      (w.mult : ℝ) * Real.log (w (algebraMap (𝓞 K) K (u : 𝓞 K))) := by
  unfold genuineArchLog
  congr 2
  exact InfinitePlace.Completion.norm_coe w
    ((WithAbs.equiv _).symm (algebraMap (𝓞 K) K (u : 𝓞 K)))
theorem genuineArchLog_unit_sum (u : (𝓞 K)ˣ) :
    ∑ w, genuineArchLog K (genuineUnitIdele K u) w = 0 := by
  simp_rw [genuineArchLog_unit]
  exact Units.sum_mult_mul_log u
theorem genuineArchLog_unit_restrict (u : (𝓞 K)ˣ)
    (w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀}) :
    genuineArchLog K (genuineUnitIdele K u) w =
      Units.logEmbedding K (Additive.ofMul u) w := by
  rw [genuineArchLog_unit, Units.dirichletUnitTheorem.logEmbedding_component]
theorem genuineArchLog_mul (a b : HeckeIdeles K) (w : InfinitePlace K) :
    genuineArchLog K (a * b) w = genuineArchLog K a w + genuineArchLog K b w := by
  have hn (c : HeckeIdeles K) : ‖c.val.1 w‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    have h : c.val.1 w * (c⁻¹).val.1 w = 1 :=
      congrArg (fun x : HeckeAdeles K => x.1 w) c.val_inv
    exact left_ne_zero_of_mul_eq_one h
  change (w.mult : ℝ) * Real.log ‖a.val.1 w * b.val.1 w‖ = _
  rw [norm_mul, Real.log_mul (hn a) (hn b)]
  exact mul_add _ _ _
/-- This uses actual principal ideles; their finite and angular components
remain present. No periodicity of a positive radial section is presumed. -/
theorem genuineArchLog_principal_unit_translate (a : HeckeIdeles K)
    (u : (𝓞 K)ˣ)
    (w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀}) :
    genuineArchLog K (a * genuineUnitIdele K u) w =
      genuineArchLog K a w + Units.logEmbedding K (Additive.ofMul u) w := by
  rw [genuineArchLog_mul, genuineArchLog_unit_restrict]
end MasulloGRH

namespace MasulloGRH
open NumberField
variable (K : Type*) [Field K] [NumberField K]
/-- Reconstruction of the omitted coordinate with the genuine place weights. -/
noncomputable def genuineRestoreUnitLog
    (v : Units.dirichletUnitTheorem.logSpace K) (w : InfinitePlace K) : ℝ := by
  classical
  exact if h : w = Units.dirichletUnitTheorem.w₀ then - ∑ j, v j else v ⟨w, h⟩

theorem genuineRestoreUnitLog_eq_actual (u : (𝓞 K)ˣ) :
    genuineRestoreUnitLog K (Units.logEmbedding K (Additive.ofMul u)) =
      genuineArchLog K (genuineUnitIdele K u) := by
  classical
  funext w
  unfold genuineRestoreUnitLog
  split_ifs with h
  · subst w
    rw [Units.dirichletUnitTheorem.sum_logEmbedding_component, genuineArchLog_unit]
    ring
  · exact (genuineArchLog_unit_restrict K u ⟨w,h⟩).symm

/-- Principal-unit reduction keeps the actual idele class. -/
theorem genuineUnitIdele_class (u : (𝓞 K)ˣ) :
    (QuotientGroup.mk (genuineUnitIdele K u) : HeckeIdeleClasses K) = 1 := by
  change genuineUnitIdele K u ∈ (QuotientGroup.mk' (principalIdeles K)).ker
  rw [QuotientGroup.ker_mk']
  exact ⟨Units.map (algebraMap (𝓞 K) K).toMonoidHom u, rfl⟩

theorem genuineArchLog_unit_reduction (a : HeckeIdeles K) (u : (𝓞 K)ˣ) :
    (QuotientGroup.mk (a * genuineUnitIdele K u) : HeckeIdeleClasses K) =
      QuotientGroup.mk a ∧
    (fun w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀} =>
      genuineArchLog K (a * genuineUnitIdele K u) w) =
      (fun w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀} =>
        genuineArchLog K a w + Units.logEmbedding K (Additive.ofMul u) w) := by
  constructor
  · change (QuotientGroup.mk a : HeckeIdeleClasses K) *
      QuotientGroup.mk (genuineUnitIdele K u) = QuotientGroup.mk a
    rw [genuineUnitIdele_class, mul_one]
  · funext w
    exact genuineArchLog_principal_unit_translate K a u w

end MasulloGRH

namespace MasulloGRH
open NumberField
variable (K : Type*) [Field K] [NumberField K]
/-- A compact set of reduced archimedean logarithms meets every genuine idele
class after multiplication by an actual integral principal unit. This is the
Dirichlet-lattice part of the norm-one compact-cover construction. -/
theorem genuineArchLog_compact_unit_representatives :
    ∃ S : Set (Units.dirichletUnitTheorem.logSpace K), IsCompact S ∧
      ∀ a : HeckeIdeles K, ∃ u : (𝓞 K)ˣ,
        (QuotientGroup.mk (a * genuineUnitIdele K u) : HeckeIdeleClasses K) =
          QuotientGroup.mk a ∧
        (fun w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀} =>
          genuineArchLog K (a * genuineUnitIdele K u) w) ∈ S := by
  classical
  let L := Units.unitLattice K
  let b := (IsZLattice.basis L).ofZLatticeBasis ℝ L
  have hs : Submodule.span ℤ (Set.range b) = L :=
    Module.Basis.ofZLatticeBasis_span ℝ L (IsZLattice.basis L)
  refine ⟨closure (ZSpan.fundamentalDomain b),
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure, ?_⟩
  intro a
  let x : Units.dirichletUnitTheorem.logSpace K := fun w => genuineArchLog K a w
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  have hvL : (v : Units.dirichletUnitTheorem.logSpace K) ∈ L := by
    rw [← hs]
    exact v.property
  change (v : Units.dirichletUnitTheorem.logSpace K) ∈
    Submodule.map (Units.logEmbedding K).toIntLinearMap ⊤ at hvL
  obtain ⟨u, -, hu⟩ := Submodule.mem_map.mp hvL
  have hu' : Units.logEmbedding K u = (v : Units.dirichletUnitTheorem.logSpace K) := hu
  refine ⟨u.toMul, (genuineArchLog_unit_reduction K a u.toMul).1, ?_⟩
  apply subset_closure
  have htrans : (fun w : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀} =>
      genuineArchLog K (a * genuineUnitIdele K u.toMul) w) =
      (v : Units.dirichletUnitTheorem.logSpace K) + x := by
    funext w
    rw [genuineArchLog_principal_unit_translate]
    change x w + (Units.logEmbedding K u) w = (v : Units.dirichletUnitTheorem.logSpace K) w + x w
    rw [hu']
    exact add_comm _ _
  rw [htrans]
  exact hv
end MasulloGRH

namespace MasulloGRH
open NumberField
variable (K : Type*) [Field K] [NumberField K]
theorem genuineRestoreUnitLog_continuous : Continuous (genuineRestoreUnitLog K) := by
  classical
  apply continuous_pi
  intro w
  by_cases h : w = Units.dirichletUnitTheorem.w₀
  · have hc : Continuous (fun v : Units.dirichletUnitTheorem.logSpace K => - ∑ j, v j) :=
      (continuous_finset_sum Finset.univ (fun j _ => continuous_apply j)).neg
    simpa [genuineRestoreUnitLog, h] using hc
  · simpa [genuineRestoreUnitLog, h] using
      (continuous_apply (⟨w, h⟩ : {w : InfinitePlace K // w ≠ Units.dirichletUnitTheorem.w₀}))

theorem genuineRestoreUnitLog_of_sum_zero (x : InfinitePlace K → ℝ)
    (hx : ∑ w, x w = 0) :
    genuineRestoreUnitLog K (fun w => x w) = x := by
  classical
  funext w
  unfold genuineRestoreUnitLog
  split_ifs with h
  · subst w
    have hs := Fintype.sum_eq_add_sum_subtype_ne x Units.dirichletUnitTheorem.w₀
    rw [hx] at hs
    linarith
  · rfl

/-- Full weighted log representatives for actual archimedean norm-one ideles.
Compactness of logarithms is not compactness of the full idele representative
set; the finite-unit and angular factors remain to be assembled. -/
theorem genuineFullArchLog_compact_unit_representatives :
    ∃ S : Set (InfinitePlace K → ℝ), IsCompact S ∧
      ∀ a : HeckeIdeles K, (∑ w, genuineArchLog K a w) = 0 →
        ∃ u : (𝓞 K)ˣ,
          (QuotientGroup.mk (a * genuineUnitIdele K u) : HeckeIdeleClasses K) =
            QuotientGroup.mk a ∧
          genuineArchLog K (a * genuineUnitIdele K u) ∈ S := by
  obtain ⟨T, hT, hcover⟩ := genuineArchLog_compact_unit_representatives K
  refine ⟨genuineRestoreUnitLog K '' T,
    hT.image (genuineRestoreUnitLog_continuous K), ?_⟩
  intro a ha
  obtain ⟨u, hclass, hu⟩ := hcover a
  refine ⟨u, hclass, ?_⟩
  have hz : ∑ w, genuineArchLog K (a * genuineUnitIdele K u) w = 0 := by
    simp_rw [genuineArchLog_mul]
    rw [Finset.sum_add_distrib, ha, genuineArchLog_unit_sum, zero_add]
  exact ⟨_, hu, genuineRestoreUnitLog_of_sum_zero K _ hz⟩
end MasulloGRH

set_option linter.unusedSectionVars false
/-! Round 80 B, repairing the round-79 candidate: actual archimedean compact pieces for the arithmetic
norm-one covering. Both values and inverses are bounded, so the compact
piece lives in the genuine units topology and cannot acquire zero points.
The ideal-class/unit-lattice covering of the whole quotient is still open. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

def genuineArchBox (R : ℝ) : Set (NumberField.InfiniteAdeleRing K) :=
  Set.univ.pi (fun w => Metric.closedBall (0 : w.Completion) R)

theorem genuineArchBox_isCompact (R : ℝ) : IsCompact (genuineArchBox K R) := by
  have hc (w : NumberField.InfinitePlace K) :
      IsCompact (Metric.closedBall (0 : w.Completion) R) := by
    classical
    by_cases h : w.IsReal
    · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal h
      have heq : Metric.closedBall (0 : w.Completion) R =
          e ⁻¹' Metric.closedBall (e 0) R := by
        ext x
        simp only [Set.mem_preimage, Metric.mem_closedBall, e.isometry.dist_eq]
      rw [heq]
      exact e.toHomeomorph.isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall (e 0) R)
    · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
        (w.not_isReal_iff_isComplex.mp h)
      have heq : Metric.closedBall (0 : w.Completion) R =
          e ⁻¹' Metric.closedBall (e 0) R := by
        ext x
        simp only [Set.mem_preimage, Metric.mem_closedBall, e.isometry.dist_eq]
      rw [heq]
      exact e.toHomeomorph.isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall (e 0) R)
  exact isCompact_univ_pi hc

def genuineArchUnitBox (R : ℝ) : Set (NumberField.InfiniteAdeleRing K)ˣ :=
  Units.embedProduct _ ⁻¹'
    (genuineArchBox K R ×ˢ (MulOpposite.op '' genuineArchBox K R))

theorem genuineArchUnitBox_isCompact (R : ℝ) :
    IsCompact (genuineArchUnitBox K R) := by
  letI : T1Space (NumberField.InfiniteAdeleRing K) :=
    inferInstanceAs (T1Space (∀ w : NumberField.InfinitePlace K, w.Completion))
  apply Units.isClosedEmbedding_embedProduct.isCompact_preimage
  exact (genuineArchBox_isCompact K R).prod
    ((genuineArchBox_isCompact K R).image MulOpposite.continuous_op)

noncomputable def genuineArchUnitIdele (u : (NumberField.InfiniteAdeleRing K)ˣ) :
    HeckeIdeles K where
  val := (u.val, 1)
  inv := (u.inv, 1)
  val_inv := Prod.ext u.val_inv (one_mul 1)
  inv_val := Prod.ext u.inv_val (one_mul 1)

theorem genuineArchUnitIdele_continuous : Continuous (genuineArchUnitIdele K) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact Units.continuous_val.prodMk continuous_const
  · exact Units.continuous_coe_inv.prodMk continuous_const

theorem genuineArchUnitIdele_compact (R : ℝ) :
    IsCompact (genuineArchUnitIdele K '' genuineArchUnitBox K R) :=
  (genuineArchUnitBox_isCompact K R).image (genuineArchUnitIdele_continuous K)

end MasulloGRH

/-! Round 81 C: promote the genuine weighted-log reduction to compact
representatives of the actual archimedean unit components. -/
namespace MasulloGRH
open NumberField
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineArchProjection (a : HeckeIdeles K) :
    (InfiniteAdeleRing K)ˣ where
  val := a.val.1
  inv := a.inv.1
  val_inv := congrArg Prod.fst a.val_inv
  inv_val := congrArg Prod.fst a.inv_val

theorem genuineArchLog_inv (a : HeckeIdeles K) (w : InfinitePlace K) :
    genuineArchLog K a⁻¹ w = - genuineArchLog K a w := by
  have h := genuineArchLog_mul K a a⁻¹ w
  have hz : genuineArchLog K (1 : HeckeIdeles K) w = 0 := by
    change (w.mult : ℝ) * Real.log ‖(1 : w.Completion)‖ = 0
    simp
  rw [mul_inv_cancel, hz] at h
  linarith

theorem genuineArch_norm_le_exp (a : HeckeIdeles K) (w : InfinitePlace K)
    (M : ℝ) (hM : |genuineArchLog K a w| ≤ M) :
    ‖a.val.1 w‖ ≤ Real.exp M := by
  have hn : 0 < ‖a.val.1 w‖ := by
    apply norm_pos_iff.mpr
    have h : a.val.1 w * a.inv.1 w = 1 :=
      congrArg (fun x : HeckeAdeles K => x.1 w) a.val_inv
    exact left_ne_zero_of_mul_eq_one h
  have hm : (1 : ℝ) ≤ (w.mult : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (InfinitePlace.mult_pos (w := w)))
  have hl : |Real.log ‖a.val.1 w‖| ≤ M := by
    calc
      |Real.log ‖a.val.1 w‖| ≤ (w.mult : ℝ) * |Real.log ‖a.val.1 w‖| :=
        le_mul_of_one_le_left (abs_nonneg _) hm
      _ = |genuineArchLog K a w| := by
        rw [genuineArchLog, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ w.mult)]
      _ ≤ M := hM
  exact (Real.log_le_iff_le_exp hn).mp ((le_abs_self _).trans hl)

/-- The compact archimedean unit set is independent of the idele. Actual
integral principal units preserve the class, including finite components.
The displayed zero-sum hypothesis is archimedean, not global norm one. -/
theorem genuineArch_compact_unit_reduction :
    ∃ R : ℝ, IsCompact (genuineArchUnitIdele K '' genuineArchUnitBox K R) ∧
      ∀ a : HeckeIdeles K, (∑ w, genuineArchLog K a w) = 0 →
        ∃ u : (𝓞 K)ˣ,
          (QuotientGroup.mk (a * genuineUnitIdele K u) : HeckeIdeleClasses K) =
            QuotientGroup.mk a ∧
          genuineArchUnitIdele K (genuineArchProjection K (a * genuineUnitIdele K u)) ∈
            genuineArchUnitIdele K '' genuineArchUnitBox K R := by
  classical
  obtain ⟨S, hS, hcover⟩ := genuineFullArchLog_compact_unit_representatives K
  obtain ⟨M, hM⟩ := hS.isBounded.exists_norm_le
  refine ⟨Real.exp M, genuineArchUnitIdele_compact K _, ?_⟩
  intro a ha
  obtain ⟨u, hclass, hu⟩ := hcover a ha
  let b := a * genuineUnitIdele K u
  have hb (w : InfinitePlace K) : |genuineArchLog K b w| ≤ M := by
    exact (norm_le_pi_norm (genuineArchLog K b) w).trans (hM _ hu)
  have hval : b.val.1 ∈ genuineArchBox K (Real.exp M) := by
    intro w _
    simpa only [Metric.mem_closedBall, dist_zero_right] using genuineArch_norm_le_exp K b w M (hb w)
  have hinv : b.inv.1 ∈ genuineArchBox K (Real.exp M) := by
    intro w _
    have hi : |genuineArchLog K b⁻¹ w| ≤ M := by
      rw [genuineArchLog_inv, abs_neg]
      exact hb w
    simpa only [Metric.mem_closedBall, dist_zero_right] using genuineArch_norm_le_exp K b⁻¹ w M hi
  refine ⟨u, hclass, genuineArchProjection K b, ?_, rfl⟩
  change b.val.1 ∈ genuineArchBox K (Real.exp M) ∧
    MulOpposite.op b.inv.1 ∈ MulOpposite.op '' genuineArchBox K (Real.exp M)
  exact ⟨hval, b.inv.1, hinv, rfl⟩
end MasulloGRH

namespace MasulloGRH
open NumberField
variable (K : Type*) [Field K] [NumberField K]
/-- Exactly the genuine global modulus used by the preserved A76 consumer. -/
noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem genuineArchLog_sum_zero_of_modulus_one (a : HeckeIdeles K)
    (ha : genuineIdeleModulus K a = 1)
    (hf : ∀ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖ = 1) :
    ∑ w, genuineArchLog K a w = 0 := by
  have hp : (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) = 1 := by
    simpa [genuineIdeleModulus, hf] using ha
  have hn (w : InfinitePlace K) : ‖a.val.1 w‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    have h : a.val.1 w * a.inv.1 w = 1 :=
      congrArg (fun x : HeckeAdeles K => x.1 w) a.val_inv
    exact left_ne_zero_of_mul_eq_one h
  have hl := congrArg Real.log hp
  rw [Real.log_prod (fun w _ => pow_ne_zero _ (hn w)), Real.log_one] at hl
  simpa only [Real.log_pow, genuineArchLog] using hl

/-- Actual modulus-one consumer; finite norms one remains an explicit arithmetic
premise to be obtained by finite ideal-class reduction. -/
theorem genuineArch_compact_reduction_of_global_modulus_one :
    ∃ R : ℝ, IsCompact (genuineArchUnitIdele K '' genuineArchUnitBox K R) ∧
      ∀ a : HeckeIdeles K, genuineIdeleModulus K a = 1 →
        (∀ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖ = 1) →
        ∃ u : (𝓞 K)ˣ,
          (QuotientGroup.mk (a * genuineUnitIdele K u) : HeckeIdeleClasses K) =
            QuotientGroup.mk a ∧
          genuineArchUnitIdele K (genuineArchProjection K (a * genuineUnitIdele K u)) ∈
            genuineArchUnitIdele K '' genuineArchUnitBox K R := by
  obtain ⟨R, hR, hcover⟩ := genuineArch_compact_unit_reduction K
  exact ⟨R, hR, fun a ha hf => hcover a
    (genuineArchLog_sum_zero_of_modulus_one K a ha hf)⟩
end MasulloGRH

/- Finite integral-unit compactness reused from F53 exact checked source. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev FinitePrime := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
abbrev LocalField (v : FinitePrime K) := v.adicCompletion K
end MasulloGRH
open scoped NumberField Valued WithZero
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
/-- Arithmetic residue-field finiteness suffices for compactness of the actual local integer ring. -/
theorem localInteger_compact_of_finite_residue
    [Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K)))] :
    IsCompact {x : v.adicCompletion K | Valued.v x ≤ 1} := by
  have hd : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  letI : ProperSpace (v.adicCompletion K) :=
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
      ⟨inferInstance, hd, inferInstance⟩
  have hc : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  exact isCompact_iff_compactSpace.mpr hc


end MasulloGRH
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open scoped NumberField Valued WithZero
open IsDedekindDomain
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

theorem localInteger_rational_approximation (x : v.adicCompletionIntegers K) :
    ∃ y : K, v.valuation K y ≤ 1 ∧ Valued.v ((y : v.adicCompletion K) - x) < 1 := by
  have hd : DenseRange (fun y : K => (y : v.adicCompletion K)) :=
    UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  have ho : IsOpen {y : v.adicCompletion K | Valued.v (y - x) < 1} :=
    (Valued.isOpen_ball (v.adicCompletion K) 1).preimage (continuous_id.sub continuous_const)
  obtain ⟨y, hy⟩ := hd.exists_mem_open ho ⟨x, by simp⟩
  refine ⟨y, ?_, hy⟩
  rw [← v.valuedAdicCompletion_eq_valuation']
  calc
    Valued.v (y : v.adicCompletion K) = Valued.v (((y : v.adicCompletion K) - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (Valued.v ((y : v.adicCompletion K) - x)) (Valued.v (x : v.adicCompletion K)) := Valued.v.map_add _ _
    _ ≤ 1 := max_le (le_of_lt hy) x.property

noncomputable def localIntegerCompletionMap :
    (v.valuation K).valuationSubring →+* v.adicCompletionIntegers K where
  toFun a := ⟨(a : K), by
    change Valued.v ((a : K) : v.adicCompletion K) ≤ 1
    rw [v.valuedAdicCompletion_eq_valuation']
    exact a.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by
    ext
    exact map_add (algebraMap K (v.adicCompletion K)) (a : K) (b : K)
  map_mul' a b := by
    ext
    exact map_mul (algebraMap K (v.adicCompletion K)) (a : K) (b : K)

theorem localResidue_finite_of_rational_residue
    [Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  let f := (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
    (localIntegerCompletionMap K v)
  have hf : ∀ a ∈ IsLocalRing.maximalIdeal (v.valuation K).valuationSubring, f a = 0 := by
    intro a ha
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr
    change Valued.v ((a : K) : v.adicCompletion K) < 1
    rw [v.valuedAdicCompletion_eq_valuation']
    exact (Valuation.mem_maximalIdeal_iff K (v.valuation K)).mp ha
  let g := Ideal.Quotient.lift (IsLocalRing.maximalIdeal (v.valuation K).valuationSubring) f hf
  have hsur : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy, hxy⟩ := localInteger_rational_approximation K v x
    refine ⟨Ideal.Quotient.mk _ ⟨y, hy⟩, ?_⟩
    change IsLocalRing.residue _ (localIntegerCompletionMap K v ⟨y, hy⟩) =
      IsLocalRing.residue _ x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr hxy
  letI : Finite ((v.valuation K).valuationSubring ⧸ IsLocalRing.maximalIdeal (v.valuation K).valuationSubring) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring))
  exact Finite.of_surjective g hsur

end MasulloGRH
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open scoped NumberField Valued WithZero
open IsDedekindDomain Localization
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
local instance : IsDedekindDomain
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isDedekindDomain (𝓞 K) v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)
local instance : IsLocalRing (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isLocalRing
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) v.asIdeal
noncomputable def arithmeticValuationSubring : ValuationSubring K :=
  .ofSubring (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring fun x =>
    by simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger
        (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) x
instance : Algebra (𝓞 K) (arithmeticValuationSubring K v) :=
  (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).algebra'
instance : IsDedekindDomain (arithmeticValuationSubring K v) :=
  IsLocalization.AtPrime.isDedekindDomain (𝓞 K) v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)
instance : IsLocalization (v.asIdeal.primeCompl) (arithmeticValuationSubring K v) :=
  Localization.subalgebra.isLocalization_ofField K (v.asIdeal.primeCompl) _
theorem arithmeticValuationSubring_le :
    arithmeticValuationSubring K v ≤ (v.valuation K).valuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  suffices (v.valuation K) (a / (s : K)) ≤ 1 by rwa [division_def] at this
  rwa [v.valuation_div_le_one_iff K a (by aesop) (fun _ => by contradiction)]

theorem arithmeticValuationSubring_eq :
    arithmeticValuationSubring K v = (v.valuation K).valuationSubring := by
  apply le_antisymm (arithmeticValuationSubring_le K v)
  intro x hx
  by_cases hzero : x = 0
  · simp [hzero]
  rcases (arithmeticValuationSubring K v).mem_or_inv_mem x with h | h
  · exact h
  rcases h with ⟨a, s, hs, heq⟩
  have ha : a ≠ 0 := by
    intro ha
    apply hzero
    simpa [ha] using heq
  have hxform : x = (s : K) / (a : K) := by
    have hh := congrArg Inv.inv heq
    simpa [div_eq_mul_inv, mul_comm] using hh
  have han : a ∉ v.asIdeal := by
    apply (v.valuation_div_le_one_iff K s ha (fun _ => hs)).mp
    simpa [← hxform] using hx
  exact ⟨s, a, han, by simpa [div_eq_mul_inv] using hxform⟩
theorem rationalResidue_finite :
    Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring) := by
  rw [← arithmeticValuationSubring_eq K v]
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (arithmeticValuationSubring K v)
  exact Finite.of_surjective e e.surjective
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem localInteger_compactSpace (v : FinitePrime K) :
    CompactSpace (v.adicCompletionIntegers K) := by
  letI := rationalResidue_finite K v
  letI : Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K))) :=
    localResidue_finite_of_rational_residue K v
  exact isCompact_iff_compactSpace.mp (localInteger_compact_of_finite_residue K v)

theorem localIntegralUnits_compactSpace (v : FinitePrime K) :
    CompactSpace (v.adicCompletionIntegers K)ˣ := by
  letI := localInteger_compactSpace K v
  infer_instance


end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual finite idele group with its units topology. -/
abbrev FiniteIdeles := (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ

noncomputable def finiteIntegralUnitIdele
    (x : ∀ v : FinitePrime K, (v.adicCompletionIntegers K)ˣ) : FiniteIdeles K where
  val := RestrictedProduct.structureMap _ _ Filter.cofinite (fun v => (x v).val)
  inv := RestrictedProduct.structureMap _ _ Filter.cofinite (fun v => (x v).inv)
  val_inv := by
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    exact congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).val_inv
  inv_val := by
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    exact congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).inv_val

/-- Integral units require both an adele and its inverse to be integral everywhere. -/
def finiteIntegralUnits : Subgroup (FiniteIdeles K) where
  carrier := {a | (∀ v, a.val v ∈ v.adicCompletionIntegers K) ∧
    (∀ v, a.inv v ∈ v.adicCompletionIntegers K)}
  one_mem' := ⟨fun v => (v.adicCompletionIntegers K).one_mem,
    fun v => (v.adicCompletionIntegers K).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    exact ⟨fun v => (v.adicCompletionIntegers K).mul_mem _ _ (ha v) (hb v),
      fun v => (v.adicCompletionIntegers K).mul_mem _ _ (hbi v) (hai v)⟩
  inv_mem' := by
    rintro a ⟨ha, hi⟩
    exact ⟨hi, ha⟩

theorem finiteIntegralUnitIdele_continuous : Continuous (finiteIntegralUnitIdele K) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v))
  · exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v))

theorem finiteIntegralUnits_eq_range :
    (finiteIntegralUnits K : Set (FiniteIdeles K)) = Set.range (finiteIntegralUnitIdele K) := by
  ext a
  constructor
  · rintro ⟨ha, hi⟩
    let x : ∀ v : FinitePrime K, (v.adicCompletionIntegers K)ˣ := fun v =>
      { val := ⟨a.val v, ha v⟩
        inv := ⟨a.inv v, hi v⟩
        val_inv := Subtype.ext (congrArg (fun z : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => z v) a.val_inv)
        inv_val := Subtype.ext (congrArg (fun z : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => z v) a.inv_val) }
    refine ⟨x, Units.ext ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨fun v => (x v).val.property, fun v => (x v).inv.property⟩

theorem finiteIntegralUnits_isCompact :
    IsCompact (finiteIntegralUnits K : Set (FiniteIdeles K)) := by
  letI (v : FinitePrime K) : CompactSpace (v.adicCompletionIntegers K)ˣ :=
    localIntegralUnits_compactSpace K v
  rw [finiteIntegralUnits_eq_range]
  exact isCompact_range (finiteIntegralUnitIdele_continuous K)


end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineFiniteProjection (a : HeckeIdeles K) : FiniteIdeles K where
  val := a.val.2
  inv := a.inv.2
  val_inv := congrArg Prod.snd a.val_inv
  inv_val := congrArg Prod.snd a.inv_val
noncomputable def genuineFiniteUnitIdele (a : FiniteIdeles K) : HeckeIdeles K where
  val := (1, a.val)
  inv := (1, a.inv)
  val_inv := Prod.ext (one_mul 1) a.val_inv
  inv_val := Prod.ext (one_mul 1) a.inv_val

theorem genuineFiniteUnitIdele_continuous : Continuous (genuineFiniteUnitIdele K) := by
  apply Units.continuous_iff.mpr
  exact ⟨continuous_const.prodMk Units.continuous_val,
    continuous_const.prodMk Units.continuous_coe_inv⟩

theorem genuineArchFinite_factorization (a : HeckeIdeles K) :
    genuineArchUnitIdele K (genuineArchProjection K a) *
      genuineFiniteUnitIdele K (genuineFiniteProjection K a) = a := by
  apply Units.ext
  exact Prod.ext (mul_one _) (one_mul _)

theorem genuineFiniteProjection_integral_of_valuations (a : HeckeIdeles K)
    (ha : ∀ v : FinitePrime K, Valued.v (a.val.2 v) = 1) :
    genuineFiniteProjection K a ∈ finiteIntegralUnits K := by
  refine ⟨fun v => le_of_eq (ha v), ?_⟩
  intro v
  have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul]
    have he : a.val.2 v * a.inv.2 v = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
    rw [he, map_one]
  rw [ha v, one_mul] at hm
  exact le_of_eq hm

theorem genuineFinite_norm_one_of_valuation_one (a : HeckeIdeles K)
    (ha : ∀ v : FinitePrime K, Valued.v (a.val.2 v) = 1)
    (v : NumberField.FinitePlace K) : ‖a.val.2 v.maximalIdeal‖ = 1 := by
  change Valued.norm (a.val.2 v.maximalIdeal) = 1
  rw [Valued.norm_def, ha, map_one]
  rfl

/-- The actual finite-unit and archimedean bounds form a compact set of full
ideles. This supplies the product set in the arithmetic compact-cover route. -/
theorem genuineFullIntegralBox_isCompact (R : ℝ) :
    IsCompact ((fun p : HeckeIdeles K × FiniteIdeles K =>
      p.1 * genuineFiniteUnitIdele K p.2) ''
      ((genuineArchUnitIdele K '' genuineArchUnitBox K R) ×ˢ
        (finiteIntegralUnits K : Set (FiniteIdeles K)))) := by
  apply ((genuineArchUnitIdele_compact K R).prod (finiteIntegralUnits_isCompact K)).image
  exact continuous_fst.mul ((genuineFiniteUnitIdele_continuous K).comp continuous_snd)
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineUnitIdele_finite_valuation (u : (𝓞 K)ˣ) (v : FinitePrime K) :
    Valued.v ((genuineUnitIdele K u).val.2 v) = 1 := by
  have hv : Valued.v ((genuineUnitIdele K u).val.2 v) ≤ 1 := by
    change Valued.v ((algebraMap (𝓞 K) K u.val : K) : v.adicCompletion K) ≤ 1
    rw [v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one _
  have hi : Valued.v ((genuineUnitIdele K u).inv.2 v) ≤ 1 := by
    change Valued.v ((algebraMap (𝓞 K) K u.inv : K) : v.adicCompletion K) ≤ 1
    rw [v.valuedAdicCompletion_eq_valuation']
    exact v.valuation_le_one _
  have hm : Valued.v ((genuineUnitIdele K u).val.2 v) *
      Valued.v ((genuineUnitIdele K u).inv.2 v) = 1 := by
    rw [← map_mul]
    have he : (genuineUnitIdele K u).val.2 v * (genuineUnitIdele K u).inv.2 v = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 v) (genuineUnitIdele K u).val_inv
    rw [he, map_one]
  apply le_antisymm hv
  calc
    1 = Valued.v ((genuineUnitIdele K u).val.2 v) *
      Valued.v ((genuineUnitIdele K u).inv.2 v) := hm.symm
    _ ≤ Valued.v ((genuineUnitIdele K u).val.2 v) * 1 := mul_le_mul_right hi _
    _ = _ := mul_one _

/-- Compact full-idele representatives for the modulus-one, finite-unit
sector. The finite ideal-class representatives are a separate remaining step. -/
theorem genuineIntegralNormOne_compact_representatives :
    ∃ S : Set (HeckeIdeles K), IsCompact S ∧
      ∀ a : HeckeIdeles K, genuineIdeleModulus K a = 1 →
        (∀ v : FinitePrime K, Valued.v (a.val.2 v) = 1) →
        ∃ b ∈ S, (QuotientGroup.mk b : HeckeIdeleClasses K) = QuotientGroup.mk a := by
  obtain ⟨R, _, hcover⟩ := genuineArch_compact_reduction_of_global_modulus_one K
  let S := (fun p : HeckeIdeles K × FiniteIdeles K =>
      p.1 * genuineFiniteUnitIdele K p.2) ''
      ((genuineArchUnitIdele K '' genuineArchUnitBox K R) ×ˢ
        (finiteIntegralUnits K : Set (FiniteIdeles K)))
  refine ⟨S, genuineFullIntegralBox_isCompact K R, ?_⟩
  intro a ha hv
  obtain ⟨u, hclass, harch⟩ := hcover a ha
    (genuineFinite_norm_one_of_valuation_one K a hv)
  let b := a * genuineUnitIdele K u
  have hb : ∀ v : FinitePrime K, Valued.v (b.val.2 v) = 1 := by
    intro v
    change Valued.v (a.val.2 v * (genuineUnitIdele K u).val.2 v) = 1
    rw [map_mul, hv, genuineUnitIdele_finite_valuation, one_mul]
  refine ⟨b, ?_, hclass⟩
  exact ⟨(genuineArchUnitIdele K (genuineArchProjection K b), genuineFiniteProjection K b),
    ⟨harch, genuineFiniteProjection_integral_of_valuations K b hb⟩,
    genuineArchFinite_factorization K b⟩
end MasulloGRH

/- A82 checked finite ideal-class reduction, exact source retained. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineIdele_nonunit_finite (a : HeckeIdeles K) :
    {v : FinitePrime K | Valued.v (a.val.2 v) ≠ 1}.Finite := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [a.val.2.property, a.inv.2.property] with v hv hi
  change Valued.v (a.val.2 v) ≤ 1 at hv
  change Valued.v (a.inv.2 v) ≤ 1 at hi
  have he : a.val.2 v * a.inv.2 v = 1 :=
    congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
  have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul, he, map_one]
  apply le_antisymm hv
  calc
    1 = Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) := hm.symm
    _ ≤ Valued.v (a.val.2 v) * 1 := by gcongr
    _ = _ := mul_one _


noncomputable def finiteIdeleOrder (a : HeckeIdeles K) : FinitePrime K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => -(Valued.v (a.val.2 v)).log) (by
    apply (genuineIdele_nonunit_finite K a).subset
    intro v hv
    change -(Valued.v (a.val.2 v)).log ≠ 0 at hv
    change Valued.v (a.val.2 v) ≠ 1
    intro he
    apply hv
    rw [he]
    simp)

theorem genuineIdele_coordinate_valuation_ne_zero (a : HeckeIdeles K) (v : FinitePrime K) :
    Valued.v (a.val.2 v) ≠ 0 := by
  have he : a.val.2 v * a.inv.2 v = 1 :=
    congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
  have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul, he, map_one]
  intro hz
  rw [hz, zero_mul] at hm
  exact zero_ne_one hm

theorem finiteIdeleOrder_valuation (a : HeckeIdeles K) (v : FinitePrime K) :
    Valued.v (a.val.2 v) = WithZero.exp (-(finiteIdeleOrder K a v)) := by
  change Valued.v (a.val.2 v) = WithZero.exp (-(-(Valued.v (a.val.2 v)).log))
  rw [neg_neg, WithZero.exp_log (genuineIdele_coordinate_valuation_ne_zero K a v)]

theorem finiteIdeleOrder_eq_iff (a b : HeckeIdeles K) :
    finiteIdeleOrder K a = finiteIdeleOrder K b ↔
      ∀ v : FinitePrime K, Valued.v (a.val.2 v) = Valued.v (b.val.2 v) := by
  constructor
  · intro h v
    rw [finiteIdeleOrder_valuation K a v, finiteIdeleOrder_valuation K b v, h]
  · intro h
    ext v
    change -(Valued.v (a.val.2 v)).log = -(Valued.v (b.val.2 v)).log
    rw [h v]


noncomputable def genuineFiniteFractionalIdeal (a : HeckeIdeles K) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  ∏ᶠ v : FinitePrime K,
    (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (finiteIdeleOrder K a v)

/-- Exact finite-prime orders of the actual idele's fractional ideal. -/
theorem genuineFiniteFractionalIdeal_count (a : HeckeIdeles K) (v : FinitePrime K) :
    FractionalIdeal.count K v (genuineFiniteFractionalIdeal K a) = finiteIdeleOrder K a v := by
  apply FractionalIdeal.count_finprod K v
  exact Filter.eventually_cofinite.mpr (finiteIdeleOrder K a).finite_support

/-- Principal integral ideles have precisely the usual ideal prime exponents. -/
theorem finiteIdeleOrder_principal_integral (r : 𝓞 K) (hr : (r : K) ≠ 0)
    (v : FinitePrime K) :
    finiteIdeleOrder K (principalIdele K (Units.mk0 (r : K) hr)) v =
      FractionalIdeal.count K v (Ideal.span {r} : Ideal (𝓞 K)) := by
  have hr0 : r ≠ 0 := by intro h; exact hr (by rw [h]; rfl)
  have hI : Ideal.span ({r} : Set (𝓞 K)) ≠ 0 := by
    change Ideal.span ({r} : Set (𝓞 K)) ≠ ⊥
    intro hz
    have hm : r ∈ Ideal.span ({r} : Set (𝓞 K)) := Ideal.subset_span (Set.mem_singleton r)
    rw [hz] at hm
    exact hr0 hm
  change -(Valued.v ((principalIdele K (Units.mk0 (r : K) hr)).val.2 v)).log = _
  have hv : Valued.v ((principalIdele K (Units.mk0 (r : K) hr)).val.2 v) =
      v.intValuation r := by
    change Valued.v ((r : K) : v.adicCompletion K) = _
    rw [v.valuedAdicCompletion_eq_valuation', v.valuation_of_algebraMap]
  rw [hv, v.intValuation_if_neg hr0, WithZero.log_exp, neg_neg]
  exact (FractionalIdeal.count_coe K v hI).symm

/-- The finite-ideal construction agrees with the actual principal ideal for
nonzero algebraic integers. This is used in the principal-idele reduction
needed for compact norm-one representatives, not a trace assertion. -/
theorem genuineFiniteFractionalIdeal_principal_integral
    (r : 𝓞 K) (hr : (r : K) ≠ 0) :
    genuineFiniteFractionalIdeal K (principalIdele K (Units.mk0 (r : K) hr)) =
      (Ideal.span {r} : Ideal (𝓞 K)) := by
  have hr0 : r ≠ 0 := by intro h; exact hr (by rw [h]; rfl)
  have hI : (Ideal.span {r} : Ideal (𝓞 K)) ≠ 0 := by
    change Ideal.span ({r} : Set (𝓞 K)) ≠ ⊥
    intro hz
    have hm : r ∈ Ideal.span ({r} : Set (𝓞 K)) := Ideal.subset_span (Set.mem_singleton r)
    rw [hz] at hm
    exact hr0 hm
  unfold genuineFiniteFractionalIdeal
  simp_rw [finiteIdeleOrder_principal_integral]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)


/-- Actual finite valuation orders are additive under idele multiplication. -/
theorem finiteIdeleOrder_mul (a b : HeckeIdeles K) :
    finiteIdeleOrder K (a * b) = finiteIdeleOrder K a + finiteIdeleOrder K b := by
  ext v
  change -(Valued.v (a.val.2 v * b.val.2 v)).log =
    -(Valued.v (a.val.2 v)).log + -(Valued.v (b.val.2 v)).log
  rw [map_mul, WithZero.log_mul (genuineIdele_coordinate_valuation_ne_zero K a v)
    (genuineIdele_coordinate_valuation_ne_zero K b v)]
  ring


/-- Every nonzero field element, with no integrality restriction, has the
correct principal fractional ideal. This is the principal-idele bridge needed
for reduction by the finite ideal class group. -/
theorem genuineFiniteFractionalIdeal_principal (x : Kˣ) :
    genuineFiniteFractionalIdeal K (principalIdele K x) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) := by
  classical
  obtain ⟨r, d, h⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors (𝓞 K)) (x : K)
  have hr : r ≠ 0 := IsLocalization.ne_zero_of_mk'_ne_zero (by rw [h]; exact x.ne_zero)
  have hd : (d : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have ho (v : FinitePrime K) :
      finiteIdeleOrder K (principalIdele K x) v =
        (↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r})).factors) : ℤ) -
        ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(d : 𝓞 K)})).factors) := by
    change -(Valued.v ((x : K) : v.adicCompletion K)).log = _
    rw [v.valuedAdicCompletion_eq_valuation', ← h, v.valuation_of_mk',
      WithZero.log_div (v.intValuation_ne_zero r hr) (v.intValuation_ne_zero (d : 𝓞 K) hd),
      v.intValuation_if_neg hr, v.intValuation_if_neg hd, WithZero.log_exp, WithZero.log_exp]
    ring
  unfold genuineFiniteFractionalIdeal
  simp_rw [ho]
  rw [← h]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization_principal_fraction hr d


theorem genuineFiniteFractionalIdeal_eq_iff (a b : HeckeIdeles K) :
    genuineFiniteFractionalIdeal K a = genuineFiniteFractionalIdeal K b ↔
      finiteIdeleOrder K a = finiteIdeleOrder K b := by
  constructor
  · intro h
    ext v
    simpa only [genuineFiniteFractionalIdeal_count] using
      congrArg (FractionalIdeal.count K v) h
  · intro h
    unfold genuineFiniteFractionalIdeal
    rw [h]

theorem finiteIdeleOrder_one : finiteIdeleOrder K 1 = 0 := by
  ext v
  change -(Valued.v (1 : v.adicCompletion K)).log = 0
  simp

theorem finiteIdeleOrder_inv (a : HeckeIdeles K) :
    finiteIdeleOrder K a⁻¹ = -finiteIdeleOrder K a := by
  have h := finiteIdeleOrder_mul K a a⁻¹
  rw [mul_inv_cancel, finiteIdeleOrder_one] at h
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h.symm)

/-- A principal fractional ideal is exactly removable by its actual principal
idele, leaving zero finite valuation orders. This is the arithmetic reduction
step for the compact finite-integral-unit factors in norm-one representatives. -/
theorem genuineFiniteFractionalIdeal_principal_reduction
    (a : HeckeIdeles K) (x : Kˣ) :
    genuineFiniteFractionalIdeal K a =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) ↔
    finiteIdeleOrder K (a * (principalIdele K x)⁻¹) = 0 := by
  rw [← genuineFiniteFractionalIdeal_principal K x,
    genuineFiniteFractionalIdeal_eq_iff, finiteIdeleOrder_mul, finiteIdeleOrder_inv,
    ← sub_eq_add_neg, sub_eq_zero]


/-- Principal reduction has unit valuation at every actual finite completion. -/
theorem genuineFiniteFractionalIdeal_principal_reduction_valuations
    (a : HeckeIdeles K) (x : Kˣ) :
    genuineFiniteFractionalIdeal K a =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) ↔
    ∀ v : FinitePrime K, Valued.v ((a * (principalIdele K x)⁻¹).val.2 v) = 1 := by
  rw [genuineFiniteFractionalIdeal_principal_reduction,
    ← finiteIdeleOrder_one K, finiteIdeleOrder_eq_iff]
  change (∀ v : FinitePrime K, Valued.v ((a * (principalIdele K x)⁻¹).val.2 v) =
    Valued.v (1 : v.adicCompletion K)) ↔ _
  simp only [map_one]


/-- The valuation-product ideal is nonzero, including when all orders vanish. -/
theorem genuineFiniteFractionalIdeal_ne_zero (a : HeckeIdeles K) :
    genuineFiniteFractionalIdeal K a ≠ 0 := by
  intro h
  have ho : finiteIdeleOrder K a = 0 := by
    ext v
    have hc := genuineFiniteFractionalIdeal_count K a v
    rw [h, FractionalIdeal.count_zero] at hc
    exact hc.symm
  have he : genuineFiniteFractionalIdeal K a = 1 := by
    unfold genuineFiniteFractionalIdeal
    simp [ho]
  exact zero_ne_one (h.symm.trans he)

/-- Multiplication compatibility for the actual idele-to-ideal map. -/
theorem genuineFiniteFractionalIdeal_mul (a b : HeckeIdeles K) :
    genuineFiniteFractionalIdeal K (a * b) =
      genuineFiniteFractionalIdeal K a * genuineFiniteFractionalIdeal K b := by
  have ha := genuineFiniteFractionalIdeal_ne_zero K a
  have hb := genuineFiniteFractionalIdeal_ne_zero K b
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K (mul_ne_zero ha hb)]
  change (∏ᶠ v : FinitePrime K,
    (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^
      (finiteIdeleOrder K (a * b) v)) = _
  congr 1
  funext v
  rw [FractionalIdeal.count_mul K v ha hb, genuineFiniteFractionalIdeal_count,
    genuineFiniteFractionalIdeal_count, finiteIdeleOrder_mul, Finsupp.add_apply]


noncomputable def genuineFiniteFractionalIdealHom :
    HeckeIdeles K →* (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ where
  toFun a := Units.mk0 (genuineFiniteFractionalIdeal K a)
    (genuineFiniteFractionalIdeal_ne_zero K a)
  map_one' := by
    apply Units.ext
    change genuineFiniteFractionalIdeal K 1 = 1
    unfold genuineFiniteFractionalIdeal
    simp [finiteIdeleOrder_one]
  map_mul' a b := Units.ext (genuineFiniteFractionalIdeal_mul K a b)

noncomputable def genuineFiniteIdealClass : HeckeIdeles K →* ClassGroup (𝓞 K) :=
  ClassGroup.mk.comp (genuineFiniteFractionalIdealHom K)

/-- Triviality of the genuine finite ideal class produces an actual principal
field element, not an assumed arithmetic identification. -/
theorem genuineFiniteIdealClass_one_principal (a : HeckeIdeles K)
    (h : genuineFiniteIdealClass K a = 1) :
    ∃ x : Kˣ, genuineFiniteFractionalIdeal K a =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) := by
  have hp : (genuineFiniteFractionalIdeal K a : Submodule (𝓞 K) K).IsPrincipal :=
    ClassGroup.mk_eq_one_iff.mp h
  letI := hp
  let x : K := Submodule.IsPrincipal.generator
    (genuineFiniteFractionalIdeal K a : Submodule (𝓞 K) K)
  have he : genuineFiniteFractionalIdeal K a =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) x :=
    FractionalIdeal.eq_spanSingleton_of_principal _
  have hx : x ≠ 0 := by
    intro hz
    apply genuineFiniteFractionalIdeal_ne_zero K a
    rw [he, hz, FractionalIdeal.spanSingleton_zero]
  exact ⟨Units.mk0 x hx, he⟩

/-- Finite class reduction on the actual ideles. The residual has zero finite
orders after division by one of finitely many actual ideles and a principal
idele. This is the finite-place premise of compact norm-one representatives. -/
theorem genuineFiniteIdele_finite_class_reduction :
    ∃ S : Finset (HeckeIdeles K), ∀ a : HeckeIdeles K,
      ∃ b ∈ S, ∃ x : Kˣ,
        finiteIdeleOrder K (a * b⁻¹ * (principalIdele K x)⁻¹) = 0 := by
  classical
  let Q := Set.range (genuineFiniteIdealClass K)
  letI : Fintype Q := Fintype.ofFinite Q
  let rep : Q → HeckeIdeles K := fun c => Classical.choose c.property
  have hrep (c : Q) : genuineFiniteIdealClass K (rep c) = c.val :=
    Classical.choose_spec c.property
  refine ⟨Finset.univ.image rep, ?_⟩
  intro a
  let c : Q := ⟨genuineFiniteIdealClass K a, a, rfl⟩
  refine ⟨rep c, Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩, ?_⟩
  have hc : genuineFiniteIdealClass K (a * (rep c)⁻¹) = 1 := by
    rw [map_mul, map_inv, hrep c]
    exact mul_inv_cancel _
  obtain ⟨x, hx⟩ := genuineFiniteIdealClass_one_principal K (a * (rep c)⁻¹) hc
  exact ⟨x, (genuineFiniteFractionalIdeal_principal_reduction K _ x).mp hx⟩


/-- Exact local-valuation form consumed by the compact finite-integral-unit
classification. No compactness or spectral identification is assumed here. -/
theorem genuineFiniteIdele_finite_class_reduction_valuations :
    ∃ S : Finset (HeckeIdeles K), ∀ a : HeckeIdeles K,
      ∃ b ∈ S, ∃ x : Kˣ, ∀ v : FinitePrime K,
        Valued.v ((a * b⁻¹ * (principalIdele K x)⁻¹).val.2 v) = 1 := by
  obtain ⟨S, hS⟩ := genuineFiniteIdele_finite_class_reduction K
  refine ⟨S, ?_⟩
  intro a
  obtain ⟨b, hb, x, hx⟩ := hS a
  refine ⟨b, hb, x, ?_⟩
  rw [← finiteIdeleOrder_one K, finiteIdeleOrder_eq_iff] at hx
  intro v
  have hv := hx v
  change Valued.v ((a * b⁻¹ * (principalIdele K x)⁻¹).val.2 v) =
    Valued.v (1 : v.adicCompletion K) at hv
  simpa only [map_one] using hv

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineIdeleModulus_principal (a : Kˣ) :
    genuineIdeleModulus K (principalIdele K a) = 1 := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(principalIdele K a).val.1 w‖ = w (a : K) := by
    exact NumberField.InfinitePlace.Completion.norm_coe w
      ((WithAbs.equiv _).symm (a : K))
  have hf (v : NumberField.FinitePlace K) :
      ‖(principalIdele K a).val.2 v.maximalIdeal‖ = v (a : K) := by
    exact NumberField.FinitePlace.norm_embedding_eq v (a : K)
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  exact NumberField.prod_abs_eq_one (K := K) a.ne_zero
/-- Outside finitely many finite places, an actual idele has local norm one. -/
theorem genuineIdele_finite_norm_support (a : HeckeIdeles K) :
    (Function.mulSupport (fun v : NumberField.FinitePlace K =>
      ‖a.val.2 v.maximalIdeal‖)).Finite := by
  have he : ∀ᶠ v in Filter.cofinite, ‖a.val.2 v‖ = 1 := by
    filter_upwards [RestrictedProduct.eventually _ _ a.val.2,
      RestrictedProduct.eventually _ _ (a⁻¹).val.2] with v hv hi
    change Valued.v (a.val.2 v) ≤ 1 at hv
    change Valued.v ((a⁻¹).val.2 v) ≤ 1 at hi
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 := by
      have h := congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
      exact h
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm hv
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right hi _
        _ = Valued.v (a.val.2 v) := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  exact (Filter.eventually_cofinite.mp he).preimage
    NumberField.FinitePlace.maximalIdeal_injective.injOn
theorem genuineIdeleModulus_mul (a b : HeckeIdeles K) :
    genuineIdeleModulus K (a * b) = genuineIdeleModulus K a * genuineIdeleModulus K b := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(a * b).val.1 w‖ ^ w.mult =
        ‖a.val.1 w‖ ^ w.mult * ‖b.val.1 w‖ ^ w.mult := by
    change ‖a.val.1 w * b.val.1 w‖ ^ w.mult = _
    rw [norm_mul, mul_pow]
  have hf (v : NumberField.FinitePlace K) :
      ‖(a * b).val.2 v.maximalIdeal‖ =
        ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ := by
    change ‖a.val.2 v.maximalIdeal * b.val.2 v.maximalIdeal‖ = _
    exact norm_mul _ _
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib
    (genuineIdele_finite_norm_support K a) (genuineIdele_finite_norm_support K b)]
  ring

theorem genuineIdeleModulus_ne_zero (a : HeckeIdeles K) :
    genuineIdeleModulus K a ≠ 0 := by
  have h1 : genuineIdeleModulus K 1 = 1 := by
    simpa only [map_one] using genuineIdeleModulus_principal K 1
  have hp := genuineIdeleModulus_mul K a a⁻¹
  rw [mul_inv_cancel, h1] at hp
  intro hz
  rw [hz, zero_mul] at hp
  exact one_ne_zero hp


end MasulloGRH
namespace MasulloGRH
open NumberField.InfinitePlace.Completion
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineRealAtPlace (w : NumberField.InfinitePlace K) : ℝ →+* w.Completion := by
  classical
  exact if h : w.IsReal then (ringEquivRealOfIsReal h).symm.toRingHom
    else (ringEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp
      Complex.ofRealHom

omit [NumberField K] in
theorem genuineRealAtPlace_norm (w : NumberField.InfinitePlace K) (r : ℝ) :
    ‖genuineRealAtPlace K w r‖ = |r| := by
  classical
  unfold genuineRealAtPlace
  split_ifs with h
  · simpa only [Real.norm_eq_abs] using
      (isometryEquivRealOfIsReal h).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivRealOfIsReal h).symm) r
  · simpa only [RingHom.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
      (isometryEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm) (r : ℂ)

/-- The actual archimedean section candidate, finite components identically one. -/
noncomputable def genuineSectionIdele (w : NumberField.InfinitePlace K) (t : ℝ) :
    HeckeIdeles K := by
  classical
  let a : ℝ := t / (w.mult : ℝ)
  refine ⟨(fun v => genuineRealAtPlace K v (if v = w then Real.exp a else 1), 1),
    (fun v => genuineRealAtPlace K v (if v = w then Real.exp (-a) else 1), 1), ?_, ?_⟩
  · apply Prod.ext
    · funext v
      change genuineRealAtPlace K v _ * genuineRealAtPlace K v _ = 1
      rw [← map_mul]
      split_ifs <;> simp [← Real.exp_add]
    · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul _
  · apply Prod.ext
    · funext v
      change genuineRealAtPlace K v _ * genuineRealAtPlace K v _ = 1
      rw [← map_mul]
      split_ifs <;> simp [← Real.exp_add]
    · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul _

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem genuineSectionIdele_modulus (w : NumberField.InfinitePlace K) (t : ℝ) :
    genuineIdeleModulus K (genuineSectionIdele K w t) = Real.exp t := by
  classical
  have hn (v : NumberField.InfinitePlace K) :
      ‖(genuineSectionIdele K w t).val.1 v‖ ^ v.mult =
        if v = w then Real.exp (t / (w.mult : ℝ)) ^ w.mult else 1 := by
    change ‖genuineRealAtPlace K v (if v = w then _ else _)‖ ^ v.mult = _
    rw [genuineRealAtPlace_norm]
    split_ifs with h
    · subst v
      rw [abs_of_pos (Real.exp_pos _)]
    · simp
  unfold genuineIdeleModulus
  simp_rw [hn]
  have hm : (w.mult : ℝ) ≠ 0 := by exact_mod_cast (NumberField.InfinitePlace.mult_ne_zero (w := w))
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  change Real.exp (t / (w.mult : ℝ)) ^ w.mult * (∏ᶠ _v : NumberField.FinitePlace K, ‖(1 : LocalField K _v.maximalIdeal)‖) = _
  simp only [norm_one, finprod_one, mul_one]
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hm]

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineIdeleModulus_pos (a : HeckeIdeles K) : 0 < genuineIdeleModulus K a := by
  apply lt_of_le_of_ne _ (genuineIdeleModulus_ne_zero K a).symm
  unfold genuineIdeleModulus
  exact mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
    (finprod_nonneg fun _ => norm_nonneg _)

theorem genuineIdeleModulus_inv (a : HeckeIdeles K) :
    genuineIdeleModulus K a⁻¹ = (genuineIdeleModulus K a)⁻¹ := by
  have h := genuineIdeleModulus_mul K a a⁻¹
  have h1 : genuineIdeleModulus K 1 = 1 := by
    simpa only [map_one] using genuineIdeleModulus_principal K 1
  rw [mul_inv_cancel, h1] at h
  apply mul_left_cancel₀ (genuineIdeleModulus_ne_zero K a)
  rw [← h, mul_inv_cancel₀ (genuineIdeleModulus_ne_zero K a)]

/-- Compact representatives in actual ideles for every genuine modulus-one class.
The finite class representatives are normalized with the actual radial section. -/
theorem genuineNormOne_compact_representatives :
    ∃ S : Set (HeckeIdeles K), IsCompact S ∧
      ∀ a : HeckeIdeles K, genuineIdeleModulus K a = 1 →
        ∃ b ∈ S, (QuotientGroup.mk b : HeckeIdeleClasses K) = QuotientGroup.mk a := by
  classical
  obtain ⟨F, hF⟩ := genuineFiniteIdele_finite_class_reduction_valuations K
  obtain ⟨T, hT, hcover⟩ := genuineIntegralNormOne_compact_representatives K
  let w : NumberField.InfinitePlace K := NumberField.Units.dirichletUnitTheorem.w₀
  let B : HeckeIdeles K → HeckeIdeles K := fun b =>
    b * genuineSectionIdele K w (-Real.log (genuineIdeleModulus K b))
  have hB (b : HeckeIdeles K) : genuineIdeleModulus K (B b) = 1 := by
    dsimp [B]
    rw [genuineIdeleModulus_mul, genuineSectionIdele_modulus, Real.exp_neg,
      Real.exp_log (genuineIdeleModulus_pos K b)]
    exact mul_inv_cancel₀ (genuineIdeleModulus_ne_zero K b)
  let S := (fun p : HeckeIdeles K × HeckeIdeles K => p.1 * p.2) ''
    (T ×ˢ (B '' (F : Set (HeckeIdeles K))))
  have hS : IsCompact S :=
    (hT.prod ((F.finite_toSet.image B).isCompact)).image (continuous_fst.mul continuous_snd)
  refine ⟨S, hS, ?_⟩
  intro a ha
  obtain ⟨b, hb, x, hx⟩ := hF a
  let r := a * (B b)⁻¹ * (principalIdele K x)⁻¹
  have hr : genuineIdeleModulus K r = 1 := by
    dsimp [r]
    rw [genuineIdeleModulus_mul, genuineIdeleModulus_mul,
      genuineIdeleModulus_inv, genuineIdeleModulus_inv, ha, hB,
      genuineIdeleModulus_principal]
    norm_num
  have hv : ∀ v : FinitePrime K, Valued.v (r.val.2 v) = 1 := by
    intro v
    change Valued.v (a.val.2 v * (1 * b.inv.2 v) * (principalIdele K x).inv.2 v) = 1
    simpa only [one_mul] using hx v
  obtain ⟨c, hc, he⟩ := hcover r hr hv
  refine ⟨c * B b, ⟨(c, B b), ⟨hc, ⟨b, hb, rfl⟩⟩, rfl⟩, ?_⟩
  have hp : (QuotientGroup.mk (principalIdele K x) : HeckeIdeleClasses K) = 1 := by
    change principalIdele K x ∈ (QuotientGroup.mk' (principalIdeles K)).ker
    rw [QuotientGroup.ker_mk']
    exact ⟨x, rfl⟩
  rw [QuotientGroup.mk_mul, he]
  simp only [r, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hp, inv_one, mul_one]
  group
end MasulloGRH

/- Round 84: A76 actual logarithm and Haar consumers, with arithmetic compactness discharged below. -/
namespace MasulloGRH
open MeasureTheory Topology Filter
open NumberField.InfinitePlace.Completion
open scoped ENNReal NNReal
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)

instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

instance classMeasurableInv : MeasurableInv (HeckeIdeleClasses K) := by
  infer_instance
instance classMeasurableMul : MeasurableMul (HeckeIdeleClasses K) := by
  infer_instance

noncomputable def genuineIdeleLog (a : HeckeIdeles K) : ℂ :=
  (Real.log (genuineIdeleModulus K a) : ℂ)
/-- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]

/-- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
local-norm logarithm. This is not supplied by an abstract replacement norm. -/
noncomputable def genuineLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeles K →* Multiplicative ℂ where
  toFun a := Multiplicative.ofAdd (genuineIdeleLog K a)
  map_one' := by
    change genuineIdeleLog K 1 = 0
    simpa only [map_one] using genuineIdeleLog_principal K 1
  map_mul' a b := hadd a b

noncomputable def genuineClassLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeleClasses K →* Multiplicative ℂ :=
  QuotientGroup.lift (principalIdeles K) (genuineLogHom K hadd) (by
    rintro x ⟨a, rfl⟩
    exact genuineIdeleLog_principal K a)

noncomputable def genuineClassLog
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (x : HeckeIdeleClasses K) : ℂ :=
  Multiplicative.toAdd (genuineClassLogHom K hadd x)

theorem genuineClassLog_mk
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (a : HeckeIdeles K) :
    genuineClassLog K hadd (QuotientGroup.mk a) = genuineIdeleLog K a := rfl

theorem genuineClassLog_translate
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (g x : HeckeIdeleClasses K) :
    genuineClassLog K hadd (g⁻¹ * x) =
      genuineClassLog K hadd x - genuineClassLog K hadd g := by
  unfold genuineClassLog
  rw [map_mul, map_inv]
  change -Multiplicative.toAdd (genuineClassLogHom K hadd g) +
    Multiplicative.toAdd (genuineClassLogHom K hadd x) = _
  abel


theorem genuineArithmeticClassLog_continuous
    (hcont : Continuous (genuineIdeleLog K)) :
    Continuous (genuineClassLog K (genuineIdeleLog_add K)) := by
  exact hcont.quotient_lift _


noncomputable def integralFiniteAdele (x : ∀ v : FinitePrime K, v.adicCompletionIntegers K) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun v : FinitePrime K => LocalField K v)
    (fun v => (v.adicCompletionIntegers K : Set (LocalField K v))) Filter.cofinite x

theorem integralFiniteSet_open : IsOpen
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} := by
  have hr : {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} =
      Set.range (integralFiniteAdele K) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact fun v => (x v).property
  rw [hr]
  exact (RestrictedProduct.isOpenEmbedding_structureMap (fun v =>
    (Valued.isClopen_closedBall (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen)).isOpen_range

noncomputable def finiteNorm (a : HeckeIdeles K) : ℝ :=
  ∏ᶠ v : NumberField.FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem finiteNorm_mul (a b : HeckeIdeles K) :
    finiteNorm K (a*b) = finiteNorm K a * finiteNorm K b := by
  unfold finiteNorm
  have h (v : NumberField.FinitePlace K) :
      ‖(a*b).val.2 v.maximalIdeal‖ = ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ :=
    norm_mul _ _
  simp_rw [h]
  exact finprod_mul_distrib (genuineIdele_finite_norm_support K a)
    (genuineIdele_finite_norm_support K b)

theorem finiteNorm_one_of_integral (a : HeckeIdeles K)
    (ha : ∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1)
    (hi : ∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1) :
    finiteNorm K a = 1 := by
  have hn (v : FinitePrime K) : ‖a.val.2 v‖ = 1 := by
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm (ha v)
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right (hi v) _
        _ = _ := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  simp [finiteNorm, hn]

theorem finiteNorm_continuous : Continuous (finiteNorm K) := by
  let U : Set (HeckeIdeles K) := {a | (∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1) ∧
    (∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1)}
  have ho : IsOpen U := (integralFiniteSet_open K).preimage
    (continuous_snd.comp Units.continuous_val) |>.inter
      ((integralFiniteSet_open K).preimage (continuous_snd.comp Units.continuous_coe_inv))
  have h1 : (1 : HeckeIdeles K) ∈ U := by
    constructor <;> intro v <;> change Valued.v (1 : LocalField K v) ≤ 1 <;> simp
  rw [continuous_iff_continuousAt]
  intro a
  have hV : ∀ᶠ b in 𝓝 a, a⁻¹*b ∈ U :=
    ((ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1))
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [hV] with b hb
  have h := finiteNorm_one_of_integral K (a⁻¹*b) hb.1 hb.2
  have he := finiteNorm_mul K a (a⁻¹*b)
  simpa [h, mul_assoc] using he

theorem genuineIdeleModulus_continuous : Continuous (genuineIdeleModulus K) := by
  have h : Continuous (fun a : HeckeIdeles K =>
      ∏ w : NumberField.InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) := by fun_prop
  exact h.mul (finiteNorm_continuous K)

theorem genuineIdeleLog_continuous : Continuous (genuineIdeleLog K) := by
  exact Complex.continuous_ofReal.comp ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K))
noncomputable def genuineRealClassLog (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re

theorem genuineSectionIdele_log (w : NumberField.InfinitePlace K) (t : ℝ) :
    genuineIdeleLog K (genuineSectionIdele K w t) = (t : ℂ) := by
  simp only [genuineIdeleLog, genuineSectionIdele_modulus, Real.log_exp]

noncomputable def genuineSectionClass (w : NumberField.InfinitePlace K) (t : ℝ) :
    HeckeIdeleClasses K := QuotientGroup.mk (genuineSectionIdele K w t)

theorem genuineSectionClass_log (w : NumberField.InfinitePlace K) (t : ℝ) :
    genuineRealClassLog K (genuineSectionClass K w t) = t := by
  change (genuineIdeleLog K (genuineSectionIdele K w t)).re = t
  rw [genuineSectionIdele_log, Complex.ofReal_re]

theorem genuineRealAtPlace_continuous (w : NumberField.InfinitePlace K) :
    Continuous (genuineRealAtPlace K w) := by
  classical
  unfold genuineRealAtPlace
  split_ifs with h
  · exact (isometryEquivRealOfIsReal h).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm.continuous.comp
      Complex.continuous_ofReal

theorem genuineSectionIdele_continuous (w : NumberField.InfinitePlace K) :
    Continuous (genuineSectionIdele K w) := by
  classical
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun t : ℝ =>
      ((fun v => genuineRealAtPlace K v (if v = w then Real.exp (t / (w.mult : ℝ)) else 1)),
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro v
    by_cases h : v = w
    · simp only [h, if_true]
      exact (genuineRealAtPlace_continuous K v).comp
        (Real.continuous_exp.comp (continuous_id.div_const _))
    · simp only [h, if_false]
      exact continuous_const
  · change Continuous (fun t : ℝ =>
      ((fun v => genuineRealAtPlace K v (if v = w then Real.exp (-(t / (w.mult : ℝ))) else 1)),
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro v
    by_cases h : v = w
    · simp only [h, if_true]
      exact (genuineRealAtPlace_continuous K v).comp
        (Real.continuous_exp.comp (continuous_id.div_const _).neg)
    · simp only [h, if_false]
      exact continuous_const

theorem genuineSectionIdele_add (w : NumberField.InfinitePlace K) (s t : ℝ) :
    genuineSectionIdele K w (s+t) = genuineSectionIdele K w s * genuineSectionIdele K w t := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext v
    change genuineRealAtPlace K v (if v = w then _ else _) =
      genuineRealAtPlace K v (if v = w then _ else _) *
        genuineRealAtPlace K v (if v = w then _ else _)
    rw [← map_mul]
    congr 1
    split_ifs <;> simp [add_div, Real.exp_add]
  · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) = 1 * 1
    exact (one_mul _).symm

theorem genuineSectionClass_continuous (w : NumberField.InfinitePlace K) :
    Continuous (genuineSectionClass K w) :=
  QuotientGroup.continuous_mk.comp (genuineSectionIdele_continuous K w)

theorem genuineSectionClass_add (w : NumberField.InfinitePlace K) (s t : ℝ) :
    genuineSectionClass K w (s+t) = genuineSectionClass K w s * genuineSectionClass K w t := by
  change QuotientGroup.mk (genuineSectionIdele K w (s+t)) = _
  rw [genuineSectionIdele_add]
  rfl

theorem genuineRealClassLog_mul (x y : HeckeIdeleClasses K) :
    genuineRealClassLog K (x*y) = genuineRealClassLog K x + genuineRealClassLog K y := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_mul]
  rfl

theorem genuineRealClassLog_inv (x : HeckeIdeleClasses K) :
    genuineRealClassLog K x⁻¹ = -genuineRealClassLog K x := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_inv]
  rfl

theorem genuineRealClassLog_continuous : Continuous (genuineRealClassLog K) :=
  Complex.continuous_re.comp
    (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K))

abbrev GenuineNormOneClass := {x : HeckeIdeleClasses K // genuineRealClassLog K x = 0}

/-- The norm-one factor is the actual zero fiber of the arithmetic logarithm,
with its inherited quotient topology, rather than a replacement group. -/
noncomputable def genuineClassRadialHomeomorph (w : NumberField.InfinitePlace K) :
    HeckeIdeleClasses K ≃ₜ (GenuineNormOneClass K × ℝ) where
  toFun x := (⟨x * (genuineSectionClass K w (genuineRealClassLog K x))⁻¹, by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv, genuineSectionClass_log]
    exact add_neg_cancel _⟩, genuineRealClassLog K x)
  invFun p := p.1.val * genuineSectionClass K w p.2
  left_inv x := by
    dsimp
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  right_inv p := by
    rcases p with ⟨u,t⟩
    have h : genuineRealClassLog K (u.val * genuineSectionClass K w t) = t := by
      rw [genuineRealClassLog_mul, u.property, genuineSectionClass_log, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (u.val * genuineSectionClass K w t) *
        (genuineSectionClass K w (genuineRealClassLog K
          (u.val * genuineSectionClass K w t)))⁻¹ = u.val
      rw [h]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    · exact h
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_id.mul
        ((genuineSectionClass_continuous K w).comp (genuineRealClassLog_continuous K)).inv
    · exact genuineRealClassLog_continuous K
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((genuineSectionClass_continuous K w).comp continuous_snd)
noncomputable def genuineClassLogReal (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re


/-- Arithmetic compactness of the actual norm-one idele-class quotient. -/
theorem genuineNormOneClass_compact : CompactSpace (GenuineNormOneClass K) := by
  obtain ⟨S, hS, hcover⟩ := genuineNormOne_compact_representatives K
  have hq : IsCompact ((QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) '' S) :=
    hS.image QuotientGroup.continuous_mk
  have hc : IsClosed {x : HeckeIdeleClasses K | genuineRealClassLog K x = 0} :=
    isClosed_eq (genuineRealClassLog_continuous K) continuous_const
  have hs : {x : HeckeIdeleClasses K | genuineRealClassLog K x = 0} ⊆
      (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) '' S := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro a ha
    change Real.log (genuineIdeleModulus K a) = 0 at ha
    have hm : genuineIdeleModulus K a = 1 := by
      calc
        genuineIdeleModulus K a = Real.exp (Real.log (genuineIdeleModulus K a)) :=
          (Real.exp_log (genuineIdeleModulus_pos K a)).symm
        _ = 1 := by rw [ha, Real.exp_zero]
    obtain ⟨b, hb, he⟩ := hcover a hm
    exact ⟨b, hb, he⟩
  exact isCompact_iff_compactSpace.mp (hq.of_isClosed_subset hc hs)

theorem genuineLog_pushforward_addInvariant
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] :
    (Measure.map (genuineClassLogReal K) μ).IsAddLeftInvariant := by
  constructor
  intro t
  have hL : Measurable (genuineClassLogReal K) :=
    (genuineRealClassLog_continuous K).measurable
  have hs : Measurable (fun x : HeckeIdeleClasses K => genuineSectionClass K w t * x) :=
    (continuous_const.mul continuous_id).measurable
  have ht : Measurable (fun x : ℝ => t + x) :=
    (continuous_const.add continuous_id).measurable
  rw [Measure.map_map ht hL]
  have he : (fun x => t + x) ∘ genuineClassLogReal K =
      genuineClassLogReal K ∘ (fun x => genuineSectionClass K w t * x) := by
    funext x
    change t + genuineRealClassLog K x =
      genuineRealClassLog K (genuineSectionClass K w t * x)
    rw [genuineRealClassLog_mul, genuineSectionClass_log]
  rw [he, ← Measure.map_map hL hs, map_mul_left_eq_self]

theorem genuineLog_compact_preimage
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K) {S : Set ℝ} (hS : IsCompact S) :
    IsCompact ((genuineClassLogReal K) ⁻¹' S) := by
  have he : (genuineClassLogReal K) ⁻¹' S =
      (genuineClassRadialHomeomorph K w).symm ''
        ((Set.univ : Set (GenuineNormOneClass K)) ×ˢ S) := by
    ext x
    constructor
    · intro hx
      refine ⟨genuineClassRadialHomeomorph K w x, ?_,
        (genuineClassRadialHomeomorph K w).symm_apply_apply x⟩
      exact ⟨Set.mem_univ _, hx⟩
    · rintro ⟨⟨u,t⟩, ht, rfl⟩
      change genuineRealClassLog K (u.val * genuineSectionClass K w t) ∈ S
      rw [genuineRealClassLog_mul, u.property, genuineSectionClass_log, zero_add]
      exact ht.2
  rw [he]
  exact (isCompact_univ.prod hS).image (genuineClassRadialHomeomorph K w).symm.continuous

theorem genuineLog_pushforward_finiteOnCompacts
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (Measure.map (genuineClassLogReal K) μ) := by
  constructor
  intro S hS
  have hL : Measurable (genuineClassLogReal K) :=
    (genuineRealClassLog_continuous K).measurable
  rw [Measure.map_apply hL hS.isClosed.measurableSet]
  exact (genuineLog_compact_preimage K w hS).measure_lt_top

theorem genuineLog_pushforward_eq_smul_volume
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] :
    ∃ V : ℝ≥0, Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume := by
  letI := genuineLog_pushforward_addInvariant K w μ
  letI := genuineLog_pushforward_finiteOnCompacts K w μ
  refine ⟨(Measure.map (genuineClassLogReal K) μ).addHaarScalarFactor volume, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul _ volume

theorem genuineLog_pushforward_positive_unitSlab
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume := by
  obtain ⟨V, hpush⟩ := genuineLog_pushforward_eq_smul_volume K w μ
  have hL : Measurable (genuineClassLogReal K) :=
    (genuineRealClassLog_continuous K).measurable
  have hV : V ≠ 0 := by
    intro he
    apply hμ
    have h := congrArg (fun ν : Measure ℝ => ν Set.univ) hpush
    simpa [Measure.map_apply hL MeasurableSet.univ, he] using h
  refine ⟨V, pos_iff_ne_zero.mpr hV, ?_, hpush⟩
  have h := congrArg (fun ν : Measure ℝ => ν (Set.Ioc 0 1)) hpush
  simpa [Measure.map_apply hL measurableSet_Ioc] using h


/-- The actual arithmetic compactness supplies the previously missing Haar
pushforward premise. The measure remains an explicit invariant, compact-finite,
nonzero measure; its prescribed arithmetic normalization is a separate premise. -/
theorem genuineLog_pushforward_positive_unitSlab_arithmetic
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume := by
  letI := genuineNormOneClass_compact K
  exact genuineLog_pushforward_positive_unitSlab K w μ hμ
end MasulloGRH


/- Exact C85 definitions reused for the genuine coefficient norm. -/
open MeasureTheory
open scoped NNReal ENNReal
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K →* Circle :=
  QuotientGroup.lift (principalIdeles K) χ.character.toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact χ.trivial_on_principal a)

/-- The descended character is the original genuine idelic character. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (a : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk a) = χ.character a := rfl

noncomputable def genuineSpectralJet (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  ((classCharacter K χ x : ℂ) *
    Complex.exp (z * genuineClassLog K (genuineIdeleLog_add K) x)) *
      genuineClassLog K (genuineIdeleLog_add K) x ^ m


theorem genuineClassLog_eq_real_G (x : HeckeIdeleClasses K) :
    genuineClassLog K (genuineIdeleLog_add K) x = (genuineClassLogReal K x : ℂ) := by
  refine Quotient.inductionOn' x ?_
  intro a
  rfl

theorem genuineSpectralJet_norm (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineSpectralJet K χ z m x‖ =
      Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m := by
  unfold genuineSpectralJet
  rw [genuineClassLog_eq_real_G]
  simp [norm_pow, Complex.norm_exp, Complex.mul_re,
    Complex.norm_real, Real.norm_eq_abs]

noncomputable def genuineStripWeight (α : ℝ) (d : ℕ) (x : HeckeIdeleClasses K) : ℝ :=
  Real.exp (2 * α * |genuineClassLogReal K x|) * (1 + genuineClassLogReal K x ^ 2) ^ d

theorem genuineStripWeight_pos (α : ℝ) (d : ℕ) (x : HeckeIdeleClasses K) :
    0 < genuineStripWeight K α d x := by
  unfold genuineStripWeight
  positivity

/-- Exact squared reciprocal-weight coefficient density. Its integral is the
missing dual L2 norm in the actual global coefficient/trace calculation. -/
theorem genuineSpectralJet_dual_density (α : ℝ) (d : ℕ)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineSpectralJet K χ z m x /
      (Real.sqrt (genuineStripWeight K α d x) : ℂ)‖ ^ 2 =
    (Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m) ^ 2 /
      genuineStripWeight K α d x := by
  rw [norm_div, genuineSpectralJet_norm, div_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (le_of_lt (genuineStripWeight_pos K α d x))]


end MasulloGRH
open MeasureTheory
namespace Round89F
theorem stripBoundaryDensity_integrable (α b : ℝ) (hstrip : |b| ≤ α)
    (m d : ℕ) (hmd : m < d) :
    Integrable (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
  have hcont : Continuous (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  apply integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hq : 0 < 1+t^2 := by positivity
  have hq1 : 1 ≤ 1+t^2 := by nlinarith [sq_nonneg t]
  have hrew : (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d) =
      (Real.exp (2*b*t-2*α*|t|) * |t|^(2*m)) / (1+t^2)^d := by
    rw [Real.exp_sub, show 2*b*t = b*t+b*t by ring, Real.exp_add]
    rw [show 2*m = m*2 by omega, pow_mul]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrew, ← one_div]
  have hb : b*t ≤ |b| * |t| := by simpa [abs_mul] using le_abs_self (b*t)
  have hbt := mul_le_mul_of_nonneg_right hstrip (abs_nonneg t)
  have he : Real.exp (2*b*t-2*α*|t|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hp : |t|^(2*m) ≤ (1+t^2)^m := by
    rw [pow_mul, sq_abs]
    exact pow_le_pow_left₀ (sq_nonneg t) (by linarith) m
  apply (div_le_div_iff₀ (pow_pos hq d) hq).mpr
  calc
    _ ≤ (1+t^2)^m * (1+t^2) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_of_le_one_left (by positivity) he).trans hp) (le_of_lt hq)
    _ = (1+t^2)^(m+1) := (pow_succ _ _).symm
    _ ≤ 1 * (1+t^2)^d := by
      simpa only [one_mul] using (pow_le_pow_right₀ hq1 (show m+1 ≤ d by omega))

/-- Quantitative boundary coefficient cost, uniform in every m<d. -/
theorem boundary_dual_energy_le (α b : ℝ) (hstrip : |b| ≤ α)
    (m d : ℕ) (hmd : m < d) :
    (∫ t : ℝ, (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) ≤
      ∫ t : ℝ, (1+t^2)⁻¹ := by
  apply integral_mono (stripBoundaryDensity_integrable α b hstrip m d hmd)
    integrable_inv_one_add_sq
  intro t
  dsimp only
  have hq : 0 < 1+t^2 := by positivity
  have hq1 : 1 ≤ 1+t^2 := by nlinarith [sq_nonneg t]
  have hrew : (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d) =
      (Real.exp (2*b*t-2*α*|t|) * |t|^(2*m)) / (1+t^2)^d := by
    rw [Real.exp_sub, show 2*b*t = b*t+b*t by ring, Real.exp_add]
    rw [show 2*m = m*2 by omega, pow_mul]
    field_simp
  rw [hrew, ← one_div]
  have hb : b*t ≤ |b| * |t| := by simpa [abs_mul] using le_abs_self (b*t)
  have hbt := mul_le_mul_of_nonneg_right hstrip (abs_nonneg t)
  have he : Real.exp (2*b*t-2*α*|t|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hp : |t|^(2*m) ≤ (1+t^2)^m := by
    rw [pow_mul, sq_abs]
    exact pow_le_pow_left₀ (sq_nonneg t) (by linarith) m
  apply (div_le_div_iff₀ (pow_pos hq d) hq).mpr
  calc
    _ ≤ (1+t^2)^m * (1+t^2) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_of_le_one_left (by positivity) he).trans hp) (le_of_lt hq)
    _ = (1+t^2)^(m+1) := (pow_succ _ _).symm
    _ ≤ 1 * (1+t^2)^d := by
      simpa only [one_mul] using (pow_le_pow_right₀ hq1 (show m+1 ≤ d by omega))
end Round89F

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineSpectralJet_dual_energy_bound_arithmetic
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (α : ℝ) (d : ℕ) (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (hstrip : |z.re| ≤ α) (hmd : m < d) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume ∧
      Integrable (fun x => ‖genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)‖ ^ 2) μ ∧
      (∫ x, ‖genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)‖ ^ 2 ∂μ) ≤
        (V : ℝ) * ∫ t : ℝ, (1+t^2)⁻¹ := by
  obtain ⟨V, hV, hmass, hpush⟩ :=
    genuineLog_pushforward_positive_unitSlab_arithmetic K w μ hμ
  refine ⟨V, hV, hmass, hpush, ?_⟩
  let g : ℝ → ℝ := fun t => (Real.exp (z.re*t) * |t|^m)^2 /
    (Real.exp (2*α*|t|) * (1+t^2)^d)
  have hg : Continuous g := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  have hL : Continuous (genuineClassLogReal K) :=
    Complex.continuous_re.comp
      (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K))
  have hdens (x : HeckeIdeleClasses K) :
      ‖genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)‖ ^ 2 =
        g (genuineClassLogReal K x) := by
    simpa only [g, genuineStripWeight] using
      genuineSpectralJet_dual_density K α d χ z m x
  have hi : Integrable g (Measure.map (genuineClassLogReal K) μ) := by
    rw [hpush]
    exact (Round89F.stripBoundaryDensity_integrable α z.re hstrip m d hmd).smul_measure (by simp)
  constructor
  · simp_rw [hdens]
    exact (integrable_map_measure hg.aestronglyMeasurable hL.measurable.aemeasurable).mp hi
  · simp_rw [hdens]
    calc
      _ = ∫ t, g t ∂Measure.map (genuineClassLogReal K) μ :=
        (integral_map hL.measurable.aemeasurable hg.aestronglyMeasurable).symm
      _ = (V : ℝ) * ∫ t : ℝ, g t := by
        rw [hpush, integral_smul_measure]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Round89F.boundary_dual_energy_le α z.re hstrip m d hmd) V.property
end MasulloGRH

namespace Round91E
open MeasureTheory
open MasulloGRH

/-- Converts a proved energy estimate into an actual continuous functional,
without assuming a dual norm estimate. -/
theorem coefficient_functional_of_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℂ) (hg : AEStronglyMeasurable g μ)
    (hi : Integrable (fun x => ‖g x‖ ^ 2) μ) (B : ℝ)
    (hB : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ B) :
    ∃ L : Lp ℂ 2 μ →L[ℂ] ℂ,
      (∀ f, L f = ∫ x, inner ℂ (g x) (f x) ∂μ) ∧ ‖L‖ ^ 2 ≤ B := by
  have hm : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm hg).mpr hi
  let v := hm.toLp g
  refine ⟨innerSL ℂ v, ?_, ?_⟩
  · intro f
    rw [innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    simp only [v, hx]
  · rw [innerSL_apply_norm]
    have hin : Integrable (fun x => inner ℂ (v x) (v x)) μ := by
      apply hi.ofReal.congr
      filter_upwards [hm.coeFn_toLp] with x hx
      simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
    calc
      ‖v‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
        rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
          ← integral_re hin]
        apply integral_congr_ae
        filter_upwards [hm.coeFn_toLp] with x hx
        simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
      _ ≤ B := hB

/-- Genuine idele-class continuous dual-factor bound in the unitary L2
realization of the manuscript's weighted Hilbert space. Measurability is
explicit; no nuclearity, lift estimate, or summability is assumed. -/
theorem genuine_coefficient_functional_bound
    (K : Type*) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (α : ℝ) (d : ℕ) (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (hstrip : |z.re| ≤ α) (hmd : m < d)
    (hmeas : AEStronglyMeasurable (fun x =>
      genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)) μ) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      ∃ L : Lp ℂ 2 μ →L[ℂ] ℂ,
        (∀ f, L f = ∫ x, inner ℂ
          (genuineSpectralJet K χ z m x /
            (Real.sqrt (genuineStripWeight K α d x) : ℂ)) (f x) ∂μ) ∧
        ‖L‖ ^ 2 ≤ (V : ℝ) * ∫ t : ℝ, (1+t^2)⁻¹ := by
  obtain ⟨V, hV, hmass, _, hi, hb⟩ :=
    genuineSpectralJet_dual_energy_bound_arithmetic K w μ hμ α d χ z m hstrip hmd
  exact ⟨V, hV, hmass, coefficient_functional_of_energy μ _ hmeas hi _ hb⟩

end Round91E


/- Round 92 H review: exact A91 tail extension after shared arithmetic source. -/
namespace Round92H
open MeasureTheory MasulloGRH Round91E
/-- Correct bilinear coefficient convention for the manuscript pairing. -/
theorem bilinear_coefficient_functional_of_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g : X → ℂ) (hg : AEStronglyMeasurable g μ)
    (hi : Integrable (fun x => ‖g x‖ ^ 2) μ) (B : ℝ)
    (hB : (∫ x, ‖g x‖ ^ 2 ∂μ) ≤ B) :
    ∃ L : Lp ℂ 2 μ →L[ℂ] ℂ,
      (∀ f, L f = ∫ x, g x * f x ∂μ) ∧ ‖L‖ ^ 2 ≤ B := by
  obtain ⟨L, hL, hnorm⟩ := coefficient_functional_of_energy μ
    (fun x => star (g x)) hg.star (by simpa using hi) B (by simpa using hB)
  refine ⟨L, ?_, hnorm⟩
  intro f
  rw [hL]
  congr 1
  funext x
  simp [RCLike.inner_apply, mul_comm]


/-- The genuine bilinear coefficient functional, with its exact action on
weighted-L2 representatives. This controls a dual factor only. -/
theorem genuine_bilinear_coefficient_functional_bound
    (K : Type*) [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (α : ℝ) (d : ℕ) (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (hstrip : |z.re| ≤ α) (hmd : m < d)
    (hmeas : AEStronglyMeasurable (fun x =>
      genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)) μ) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      ∃ L : Lp ℂ 2 μ →L[ℂ] ℂ,
        (∀ F, L F = ∫ x,
          (genuineSpectralJet K χ z m x /
            (Real.sqrt (genuineStripWeight K α d x) : ℂ)) * F x ∂μ) ∧
        ‖L‖ ^ 2 ≤ (V : ℝ) * Real.pi ∧
        ∀ (f : HeckeIdeleClasses K → ℂ)
          (hf : MemLp (fun x =>
            (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ),
          L (hf.toLp (fun x =>
            (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x)) =
            ∫ x, f x * genuineSpectralJet K χ z m x ∂μ := by
  obtain ⟨V, hV, hmass, _, hi, hb⟩ :=
    genuineSpectralJet_dual_energy_bound_arithmetic K v μ hμ α d χ z m hstrip hmd
  obtain ⟨L, hL, hnorm⟩ := bilinear_coefficient_functional_of_energy μ
    (fun x => genuineSpectralJet K χ z m x /
      (Real.sqrt (genuineStripWeight K α d x) : ℂ)) hmeas hi _ hb
  refine ⟨V, hV, hmass, L, hL, ?_, ?_⟩
  · simpa only [integral_univ_inv_one_add_sq] using hnorm
  · intro f hf
    rw [hL]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    have hn : (Real.sqrt (genuineStripWeight K α d x) : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (genuineStripWeight_pos K α d x))
    calc
      _ = ((genuineSpectralJet K χ z m x /
          (Real.sqrt (genuineStripWeight K α d x) : ℂ)) *
          (Real.sqrt (genuineStripWeight K α d x) : ℂ)) * f x :=
        (mul_assoc _ _ _).symm
      _ = genuineSpectralJet K χ z m x * f x := by rw [div_mul_cancel₀ _ hn]
      _ = _ := mul_comm _ _

end Round92H


namespace Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Riesz-normalized lift for one coefficient. Its norm is controlled
by the reciprocal of the coefficient vector's norm, not by an upper
bound on that norm. -/
noncomputable def canonicalLift (v : H) : H :=
  ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ • v

/-- Exact normalization of the actual Riesz lift. -/
theorem canonicalLift_pairing (v : H) (hv : v ≠ 0) :
    inner ℂ v (canonicalLift v) = 1 := by
  rw [canonicalLift, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have hn : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  simpa only [Complex.ofReal_pow] using inv_mul_cancel₀ hn

/-- The exact primal cost; an upper dual bound cannot give this upper cost. -/
theorem canonicalLift_norm (v : H) :
    ‖canonicalLift v‖ = ‖v‖⁻¹ := by
  rw [canonicalLift, norm_smul, norm_inv]
  have hn : ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ = ‖v‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v‖)]
  rw [hn]
  by_cases hv : ‖v‖ = 0
  · simp [hv]
  · field_simp

/-- Quantitative minimum-norm property, without a lift-bound hypothesis. -/
theorem canonicalLift_minimal (v u : H) (hu : inner ℂ v u = 1) :
    ‖canonicalLift v‖ ≤ ‖u‖ := by
  have h : 1 ≤ ‖v‖ * ‖u‖ := by
    simpa [hu] using norm_inner_le_norm (𝕜 := ℂ) v u
  have hv : 0 < ‖v‖ := by
    have := norm_nonneg u
    have := norm_nonneg v
    nlinarith
  rw [canonicalLift_norm, inv_eq_one_div]
  exact (div_le_iff₀ hv).mpr (by nlinarith)

/-- Exact smoothed rank-one cost; this exhibits the denominator the
actual global lift estimate must control. -/
theorem canonicalLift_smoothed_cost (A : H →L[ℂ] H) (v : H) :
    ‖A (canonicalLift v)‖ * ‖innerSL ℂ v‖ = ‖A v‖ / ‖v‖ := by
  rw [canonicalLift, map_smul, norm_smul, norm_inv, innerSL_apply_norm]
  have hn : ‖((‖v‖ ^ 2 : ℝ) : ℂ)‖ = ‖v‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖v‖)]
  rw [hn]
  by_cases hv : ‖v‖ = 0
  · simp [hv]
  · field_simp

end Round93H

namespace Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a genuine orthogonal residual r of a coefficient vector v, this
is the required simultaneous normalization. Orthogonality, not a bound,
is the hypothesis. Apply with r=v-Qv for the closed span of other jets. -/
theorem residualLift_pairing (v r : H) (hr : r ≠ 0)
    (hortho : inner ℂ (v-r) r = 0) :
    inner ℂ v (canonicalLift r) = 1 := by
  have h : inner ℂ v r = inner ℂ r r := by
    rw [inner_sub_left] at hortho
    exact sub_eq_zero.mp hortho
  rw [canonicalLift, inner_smul_right, h]
  simpa only [canonicalLift, inner_smul_right] using canonicalLift_pairing r hr

/-- The coefficient vector's orthogonal residual determines the exact
smoothed rank-one cost, exposing the inverse-Gram conditioning factor. -/
theorem residualLift_smoothed_cost (A : H →L[ℂ] H) (v r : H) :
    ‖A (canonicalLift r)‖ * ‖innerSL ℂ v‖ =
      ‖A r‖ * ‖v‖ / ‖r‖^2 := by
  rw [canonicalLift, map_smul, norm_smul, norm_inv, innerSL_apply_norm]
  have hn : ‖((‖r‖ ^ 2 : ℝ) : ℂ)‖ = ‖r‖ ^ 2 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖r‖)]
  rw [hn]
  ring

end Round93H


namespace Round93H
open MeasureTheory MasulloGRH

/-- The coefficient vectors whose orthogonal residuals determine the
actual lift conditioning. Arithmetic energy is proved in the reused source.
This does not assert that the residuals have a uniform positive norm. -/
theorem genuine_coefficient_residual_cost
    (K : Type*) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (α : ℝ) (d : ℕ) (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (hstrip : |z.re| ≤ α) (hmd : m < d)
    (hmeas : AEStronglyMeasurable (fun x =>
      genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)) μ) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      ∃ v : Lp ℂ 2 μ,
        (∀ F, inner ℂ v F = ∫ x,
          (genuineSpectralJet K χ z m x /
            (Real.sqrt (genuineStripWeight K α d x) : ℂ)) * F x ∂μ) ∧
        ‖v‖ ^ 2 ≤ (V : ℝ) * Real.pi ∧
        ∀ (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : Lp ℂ 2 μ),
          ‖A (canonicalLift r)‖ * ‖innerSL ℂ v‖ =
            ‖A r‖ * ‖v‖ / ‖r‖^2 := by
  obtain ⟨V, hV, hmass, _, hi, hb⟩ :=
    genuineSpectralJet_dual_energy_bound_arithmetic K w μ hμ α d χ z m hstrip hmd
  let g := fun x => genuineSpectralJet K χ z m x /
    (Real.sqrt (genuineStripWeight K α d x) : ℂ)
  have hm : MemLp (fun x => star (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hmeas.star).mpr (by simpa [g] using hi)
  let v := hm.toLp (fun x => star (g x))
  have hv (F : Lp ℂ 2 μ) : inner ℂ v F = ∫ x, g x * F x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    change inner ℂ ((hm.toLp (fun x => star (g x))) x) (F x) = _
    rw [hx]
    change F x * star (star (g x)) = g x * F x
    rw [star_star, mul_comm]
  obtain ⟨L, hL, hnorm⟩ := Round92H.bilinear_coefficient_functional_of_energy
    μ g hmeas hi _ hb
  have hLv : L = innerSL ℂ v := by
    ext F
    rw [hL, innerSL_apply_apply, hv]
  refine ⟨V, hV, hmass, v, hv, ?_, ?_⟩
  · rw [hLv, innerSL_apply_norm] at hnorm
    simpa only [integral_univ_inv_one_add_sq] using hnorm
  · intro A r
    exact residualLift_smoothed_cost A v r

end Round93H

#check Round93H.genuine_coefficient_residual_cost
#print axioms Round93H.genuine_coefficient_residual_cost

namespace Round95H
open Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable def orthogonalResidual (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v : H) : H := v - M.starProjection v

 theorem orthogonalResidual_mem (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v : H) : orthogonalResidual M v ∈ Mᗮ :=
  Submodule.sub_starProjection_mem_orthogonal v

 theorem orthogonalResidual_pairing (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v u : H) (hu : u ∈ Mᗮ) :
    inner ℂ (orthogonalResidual M v) u = inner ℂ v u := by
  have hp := (M.mem_orthogonal u).mp hu (M.starProjection v)
    (M.starProjection_apply_mem v)
  simp only [orthogonalResidual, inner_sub_left, hp, sub_zero]

 theorem orthogonalResidual_nonzero_of_lift (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v u : H) (hu : u ∈ Mᗮ)
    (hvu : inner ℂ v u = 1) : orthogonalResidual M v ≠ 0 := by
  have h := orthogonalResidual_pairing M v u hu
  rw [hvu] at h
  intro hz
  rw [hz, inner_zero_left] at h
  exact zero_ne_one h

 theorem orthogonalResidualLift_pairing (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v : H) (hr : orthogonalResidual M v ≠ 0) :
    inner ℂ v (canonicalLift (orthogonalResidual M v)) = 1 := by
  apply residualLift_pairing v _ hr
  have h := (M.mem_orthogonal (orthogonalResidual M v)).mp
    (orthogonalResidual_mem M v) (M.starProjection v) (M.starProjection_apply_mem v)
  have he : v - orthogonalResidual M v = M.starProjection v := by
    unfold orthogonalResidual
    abel
  rw [he]
  exact h

 theorem orthogonalResidualLift_annihilates (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v w : H) (hw : w ∈ M) :
    inner ℂ w (canonicalLift (orthogonalResidual M v)) = 0 := by
  have h := (M.mem_orthogonal (orthogonalResidual M v)).mp
    (orthogonalResidual_mem M v) w hw
  simp only [canonicalLift, inner_smul_right, h, mul_zero]

 theorem orthogonalResidualLift_minimal (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v u : H) (hu : u ∈ Mᗮ)
    (hvu : inner ℂ v u = 1) :
    ‖canonicalLift (orthogonalResidual M v)‖ ≤ ‖u‖ := by
  apply canonicalLift_minimal
  rw [orthogonalResidual_pairing M v u hu, hvu]

 theorem orthogonalResidualLift_exact_cost (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (A : H →L[ℂ] H) (v : H) :
    ‖A (canonicalLift (orthogonalResidual M v))‖ * ‖innerSL ℂ v‖ =
      ‖A (orthogonalResidual M v)‖ * ‖v‖ / ‖orthogonalResidual M v‖^2 :=
  residualLift_smoothed_cost A v (orthogonalResidual M v)

#check orthogonalResidual_nonzero_of_lift
#print axioms orthogonalResidual_nonzero_of_lift
#check orthogonalResidualLift_pairing
#print axioms orthogonalResidualLift_pairing
#check orthogonalResidualLift_annihilates
#print axioms orthogonalResidualLift_annihilates
#check orthogonalResidualLift_minimal
#print axioms orthogonalResidualLift_minimal
#check orthogonalResidualLift_exact_cost
#print axioms orthogonalResidualLift_exact_cost
end Round95H


namespace Round95H
open MeasureTheory MasulloGRH Round93H

/-- Genuine arithmetic coefficient with its constructed orthogonal-residual
lift. This isolates the exact analytic denominator; no summability follows. -/
theorem genuine_constructed_residual_lift
    (K : Type*) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (α : ℝ) (d : ℕ) (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (hstrip : |z.re| ≤ α) (hmd : m < d)
    (hmeas : AEStronglyMeasurable (fun x =>
      genuineSpectralJet K χ z m x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)) μ) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      ∃ v : Lp ℂ 2 μ,
        (∀ F, inner ℂ v F = ∫ x,
          (genuineSpectralJet K χ z m x /
            (Real.sqrt (genuineStripWeight K α d x) : ℂ)) * F x ∂μ) ∧
        ‖v‖ ^ 2 ≤ (V : ℝ) * Real.pi ∧
        ∀ (M : Submodule ℂ (Lp ℂ 2 μ)) [M.HasOrthogonalProjection],
          (orthogonalResidual M v ≠ 0 →
            inner ℂ v (canonicalLift (orthogonalResidual M v)) = 1) ∧
          (∀ q ∈ M, inner ℂ q (canonicalLift (orthogonalResidual M v)) = 0) ∧
          (∀ u ∈ Mᗮ, inner ℂ v u = 1 →
            ‖canonicalLift (orthogonalResidual M v)‖ ≤ ‖u‖) ∧
          (∀ A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ,
            ‖A (canonicalLift (orthogonalResidual M v))‖ * ‖innerSL ℂ v‖ =
              ‖A (orthogonalResidual M v)‖ * ‖v‖ / ‖orthogonalResidual M v‖^2) := by
  obtain ⟨V, hV, hmass, v, hv, hb, _⟩ :=
    genuine_coefficient_residual_cost K w μ hμ α d χ z m hstrip hmd hmeas
  refine ⟨V, hV, hmass, v, hv, hb, ?_⟩
  intro M inst
  exact ⟨orthogonalResidualLift_pairing M v,
    orthogonalResidualLift_annihilates M v,
    fun u hu hvu => orthogonalResidualLift_minimal M v u hu hvu,
    fun A => orthogonalResidualLift_exact_cost M A v⟩

#check genuine_constructed_residual_lift
#print axioms genuine_constructed_residual_lift
end Round95H

namespace Round95H
open Round93H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H] {ι : Type*}

noncomputable def otherCoefficientSpace (v : ι → H) (i : ι) : Submodule ℂ H :=
  (Submodule.span ℂ (v '' {j | j ≠ i})).topologicalClosure

noncomputable instance otherCoefficientSpace_hasProjection (v : ι → H) (i : ι) :
    (otherCoefficientSpace v i).HasOrthogonalProjection := by
  letI : CompleteSpace (otherCoefficientSpace v i) :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  infer_instance

omit [CompleteSpace H] in
 theorem otherCoefficient_mem (v : ι → H) (i j : ι) (hj : j ≠ i) :
    v j ∈ otherCoefficientSpace v i := by
  apply Submodule.le_topologicalClosure
  exact Submodule.subset_span ⟨j, hj, rfl⟩

 theorem all_other_coefficients_annihilated (v : ι → H) (i j : ι) (hj : j ≠ i) :
    inner ℂ (v j)
      (canonicalLift (orthogonalResidual (otherCoefficientSpace v i) (v i))) = 0 :=
  orthogonalResidualLift_annihilates _ _ _ (otherCoefficient_mem v i j hj)

 theorem residual_eq_zero_iff_closed_dependence (v : ι → H) (i : ι) :
    orthogonalResidual (otherCoefficientSpace v i) (v i) = 0 ↔
      v i ∈ otherCoefficientSpace v i := by
  rw [orthogonalResidual, sub_eq_zero, eq_comm]
  exact Submodule.starProjection_eq_self_iff

#check all_other_coefficients_annihilated
#print axioms all_other_coefficients_annihilated
#check residual_eq_zero_iff_closed_dependence
#print axioms residual_eq_zero_iff_closed_dependence
end Round95H


namespace Round96H
open Round93H Round95H
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The constructed all-label denominator is bounded by every approximation
from the other coefficient space. This controls the actual lift conditioning. -/
theorem residual_norm_le_distance (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v q : H) (hq : q ∈ M) :
    ‖orthogonalResidual M v‖ ≤ ‖v-q‖ := by
  by_cases hr : orthogonalResidual M v = 0
  · simp [hr]
  · have hp := orthogonalResidualLift_pairing M v hr
    have hz := orthogonalResidualLift_annihilates M v q hq
    have he : inner ℂ (v-q) (canonicalLift (orthogonalResidual M v)) = 1 := by
      rw [inner_sub_left, hp, hz, sub_zero]
    have hb : 1 ≤ ‖v-q‖ * ‖orthogonalResidual M v‖⁻¹ := by
      simpa only [he, norm_one, canonicalLift_norm] using
        norm_inner_le_norm (𝕜 := ℂ) (v-q) (canonicalLift (orthogonalResidual M v))
    have hn : 0 < ‖orthogonalResidual M v‖ := norm_pos_iff.mpr hr
    have hd : 1 * ‖orthogonalResidual M v‖ ≤ ‖v-q‖ :=
      (le_div_iff₀ hn).mp (by simpa only [div_eq_mul_inv] using hb)
    simpa only [one_mul] using hd

/-- No numerical lower bound on residuals is assumed. A nonzero residual
constructs the normalized lift and forces this exact separation cost. -/
theorem residualLift_separation_cost (M : Submodule ℂ H)
    [M.HasOrthogonalProjection] (v q : H) (hq : q ∈ M)
    (hr : orthogonalResidual M v ≠ 0) :
    1 ≤ ‖v-q‖ * ‖canonicalLift (orthogonalResidual M v)‖ := by
  have hp := orthogonalResidualLift_pairing M v hr
  have hz := orthogonalResidualLift_annihilates M v q hq
  have he : inner ℂ (v-q) (canonicalLift (orthogonalResidual M v)) = 1 := by
    rw [inner_sub_left, hp, hz, sub_zero]
  simpa only [he, norm_one] using
    norm_inner_le_norm (𝕜 := ℂ) (v-q) (canonicalLift (orthogonalResidual M v))

variable [CompleteSpace H] {ι : Type*}
theorem allLabel_residual_norm_le_pair_distance (v : ι → H) (i j : ι)
    (hj : j ≠ i) :
    ‖orthogonalResidual (otherCoefficientSpace v i) (v i)‖ ≤ ‖v i-v j‖ :=
  residual_norm_le_distance _ _ _ (otherCoefficient_mem v i j hj)

#check residual_norm_le_distance
#print axioms residual_norm_le_distance
#check residualLift_separation_cost
#print axioms residualLift_separation_cost
#check allLabel_residual_norm_le_pair_distance
#print axioms allLabel_residual_norm_le_pair_distance
end Round96H


namespace Round96H
open MeasureTheory Round93H Round95H MasulloGRH

/-- Exact energy of a difference of constructed coefficient vectors. -/
theorem coefficientVector_difference_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (g q : X → ℂ) (hg : MemLp g 2 μ) (hq : MemLp q 2 μ) :
    ‖hg.toLp g - hq.toLp q‖^2 = ∫ x, ‖g x-q x‖^2 ∂μ := by
  let v := hg.toLp g - hq.toLp q
  have hae : ∀ᵐ x ∂μ, v x = g x-q x := by
    filter_upwards [Lp.coeFn_sub (hg.toLp g) (hq.toLp q), hg.coeFn_toLp,
      hq.coeFn_toLp] with x hx hy hz
    exact hx.trans (by
      change (hg.toLp g) x - (hq.toLp q) x = _
      rw [hy, hz])
  have hi : Integrable (fun x => ‖g x-q x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (hg.aestronglyMeasurable.sub
      hq.aestronglyMeasurable)).mp (hg.sub hq)
  have hin : Integrable (fun x => inner ℂ (v x) (v x)) μ := by
    apply hi.ofReal.congr
    filter_upwards [hae] with x hx
    simp [hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  change ‖v‖^2 = _
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re hin]
  apply integral_congr_ae
  filter_upwards [hae] with x hx
  simp [hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Genuine arithmetic normalized coefficients, simultaneously constructed
in L2. The residual estimate is unconditional; nonvanishing is not claimed. -/
theorem genuine_allLabel_residual_energy
    (K : Type*) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (α : ℝ) (d : ℕ) {ι : Type*}
    (χ : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (hstrip : ∀ i, |(z i).re| ≤ α) (hmd : ∀ i, m i < d)
    (hmeas : ∀ i, AEStronglyMeasurable (fun x =>
      genuineSpectralJet K (χ i) (z i) (m i) x /
        (Real.sqrt (genuineStripWeight K α d x) : ℂ)) μ) :
    ∃ v : ι → Lp ℂ 2 μ,
      (∀ i F, inner ℂ (v i) F = ∫ x,
        (genuineSpectralJet K (χ i) (z i) (m i) x /
          (Real.sqrt (genuineStripWeight K α d x) : ℂ)) * F x ∂μ) ∧
      ∀ i j, j ≠ i →
        ‖orthogonalResidual (otherCoefficientSpace v i) (v i)‖^2 ≤
          ∫ x, ‖genuineSpectralJet K (χ i) (z i) (m i) x /
            (Real.sqrt (genuineStripWeight K α d x) : ℂ) -
            genuineSpectralJet K (χ j) (z j) (m j) x /
            (Real.sqrt (genuineStripWeight K α d x) : ℂ)‖^2 ∂μ := by
  let g : ι → HeckeIdeleClasses K → ℂ := fun i x =>
    genuineSpectralJet K (χ i) (z i) (m i) x /
      (Real.sqrt (genuineStripWeight K α d x) : ℂ)
  have hm (i : ι) : MemLp (fun x => star (g i x)) 2 μ := by
    obtain ⟨V, hV, hmass, hpush, hi, hb⟩ :=
      genuineSpectralJet_dual_energy_bound_arithmetic K w μ hμ α d
        (χ i) (z i) (m i) (hstrip i) (hmd i)
    exact (memLp_two_iff_integrable_sq_norm (hmeas i).star).mpr
      (by simpa [g] using hi)
  let v : ι → Lp ℂ 2 μ := fun i => (hm i).toLp (fun x => star (g i x))
  refine ⟨v, ?_, ?_⟩
  · intro i F
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hm i).coeFn_toLp] with x hx
    change inner ℂ (((hm i).toLp (fun x => star (g i x))) x) (F x) = _
    rw [hx]
    change F x * star (star (g i x)) = g i x * F x
    rw [star_star, mul_comm]
  · intro i j hj
    have hb := allLabel_residual_norm_le_pair_distance v i j hj
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have he := coefficientVector_difference_energy μ
      (fun x => star (g i x)) (fun x => star (g j x)) (hm i) (hm j)
    have he' : ‖v i-v j‖^2 = ∫ x, ‖g i x-g j x‖^2 ∂μ := by
      simpa only [v, ← star_sub, norm_star] using he
    exact he' ▸ hs

#check coefficientVector_difference_energy
#print axioms coefficientVector_difference_energy
#check genuine_allLabel_residual_energy
#print axioms genuine_allLabel_residual_energy
end Round96H
