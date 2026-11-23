import Mathlib
attribute [local instance] Classical.propDecidable

noncomputable section
open scoped NumberField Valued WithZero ENNReal NNReal
open NumberField MeasureTheory
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
noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖

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

namespace Masullo.IdeleClassGeometry
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable def classLog : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (fun y => Real.log (genuineIdeleModulus K y)) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    change Real.log (genuineIdeleModulus K x) = Real.log (genuineIdeleModulus K y)
    rw [hy, genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul])

end Masullo.IdeleClassGeometry
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)
instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩
end MasulloGRH

namespace MasulloGRH
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
abbrev FinitePrime := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
abbrev LocalField (v : FinitePrime K) := v.adicCompletion K
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

end MasulloGRH

namespace Masullo.WeightedIdeleClass
open MasulloGRH Masullo.IdeleClassGeometry MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Arithmetic logarithm on the actual idele-class quotient. -/
theorem classLog_mul (g x : HeckeIdeleClasses K) :
    classLog K (g * x) = classLog K g + classLog K x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  change Real.log (genuineIdeleModulus K (a*b)) = _
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b)]
  rfl

theorem classLog_continuous : Continuous (classLog K) :=
  ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K)).quotient_lift _

end Masullo.WeightedIdeleClass
end

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace NIdelicTopology

section Residue

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem isUnit_iff_valued_eq_one (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  have hv : (Valued.v : Valuation (v.adicCompletion K) _).Integers (v.adicCompletionIntegers K) :=
    ⟨Subtype.coe_injective, fun y => y.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  exact hv.isUnit_iff_valuation_eq_one

theorem denseRange_algebraMap : DenseRange (algebraMap K (v.adicCompletion K)) := by
  exact (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation K))).comp
    (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_valued_eq_one v, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_of_algebraMap, intValuation_eq_one_iff, not_not]

theorem exists_valuation_sub_lt_one (k : K) (hk : v.valuation K k ≤ 1) :
    ∃ r : R, v.valuation K (k - algebraMap (R) K r) < 1 := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (R)) k
  dsimp only at hab
  subst hab
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hspan : Ideal.span {(b : R)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb0
  have hfin := Ideal.finite_factors hspan
  have hn : ∀ w : HeightOneSpectrum (R),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) ≤ w.intValuation (b : R) := by
    intro w
    rw [intValuation_def, if_neg hb0]
    exact ⟨_, le_rfl⟩
  choose n hn using hn
  have hdist : ∀ i ∈ insert v hfin.toFinset, ∀ j ∈ insert v hfin.toFinset, i ≠ j →
      (fun w : HeightOneSpectrum (R) => w.asIdeal) i ≠ (fun w => w.asIdeal) j := by
    intro i _ j _ hij h
    exact hij (HeightOneSpectrum.ext h)
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v hfin.toFinset)
    (fun w : HeightOneSpectrum (R) => w.asIdeal)
    (fun w => if w = v then 1 else n w)
    (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime) hdist
    (fun w => if (w : HeightOneSpectrum (R)) = v then (1 : R) else 0)
  have hcv : c ∉ v.asIdeal := by
    intro hmem
    have h1 := hc v (Finset.mem_insert_self v _)
    simp at h1
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 := v.asIdeal.sub_mem hmem h1
    simpa using h2
  have hcw : ∀ w ∈ hfin.toFinset, w ≠ v → c ∈ w.asIdeal ^ n w := by
    intro w hw hwv
    have h1 := hc w (Finset.mem_insert_of_mem hw)
    simpa [hwv] using h1
  have key : ∀ w : HeightOneSpectrum (R),
      w.valuation K (algebraMap (R) K c * IsLocalization.mk' K a b) ≤ 1 := by
    intro w
    have hvc : w.valuation K (algebraMap (R) K c) = w.intValuation c :=
      valuation_of_algebraMap w c
    rw [map_mul, hvc]
    by_cases hwv : w = v
    · rw [hwv, intValuation_eq_one_iff.mpr hcv, one_mul]
      exact hk
    · rw [valuation_of_mk']
      have hbne : w.intValuation (b : R) ≠ 0 := by
        exact intValuation_ne_zero w _ hb0
      by_cases hwS : w ∈ hfin.toFinset
      · have hc' : w.intValuation c ≤ w.intValuation (b : R) :=
          ((intValuation_le_pow_iff_mem w c (n w)).mpr (hcw w hwS hwv)).trans (hn w)
        rw [div_eq_mul_inv]
        calc w.intValuation c * (w.intValuation a * (w.intValuation (b : R))⁻¹)
            ≤ w.intValuation (b : R) * (1 * (w.intValuation (b : R))⁻¹) := by
              exact mul_le_mul' hc' (mul_le_mul_left (intValuation_le_one w a) _)
          _ = 1 := by rw [one_mul, mul_inv_cancel₀ hbne]
      · have hb1 : w.intValuation (b : R) = 1 := by
          rw [intValuation_eq_one_iff]
          intro hmem
          exact hwS (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr hmem))
        rw [hb1, div_one]
        exact mul_le_one' (intValuation_le_one w c) (intValuation_le_one w a)
  obtain ⟨r', hr'⟩ := RingHom.mem_range.mp (mem_integers_of_valuation_le_one K _ key)
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hcv
  refine ⟨y * r', ?_⟩
  have hi' : i = 1 - y * c := by linear_combination hyi
  have hdiff : IsLocalization.mk' K a b - algebraMap (R) K (y * r') =
      IsLocalization.mk' K a b * algebraMap (R) K i := by
    rw [hi']
    simp only [map_mul, map_sub, map_one, hr']
    ring
  rw [hdiff, map_mul]
  have hvi : v.valuation K (algebraMap (R) K i) < 1 := (valuation_lt_one_iff_mem v i).mpr hi
  calc v.valuation K (IsLocalization.mk' K a b) * v.valuation K (algebraMap (R) K i)
      ≤ 1 * v.valuation K (algebraMap (R) K i) := by
        exact mul_le_mul_left hk _
    _ = v.valuation K (algebraMap (R) K i) := one_mul _
    _ < 1 := hvi


theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) :
    ∃ r : R, x - algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by

  have hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by
      exact hy⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1 := by
    rw [Valuation.map_sub_swap]; exact hk

  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (k : v.adicCompletion K) = (x : v.adicCompletion K) -
        ((x : v.adicCompletion K) - (k : v.adicCompletion K)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_one v k hk1
  refine ⟨r, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_valued_eq_one v]
  refine ne_of_lt ?_
  have hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1 := by
    have := valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r)
    exact this.trans_lt (by simpa using hr)
  have : ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) +
        algebraMap K (v.adicCompletion K) (k - algebraMap R K r) := by
    rw [map_sub]
    simp [algebraMap_adicCompletion]
  rw [this]
  exact Valuation.map_add_lt _ hk' hr'

noncomputable def toResidueFieldAdicCompletionIntegers :
    R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap R (v.adicCompletionIntegers K))

theorem ker_toResidueFieldAdicCompletionIntegers :
    RingHom.ker (toResidueFieldAdicCompletionIntegers (K := K) v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]

theorem toResidueFieldAdicCompletionIntegers_surjective :
    Function.Surjective (toResidueFieldAdicCompletionIntegers (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_maximalIdeal v x
  exact ⟨r, (Ideal.Quotient.eq.2 hr).symm⟩

noncomputable def residueFieldEquiv :
    (R ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_toResidueFieldAdicCompletionIntegers v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueFieldAdicCompletionIntegers_surjective v))

@[simp]
theorem residueFieldEquiv_mk (r : R) :
    residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) :=
  rfl

end Residue

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  Finite.of_equiv _ (residueFieldEquiv v).toEquiv

theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquiv v).toEquiv).symm

end NumberField

section Topology

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (Valued.isClopen_integer (v.adicCompletion K)).isClosed

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    (isClosed_adicCompletionIntegers v).completeSpace_coe
  have : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have h : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.2 h

instance : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)

instance : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_adicCompletionIntegers v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpen_adicCompletionIntegers v).mem_nhds (v.adicCompletionIntegers K).zero_mem)

instance : CompleteSpace (v.adicCompletionIntegers K) :=
  (isClosed_adicCompletionIntegers v).completeSpace_coe

end Topology

end NIdelicTopology
namespace NIdelicTopology
open IsDedekindDomain NumberField
variable (K : Type*) [Field K] [NumberField K]
instance finiteAdeleT2 : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite))
end NIdelicTopology

/- Adapted supplied ALPO source: GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean -/

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

abbrev IdeleGroup : Type _ := ((NumberField.AdeleRing (𝓞 K) K))ˣ

namespace IdeleGroup

theorem isEmbedding_val_inv :
    IsEmbedding (fun x : IdeleGroup K ↦ ((x : (NumberField.AdeleRing (𝓞 K) K)), ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)))) :=
  ((Homeomorph.refl ((NumberField.AdeleRing (𝓞 K) K))).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
    (Units.isEmbedding_embedProduct (M := (NumberField.AdeleRing (𝓞 K) K)))

example : IsTopologicalGroup (IdeleGroup K) := inferInstance

def prodEquiv :
    IdeleGroup K ≃ₜ* (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ where
  toMulEquiv := MulEquiv.prodUnits
  continuous_toFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_toFun
  continuous_invFun := (Homeomorph.prodUnits (α := InfiniteAdeleRing K)
    (β := FiniteAdeleRing (𝓞 K) K)).continuous_invFun

@[simp]
theorem prodEquiv_apply_fst (x : IdeleGroup K) :
    ((prodEquiv K x).1 : InfiniteAdeleRing K) = (x : (NumberField.AdeleRing (𝓞 K) K)).1 := rfl

@[simp]
theorem prodEquiv_apply_snd (x : IdeleGroup K) :
    ((prodEquiv K x).2 : FiniteAdeleRing (𝓞 K) K) = (x : (NumberField.AdeleRing (𝓞 K) K)).2 := rfl

def toInfinite : IdeleGroup K →* (InfiniteAdeleRing K)ˣ :=
  (MonoidHom.fst _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom

def toFinite : IdeleGroup K →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  (MonoidHom.snd _ _).comp (prodEquiv K).toMulEquiv.toMonoidHom

theorem continuous_toInfinite : Continuous (toInfinite K) :=
  continuous_fst.comp (prodEquiv K).continuous

theorem continuous_toFinite : Continuous (toFinite K) :=
  continuous_snd.comp (prodEquiv K).continuous

def diagonal : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom

@[simp]
theorem coe_diagonal (x : Kˣ) : ((diagonal K x : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)) = algebraMap K (NumberField.AdeleRing (𝓞 K) K) x :=
  rfl

theorem diagonal_injective : Function.Injective (diagonal K) := by
  intro x y h
  ext
  exact AdeleRing.algebraMap_injective (𝓞 K) K (congrArg Units.val h)

end IdeleGroup

abbrev IdeleClassGroup : Type _ := IdeleGroup K ⧸ (IdeleGroup.diagonal K).range

namespace IdeleClassGroup

example : CommGroup (IdeleClassGroup K) := inferInstance

example : IsTopologicalGroup (IdeleClassGroup K) := inferInstance

def mk : IdeleGroup K →* IdeleClassGroup K := QuotientGroup.mk' _

theorem continuous_mk : Continuous (mk K) := QuotientGroup.continuous_mk

theorem isOpenMap_mk : IsOpenMap (mk K) := QuotientGroup.isOpenMap_coe

theorem mk_surjective : Function.Surjective (mk K) := QuotientGroup.mk'_surjective _

theorem mk_diagonal (x : Kˣ) : mk K (IdeleGroup.diagonal K x) = 1 :=
  (QuotientGroup.eq_one_iff _).2 ⟨x, rfl⟩

theorem ker_mk : (mk K).ker = (IdeleGroup.diagonal K).range := QuotientGroup.ker_mk' _

end IdeleClassGroup

namespace IdeleGroup

section Finite

variable {K}

open Classical in

def finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := ⟨Pi.mulSingle v x, by
    have he : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ≠ v :=
      Filter.eventually_cofinite.mpr (by simp)
    filter_upwards [he] with w hw
    rw [Pi.mulSingle_eq_of_ne hw]
    exact one_mem _⟩
  map_one' := Subtype.ext (Pi.mulSingle_one (M := fun w : HeightOneSpectrum (𝓞 K) ↦
    w.adicCompletion K) v)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul v x y)

open Classical in
theorem finiteAdeleSingle_apply (v w : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingle v x w = Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 K) ↦
      u.adicCompletion K) v x w := rfl

@[simp]
theorem finiteAdeleSingle_apply_self (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAdeleSingle v x v = x := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_same v x

theorem finiteAdeleSingle_apply_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : v.adicCompletion K) : finiteAdeleSingle v x w = 1 := by
  classical
  rw [finiteAdeleSingle_apply]
  exact Pi.mulSingle_eq_of_ne h x

theorem continuous_finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteAdeleSingle (K := K) v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by
    simp
  let g : v.adicCompletion K → Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K]_[Filter.principal {v}ᶜ] :=
    fun x ↦ ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw ↦ by
      rw [Pi.mulSingle_eq_of_ne hw x]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have hfg : (finiteAdeleSingle (K := K) v : v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := by
    rfl
  rw [hfg]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

def finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod 1 (finiteAdeleSingle v) :
    v.adicCompletion K →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

def finiteProj (v : HeightOneSpectrum (𝓞 K)) : IdeleGroup K →* (v.adicCompletion K)ˣ :=
  Units.map (((RestrictedProduct.evalMonoidHom
      (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v).comp
    (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* v.adicCompletion K)

@[simp]
theorem coe_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((finiteEmbedding v x : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)) =
      (1, finiteAdeleSingle v (x : v.adicCompletion K)) :=
  rfl

@[simp]
theorem coe_finiteProj (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ((finiteProj v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (x : (NumberField.AdeleRing (𝓞 K) K)).2 v :=
  rfl

theorem continuous_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteEmbedding (K := K) v) :=
  Units.continuous_map (continuous_const.prodMk (continuous_finiteAdeleSingle v))

theorem continuous_finiteProj (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteProj (K := K) v) :=
  Units.continuous_map ((RestrictedProduct.continuous_eval v).comp continuous_snd)

@[simp]
theorem finiteProj_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    finiteProj v (finiteEmbedding v x) = x := by
  ext
  simp

theorem finiteProj_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteProj w (finiteEmbedding v x) = 1 := by
  ext
  simp [finiteAdeleSingle_apply_of_ne h]

@[simp]
theorem coe_finiteProj_diagonal (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    ((finiteProj v (diagonal K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((x : K) : v.adicCompletion K) :=
  rfl

end Finite

section Infinite

variable {K}

open Classical in

def infiniteAdeleSingle (w : InfinitePlace K) : w.Completion →* InfiniteAdeleRing K :=
  MonoidHom.mulSingle (fun u : InfinitePlace K ↦ u.Completion) w

omit [NumberField K] in
open Classical in
theorem infiniteAdeleSingle_apply (w u : InfinitePlace K) (x : w.Completion) :
    infiniteAdeleSingle w x u = Pi.mulSingle (M := fun u : InfinitePlace K ↦ u.Completion) w x u :=
  rfl

omit [NumberField K] in
theorem continuous_infiniteAdeleSingle (w : InfinitePlace K) :
    Continuous (infiniteAdeleSingle w) := by
  classical
  exact continuous_mulSingle (A := fun u : InfinitePlace K ↦ u.Completion) w

def infiniteEmbedding (w : InfinitePlace K) : (w.Completion)ˣ →* IdeleGroup K :=
  Units.map ((MonoidHom.prod (infiniteAdeleSingle w) 1 :
    w.Completion →* InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

def infiniteProj (w : InfinitePlace K) : IdeleGroup K →* (w.Completion)ˣ :=
  Units.map (((Pi.evalMonoidHom (fun u : InfinitePlace K ↦ u.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) :
    InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K →* w.Completion)

@[simp]
theorem coe_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((infiniteEmbedding w x : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)) =
      (infiniteAdeleSingle w (x : w.Completion), 1) :=
  rfl

@[simp]
theorem coe_infiniteProj (w : InfinitePlace K) (x : IdeleGroup K) :
    ((infiniteProj w x : (w.Completion)ˣ) : w.Completion) = (x : (NumberField.AdeleRing (𝓞 K) K)).1 w :=
  rfl

theorem continuous_infiniteEmbedding (w : InfinitePlace K) :
    Continuous (infiniteEmbedding (K := K) w) :=
  Units.continuous_map ((continuous_infiniteAdeleSingle w).prodMk continuous_const)

theorem continuous_infiniteProj (w : InfinitePlace K) :
    Continuous (infiniteProj (K := K) w) :=
  Units.continuous_map ((continuous_apply w).comp continuous_fst)

@[simp]
theorem infiniteProj_infiniteEmbedding (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    infiniteProj w (infiniteEmbedding w x) = x := by
  classical
  ext
  simp [infiniteAdeleSingle_apply]

theorem infiniteProj_infiniteEmbedding_of_ne {w u : InfinitePlace K} (h : u ≠ w)
    (x : (w.Completion)ˣ) : infiniteProj u (infiniteEmbedding w x) = 1 := by
  classical
  ext
  simp [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne h]

@[simp]
theorem coe_infiniteProj_diagonal (w : InfinitePlace K) (x : Kˣ) :
    ((infiniteProj w (diagonal K x) : (w.Completion)ˣ) : w.Completion) =
      ((x : K) : w.Completion) :=
  rfl

end Infinite

def integralAtFinite : Submonoid (NumberField.AdeleRing (𝓞 K) K) where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K}
  one_mem' v := one_mem (v.adicCompletionIntegers K)
  mul_mem' ha hb v := mul_mem (ha v) (hb v)

theorem mem_integralAtFinite {a : (NumberField.AdeleRing (𝓞 K) K)} :
    a ∈ integralAtFinite K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem isOpen_integralAtFinite : IsOpen (integralAtFinite K : Set (NumberField.AdeleRing (𝓞 K) K)) :=
  (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 K) ↦
    Valued.isOpen_valuationSubring (v.adicCompletion K)).preimage continuous_snd

def standardOpenSubgroup : Subgroup (IdeleGroup K) := (integralAtFinite K).units

theorem mem_standardOpenSubgroup {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      (x : (NumberField.AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ∧
        ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K := by
  rw [standardOpenSubgroup, Submonoid.mem_units_iff, mem_integralAtFinite, mem_integralAtFinite,
    ← forall_and]

theorem isOpen_standardOpenSubgroup : IsOpen (standardOpenSubgroup K : Set (IdeleGroup K)) :=
  Submonoid.isOpen_units (isOpen_integralAtFinite K)

end IdeleGroup

end

end GroundTheory.Global

/- Adapted supplied ALPO source: GroundTheory/GlobalFields/IdeleGroups/IdeleNorms.lean -/

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology Filter
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

variable {K}

@[simp] theorem adele_fst_mul_apply (a b : (NumberField.AdeleRing (𝓞 K) K)) (w : InfinitePlace K) :
    (a * b).1 w = a.1 w * b.1 w := rfl

@[simp] theorem adele_snd_mul_apply (a b : (NumberField.AdeleRing (𝓞 K) K)) (v : HeightOneSpectrum (𝓞 K)) :
    (a * b).2 v = a.2 v * b.2 v := rfl

@[simp] theorem adele_fst_one_apply (w : InfinitePlace K) : (1 : (NumberField.AdeleRing (𝓞 K) K)).1 w = 1 := rfl

@[simp] theorem adele_snd_one_apply (v : HeightOneSpectrum (𝓞 K)) : (1 : (NumberField.AdeleRing (𝓞 K) K)).2 v = 1 := rfl

theorem norm_eq_one_of_mul_eq_one {v : HeightOneSpectrum (𝓞 K)} {a b : v.adicCompletion K}
    (hab : a * b = 1) (ha : a ∈ v.adicCompletionIntegers K)
    (hb : b ∈ v.adicCompletionIntegers K) : ‖a‖ = 1 := by
  have ha' : ‖a‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 ha)
  have hb' : ‖b‖ ≤ 1 := (Valued.toNormedField.norm_le_one_iff).2
    ((HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 K) K v).1 hb)
  have h1 : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hab, norm_one]
  nlinarith [norm_nonneg a, norm_nonneg b]

theorem finite_mul_inv (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : (NumberField.AdeleRing (𝓞 K) K)).2 v *
      ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2 v = 1 :=
  congrArg (fun a : NumberField.AdeleRing (𝓞 K) K => a.2 v) x.val_inv

theorem infinite_mul_inv (x : IdeleGroup K) (w : InfinitePlace K) :
    (x : (NumberField.AdeleRing (𝓞 K) K)).1 w * ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).1 w = 1 := by
  have h : ((x : (NumberField.AdeleRing (𝓞 K) K)) * ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K))).1 w = 1 := by simp
  rwa [adele_fst_mul_apply] at h

theorem finite_ne_zero (x : IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    (x : (NumberField.AdeleRing (𝓞 K) K)).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (finite_mul_inv x v)

theorem infinite_ne_zero (x : IdeleGroup K) (w : InfinitePlace K) : (x : (NumberField.AdeleRing (𝓞 K) K)).1 w ≠ 0 :=
  left_ne_zero_of_mul_eq_one (infinite_mul_inv x w)

theorem eventually_norm_eq_one (x : IdeleGroup K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ‖(x : (NumberField.AdeleRing (𝓞 K) K)).2 v‖ = 1 := by
  filter_upwards [(x : (NumberField.AdeleRing (𝓞 K) K)).2.2, ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2.2] with v h1 h2
  exact norm_eq_one_of_mul_eq_one (finite_mul_inv x v) h1 h2

theorem finite_mulSupport_norm (x : IdeleGroup K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) ↦ ‖(x : (NumberField.AdeleRing (𝓞 K) K)).2 v‖).Finite :=
  Filter.eventually_cofinite.1 (eventually_norm_eq_one x)

def infiniteModule (x : IdeleGroup K) : ℝ :=
  ∏ w : InfinitePlace K, ‖(x : (NumberField.AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult

def finiteModule (x : IdeleGroup K) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : (NumberField.AdeleRing (𝓞 K) K)).2 v‖

theorem infiniteModule_mul (x y : IdeleGroup K) :
    infiniteModule (x * y) = infiniteModule x * infiniteModule y := by
  simp only [infiniteModule, Units.val_mul, adele_fst_mul_apply, norm_mul, mul_pow,
    Finset.prod_mul_distrib]

theorem finiteModule_mul (x y : IdeleGroup K) :
    finiteModule (x * y) = finiteModule x * finiteModule y := by
  simp only [finiteModule, Units.val_mul, adele_snd_mul_apply, norm_mul]
  exact finprod_mul_distrib (finite_mulSupport_norm x) (finite_mulSupport_norm y)

theorem infiniteModule_pos (x : IdeleGroup K) : 0 < infiniteModule x :=
  Finset.prod_pos fun w _ ↦ pow_pos (norm_pos_iff.2 (infinite_ne_zero x w)) _

theorem finiteModule_pos (x : IdeleGroup K) : 0 < finiteModule x := by
  rw [finiteModule, finprod_eq_prod _ (finite_mulSupport_norm x)]
  exact Finset.prod_pos fun v _ ↦ norm_pos_iff.2 (finite_ne_zero x v)

variable (K) in

def ideleModule : IdeleGroup K →* {r : ℝ // 0 < r} where
  toFun x := ⟨infiniteModule x * finiteModule x, mul_pos (infiniteModule_pos x) (finiteModule_pos x)⟩
  map_one' := by
    ext
    have hf (v : HeightOneSpectrum (𝓞 K)) :
        ‖(1 : FiniteAdeleRing (𝓞 K) K) v‖ = 1 := by
      change ‖(1 : v.adicCompletion K)‖ = 1
      exact norm_one
    simp [infiniteModule, finiteModule, hf]
  map_mul' x y := by
    ext
    simp only [Positive.val_mul, infiniteModule_mul, finiteModule_mul]
    ring

theorem ideleModule_apply (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = infiniteModule x * finiteModule x :=
  rfl

theorem ideleModule_eq (x : IdeleGroup K) :
    (ideleModule K x : ℝ) = (∏ w : InfinitePlace K, ‖(x : (NumberField.AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(x : (NumberField.AdeleRing (𝓞 K) K)).2 v‖ :=
  rfl

theorem continuous_infiniteModule : Continuous (infiniteModule (K := K)) := by
  unfold infiniteModule
  fun_prop

theorem finiteModule_eq_one_of_mem {x : IdeleGroup K} (hx : x ∈ standardOpenSubgroup K) :
    finiteModule x = 1 :=
  finprod_eq_one_of_forall_eq_one fun v ↦
    norm_eq_one_of_mul_eq_one (finite_mul_inv x v) ((mem_standardOpenSubgroup K).1 hx v).1
      ((mem_standardOpenSubgroup K).1 hx v).2

theorem continuous_finiteModule : Continuous (finiteModule (K := K)) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hU : (fun y ↦ x⁻¹ * y) ⁻¹' (standardOpenSubgroup K : Set (IdeleGroup K)) ∈ 𝓝 x :=
    ((isOpen_standardOpenSubgroup K).preimage (continuous_const.mul continuous_id)).mem_nhds
      (by simp [(standardOpenSubgroup K).one_mem])
  refine (continuousAt_const (y := finiteModule x)).congr ?_
  filter_upwards [hU] with y hy
  rw [← mul_inv_cancel_left x y, finiteModule_mul, finiteModule_eq_one_of_mem hy, mul_one]

theorem continuous_ideleModule : Continuous (ideleModule K) :=
  (continuous_infiniteModule.mul continuous_finiteModule).subtype_mk _

theorem ideleModule_infiniteEmbedding (w : InfinitePlace K) (z : (w.Completion)ˣ) :
    (ideleModule K (infiniteEmbedding w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  rw [ideleModule_eq, coe_infiniteEmbedding]
  have h1 : ∏ᶠ v : HeightOneSpectrum (𝓞 K),
      ‖((infiniteAdeleSingle w (z : w.Completion), (1 : FiniteAdeleRing (𝓞 K) K)) : (NumberField.AdeleRing (𝓞 K) K)).2 v‖
      = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ norm_one
  rw [h1, mul_one]
  refine (Fintype.prod_eq_single w fun u hu ↦ ?_).trans ?_
  · simp [infiniteAdeleSingle_apply, Pi.mulSingle_eq_of_ne hu]
  · simp [infiniteAdeleSingle_apply]

theorem ideleModule_finiteEmbedding (v : HeightOneSpectrum (𝓞 K)) (z : (v.adicCompletion K)ˣ) :
    (ideleModule K (finiteEmbedding v z) : ℝ) = ‖(z : v.adicCompletion K)‖ := by
  rw [ideleModule_eq, coe_finiteEmbedding]
  have h1 : ∏ w : InfinitePlace K,
      ‖((1 : InfiniteAdeleRing K), finiteAdeleSingle v (z : v.adicCompletion K)).1 w‖ ^ w.mult
      = 1 :=
    Finset.prod_eq_one fun w _ ↦ (by rw [norm_one, one_pow] : ‖(1 : w.Completion)‖ ^ w.mult = 1)
  rw [h1, one_mul]
  refine (finprod_eq_single _ v fun u hu ↦ ?_).trans ?_
  · simp [finiteAdeleSingle_apply_of_ne hu]
  · simp

theorem infiniteModule_diagonal (k : Kˣ) :
    infiniteModule (diagonal K k) = ∏ w : InfinitePlace K, w (k : K) ^ w.mult := by
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _

theorem finiteModule_diagonal (k : Kˣ) :
    finiteModule (diagonal K k) = ∏ᶠ w : FinitePlace K, w (k : K) := by
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  rfl

theorem ideleModule_diagonal (k : Kˣ) : ideleModule K (diagonal K k) = 1 := by
  refine Subtype.ext ?_
  rw [ideleModule_apply, infiniteModule_diagonal, finiteModule_diagonal, Positive.val_one]
  exact prod_abs_eq_one k.ne_zero

variable (K) in

def normOneSubgroup : Subgroup (IdeleGroup K) := (ideleModule K).ker

theorem mem_normOneSubgroup {x : IdeleGroup K} :
    x ∈ normOneSubgroup K ↔ (ideleModule K x : ℝ) = 1 := by
  rw [normOneSubgroup, MonoidHom.mem_ker]
  exact ⟨fun h ↦ by rw [h, Positive.val_one], fun h ↦ Subtype.ext (h.trans Positive.val_one.symm)⟩

variable (K) in

theorem isClosed_normOneSubgroup : IsClosed (normOneSubgroup K : Set (IdeleGroup K)) := by
  have h : (normOneSubgroup K : Set (IdeleGroup K)) =
      (fun x ↦ (ideleModule K x : ℝ)) ⁻¹' {1} := by
    ext x
    exact mem_normOneSubgroup
  rw [h]
  exact isClosed_singleton.preimage (continuous_subtype_val.comp continuous_ideleModule)

variable (K) in

theorem range_diagonal_le_normOneSubgroup : (diagonal K).range ≤ normOneSubgroup K := by
  rintro _ ⟨k, rfl⟩
  exact ideleModule_diagonal k

end IdeleGroup

namespace IdeleClassGroup

def ideleModule : IdeleClassGroup K →* {r : ℝ // 0 < r} :=
  QuotientGroup.lift _ (IdeleGroup.ideleModule K) (IdeleGroup.range_diagonal_le_normOneSubgroup K)

@[simp]
theorem ideleModule_mk (x : IdeleGroup K) :
    ideleModule K (mk K x) = IdeleGroup.ideleModule K x :=
  rfl

theorem continuous_ideleModule : Continuous (ideleModule K) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (IdeleGroup.continuous_ideleModule (K := K))

def normOneSubgroup : Subgroup (IdeleClassGroup K) := (ideleModule K).ker

theorem normOneSubgroup_eq_map :
    normOneSubgroup K = (IdeleGroup.normOneSubgroup K).map (mk K) := by
  ext c
  obtain ⟨x, rfl⟩ := mk_surjective K c
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    change ideleModule K (mk K x) = 1
    rw [← hyx]
    exact hy

end IdeleClassGroup

end

end GroundTheory.Global

namespace GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]
def integralFiniteAdeles (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Subring (FiniteAdeleRing R K) where
  carrier := {a | ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K}
  mul_mem' ha hb v := Subring.mul_mem _ (ha v) (hb v)
  one_mem' _ := Subring.one_mem _
  add_mem' ha hb v := Subring.add_mem _ (ha v) (hb v)
  zero_mem' _ := Subring.zero_mem _
  neg_mem' ha v := Subring.neg_mem _ (ha v)

theorem mem_integralFiniteAdeles {a : FiniteAdeleRing R K} :
    a ∈ integralFiniteAdeles R K ↔ ∀ v : HeightOneSpectrum R, a v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem isOpen_integralFiniteAdeles :
    IsOpen (integralFiniteAdeles R K : Set (FiniteAdeleRing R K)) :=
  RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem coe_mem_adicCompletionIntegers_iff (v : HeightOneSpectrum R) (k : K) :
    (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ v.valuation K k ≤ 1 := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']


end GroundTheory.Global
/- Adapted supplied ALPO source: GroundTheory/GlobalFields/IdeleGroups/UnitBound.lean -/

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology Filter NumberField.Units
  NumberField.Units.dirichletUnitTheorem
open scoped NumberField.AdeleRing RestrictedProduct

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

instance InfinitePlace.Completion.properSpace (w : InfinitePlace K) : ProperSpace w.Completion := by
  let _ : NontriviallyNormedField w.Completion :=
    { (inferInstance : NormedField w.Completion) with
      non_trivial := ⟨2, by
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) 2
        rw [map_ofNat] at h
        rw [← h]
        norm_num⟩ }
  exact ProperSpace.of_locallyCompactSpace w.Completion

theorem isCompact_integralFiniteAdeles :
    IsCompact (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) := by
  have : ∀ v : HeightOneSpectrum (𝓞 K),
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    isCompact_iff_compactSpace.1 (NIdelicTopology.isCompact_adicCompletionIntegers v)
  have hcont := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (𝓕 := Filter.cofinite)).continuous
  have h := isCompact_range hcont
  rw [RestrictedProduct.range_structureMap] at h
  exact h

namespace IdeleGroup

theorem abs_log_le_iff {r M : ℝ} (hr : 0 < r) :
    |Real.log r| ≤ M ↔ Real.exp (-M) ≤ r ∧ r ≤ Real.exp M := by
  rw [abs_le, neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (inv_pos.2 hr),
    Real.log_le_iff_le_exp hr, inv_le_comm₀ hr (Real.exp_pos _), Real.exp_neg]

omit [NumberField K] in

theorem isCompact_units_abs_log_le (w : InfinitePlace K) (M : ℝ) :
    IsCompact {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have h : ((↑) : (w.Completion)ˣ → w.Completion) ''
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M} =
      {c : w.Completion | Real.exp (-M) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp M} := by
    ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (abs_log_le_iff (norm_pos_iff.2 z.ne_zero)).1 hz
    · rintro ⟨h1, h2⟩
      have hc : c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le h1)
      exact ⟨Units.mk0 c hc, (abs_log_le_iff (norm_pos_iff.2 hc)).2 ⟨h1, h2⟩, rfl⟩
  rw [h]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : w.Completion)) (r := Real.exp M)).subset
      fun c hc ↦ by simpa using hc.2

omit [NumberField K] in

theorem isCompact_infinite_abs_log_le (M : ℝ) :
    IsCompact {y : (InfiniteAdeleRing K)ˣ |
      ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} := by
  let p := (ContinuousMulEquiv.piUnits :
    (InfiniteAdeleRing K)ˣ ≃ₜ* ∀ w : InfinitePlace K, (w.Completion)ˣ)
  have hc : IsCompact ((p ⁻¹' Set.univ.pi fun w ↦
      {z : (w.Completion)ˣ | |Real.log ‖(z : w.Completion)‖| ≤ M}) : Set (InfiniteAdeleRing K)ˣ) :=
    p.toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi fun w ↦ isCompact_units_abs_log_le K w M)
  convert hc using 1
  ext y
  exact ⟨fun hy w _ ↦ hy w, fun hy w ↦ hy w (Set.mem_univ w)⟩

theorem isCompact_finite_units_integral :
    IsCompact {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
      (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
        ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
          v.adicCompletionIntegers K} := by
  have hI := isCompact_integralFiniteAdeles K
  have h : IsCompact ((integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) ×ˢ
      (MulOpposite.unop ⁻¹' (integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))) :=
    hI.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.2 hI)
  convert Units.isClosedEmbedding_embedProduct.isCompact_preimage h using 1
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
    MulOpposite.unop_op, SetLike.mem_coe, mem_integralFiniteAdeles, ← forall_and]

theorem isCompact_abs_log_le_inter_standardOpenSubgroup (M : ℝ) :
    IsCompact {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : (NumberField.AdeleRing (𝓞 K) K)).1 w‖| ≤ M) ∧
      x ∈ standardOpenSubgroup K} := by
  let e := prodEquiv K
  have hc : IsCompact (e ⁻¹'
      ({y : (InfiniteAdeleRing K)ˣ |
        ∀ w : InfinitePlace K, |Real.log ‖(y : InfiniteAdeleRing K) w‖| ≤ M} ×ˢ
      {f : (FiniteAdeleRing (𝓞 K) K)ˣ | ∀ v : HeightOneSpectrum (𝓞 K),
        (f : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K ∧
          ((f⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v ∈
            v.adicCompletionIntegers K})) :=
    e.toHomeomorph.isCompact_preimage.2
      ((isCompact_infinite_abs_log_le K M).prod (isCompact_finite_units_integral K))
  convert hc using 1
  ext x
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).1 h2⟩,
    fun ⟨h1, h2⟩ ↦ ⟨h1, (mem_standardOpenSubgroup K).2 h2⟩⟩

def unitsToUnits : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom

omit [NumberField K] in
@[simp]
theorem coe_unitsToUnits (u : (𝓞 K)ˣ) : ((unitsToUnits K u : Kˣ) : K) = ((u : 𝓞 K) : K) :=
  rfl

theorem diagonal_unitsToUnits_mem (u : (𝓞 K)ˣ) :
    diagonal K (unitsToUnits K u) ∈ standardOpenSubgroup K := by
  rw [mem_standardOpenSubgroup K]
  intro v
  refine ⟨(coe_mem_adicCompletionIntegers_iff v _).2 (HeightOneSpectrum.valuation_le_one v _),
    ?_⟩
  rw [← map_inv]
  exact (coe_mem_adicCompletionIntegers_iff v _).2
    (HeightOneSpectrum.valuation_le_one v ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K))

theorem infiniteModule_diagonal_unitsToUnits (u : (𝓞 K)ˣ) :
    infiniteModule (diagonal K (unitsToUnits K u)) = 1 := by
  have h := congrArg Subtype.val (ideleModule_diagonal (unitsToUnits K u))
  rwa [ideleModule_apply, finiteModule_eq_one_of_mem (diagonal_unitsToUnits_mem K u), mul_one,
    Positive.val_one] at h

variable {K}

theorem norm_diagonal_mul (k : Kˣ) (y : IdeleGroup K) (w : InfinitePlace K) :
    ‖((diagonal K k * y : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).1 w‖ = w (k : K) * ‖(y : (NumberField.AdeleRing (𝓞 K) K)).1 w‖ := by
  rw [Units.val_mul, adele_fst_mul_apply, norm_mul]
  congr 1
  exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _

theorem log_infiniteModule (x : IdeleGroup K) :
    Real.log (infiniteModule x) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log ‖(x : (NumberField.AdeleRing (𝓞 K) K)).1 w‖ := by
  rw [infiniteModule, Real.log_prod fun w _ ↦ pow_ne_zero _ (norm_ne_zero_iff.2
    (infinite_ne_zero x w))]
  simp only [Real.log_pow]

def logVector (x : IdeleGroup K) : logSpace K :=
  fun w ↦ (w.1.mult : ℝ) * Real.log ‖(x : (NumberField.AdeleRing (𝓞 K) K)).1 w.1‖

theorem logVector_diagonal_mul (u : (𝓞 K)ˣ) (y : IdeleGroup K) :
    logVector (diagonal K (unitsToUnits K u) * y) =
      logEmbedding K (Additive.ofMul u) + logVector y := by
  ext w
  have hu : w.1 (((u : 𝓞 K) : K)) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 u.ne_zero
  rw [logVector, norm_diagonal_mul, coe_unitsToUnits,
    Real.log_mul hu (norm_ne_zero_iff.2 (infinite_ne_zero y w.1)),
    Pi.add_apply, logEmbedding_component, logVector, mul_add]

theorem exists_unit_forall_abs_log_le (M₀ : ℝ) : ∃ M : ℝ, ∀ y : IdeleGroup K,
    |Real.log (infiniteModule y)| ≤ M₀ → ∃ u : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log ‖((diagonal K (unitsToUnits K u) * y : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).1 w‖| ≤ M := by
  classical
  let B := (basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K)
  obtain ⟨C, hC⟩ := (ZSpan.fundamentalDomain_isBounded B).exists_norm_le
  set C' := max C 0 with hC'
  refine ⟨M₀ + Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' + C', fun y hy ↦ ?_⟩
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans hy
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨⟨e, he⟩, hmem, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain B (logVector y)
  rw [Module.Basis.ofZLatticeBasis_span ℝ (unitLattice K)] at he
  obtain ⟨u, -, rfl⟩ := he
  refine ⟨Additive.toMul u, ?_⟩
  set z := diagonal K (unitsToUnits K (Additive.toMul u)) * y with hz
  have hF : logVector z ∈ ZSpan.fundamentalDomain B := by
    rw [hz, logVector_diagonal_mul]
    exact hmem
  have hbound : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(w.1.mult : ℝ) * Real.log ‖(z : (NumberField.AdeleRing (𝓞 K) K)).1 w.1‖| ≤ C' := fun w ↦ by
    have := (norm_le_pi_norm (logVector z) w).trans (hC _ hF)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hmult : ∀ (w : InfinitePlace K) (t : ℝ), |t| ≤ |(w.mult : ℝ) * t| := fun w t ↦ by
    rw [abs_mul]
    exact le_mul_of_one_le_left (abs_nonneg t) (by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast w.mult_pos)
  have hmod : infiniteModule z = infiniteModule y := by
    rw [hz, infiniteModule_mul, infiniteModule_diagonal_unitsToUnits, one_mul]
  intro w
  by_cases hw : w = w₀
  · subst hw
    have hsum := log_infiniteModule z
    rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace K), hmod] at hsum
    have h1 : |∑ w : {w : InfinitePlace K // w ≠ w₀},
        (w.1.mult : ℝ) * Real.log ‖(z : (NumberField.AdeleRing (𝓞 K) K)).1 w.1‖| ≤
        Fintype.card {w : InfinitePlace K // w ≠ w₀} * C' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun w _ ↦ hbound w).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h2 : ((w₀ : InfinitePlace K).mult : ℝ) * Real.log ‖(z : (NumberField.AdeleRing (𝓞 K) K)).1 w₀‖ = Real.log (infiniteModule y) -
        ∑ w : {w : InfinitePlace K // w ≠ w₀},
          (w.1.mult : ℝ) * Real.log ‖(z : (NumberField.AdeleRing (𝓞 K) K)).1 w.1‖ := by
      linarith
    refine (hmult (w₀ : InfinitePlace K) _).trans ?_
    rw [h2]
    refine (abs_sub _ _).trans ?_
    linarith
  · refine (hmult w _).trans ((hbound ⟨w, hw⟩).trans ?_)
    have : 0 ≤ (Fintype.card {w : InfinitePlace K // w ≠ w₀} : ℝ) * C' :=
      mul_nonneg (Nat.cast_nonneg _) hC'0
    linarith

end IdeleGroup

end

end GroundTheory.Global

/- Adapted supplied ALPO source: GroundTheory/GlobalFields/IdeleGroups/ClassGroup.lean -/

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (coeIdeal_ne_zero.mpr v.ne_bot)

@[simp]
theorem coe_primeIdealUnit (v : HeightOneSpectrum (𝓞 K)) :
    ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) :=
  rfl

theorem fractionalIdealUnits_eq_iff {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    I = J ↔ ∀ v : HeightOneSpectrum (𝓞 K),
      count K v (I : FractionalIdeal (𝓞 K)⁰ K) = count K v (J : FractionalIdeal (𝓞 K)⁰ K) := by
  refine ⟨fun h v ↦ h ▸ rfl, fun h ↦ Units.ext ?_⟩
  rw [← finprod_heightOneSpectrum_factorization' (K := K) I.ne_zero,
    ← finprod_heightOneSpectrum_factorization' (K := K) J.ne_zero]
  exact finprod_congr fun v ↦ by rw [h v]

theorem coe_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ)
    (hn : ∀ᶠ v in Filter.cofinite, n v = 0) :
    ((∏ᶠ v, primeIdealUnit v ^ n v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n v := by
  have hfin : (Function.mulSupport fun v ↦ primeIdealUnit (K := K) v ^ n v).Finite :=
    (Filter.eventually_cofinite.1 hn).subset fun v hv h ↦ hv (by simp only [h, zpow_zero])
  rw [← Units.coeHom_apply, map_finprod _ hfin]
  exact finprod_congr fun v ↦ by simp [Units.val_zpow_eq_zpow_val]

theorem count_finprod_primeIdealUnit_zpow (n : HeightOneSpectrum (𝓞 K) → ℤ)
    (hn : ∀ᶠ v in Filter.cofinite, n v = 0) (v : HeightOneSpectrum (𝓞 K)) :
    count K v ((∏ᶠ w, primeIdealUnit w ^ n w : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = n v := by
  rw [coe_finprod_primeIdealUnit_zpow n hn, count_finprod K v n hn]

theorem finprod_primeIdealUnit_zpow_count (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∏ᶠ v, primeIdealUnit v ^ count K v (I : FractionalIdeal (𝓞 K)⁰ K) = I := by
  rw [fractionalIdealUnits_eq_iff]
  intro v
  exact count_finprod_primeIdealUnit_zpow _ (FractionalIdeal.finite_factors _) v

open Classical in
theorem count_primeIdealUnit (v w : HeightOneSpectrum (𝓞 K)) :
    count K w ((primeIdealUnit v : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      if w = v then 1 else 0 := by
  rw [coe_primeIdealUnit]
  split_ifs with h
  · subst h
    exact count_self K w
  · exact count_maximal_coprime K w (Ne.symm h)

theorem count_spanSingleton (v : HeightOneSpectrum (𝓞 K)) {a : K} (ha : a ≠ 0) :
    count K v (spanSingleton (𝓞 K)⁰ a) = -log (v.valuation K a) := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at ha
  have hI : spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K d) =
      spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K d)⁻¹ * ↑(Ideal.span {n} : Ideal (𝓞 K)) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, div_eq_mul_inv, mul_comm]
  rw [count_well_defined K v ((spanSingleton_ne_zero_iff).2 ha) hI, map_div₀,
    valuation_of_algebraMap, valuation_of_algebraMap, intValuation_if_neg _ hn0,
    intValuation_if_neg _ hd0, ← exp_sub, log_exp]
  ring

namespace IdeleGroup

def ord (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ℤ :=
  -log (Valued.v ((x : (NumberField.AdeleRing (𝓞 K) K)).2 v))

theorem valued_ne_zero (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    Valued.v ((x : (NumberField.AdeleRing (𝓞 K) K)).2 v) ≠ 0 :=
  (Valuation.ne_zero_iff _).2 (finiteProj v x).ne_zero

theorem ord_mul (v : HeightOneSpectrum (𝓞 K)) (x y : IdeleGroup K) :
    ord v (x * y) = ord v x + ord v y := by
  have h : ((x * y : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2 v = (x : (NumberField.AdeleRing (𝓞 K) K)).2 v * (y : (NumberField.AdeleRing (𝓞 K) K)).2 v := rfl
  rw [ord, ord, ord, h, map_mul, log_mul (valued_ne_zero v x) (valued_ne_zero v y), neg_add]

@[simp]
theorem ord_one (v : HeightOneSpectrum (𝓞 K)) : ord v (1 : IdeleGroup K) = 0 := by
  have h : ((1 : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2 v = 1 := rfl
  rw [ord, h, map_one, log_one, neg_zero]

theorem ord_inv (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) : ord v x⁻¹ = -ord v x := by
  have h := ord_mul v x x⁻¹
  rw [mul_inv_cancel, ord_one] at h
  omega

theorem mem_adicCompletionIntegers_iff_ord_nonneg (v : HeightOneSpectrum (𝓞 K))
    (x : IdeleGroup K) :
    (x : (NumberField.AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ↔ 0 ≤ ord v x := by
  rw [mem_adicCompletionIntegers, ord, neg_nonneg, log_le_iff_le_exp (valued_ne_zero v x),
    exp_zero]

theorem ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    ord v x = 0 ↔ (x : (NumberField.AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K := by
  rw [mem_adicCompletionIntegers_iff_ord_nonneg, mem_adicCompletionIntegers_iff_ord_nonneg,
    ord_inv]
  omega

theorem eventually_ord_eq_zero (x : IdeleGroup K) :
    ∀ᶠ v in Filter.cofinite, ord v x = 0 :=
  ((x : (NumberField.AdeleRing (𝓞 K) K)).2.2.and ((x⁻¹ : IdeleGroup K) : (NumberField.AdeleRing (𝓞 K) K)).2.2).mono fun v hv ↦
    (ord_eq_zero_iff v x).2 hv

theorem mem_standardOpenSubgroup_iff_ord {x : IdeleGroup K} :
    x ∈ standardOpenSubgroup K ↔ ∀ v : HeightOneSpectrum (𝓞 K), ord v x = 0 := by
  simp only [mem_standardOpenSubgroup, ord_eq_zero_iff]

theorem ord_finiteEmbedding_self (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ) :
    ord v (finiteEmbedding v a) = -log (Valued.v (a : v.adicCompletion K)) := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding]

theorem ord_finiteEmbedding_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (a : (v.adicCompletion K)ˣ) : ord w (finiteEmbedding v a) = 0 := by
  rw [ord, ← coe_finiteProj, finiteProj_finiteEmbedding_of_ne h, Units.val_one, map_one, log_one,
    neg_zero]

theorem ord_diagonal (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ord v (diagonal K a) = -log (v.valuation K a) := by
  rw [ord, ← coe_finiteProj, coe_finiteProj_diagonal, valuedAdicCompletion_eq_valuation']

open Classical in

theorem exists_ord_eq_ite (v : HeightOneSpectrum (𝓞 K)) :
    ∃ x : IdeleGroup K, ∀ w, ord w x = if w = v then 1 else 0 := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hne : ((π : K) : v.adicCompletion K) ≠ 0 := by
    intro h
    have h' := congrArg Valued.v h
    rw [valuedAdicCompletion_eq_valuation', hπ, map_zero] at h'
    exact exp_ne_zero h'
  refine ⟨finiteEmbedding v (Units.mk0 _ hne), fun w ↦ ?_⟩
  split_ifs with h
  · subst h
    rw [ord_finiteEmbedding_self, Units.val_mk0, valuedAdicCompletion_eq_valuation', hπ, log_exp,
      neg_neg]
  · exact ord_finiteEmbedding_of_ne h _

theorem finite_mulSupport_primeIdealUnit_zpow_ord (x : IdeleGroup K) :
    (Function.mulSupport fun v ↦ primeIdealUnit (K := K) v ^ ord v x).Finite :=
  (Filter.eventually_cofinite.1 (eventually_ord_eq_zero x)).subset fun v hv h ↦
    hv (by simp only [h, zpow_zero])

def toFractionalIdeal : IdeleGroup K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun x := ∏ᶠ v, primeIdealUnit v ^ ord v x
  map_one' := by simp only [ord_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ord_mul, zpow_add]
    exact finprod_mul_distrib (finite_mulSupport_primeIdealUnit_zpow_ord x)
      (finite_mulSupport_primeIdealUnit_zpow_ord y)

@[simp]
theorem count_toFractionalIdeal (v : HeightOneSpectrum (𝓞 K)) (x : IdeleGroup K) :
    count K v ((toFractionalIdeal x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = ord v x :=
  count_finprod_primeIdealUnit_zpow _ (eventually_ord_eq_zero x) v

theorem toFractionalIdeal_eq_iff {x : IdeleGroup K} {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    toFractionalIdeal x = I ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ord v x = count K v (I : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [fractionalIdealUnits_eq_iff, count_toFractionalIdeal]

theorem ker_toFractionalIdeal :
    (toFractionalIdeal (K := K)).ker = standardOpenSubgroup K := by
  ext x
  rw [MonoidHom.mem_ker, toFractionalIdeal_eq_iff, mem_standardOpenSubgroup_iff_ord]
  simp only [Units.val_one, count_one]

open Classical in

theorem primeIdealUnit_mem_range (v : HeightOneSpectrum (𝓞 K)) :
    primeIdealUnit v ∈ (toFractionalIdeal (K := K)).range := by
  obtain ⟨x, hx⟩ := exists_ord_eq_ite v
  refine ⟨x, toFractionalIdeal_eq_iff.2 fun w ↦ ?_⟩
  rw [hx, count_primeIdealUnit]

theorem toFractionalIdeal_surjective : Function.Surjective (toFractionalIdeal (K := K)) := by
  intro I
  have h : I ∈ (toFractionalIdeal (K := K)).range := by
    rw [← finprod_primeIdealUnit_zpow_count I]
    exact finprod_induction (· ∈ (toFractionalIdeal (K := K)).range) (one_mem _)
      (fun _ _ ↦ mul_mem) fun v ↦ zpow_mem (primeIdealUnit_mem_range v) _
  exact h

theorem toFractionalIdeal_diagonal (a : Kˣ) :
    toFractionalIdeal (diagonal K a) = toPrincipalIdeal (𝓞 K) K a := by
  rw [toFractionalIdeal_eq_iff]
  intro v
  rw [ord_diagonal, coe_toPrincipalIdeal, count_spanSingleton v a.ne_zero]

theorem _root_.GroundTheory.Global.classGroup_mk_eq_one_iff {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} :
    ClassGroup.mk (K := K) I = 1 ↔ I ∈ (toPrincipalIdeal (𝓞 K) K).range := by
  rw [ClassGroup.mk_eq_one_iff, mem_principal_ideals_iff]
  constructor
  · intro hI
    obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal (S := (I : Submodule (𝓞 K) K))
    refine ⟨x, ?_⟩
    symm
    apply Subtype.coe_injective
    simp only [FractionalIdeal.val_eq_coe, hx, coe_spanSingleton]
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by rw [← hx, coe_spanSingleton]⟩⟩

theorem _root_.GroundTheory.Global.classGroup_mk_surjective :
    Function.Surjective (ClassGroup.mk (K := K) : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ClassGroup (𝓞 K)) :=
  fun c ↦ ClassGroup.induction K (P := fun c ↦ ∃ I, ClassGroup.mk (K := K) I = c) (fun I ↦ ⟨I, rfl⟩) c

def toClassGroup : IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk (K := K)).comp toFractionalIdeal

theorem toClassGroup_apply (x : IdeleGroup K) :
    toClassGroup x = ClassGroup.mk (K := K) (toFractionalIdeal x) :=
  rfl

theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) :=
  classGroup_mk_surjective.comp toFractionalIdeal_surjective

theorem ker_toClassGroup :
    (toClassGroup (K := K)).ker = (diagonal K).range ⊔ standardOpenSubgroup K := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker, toClassGroup_apply, classGroup_mk_eq_one_iff] at hx
    obtain ⟨a, ha⟩ := hx
    have hu : (diagonal K a)⁻¹ * x ∈ standardOpenSubgroup K := by
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, toFractionalIdeal_diagonal,
        ha, inv_mul_cancel]
    exact Subgroup.mem_sup.2 ⟨diagonal K a, ⟨a, rfl⟩, _, hu, mul_inv_cancel_left _ _⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker, toClassGroup_apply, toFractionalIdeal_diagonal,
        classGroup_mk_eq_one_iff]
      exact ⟨a, rfl⟩
    · intro x hx
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker] at hx
      rw [MonoidHom.mem_ker, toClassGroup_apply, hx, map_one]

def quotientEquivClassGroup :
    IdeleGroup K ⧸ ((diagonal K).range ⊔ standardOpenSubgroup K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq ker_toClassGroup.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)

@[simp]
theorem quotientEquivClassGroup_mk (x : IdeleGroup K) :
    quotientEquivClassGroup (QuotientGroup.mk x :
      IdeleGroup K ⧸ ((diagonal K).range ⊔ standardOpenSubgroup K)) =
      ClassGroup.mk (K := K) (toFractionalIdeal x) :=
  rfl

end IdeleGroup

namespace IdeleClassGroup

open IdeleGroup

def toClassGroup : IdeleClassGroup K →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ IdeleGroup.toClassGroup
    (le_sup_left.trans_eq (ker_toClassGroup (K := K)).symm)

@[simp]
theorem toClassGroup_mk (x : IdeleGroup K) :
    toClassGroup (mk K x) = IdeleGroup.toClassGroup x :=
  rfl

theorem toClassGroup_surjective : Function.Surjective (toClassGroup (K := K)) := by
  intro c
  obtain ⟨x, rfl⟩ := IdeleGroup.toClassGroup_surjective c
  exact ⟨mk K x, rfl⟩

theorem ker_toClassGroup :
    (toClassGroup (K := K)).ker = (standardOpenSubgroup K).map (mk K) := by
  ext c
  obtain ⟨x, rfl⟩ := mk_surjective K c
  rw [MonoidHom.mem_ker, toClassGroup_mk, ← MonoidHom.mem_ker, IdeleGroup.ker_toClassGroup]
  constructor
  · intro hx
    obtain ⟨_, ⟨a, rfl⟩, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨u, hu, by rw [map_mul, mk_diagonal]; exact (one_mul (mk K u)).symm⟩
  · rintro ⟨u, hu, h⟩
    have h1 : mk K (x * u⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, ker_mk] at h1
    rw [← inv_mul_cancel_right x u]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hu)

instance : ((standardOpenSubgroup K).map (mk K)).Normal :=
  ⟨fun n hn g ↦ by rwa [mul_comm g n, mul_inv_cancel_right]⟩

def quotientEquivClassGroup :
    IdeleClassGroup K ⧸ (standardOpenSubgroup K).map (mk K) ≃* ClassGroup (𝓞 K) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toClassGroup (K := K)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ toClassGroup_surjective)

end IdeleClassGroup

end

end GroundTheory.Global

/- Adapted supplied ALPO source: GroundTheory/GlobalFields/IdeleGroups/NormOneCompact.lean -/

namespace GroundTheory.Global

open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

namespace IdeleGroup

theorem exists_finset_mul_mem_standardOpenSubgroup :
    ∃ R : Finset (IdeleGroup K), ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K := by
  classical
  let s : ClassGroup (𝓞 K) → IdeleGroup K := Function.invFun toClassGroup
  refine ⟨Finset.univ.image s, fun x ↦ ?_⟩
  have hs : toClassGroup (s (toClassGroup x)) = toClassGroup x :=
    Function.invFun_eq (toClassGroup_surjective _)
  have hmem : x * (s (toClassGroup x))⁻¹ ∈ (diagonal K).range ⊔ standardOpenSubgroup K := by
    rw [← ker_toClassGroup, MonoidHom.mem_ker, map_mul, map_inv, hs, mul_inv_cancel]
  obtain ⟨_, ⟨k, rfl⟩, u, hu, hku⟩ := Subgroup.mem_sup.1 hmem
  refine ⟨k⁻¹, s (toClassGroup x), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [map_inv, mul_assoc, ← hku, inv_mul_cancel_left]
  exact hu

theorem exists_isCompact_of_finset (R : Finset (IdeleGroup K))
    (hR : ∀ x : IdeleGroup K, ∃ k : Kˣ, ∃ r ∈ R,
      diagonal K k * x * r⁻¹ ∈ standardOpenSubgroup K) :
    ∃ D : Set (IdeleGroup K), IsCompact D ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨M, hM⟩ := exists_unit_forall_abs_log_le (K := K)
    (∑ r ∈ R, |Real.log (ideleModule K r : ℝ)|)
  let S := {x : IdeleGroup K | (∀ w : InfinitePlace K, |Real.log ‖(x : (NumberField.AdeleRing (𝓞 K) K)).1 w‖| ≤ M) ∧
    x ∈ standardOpenSubgroup K}
  refine ⟨⋃ r ∈ R, (fun s ↦ s * r) '' S, R.isCompact_biUnion fun r _ ↦
    (isCompact_abs_log_le_inter_standardOpenSubgroup K M).image
      (continuous_id.mul continuous_const), fun x hx ↦ ?_⟩
  obtain ⟨k, r, hr, hy⟩ := hR x
  set y := diagonal K k * x * r⁻¹ with hydef
  have hmod : ideleModule K y = (ideleModule K r)⁻¹ := by
    rw [hydef, map_mul, map_mul, map_inv, ideleModule_diagonal, MonoidHom.mem_ker.1 hx, one_mul,
      one_mul]
  have hinf : |Real.log (infiniteModule y)| ≤ ∑ r ∈ R, |Real.log (ideleModule K r : ℝ)| := by
    have h1 : infiniteModule y = ((ideleModule K r : ℝ))⁻¹ := by
      have := congrArg Subtype.val hmod
      rw [ideleModule_apply, finiteModule_eq_one_of_mem hy, mul_one] at this
      exact this
    rw [h1, Real.log_inv, abs_neg]
    exact Finset.single_le_sum (f := fun r ↦ |Real.log (ideleModule K r : ℝ)|)
      (fun r _ ↦ abs_nonneg _) hr
  obtain ⟨u, hu⟩ := hM y hinf
  refine ⟨unitsToUnits K u * k, Set.mem_biUnion hr
    ⟨diagonal K (unitsToUnits K u) * y, ⟨hu, mul_mem (diagonal_unitsToUnits_mem K u) hy⟩, ?_⟩⟩
  simp only [hydef, map_mul, mul_assoc, inv_mul_cancel, mul_one]

theorem exists_isCompact_normOneSubgroup :
    ∃ D : Set (IdeleGroup K), IsCompact D ∧ D ⊆ normOneSubgroup K ∧
      ∀ x ∈ normOneSubgroup K, ∃ k : Kˣ, diagonal K k * x ∈ D := by
  obtain ⟨R, hR⟩ := exists_finset_mul_mem_standardOpenSubgroup K
  obtain ⟨D, hD, hxD⟩ := exists_isCompact_of_finset K R hR
  refine ⟨D ∩ normOneSubgroup K, hD.inter_right (isClosed_normOneSubgroup K),
    Set.inter_subset_right, fun x hx ↦ ?_⟩
  obtain ⟨k, hk⟩ := hxD x hx
  exact ⟨k, hk, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) hx⟩

instance compactSpace_normOneSubgroup_quotient :
    CompactSpace (normOneSubgroup K ⧸ (diagonal K).range.subgroupOf (normOneSubgroup K)) := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  have hD' : IsCompact ((Subtype.val : normOneSubgroup K → IdeleGroup K) ⁻¹' D) :=
    (isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD
  have h : (QuotientGroup.mk : normOneSubgroup K →
      normOneSubgroup K ⧸ (diagonal K).range.subgroupOf (normOneSubgroup K)) ''
      ((Subtype.val : normOneSubgroup K → IdeleGroup K) ⁻¹' D) = Set.univ := by
    refine Set.eq_univ_of_forall fun q ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hxD x x.2
    refine ⟨⟨diagonal K k * x, mul_mem (range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩) x.2⟩, hk,
      (QuotientGroup.eq.2 ?_).symm⟩
    rw [Subgroup.mem_subgroupOf]
    refine ⟨k, ?_⟩
    change diagonal K k = ((x : IdeleGroup K))⁻¹ * (diagonal K k * x)
    rw [mul_comm (diagonal K k) x, inv_mul_cancel_left]
  exact isCompact_univ_iff.1 (h ▸ hD'.image QuotientGroup.continuous_mk)

end IdeleGroup

namespace IdeleClassGroup

theorem isCompact_normOneSubgroup :
    IsCompact (normOneSubgroup K : Set (IdeleClassGroup K)) := by
  obtain ⟨D, hD, hDJ, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup K
  have h : (normOneSubgroup K : Set (IdeleClassGroup K)) = mk K '' D := by
    rw [normOneSubgroup_eq_map, Subgroup.coe_map]
    ext c
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hxD x hx
      refine ⟨IdeleGroup.diagonal K k * x, hk, ?_⟩
      rw [map_mul, mk_diagonal]
      exact one_mul (mk K x)
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hDJ hx, rfl⟩
  rw [h]
  exact hD.image (continuous_mk K)

instance compactSpace_normOneSubgroup : CompactSpace (normOneSubgroup K) :=
  isCompact_iff_compactSpace.1 (isCompact_normOneSubgroup K)

end IdeleClassGroup

end

end GroundTheory.Global

/- Insert after OAlpoNormOneCore and the common arithmetic classLog definitions.
   This identifies ALPO's proved compact norm-one group with the actual
   classLog kernel; no compactness or Haar-normalization premise is added. -/
namespace OSourceHaar
open NumberField MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass GroundTheory.Global
open scoped NumberField Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The supplied arithmetic module is exactly the product of local norms
already used by the canonical quotient logarithm. -/
theorem ideleModule_eq_genuine (x : HeckeIdeles K) :
    (IdeleGroup.ideleModule K x : ℝ) = genuineIdeleModulus K x := by
  rw [IdeleGroup.ideleModule_eq, genuineIdeleModulus]
  congr 1
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := K))]
  rfl

theorem classLog_eq_log_ideleModule (x : HeckeIdeleClasses K) :
    classLog K x = Real.log (IdeleClassGroup.ideleModule K x : ℝ) := by
  induction x using Quotient.inductionOn with
  | h a =>
    change Real.log (genuineIdeleModulus K a) = Real.log (IdeleGroup.ideleModule K a : ℝ)
    rw [ideleModule_eq_genuine]

theorem classLog_zero_iff_normOne (x : HeckeIdeleClasses K) :
    classLog K x = 0 ↔ x ∈ IdeleClassGroup.normOneSubgroup K := by
  rw [classLog_eq_log_ideleModule]
  change Real.log (IdeleClassGroup.ideleModule K x : ℝ) = 0 ↔
    IdeleClassGroup.ideleModule K x = 1
  constructor
  · intro hx
    apply Subtype.ext
    have h := congrArg Real.exp hx
    simpa only [Real.exp_log (IdeleClassGroup.ideleModule K x).property,
      Real.exp_zero, Positive.val_one] using h
  · intro hx
    rw [hx]
    exact Real.log_one

/-- Arithmetic compactness of the exact canonical norm-one class set,
derived from the number-field class group and Dirichlet unit lattice. -/
theorem isCompact_classLog_zero :
    IsCompact {x : HeckeIdeleClasses K | classLog K x = 0} := by
  have he : {x : HeckeIdeleClasses K | classLog K x = 0} =
      ((IdeleClassGroup.normOneSubgroup K : Set (IdeleClassGroup K)) : Set (HeckeIdeleClasses K)) := by
    ext x
    exact classLog_zero_iff_normOne K x
  rw [he]
  exact IdeleClassGroup.isCompact_normOneSubgroup K

/-- Compact representatives are supplied for the actual principal quotient,
with the same original modulus, for subsequent uniform theta estimates. -/
theorem exists_compact_normOne_representatives :
    ∃ D : Set (HeckeIdeles K), IsCompact D ∧
      (∀ x ∈ D, genuineIdeleModulus K x = 1) ∧
      ∀ x : HeckeIdeles K, genuineIdeleModulus K x = 1 →
        ∃ k : Kˣ, principalIdele K k * x ∈ D := by
  obtain ⟨D, hD, hDN, hcover⟩ := IdeleGroup.exists_isCompact_normOneSubgroup K
  refine ⟨D, hD, ?_, ?_⟩
  · intro x hx
    rw [← ideleModule_eq_genuine]
    exact IdeleGroup.mem_normOneSubgroup.mp (hDN hx)
  · intro x hx
    have hN : x ∈ IdeleGroup.normOneSubgroup K :=
      IdeleGroup.mem_normOneSubgroup.mpr ((ideleModule_eq_genuine K x).trans hx)
    exact hcover x hN

end
end OSourceHaar

namespace Masullo.HomeomorphMixedSpace
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open NumberField.mixedEmbedding IsDedekindDomain
open scoped NumberField.AdeleRing nonZeroDivisors SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open scoped Classical
noncomputable def homeomorphMixedSpace : (InfiniteAdeleRing K) ≃ₜ mixedEmbedding.mixedSpace K :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace K => IsReal v)
      (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v => (isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
          (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ => not_isReal_iff_isComplex))))

omit [NumberField K] in
theorem homeomorphMixedSpace_apply (x : (InfiniteAdeleRing K)) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := rfl

variable {K}
def mixedFiniteIdele (u : (mixedSpace K)ˣ) (e : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    (AdeleRing (𝓞 K) K)ˣ where
  val := ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.val, e.val)
  inv := ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.inv, e.inv)
  val_inv := by
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.val *
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.inv = 1
      rw [← map_mul, u.val_inv, map_one]
    · exact e.val_inv
  inv_val := by
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.inv *
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm u.val = 1
      rw [← map_mul, u.inv_val, map_one]
    · exact e.inv_val
def archPart (a : (AdeleRing (𝓞 K) K)ˣ) : (mixedSpace K)ˣ where
  val := InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.1
  inv := InfiniteAdeleRing.ringEquiv_mixedSpace K a.inv.1
  val_inv := by
    rw [← map_mul]
    change InfiniteAdeleRing.ringEquiv_mixedSpace K (a.val * a.inv).1 = 1
    rw [a.val_inv]
    exact map_one _
  inv_val := by
    rw [← map_mul]
    change InfiniteAdeleRing.ringEquiv_mixedSpace K (a.inv * a.val).1 = 1
    rw [a.inv_val]
    exact map_one _

/-- Extract the actual finite unit; no valuation restriction is imposed. -/
def finitePart (a : (AdeleRing (𝓞 K) K)ˣ) : (FiniteAdeleRing (𝓞 K) K)ˣ where
  val := a.val.2
  inv := a.inv.2
  val_inv := congrArg Prod.snd a.val_inv
  inv_val := congrArg Prod.snd a.inv_val

theorem mixedFiniteIdele_parts (a : (AdeleRing (𝓞 K) K)ˣ) :
    mixedFiniteIdele (archPart a) (finitePart a) = a := by
  apply Units.ext
  apply Prod.ext
  · exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply a.val.1
  · rfl

/-- Continuity of the actual archimedean part in both value and inverse. -/
theorem continuous_archPart : Continuous (archPart (K := K)) := by
  rw [Units.continuous_iff]
  constructor
  · exact (homeomorphMixedSpace K).continuous.comp
      (continuous_fst.comp Units.continuous_val)
  · exact (homeomorphMixedSpace K).continuous.comp
      (continuous_fst.comp Units.continuous_coe_inv)

/-- Continuity of the actual finite part in the original restricted-product units. -/
theorem continuous_finitePart : Continuous (finitePart (K := K)) := by
  rw [Units.continuous_iff]
  exact ⟨continuous_snd.comp Units.continuous_val,
    continuous_snd.comp Units.continuous_coe_inv⟩

theorem continuous_mixedFiniteIdele : Continuous
    (fun p : (mixedSpace K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ =>
      mixedFiniteIdele p.1 p.2) := by
  rw [Units.continuous_iff]
  constructor
  · exact ((homeomorphMixedSpace K).symm.continuous.comp
      (Units.continuous_val.comp continuous_fst)).prodMk
      (Units.continuous_val.comp continuous_snd)
  · exact ((homeomorphMixedSpace K).symm.continuous.comp
      (Units.continuous_coe_inv.comp continuous_fst)).prodMk
      (Units.continuous_coe_inv.comp continuous_snd)

/-- The original global idele topology is the actual mixed/finite product topology. -/
def actualIdeleHomeomorph : (AdeleRing (𝓞 K) K)ˣ ≃ₜ
    ((mixedSpace K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) where
  toFun a := (archPart a, finitePart a)
  invFun p := mixedFiniteIdele p.1 p.2
  left_inv := mixedFiniteIdele_parts
  right_inv p := by
    apply Prod.ext
    · apply Units.ext
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply p.1.val
    · rfl
  continuous_toFun := continuous_archPart.prodMk continuous_finitePart
  continuous_invFun := continuous_mixedFiniteIdele

end
end Masullo.HomeomorphMixedSpace
/- Insert after JOriginalLinearTheta and the already shared JThetaSummabilityCore.
   This applies the existing lattice estimate to the actual principal series
   along genuine radial ideles. No theta decay premise is supplied. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open Masullo.HomeomorphMixedSpace
open scoped NumberField BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Scale every archimedean coordinate by t and keep the finite idele equal
to one. This is a genuine idele, constructed from a nonzero real scalar. -/
def thetaRadialIdele (t : ℝ) (ht : t ≠ 0) : HeckeIdeles K :=
  mixedFiniteIdele (Units.map (algebraMap ℝ (mixedSpace K)).toMonoidHom (Units.mk0 t ht)) 1

theorem thetaRadialIdele_arch (t : ℝ) (ht : t ≠ 0) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (thetaRadialIdele K t ht).val.1 =
      algebraMap ℝ (mixedSpace K) t := by
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

theorem thetaRadialIdele_finite (t : ℝ) (ht : t ≠ 0) :
    (thetaRadialIdele K t ht).val.2 = 1 := rfl


end
end JThetaAttachment

/- Insert after JOriginalThetaRadial. Normalization uses the actual product
   formula modulus: diagonal coordinate dilation t has modulus t^[K:Q]. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open Masullo.HomeomorphMixedSpace
open scoped NumberField BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem thetaNormAtPlace_arch (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace K x) = ‖x w‖ := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) _

theorem thetaNormAtPlace_real (t : ℝ) (w : InfinitePlace K) :
    normAtPlace w (algebraMap ℝ (mixedSpace K) t) = |t| := by
  rcases w.isReal_or_isComplex with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    change ‖t‖ = |t|
    exact Real.norm_eq_abs t
  · rw [normAtPlace_apply_of_isComplex hw]
    change ‖(t : ℂ)‖ = |t|
    simp only [Complex.norm_real, Real.norm_eq_abs]

/-- Exact idelic modulus of simultaneous real dilation at all infinite places. -/
theorem thetaRadialIdele_modulus (t : ℝ) (ht : t ≠ 0) :
    genuineIdeleModulus K (thetaRadialIdele K t ht) = |t| ^ Module.finrank ℚ K := by
  have hi (w : InfinitePlace K) : ‖(thetaRadialIdele K t ht).val.1 w‖ = |t| := by
    rw [← thetaNormAtPlace_arch K, thetaRadialIdele_arch, thetaNormAtPlace_real]
  have hf (v : FinitePlace K) : ‖(thetaRadialIdele K t ht).val.2 v.maximalIdeal‖ = 1 := by
    rw [thetaRadialIdele_finite]
    change ‖(1 : v.maximalIdeal.adicCompletion K)‖ = 1
    exact norm_one
  unfold genuineIdeleModulus
  simp only [hi, hf, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem thetaRadialIdele_classLog (t : ℝ) (ht : 0 < t) :
    classLog K (QuotientGroup.mk (thetaRadialIdele K t ht.ne')) =
      (Module.finrank ℚ K : ℝ) * Real.log t := by
  change Real.log (genuineIdeleModulus K (thetaRadialIdele K t ht.ne')) = _
  rw [thetaRadialIdele_modulus, abs_of_pos ht, Real.log_pow]

/-- The diagonal section is parametrized by the actual logarithmic modulus. -/
def thetaLogSection (u : ℝ) : HeckeIdeles K :=
  thetaRadialIdele K (Real.exp (u / (Module.finrank ℚ K : ℝ))) (Real.exp_ne_zero _)

theorem thetaLogSection_classLog (u : ℝ) :
    classLog K (QuotientGroup.mk (thetaLogSection K u)) = u := by
  rw [thetaLogSection, thetaRadialIdele_classLog K _ (Real.exp_pos _), Real.log_exp]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  exact mul_div_cancel₀ u hd

/-- The common arithmetic logarithm is surjective, with an explicit section. -/
theorem classLog_surjective : Function.Surjective (classLog K) :=
  fun u => ⟨QuotientGroup.mk (thetaLogSection K u), thetaLogSection_classLog K u⟩

theorem thetaLogSection_continuous : Continuous (thetaLogSection K) := by
  unfold thetaLogSection thetaRadialIdele
  have hc : Continuous (fun u : ℝ =>
      Units.map (algebraMap ℝ (mixedSpace K)).toMonoidHom
        (Units.mk0 (Real.exp (u / (Module.finrank ℚ K : ℝ))) (Real.exp_ne_zero _))) := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous (fun u : ℝ => algebraMap ℝ (mixedSpace K)
        (Real.exp (u / (Module.finrank ℚ K : ℝ))))
      exact (continuous_algebraMap ℝ (mixedSpace K)).comp
        (Real.continuous_exp.comp (continuous_id.div_const _))
    · change Continuous (fun u : ℝ => algebraMap ℝ (mixedSpace K)
        (Real.exp (u / (Module.finrank ℚ K : ℝ)))⁻¹)
      exact (continuous_algebraMap ℝ (mixedSpace K)).comp
        ((Real.continuous_exp.comp (continuous_id.div_const _)).inv₀ (fun _ => Real.exp_ne_zero _))
  exact (continuous_mixedFiniteIdele (K := K)).comp (hc.prodMk continuous_const)


end
end JThetaAttachment

/- Insert after OActualNormOne and JOriginalThetaLogSection.
   Original-mu radial integrability is proved by arithmetic compactness,
   literal classLog shells, Haar translation, and a summable exponential bound. -/
namespace OSourceHaar
open NumberField MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass JThetaAttachment
open scoped NumberField Topology ENNReal Pointwise
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The actual logarithmic bands are compact: multiply the proved compact
norm-one class set by the genuine continuous degree-normalized section. -/
theorem isCompact_classLog_band (l r : ℝ) :
    IsCompact {x : HeckeIdeleClasses K | l ≤ classLog K x ∧ classLog K x ≤ r} := by
  let σ : ℝ → HeckeIdeleClasses K := fun t => QuotientGroup.mk (thetaLogSection K t)
  have hσ : Continuous σ := QuotientGroup.continuous_mk.comp (thetaLogSection_continuous K)
  have hs (t : ℝ) : classLog K (σ t) = t := thetaLogSection_classLog K t
  have he : {x : HeckeIdeleClasses K | l ≤ classLog K x ∧ classLog K x ≤ r} =
      {x : HeckeIdeleClasses K | classLog K x = 0} * (σ '' Set.Icc l r) := by
    apply Set.Subset.antisymm
    · intro x hx
      refine Set.mem_mul.mpr ⟨x * (σ (classLog K x))⁻¹, ?_,
        σ (classLog K x), ⟨classLog K x, hx, rfl⟩, by simp [mul_assoc]⟩
      have h := classLog_mul K (x * (σ (classLog K x))⁻¹) (σ (classLog K x))
      rw [inv_mul_cancel_right, hs] at h
      change classLog K (x * (σ (classLog K x))⁻¹) = 0
      linarith
    · rintro x ⟨z, hz, y, ⟨t, ht, rfl⟩, rfl⟩
      change l ≤ classLog K (z * σ t) ∧ classLog K (z * σ t) ≤ r
      rw [classLog_mul, hs, hz, zero_add]
      exact ht
  rw [he]
  exact (isCompact_classLog_zero K).mul (isCompact_Icc.image hσ)

def unitLogShell (n : ℤ) : Set (HeckeIdeleClasses K) :=
  {x | (n : ℝ) ≤ classLog K x ∧ classLog K x < (n : ℝ) + 1}

theorem unitLogShell_measurable (n : ℤ) : MeasurableSet (unitLogShell K n) :=
  measurableSet_Ico.preimage (classLog_continuous K).measurable

theorem unitLogShell_cover (x : HeckeIdeleClasses K) : ∃ n : ℤ, x ∈ unitLogShell K n :=
  ⟨⌊classLog K x⌋, Int.floor_le _, Int.lt_floor_add_one _⟩

variable [MeasurableMul (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]

/-- Every unit-width shell has exactly the same ORIGINAL Haar mass. -/
theorem unitLogShell_measure_eq (n : ℤ) :
    mu (unitLogShell K n) = mu (unitLogShell K 0) := by
  let g : HeckeIdeleClasses K := QuotientGroup.mk (thetaLogSection K (n : ℝ))
  have hg : classLog K g = (n : ℝ) := thetaLogSection_classLog K (n : ℝ)
  have hpre : (fun x : HeckeIdeleClasses K => g*x) ⁻¹' unitLogShell K n =
      unitLogShell K 0 := by
    ext x
    simp only [unitLogShell, Set.mem_preimage, Set.mem_setOf_eq, Int.cast_zero]
    rw [classLog_mul, hg]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [← hpre, measure_preimage_mul]

variable [IsLocallyFiniteMeasure mu]

/-- Finiteness of the shell mass is an arithmetic compactness application,
not a supplied radial integration or finite-volume hypothesis. -/
theorem unitLogShell_measure_lt_top (n : ℤ) : mu (unitLogShell K n) < ⊤ := by
  have hsub : unitLogShell K n ⊆
      {x : HeckeIdeleClasses K | (n : ℝ) ≤ classLog K x ∧ classLog K x ≤ (n : ℝ)+1} :=
    fun x hx => ⟨hx.1, hx.2.le⟩
  exact lt_of_le_of_lt (measure_mono hsub)
    (isCompact_classLog_band K (n : ℝ) ((n : ℝ)+1)).measure_lt_top

private theorem summable_exp_abs_int {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Summable fun n : ℤ => c * Real.exp (-(δ * |(n : ℝ)|)) := by
  have hnat : Summable fun n : ℕ => Real.exp (-(δ * n)) := by
    have h := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)
    refine h.congr fun n => ?_
    ring_nf
  refine (Summable.of_nat_of_neg ?_ ?_).mul_left c
  · refine hnat.congr fun n => ?_
    simp only [Int.cast_natCast, Nat.abs_cast]
  · refine hnat.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]

/-- Every positive exponential envelope is integrable against the original
class Haar. No radial-pushforward or volume-one premise is required. -/
theorem integrable_exp_neg_abs_classLog (δ : ℝ) (hδ : 0 < δ) :
    Integrable (fun x : HeckeIdeleClasses K => Real.exp (-δ * |classLog K x|)) mu := by
  let f : HeckeIdeleClasses K → ℝ := fun x => Real.exp (-δ * |classLog K x|)
  let c : ℤ → ℝ := fun n => Real.exp δ * Real.exp (-(δ * |(n : ℝ)|))
  have hfm : Measurable f :=
    (Real.continuous_exp.comp (continuous_const.mul (classLog_continuous K).abs)).measurable
  have hf0 (x) : 0 ≤ f x := (Real.exp_pos _).le
  have hb (n : ℤ) (x : HeckeIdeleClasses K) (hx : x ∈ unitLogShell K n) : f x ≤ c n := by
    have hdiff : |classLog K x - (n : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hn : |(n : ℝ)| ≤ |classLog K x| + 1 := by
      calc
        |(n : ℝ)| = |classLog K x - (classLog K x - (n : ℝ))| := by congr 1; ring
        _ ≤ |classLog K x| + |classLog K x - (n : ℝ)| := abs_sub _ _
        _ ≤ |classLog K x| + 1 := add_le_add (le_refl _) hdiff
    change Real.exp (-δ * |classLog K x|) ≤ Real.exp δ * Real.exp (-(δ * |(n : ℝ)|))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hc : Summable c := summable_exp_abs_int hδ (Real.exp δ)
  have hpiece (n : ℤ) : IntegrableOn f (unitLogShell K n) mu := by
    refine Measure.integrableOn_of_bounded (M := c n)
      (unitLogShell_measure_lt_top K mu n).ne hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (unitLogShell_measurable K n)] with x hx
    rw [Real.norm_of_nonneg (hf0 x)]
    exact hb n x hx
  have hint (n : ℤ) : ∫ x in unitLogShell K n, ‖f x‖ ∂mu ≤
      c n * (mu (unitLogShell K 0)).toReal := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := mu) (f := fun x => ‖f x‖)
      (s := unitLogShell K n) (C := c n) (unitLogShell_measure_lt_top K mu n)
      (fun x hx => by rw [norm_norm, Real.norm_of_nonneg (hf0 x)]; exact hb n x hx)
    rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _),
      measureReal_def, unitLogShell_measure_eq K mu n] at h
    exact h
  have hsum : Summable (fun n : ℤ => ∫ x in unitLogShell K n, ‖f x‖ ∂mu) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) hint (hc.mul_right _)
  have hU : IntegrableOn f (⋃ n : ℤ, unitLogShell K n) mu :=
    integrableOn_iUnion_of_summable_integral_norm hpiece hsum
  have he : (⋃ n : ℤ, unitLogShell K n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := unitLogShell_cover K x
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rwa [he, integrableOn_univ] at hU

/-- The scalar envelope needed for weighted theta admission belongs to
L² for the same original class Haar, for every positive decay rate. -/
theorem memLp_exp_neg_abs_classLog (δ : ℝ) (hδ : 0 < δ) :
    MemLp (fun x : HeckeIdeleClasses K => Real.exp (-δ * |classLog K x|)) 2 mu := by
  have hm : AEStronglyMeasurable
      (fun x : HeckeIdeleClasses K => Real.exp (-δ * |classLog K x|)) mu :=
    (Real.continuous_exp.comp (continuous_const.mul (classLog_continuous K).abs)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  convert integrable_exp_neg_abs_classLog K mu (2*δ) (by positivity) using 1
  ext x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

end
end OSourceHaar



/- Insert after checked OOriginalHaarRadial and JOriginalThetaLogSection.
   R owns this specific radial-pushforward application; O/C review. -/
namespace RIntegrated
open MeasureTheory MeasureTheory.Measure MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass JThetaAttachment OSourceHaar
open scoped Topology
noncomputable section

/-- The logarithm pushes the original arithmetic Haar to a positive finite
multiple of Lebesgue measure. Compactness and surjectivity are applied to
the actual class group and its genuine logarithmic section. -/
theorem originalHaar_classLog_map
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Measure.map (classLog K) mu = c • (volume : Measure ℝ) := by
  let ν := Measure.map (classLog K) mu
  have hm := (classLog_continuous K).measurable
  letI : ν.IsAddLeftInvariant := by
    apply (forall_measure_preimage_add_iff ν).mp
    intro t S hS
    obtain ⟨g, hg⟩ := classLog_surjective K t
    change Measure.map (classLog K) mu ((fun x => t+x) ⁻¹' S) =
      Measure.map (classLog K) mu S
    rw [Measure.map_apply hm (measurable_const_add t hS), Measure.map_apply hm hS]
    have he : (classLog K) ⁻¹' ((fun x => t+x) ⁻¹' S) =
        (fun x => g*x) ⁻¹' ((classLog K) ⁻¹' S) := by
      ext x
      simp only [Set.mem_preimage, classLog_mul, hg]
    rw [he, measure_preimage_mul]
  letI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨?_⟩
    intro S hS
    obtain ⟨l, hl⟩ := hS.bddBelow
    obtain ⟨r, hr⟩ := hS.bddAbove
    change Measure.map (classLog K) mu S < ⊤
    rw [Measure.map_apply hm hS.measurableSet]
    have hsub : (classLog K) ⁻¹' S ⊆
        {x : HeckeIdeleClasses K | l ≤ classLog K x ∧ classLog K x ≤ r} := by
      intro x hx
      exact ⟨hl hx, hr hx⟩
    exact lt_of_le_of_lt (measure_mono hsub) (isCompact_classLog_band K l r).measure_lt_top
  letI : ν.IsOpenPosMeasure := by
    refine ⟨?_⟩
    intro U hU hUne
    change Measure.map (classLog K) mu U ≠ 0
    rw [Measure.map_apply hm hU.measurableSet]
    apply (hU.preimage (classLog_continuous K)).measure_ne_zero mu
    obtain ⟨t, ht⟩ := hUne
    obtain ⟨x, hx⟩ := classLog_surjective K t
    exact ⟨x, by simpa only [Set.mem_preimage, hx] using ht⟩
  letI : ν.IsAddHaarMeasure := {}
  let c : NNReal := addHaarScalarFactor ν (volume : Measure ℝ)
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  refine ⟨(c : ENNReal), by exact_mod_cast (ne_of_gt hc), ENNReal.coe_ne_top, ?_⟩
  exact isAddLeftInvariant_eq_smul ν (volume : Measure ℝ)

end
end RIntegrated
#check RIntegrated.originalHaar_classLog_map
#print axioms RIntegrated.originalHaar_classLog_map
