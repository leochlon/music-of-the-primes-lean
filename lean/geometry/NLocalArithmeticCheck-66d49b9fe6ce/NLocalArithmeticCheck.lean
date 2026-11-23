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

/- Actual finite local embeddings and normalized local expression. The embedding
proofs adapt ALPO GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.
This defines the local endpoint; it does not assert an unproved global trace equality. -/
namespace NLocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField IsDedekindDomain MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

open Classical in
def finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := ⟨Pi.mulSingle v x, by
    have he : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ≠ v :=
      Filter.eventually_cofinite.mpr (by simp)
    filter_upwards [he] with w hw
    rw [Pi.mulSingle_eq_of_ne hw]
    exact one_mem _⟩
  map_one' := Subtype.ext (Pi.mulSingle_one (M := fun w : HeightOneSpectrum (𝓞 K) =>
    w.adicCompletion K) v)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul v x y)

def finiteEmbedding (v : FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* HeckeIdeles K :=
  Units.map (MonoidHom.prod 1 (finiteAdeleSingle K v.maximalIdeal))

def finiteClass (v : FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* HeckeIdeleClasses K :=
  (QuotientGroup.mk' (principalIdeles K)).comp (finiteEmbedding K v)

theorem finiteEmbedding_modulus (v : FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    genuineIdeleModulus K (finiteEmbedding K v u) =
      ‖(u : v.maximalIdeal.adicCompletion K)‖ := by
  classical
  unfold genuineIdeleModulus
  have hi : (∏ w : InfinitePlace K, ‖(finiteEmbedding K v u).val.1 w‖ ^ w.mult) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    simp
  rw [hi, one_mul]
  refine (finprod_eq_single _ v fun w hw => ?_).trans ?_
  · have hn : w.maximalIdeal ≠ v.maximalIdeal :=
      fun h => hw (FinitePlace.maximalIdeal_injective h)
    change ‖Pi.mulSingle v.maximalIdeal (u : v.maximalIdeal.adicCompletion K)
      w.maximalIdeal‖ = 1
    rw [Pi.mulSingle_eq_of_ne hn]
    exact norm_one
  · change ‖Pi.mulSingle v.maximalIdeal (u : v.maximalIdeal.adicCompletion K)
      v.maximalIdeal‖ = _
    rw [Pi.mulSingle_eq_same]

theorem finiteClass_log (v : FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    classLog K (finiteClass K v u) = Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖ := by
  change Real.log (genuineIdeleModulus K (finiteEmbedding K v u)) = _
  rw [finiteEmbedding_modulus]

def finiteUnitGroup (v : FinitePlace K) : Set (v.maximalIdeal.adicCompletion K)ˣ :=
  {u | ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1}

def residueCard (v : FinitePlace K) : ℝ := (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)

def finiteLocalCoefficient (v : FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (mu : Measure (v.maximalIdeal.adicCompletion K)ˣ) : ℝ :=
  Real.log (residueCard K v) / mu.real (finiteUnitGroup K v)

def finiteLocalDensity (v : FinitePlace K) (h : HeckeIdeleClasses K → ℂ)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) : ℂ :=
  h (finiteClass K v u) * (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) /
    (‖1 - (u : v.maximalIdeal.adicCompletion K)‖ : ℂ)

def finiteLocalTerm (v : FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (mu : Measure (v.maximalIdeal.adicCompletion K)ˣ)
    (h : HeckeIdeleClasses K → ℂ) : ℂ :=
  (finiteLocalCoefficient K v mu : ℂ) * ∫ u, finiteLocalDensity K v h u ∂mu

/-- The manuscript's full norm-one vanishing removes the entire finite local
unit group from the density, including the singular point u=1. -/
theorem finiteLocalDensity_unit_zero (v : FinitePlace K)
    (h : HeckeIdeleClasses K → ℂ)
    (hh : ∀ x, classLog K x = 0 → h x = 0)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) (hu : u ∈ finiteUnitGroup K v) :
    finiteLocalDensity K v h u = 0 := by
  have he : classLog K (finiteClass K v u) = 0 := by
    rw [finiteClass_log, show ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1 from hu,
      Real.log_one]
  simp only [finiteLocalDensity, hh _ he, zero_mul, zero_div]

end
end NLocalArithmetic
#print axioms NLocalArithmetic.finiteClass_log
#print axioms NLocalArithmetic.finiteLocalDensity_unit_zero
