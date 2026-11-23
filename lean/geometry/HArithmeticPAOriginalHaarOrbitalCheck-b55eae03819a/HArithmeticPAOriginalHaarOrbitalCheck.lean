-- Exact dependency block: Q checked arithmetic/source prefix through OAllCharacterClosure
-- Check context: QFullSourceTraceCheck.lean
-- Check context: inputs/exchange/O/OGlobalSourceCheck.lean
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

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

/-- Descend the actual character; no spectrum or zero set is prescribed. -/
noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K → Circle :=
  Quotient.lift χ.character (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, map_mul, χ.trivial_on_principal, one_mul])

theorem classCharacter_continuous (χ : UnitaryHeckeCharacter K) :
    Continuous (classCharacter K χ) := χ.character.continuous.quotient_lift _

/-- Definition bridge to the same idelic character as the Euler germ. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (x : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk x) = χ.character x := rfl
end MasulloGRH

namespace Masullo.GenuineMellinJet
open MasulloGRH Masullo.IdeleClassGeometry
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

end Masullo.GenuineMellinJet

namespace Masullo.GenuineMellinJet
noncomputable def nativeHalfWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (alpha * |t|) * (1 + t^2) ^ (s/4)

theorem nativeHalfWeight_pos (alpha s t : ℝ) :
    0 < nativeHalfWeight alpha s t := by
  unfold nativeHalfWeight
  positivity

end Masullo.GenuineMellinJet

namespace Masullo.NativeHalfWeightAddLe
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet

/-- The actual half-weight has a finite, explicit translation bound. This is
 the weight estimate needed in the proof of manuscript Lemma 9.3.1.5. -/
theorem nativeHalfWeight_add_le (alpha s u t : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    nativeHalfWeight alpha s (u+t) ≤
      (Real.exp (alpha * |u|) * (2*(1+u^2))^(s/4)) * nativeHalfWeight alpha s t := by
  have hab : alpha * |u+t| ≤ alpha * |u| + alpha * |t| := by
    nlinarith [abs_add_le u t]
  have hex : Real.exp (alpha * |u+t|) ≤
      Real.exp (alpha * |u|) * Real.exp (alpha * |t|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hab
  have hpoly : 1+(u+t)^2 ≤ (2*(1+u^2))*(1+t^2) := by
    nlinarith [sq_nonneg (u-t), sq_nonneg (u*t)]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1+(u+t)^2) hpoly
    (by positivity : 0 ≤ s/4)
  rw [Real.mul_rpow (by positivity) (by positivity)] at hp
  unfold nativeHalfWeight
  calc
    _ ≤ (Real.exp (alpha * |u|) * Real.exp (alpha * |t|)) *
        ((2*(1+u^2))^(s/4) * (1+t^2)^(s/4)) :=
      mul_le_mul hex hp (by positivity) (by positivity)
    _ = _ := by ring

variable (K : Type*) [Field K] [NumberField K]

theorem actual_halfWeight_continuous (alpha s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun x : HeckeIdeleClasses K =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ)) := by
  have hl := classLog_continuous K
  unfold nativeHalfWeight
  fun_prop (disch := positivity)

/-- Original same-Haar weighted L2 is preserved by actual left translation.
No spectral operator or arbitrary diagonal is supplied as a hypothesis. -/
theorem actual_weighted_translation_memLp
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (g : HeckeIdeleClasses K) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f (g⁻¹*x)) 2 mu := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hw : Continuous w := actual_halfWeight_continuous K alpha s hs
  have hn (x : HeckeIdeleClasses K) : w x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (ne_of_gt (nativeHalfWeight_pos alpha s (classLog K x)))
  have hfm : AEStronglyMeasurable f mu := by
    have hi : Continuous (fun x => (w x)⁻¹) := hw.inv₀ hn
    have hm := hf.aestronglyMeasurable.mul hi.aestronglyMeasurable
    convert hm using 1
    funext x
    change f x = (w x * f x) * (w x)⁻¹
    rw [mul_comm (w x) (f x), mul_assoc, mul_inv_cancel₀ (hn x), mul_one]
  have hmp := measurePreserving_mul_left mu g⁻¹
  have hfshift := hf.comp_measurePreserving hmp
  have hmeas : AEStronglyMeasurable (fun x => w x * f (g⁻¹*x)) mu :=
    hw.aestronglyMeasurable.mul (hfm.comp_measurePreserving hmp)
  apply hfshift.of_le_mul hmeas
    (c := Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4))
  apply Filter.Eventually.of_forall
  intro x
  change ‖w x * f (g⁻¹*x)‖ ≤ _ * ‖w (g⁻¹*x) * f (g⁻¹*x)‖
  have he : classLog K x = classLog K g + classLog K (g⁻¹*x) := by
    rw [← classLog_mul, mul_inv_cancel_left]
  have hb := nativeHalfWeight_add_le alpha s (classLog K g) (classLog K (g⁻¹*x)) ha hs
  rw [← he] at hb
  simp only [norm_mul, w, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (nativeHalfWeight_pos alpha s _)]
  calc
    _ ≤ ((Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) *
      nativeHalfWeight alpha s (classLog K (g⁻¹*x))) * ‖f (g⁻¹*x)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by ring

/-- Quantitative same-Haar bound for the ACTUAL native weighted translation,
not an assumed boundedness constant for a postulated operator. -/
theorem actual_weighted_translation_eLpNorm
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (g : HeckeIdeleClasses K) :
    eLpNorm (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f (g⁻¹*x)) 2 mu ≤
      ENNReal.ofReal (Real.exp (alpha * |classLog K g|) *
        (2*(1+(classLog K g)^2))^(s/4)) *
      eLpNorm (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hb : ∀ x, ‖w x * f (g⁻¹*x)‖ ≤
      (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) *
      ‖w (g⁻¹*x) * f (g⁻¹*x)‖ := by
    intro x
    have he : classLog K x = classLog K g + classLog K (g⁻¹*x) := by
      rw [← classLog_mul, mul_inv_cancel_left]
    have ht := nativeHalfWeight_add_le alpha s (classLog K g) (classLog K (g⁻¹*x)) ha hs
    rw [← he] at ht
    simp only [norm_mul, w, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (nativeHalfWeight_pos alpha s _)]
    calc
      _ ≤ ((Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) *
        nativeHalfWeight alpha s (classLog K (g⁻¹*x))) * ‖f (g⁻¹*x)‖ :=
        mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = _ := by ring
  have H := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := mu) (Filter.Eventually.of_forall hb) 2
  have heq := eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
    (measurePreserving_mul_left mu g⁻¹) (p := 2)
  exact H.trans_eq (congrArg (fun n => ENNReal.ofReal
    (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) * n) heq)

/-- The original weighted Hilbert norm bound, on normalized representatives. -/
theorem actual_weighted_translation_norm
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (g : HeckeIdeleClasses K) :
    ‖(actual_weighted_translation_memLp K mu alpha s ha hs f hf g).toLp _‖ ≤
      (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) * ‖hf.toLp _‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have h := actual_weighted_translation_eLpNorm K mu alpha s ha hs f hf g
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_lt_top.ne) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4))] using ht

end Masullo.NativeHalfWeightAddLe

noncomputable section
namespace Masullo.NativeRep
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe
variable (K : Type*) [Field K] [NumberField K]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- The actual original weighted representative of a normalized L2 vector. -/
def nativeRep (F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) : ℂ :=
  F x / (nativeHalfWeight alpha s (classLog K x) : ℂ)

omit [mu.IsMulLeftInvariant] in
theorem nativeRep_normalization (F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) :
    (nativeHalfWeight alpha s (classLog K x) : ℂ) * nativeRep K mu alpha s F x = F x := by
  have hn : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  dsimp [nativeRep]
  field_simp

omit [mu.IsMulLeftInvariant] in
theorem nativeRep_memLp (F : Lp ℂ 2 mu) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      nativeRep K mu alpha s F x) 2 mu := by
  simpa only [nativeRep_normalization] using Lp.memLp F

def nativeTranslation (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  (actual_weighted_translation_memLp K mu alpha s ha hs
    (nativeRep K mu alpha s F) (nativeRep_memLp K mu alpha s F) g).toLp _

theorem nativeTranslation_ae (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    (nativeTranslation K mu alpha s ha hs g F : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
      fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        (F (g⁻¹*x) / (nativeHalfWeight alpha s (classLog K (g⁻¹*x)) : ℂ)) :=
  MemLp.coeFn_toLp _

def nativeTranslationLinear (g : HeckeIdeleClasses K) : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun := nativeTranslation K mu alpha s ha hs g
  map_add' F G := by
    apply Lp.ext
    have hadd := (measurePreserving_mul_left mu g⁻¹).quasiMeasurePreserving.ae (Lp.coeFn_add F G)
    filter_upwards [nativeTranslation_ae K mu alpha s ha hs g (F+G),
      nativeTranslation_ae K mu alpha s ha hs g F,
      nativeTranslation_ae K mu alpha s ha hs g G,
      Lp.coeFn_add (nativeTranslation K mu alpha s ha hs g F)
        (nativeTranslation K mu alpha s ha hs g G), hadd] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h4, h2, h3, h5]
    ring
  map_smul' c F := by
    apply Lp.ext
    have hsmul := (measurePreserving_mul_left mu g⁻¹).quasiMeasurePreserving.ae (Lp.coeFn_smul c F)
    filter_upwards [nativeTranslation_ae K mu alpha s ha hs g (c • F),
      nativeTranslation_ae K mu alpha s ha hs g F,
      Lp.coeFn_smul c (nativeTranslation K mu alpha s ha hs g F), hsmul] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    change _ = (c • nativeTranslation K mu alpha s ha hs g F) x
    rw [h1, h3, h2, h4]
    ring

theorem nativeTranslation_norm (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    ‖nativeTranslation K mu alpha s ha hs g F‖ ≤
      (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) * ‖F‖ := by
  have ht := actual_weighted_translation_norm K mu alpha s ha hs
    (nativeRep K mu alpha s F) (nativeRep_memLp K mu alpha s F) g
  have he : (nativeRep_memLp K mu alpha s F).toLp _ = F := by
    apply Lp.ext
    filter_upwards [(nativeRep_memLp K mu alpha s F).coeFn_toLp] with x hx
    simpa only [nativeRep_normalization] using hx
  simpa only [nativeTranslation, he] using ht

/-- Actual bounded left translation on the original weighted Hilbert space,
expressed through the original half-weight isometry, with unchanged Haar. -/
def nativeTranslationCLM (g : HeckeIdeleClasses K) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (nativeTranslationLinear K mu alpha s ha hs g).mkContinuous
    (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4))
    (nativeTranslation_norm K mu alpha s ha hs g)

theorem nativeTranslationCLM_ae (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    (nativeTranslationCLM K mu alpha s ha hs g F : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
      fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        (F (g⁻¹*x) / (nativeHalfWeight alpha s (classLog K (g⁻¹*x)) : ℂ)) :=
  nativeTranslation_ae K mu alpha s ha hs g F

end Masullo.NativeRep
end

namespace Masullo.NativeTranslationWeaklyMeasurable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe Masullo.NativeRep
variable (K : Type*) [Field K] [NumberField K]

/-- The actual same-Haar weighted translation is weakly measurable on every
native Hilbert vector. This supplies the scalar Pettis input in manuscript
Definition 9.3.1.1 without assuming orbit or coefficient measurability. -/
theorem nativeTranslation_weaklyMeasurable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (F V : Lp ℂ 2 mu) :
    StronglyMeasurable (fun g => inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F)) := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hw : Measurable w := (actual_halfWeight_continuous K alpha s hs).measurable
  have hm : Measurable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => p.1⁻¹*p.2) :=
    measurable_fst.inv.mul measurable_snd
  have hk : StronglyMeasurable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      w p.2 * (F (p.1⁻¹*p.2) / w (p.1⁻¹*p.2))) :=
    ((hw.comp measurable_snd).mul
      (((Lp.stronglyMeasurable F).measurable.comp hm).div (hw.comp hm))).stronglyMeasurable
  have hi : StronglyMeasurable (Function.uncurry (fun g x =>
      inner ℂ (V x) (w x * (F (g⁻¹*x) / w (g⁻¹*x))))) :=
    ((Lp.stronglyMeasurable V).comp_measurable measurable_snd).inner hk
  have he : (fun g => inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F)) =
      (fun g => ∫ x, inner ℂ (V x) (w x * (F (g⁻¹*x) / w (g⁻¹*x))) ∂mu) := by
    funext g
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs g F] with x hx
    rw [hx]
  rw [he]
  exact hi.integral_prod_right

end Masullo.NativeTranslationWeaklyMeasurable

namespace Masullo.NativeTranslationBound
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe
variable (K : Type*) [Field K] [NumberField K]

noncomputable def nativeTranslationBound (alpha s : ℝ) (g : HeckeIdeleClasses K) : ℝ :=
  Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)

/-- The actual compact test supplies the integrable operator-norm envelope
needed for the Pettis/Bochner convolution in manuscript (9.3.1.2). -/
theorem native_convolution_envelope_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (alpha s : ℝ) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun g => ‖h g‖ * nativeTranslationBound K alpha s g) mu := by
  have ht : Continuous (nativeTranslationBound K alpha s) := by
    unfold nativeTranslationBound
    have hl := classLog_continuous K
    fun_prop (disch := positivity)
  exact (hh.norm.mul ht).integrable_of_hasCompactSupport (hc.norm.mul_right)

end Masullo.NativeTranslationBound

namespace Masullo.NativeTranslationWeaklyMeasurable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe Masullo.NativeRep Masullo.NativeTranslationBound
variable (K : Type*) [Field K] [NumberField K]

/-- Every Hilbert scalar test of the ACTUAL compact-kernel convolution is
integrable. This is the scalar integrability prerequisite of Pettis integration,
proved from native weak measurability and the reused norm envelope. -/
theorem native_convolution_scalar_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F V : Lp ℂ 2 mu) :
    Integrable (fun g => h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F)) mu := by
  have hi := (native_convolution_envelope_integrable K mu alpha s hs h hh hc).mul_const
    (‖F‖ * ‖V‖)
  have hm := hh.stronglyMeasurable.mul (nativeTranslation_weaklyMeasurable K mu alpha s ha hs F V)
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro g
  have hb : ‖nativeTranslationCLM K mu alpha s ha hs g F‖ ≤
      nativeTranslationBound K alpha s g * ‖F‖ :=
    nativeTranslation_norm K mu alpha s ha hs g F
  simp only [Pi.mul_apply]
  rw [norm_mul]
  calc
    _ ≤ ‖h g‖ * (‖V‖ * ‖nativeTranslationCLM K mu alpha s ha hs g F‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm V _) (norm_nonneg _)
    _ ≤ ‖h g‖ * (‖V‖ * (nativeTranslationBound K alpha s g * ‖F‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
    _ = (‖h g‖ * nativeTranslationBound K alpha s g) * (‖F‖ * ‖V‖) := by ring

end Masullo.NativeTranslationWeaklyMeasurable

noncomputable section
namespace Masullo.NativePettisLinear
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe
open Masullo.NativeRep Masullo.NativeTranslationWeaklyMeasurable Masullo.NativeTranslationBound
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)

/-- The conjugate scalar integral is a genuine linear form on the original
weighted Hilbert space, with the same Haar and actual inverse translations. -/
def nativePettisLinear (F : Lp ℂ 2 mu) : Lp ℂ 2 mu →ₗ[ℂ] ℂ where
  toFun V := star (∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu)
  map_add' V W := by
    simp only [inner_add_left, mul_add]
    rw [integral_add
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc F V)
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc F W), star_add]
  map_smul' c V := by
    simp only [RingHom.id_apply, smul_eq_mul]
    have he : (fun g => h g * inner ℂ (c • V)
        (nativeTranslationCLM K mu alpha s ha hs g F)) =
        (fun g => (starRingEnd ℂ c) * (h g * inner ℂ V
          (nativeTranslationCLM K mu alpha s ha hs g F))) := by
      funext g
      rw [inner_smul_left]
      ring
    rw [he, integral_const_mul, star_mul]
    simp [mul_comm]

theorem nativePettisLinear_bound (F V : Lp ℂ 2 mu) :
    ‖nativePettisLinear K mu alpha s ha hs h hh hc F V‖ ≤
      ((∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu) * ‖F‖) * ‖V‖ := by
  change ‖star (∫ g, h g * inner ℂ V
    (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu)‖ ≤ _
  rw [norm_star]
  have hi := (native_convolution_envelope_integrable K mu alpha s hs h hh hc).mul_const
    (‖F‖ * ‖V‖)
  calc
    _ ≤ ∫ g, (‖h g‖ * nativeTranslationBound K alpha s g) * (‖F‖ * ‖V‖) ∂mu := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with g
      rw [norm_mul]
      have hb : ‖nativeTranslationCLM K mu alpha s ha hs g F‖ ≤
          nativeTranslationBound K alpha s g * ‖F‖ :=
        nativeTranslation_norm K mu alpha s ha hs g F
      calc
        _ ≤ ‖h g‖ * (‖V‖ * ‖nativeTranslationCLM K mu alpha s ha hs g F‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm V _) (norm_nonneg _)
        _ ≤ ‖h g‖ * (‖V‖ * (nativeTranslationBound K alpha s g * ‖F‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_mul_const]; ring

def nativePettisDual (F : Lp ℂ 2 mu) : Lp ℂ 2 mu →L[ℂ] ℂ :=
  (nativePettisLinear K mu alpha s ha hs h hh hc F).mkContinuous
    ((∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu) * ‖F‖)
    (nativePettisLinear_bound K mu alpha s ha hs h hh hc F)

/-- Construct the original Pettis convolution vector; no orbit-integrability
or postulated convolution operator is an input. -/
def nativePettisVector (F : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 mu)).symm
    (nativePettisDual K mu alpha s ha hs h hh hc F)

theorem nativePettisVector_pairing (F V : Lp ℂ 2 mu) :
    inner ℂ V (nativePettisVector K mu alpha s ha hs h hh hc F) =
      ∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu := by
  have ht : inner ℂ (nativePettisVector K mu alpha s ha hs h hh hc F) V =
      star (∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu) :=
    InnerProductSpace.toDual_symm_apply
  have ht' := congrArg (starRingEnd ℂ) ht
  rw [inner_conj_symm] at ht'
  simpa only [starRingEnd_apply, star_star] using ht'

end Masullo.NativePettisLinear
end

noncomputable section
namespace Masullo.NativePettisVectorBound
open MeasureTheory MasulloGRH Masullo.NativeRep Masullo.NativeTranslationWeaklyMeasurable Masullo.NativePettisLinear Masullo.NativeTranslationBound
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)

theorem nativePettisVector_bound (F : Lp ℂ 2 mu) :
    ‖nativePettisVector K mu alpha s ha hs h hh hc F‖ ≤
      (∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu) * ‖F‖ := by
  rw [nativePettisVector, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound
  · apply mul_nonneg _ (norm_nonneg F)
    apply integral_nonneg
    intro g
    unfold nativeTranslationBound
    positivity
  · intro V
    exact nativePettisLinear_bound K mu alpha s ha hs h hh hc F V

def nativeConvolutionLinear : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun := nativePettisVector K mu alpha s ha hs h hh hc
  map_add' F G := by
    apply ext_inner_left ℂ
    intro V
    rw [inner_add_right]
    simp only [nativePettisVector_pairing]
    rw [← integral_add
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc F V)
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc G V)]
    apply integral_congr_ae
    filter_upwards [] with g
    rw [map_add, inner_add_right, mul_add]
  map_smul' c F := by
    apply ext_inner_left ℂ
    intro V
    simp only [RingHom.id_apply, inner_smul_right, nativePettisVector_pairing]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with g
    rw [map_smul, inner_smul_right]
    ring

/-- Actual compact-kernel weak convolution on the native completed half-weight
realization. No bounded convolution or orbit-integrability premise is assumed. -/
def nativeConvolutionCLM : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (nativeConvolutionLinear K mu alpha s ha hs h hh hc).mkContinuous
    (∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu)
    (nativePettisVector_bound K mu alpha s ha hs h hh hc)

theorem nativeConvolutionCLM_pairing (F V : Lp ℂ 2 mu) :
    inner ℂ V (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu :=
  nativePettisVector_pairing K mu alpha s ha hs h hh hc F V

end Masullo.NativePettisVectorBound

-- The preceding native convolution construction is inherited verbatim from H.

namespace Masullo.ClosedSubspaceConvolution
open MeasureTheory MasulloGRH Masullo.NativeRep Masullo.NativePettisVectorBound
open scoped InnerProductSpace
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
variable (E : Submodule ℂ (Lp ℂ 2 mu)) [E.HasOrthogonalProjection]
variable (hE : ∀ g F, F ∈ E → nativeTranslationCLM K mu alpha s ha hs g F ∈ E)
include hE

/-- Actual same-Haar convolution preserves any closed native translation
submodule. Convolution invariance is DERIVED from scalar Pettis integration. -/
theorem actual_closed_subspace_convolution (F : Lp ℂ 2 mu) (hF : F ∈ E) :
    nativeConvolutionCLM K mu alpha s ha hs h hh hc F ∈ E := by
  rw [← E.orthogonal_orthogonal]
  change ∀ V ∈ E.orthogonal, inner ℂ V
    (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) = 0
  intro V hV
  rw [nativeConvolutionCLM_pairing]
  apply integral_eq_zero_of_ae
  filter_upwards [] with g
  have hz : inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) = 0 :=
    inner_eq_zero_symm.mp (hV _ (hE g F hF))
  simp only [hz, mul_zero, Pi.zero_apply]

/-- PAQ=0, where Q is the actual geometric projection and P=1-Q.
No commutation of A with either orthogonal factor is asserted. -/
theorem actual_PAQ_zero :
    (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - E.starProjection).comp
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc)).comp E.starProjection = 0 := by
  apply ContinuousLinearMap.ext
  intro F
  change nativeConvolutionCLM K mu alpha s ha hs h hh hc (E.starProjection F) -
    E.starProjection (nativeConvolutionCLM K mu alpha s ha hs h hh hc (E.starProjection F)) = 0
  apply sub_eq_zero.mpr
  exact (Submodule.starProjection_eq_self_iff.mpr
    (actual_closed_subspace_convolution K mu alpha s ha hs h hh hc E hE _
      (E.starProjection_apply_mem F))).symm

/-- BOTH genuine left factors, convolution first. The geometric off-diagonal
QAP is retained; translation-invariance of E does not make E reducing. -/
theorem actual_global_convolution_blocks (F : Lp ℂ 2 mu) :
    let A := nativeConvolutionCLM K mu alpha s ha hs h hh hc
    let Q := E.starProjection
    (A F - Q (A F) = A (F-Q F) - Q (A (F-Q F))) ∧
    (Q (A F) = A (Q F) + Q (A (F-Q F))) := by
  dsimp only
  have hi := Submodule.starProjection_eq_self_iff.mpr
    (actual_closed_subspace_convolution K mu alpha s ha hs h hh hc E hE _
      (E.starProjection_apply_mem F))
  simp only [map_sub, hi]
  constructor <;> abel

/-- A geometric candidate's complete defect splits into its geometric-input
error and its spectral-input error. Checking only global theta inputs cannot
remove the second summand, even if its range is geometric. -/
theorem actual_global_candidate_defect
    (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (F : Lp ℂ 2 mu) :
    let A := nativeConvolutionCLM K mu alpha s ha hs h hh hc
    let Q := E.starProjection
    T F-Q (A F) = (T (Q F)-A (Q F)) +
      (T (F-Q F)-Q (A (F-Q F))) := by
  dsimp only
  have hi := Submodule.starProjection_eq_self_iff.mpr
    (actual_closed_subspace_convolution K mu alpha s ha hs h hh hc E hE _
      (E.starProjection_apply_mem F))
  simp only [map_sub, hi]
  abel

end Masullo.ClosedSubspaceConvolution

namespace PIntervalConvolution
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
open Masullo.NativePettisVectorBound

noncomputable def intervalHalfWeight (l r s t : ℝ) : ℝ :=
  Real.exp (max (l*t) (r*t)) * (1+t^2)^(s/4)

/-- Exact nonsymmetric-interval reduction; no endpoint is discarded. -/
theorem interval_max (l r t : ℝ) (hlr : l ≤ r) :
    max (l*t) (r*t) = ((l+r)/2)*t + ((r-l)/2)*|t| := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht, max_eq_right (mul_le_mul_of_nonneg_right hlr ht)]
    ring
  · have ht' : t ≤ 0 := le_of_not_ge ht
    rw [abs_of_nonpos ht', max_eq_left (mul_le_mul_of_nonpos_right hlr ht')]
    ring

theorem interval_halfWeight (l r s t : ℝ) (hlr : l ≤ r) :
    intervalHalfWeight l r s t =
      Real.exp (((l+r)/2)*t) * nativeHalfWeight ((r-l)/2) s t := by
  unfold intervalHalfWeight nativeHalfWeight
  rw [interval_max l r t hlr, Real.exp_add]
  ring

variable (K : Type*) [Field K] [NumberField K]

noncomputable def radialTwist (b : ℝ) (x : HeckeIdeleClasses K) : ℂ :=
  Complex.exp ((b : ℂ) * (classLog K x : ℂ))

theorem radialTwist_mul (b : ℝ) (g x : HeckeIdeleClasses K) :
    radialTwist K b (g*x) = radialTwist K b g * radialTwist K b x := by
  unfold radialTwist
  rw [classLog_mul, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem radialTwist_continuous (b : ℝ) : Continuous (radialTwist K b) := by
  unfold radialTwist
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (classLog_continuous K))).cexp

theorem twisted_test_compact (b : ℝ) (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Continuous (fun g => radialTwist K b g * h g) ∧
      HasCompactSupport (fun g => radialTwist K b g * h g) :=
  ⟨(radialTwist_continuous K b).mul hh, hc.mul_left⟩

/-- Conjugation by the midpoint twist preserves inverse-input convolution
and twists its KERNEL by the same midpoint. The measure is unchanged. -/
theorem interval_convolution_conjugacy
    (mu : Measure (HeckeIdeleClasses K)) (b : ℝ)
    (h f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    radialTwist K b x * (∫ g, h g * f (g⁻¹*x) ∂mu) =
      ∫ g, (radialTwist K b g * h g) *
        (radialTwist K b (g⁻¹*x) * f (g⁻¹*x)) ∂mu := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  have ht : radialTwist K b x =
      radialTwist K b g * radialTwist K b (g⁻¹*x) := by
    rw [← radialTwist_mul, mul_inv_cancel_left]
  rw [ht]
  ring

/-- The original interval weight becomes the centered weight on the
midpoint-twisted function, for every number field and every Haar measure. -/
theorem interval_memLp_iff
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ) (hlr : l ≤ r)
    (f : HeckeIdeleClasses K → ℂ) :
    MemLp (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) * f x) 2 mu ↔
      MemLp (fun x => (nativeHalfWeight ((r-l)/2) s (classLog K x) : ℂ) *
        (radialTwist K ((l+r)/2) x * f x)) 2 mu := by
  have he : (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) * f x) =
      (fun x => (nativeHalfWeight ((r-l)/2) s (classLog K x) : ℂ) *
        (radialTwist K ((l+r)/2) x * f x)) := by
    funext x
    rw [interval_halfWeight l r s _ hlr]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, radialTwist]
    ring
  rw [he]

variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Bounded actual convolution in the nonsymmetric interval realization.
Both requested test partners instantiate h separately. -/
noncomputable def intervalConvolutionCLM
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h) :
    Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  nativeConvolutionCLM K mu ((r-l)/2) s (by linarith) hs
    (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2

/-- The genuine closed-source projection is on the left. Source translation
invariance is the displayed remaining arithmetic application premise. -/
theorem interval_PA_source_zero
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [E.HasOrthogonalProjection]
    (hE : ∀ g F, F ∈ E →
      Masullo.NativeRep.nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g F ∈ E) :
    (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - E.starProjection).comp
      (intervalConvolutionCLM K mu l r s hlr hs h hh hc)).comp E.starProjection = 0 := by
  exact Masullo.ClosedSubspaceConvolution.actual_PAQ_zero K mu ((r-l)/2) s
    (by linarith) hs (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2 E hE

end PIntervalConvolution


-- P original-Haar lemmas, compiled independently before assembly.

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


-- Reviewed exact elementary blocks by participant D.
namespace DReview
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
/-- The physical cutoff is on the actual class logarithm. -/
def physicalBand (n : ℕ) : Set (HeckeIdeleClasses K) :=
  {x | |classLog K x| ≤ (n : ℝ)}

theorem physicalBand_measurable (n : ℕ) : MeasurableSet (physicalBand K n) :=
  measurableSet_le (classLog_continuous K).measurable.abs measurable_const

/-- A fixed original-Haar diagonal is exhausted in the physical variable. -/
theorem originalHaar_physical_limit (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun n => ∫ x, (physicalBand K n).indicator d x ∂mu)
      atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · intro n
    exact hd.aestronglyMeasurable.indicator (physicalBand_measurable K n)
  · exact hd.norm
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ physicalBand K n <;> simp [hx])
  · apply Filter.Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : x ∈ physicalBand K n := hN.trans (by exact_mod_cast hn)
    simp [hx]

/-- The same actual quotient logarithm reverses sign under inversion. -/
theorem classLog_inv (x : HeckeIdeleClasses K) : classLog K x⁻¹ = -classLog K x := by
  have h1 := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h1
  have hz : classLog K 1 = 0 := by linarith
  have hi := classLog_mul K x x⁻¹
  rw [mul_inv_cancel, hz] at hi
  linarith

/-- Reverse conjugation, retaining complex tests. -/
noncomputable def sharp (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  star (phi x⁻¹)

theorem sharp_log (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    sharp K (fun y => (classLog K y : ℂ) * phi y) x =
      -(classLog K x : ℂ) * sharp K phi x := by
  simp [sharp, classLog_inv, star_mul, mul_comm]

theorem sharp_compact (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi) :
    Continuous (sharp K phi) ∧ HasCompactSupport (sharp K phi) := by
  refine ⟨hh.star.comp continuous_inv, ?_⟩
  exact (hc.comp_homeomorph (Homeomorph.inv (HeckeIdeleClasses K))).comp_left
    (show star (0 : ℂ) = 0 by simp)

/-- Both manuscript kernels meet the same compact-continuity hypotheses. -/
theorem both_sharp_tests_compact (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi) :
    (Continuous (sharp K phi) ∧ HasCompactSupport (sharp K phi)) ∧
    (Continuous (sharp K (fun x => (classLog K x : ℂ) * phi x)) ∧
      HasCompactSupport (sharp K (fun x => (classLog K x : ℂ) * phi x))) := by
  refine ⟨sharp_compact K phi hh hc, ?_⟩
  exact sharp_compact K _
    ((Complex.continuous_ofReal.comp (classLog_continuous K)).mul hh) hc.mul_left

/-- Vanishing on the full norm-one subgroup is preserved by sharp. -/
theorem sharp_vanishes_normOne (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (x : HeckeIdeleClasses K) (hx : classLog K x = 0) : sharp K phi x = 0 := by
  have hi : classLog K x⁻¹ = 0 := by rw [classLog_inv, hx, neg_zero]
  simp [sharp, hphi x⁻¹ hi]


end DReview

-- Reviewed source-closure and directed exhaustion proofs by participant O.
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

namespace PCombinedReview
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OSourceClosure
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Both original tests on the literal two-moment source closure, for a
nonsymmetric interval. Convolution is constructed, and source invariance is
derived from the displayed original theta translation supplier. -/
theorem both_tests_original_source
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (B : HeckeIdeleClasses K → V →ₗ[ℂ] V)
    (c0 cF : HeckeIdeleClasses K → ℂ)
    (h0 : ∀ g f, e0 (B g f) = c0 g * e0 f)
    (hF : ∀ g f, eF (B g f) = cF g * eF f)
    (hint : ∀ g f,
      Masullo.NativeRep.nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g
        (Theta f) = Theta (restrictedAction e0 eF (B g) (c0 g) (cF g) (h0 g) (hF g) f))
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let S := (sourceClosure e0 eF Theta).starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - S
    (P.comp A0).comp S = 0 ∧ (P.comp A1).comp S = 0 := by
  have hE : ∀ g F, F ∈ sourceClosure e0 eF Theta →
      Masullo.NativeRep.nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g F ∈
        sourceClosure e0 eF Theta := by
    intro g
    exact theta_closure_invariant e0 eF Theta _ (B g) (c0 g) (cF g)
      (h0 g) (hF g) (hint g)
  have tests := DReview.both_sharp_tests_compact K phi hh hc
  exact ⟨interval_PA_source_zero K mu l r s hlr hs _ tests.1.1 tests.1.2 _ hE,
    interval_PA_source_zero K mu l r s hlr hs _ tests.2.1 tests.2.2 _ hE⟩

/-- The midpoint reduction preserves every fixed compact character component. -/
theorem midpoint_preserves_component (b : ℝ)
    (chi : UnitaryHeckeCharacter K) (h : HeckeIdeleClasses K → ℂ)
    (hh : ∀ c x, classLog K c = 0 → h (c*x) = (classCharacter K chi c : ℂ) * h x)
    (c x : HeckeIdeleClasses K) (hc : classLog K c = 0) :
    radialTwist K b (c*x) * h (c*x) =
      (classCharacter K chi c : ℂ) * (radialTwist K b x * h x) := by
  rw [radialTwist_mul, hh c x hc]
  have hz : radialTwist K b c = 1 := by simp [radialTwist, hc]
  rw [hz, one_mul]
  ring

end PCombinedReview



set_option linter.unusedSectionVars false
/- Insert after the existing native arithmetic definitions. No duplicate arithmetic prefix.
   Extracted from checked JThetaDescent; closure invariance remains owned by O. -/
namespace Masullo.IdeleTheta
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual principal-idele series from the proof of Theorem 2.2.3.4.
For original Schwartz--Bruhat tests its convergence is Lemma 2.2.2.1;
that analytic theorem is not asserted here by use of the totalized tsum. -/
noncomputable def ideleTheta (f : HeckeAdeles K → ℂ) (x : HeckeIdeles K) : ℂ :=
  ∑' u : Kˣ, f ((principalIdele K u * x).val)

/-- Representative independence is proved by actual principal-idele reindexing,
not assumed as an arbitrary invariance field on the theta map. -/
theorem ideleTheta_principal (f : HeckeAdeles K → ℂ)
    (v : Kˣ) (x : HeckeIdeles K) :
    ideleTheta K f (principalIdele K v * x) = ideleTheta K f x := by
  have h := (Equiv.mulRight v).tsum_eq
    (fun u : Kˣ => f ((principalIdele K u * x).val))
  change (∑' u : Kˣ, f ((principalIdele K (u*v) * x).val)) = _ at h
  simpa only [ideleTheta, map_mul, mul_assoc] using h

/-- The original principal series descended to the existing arithmetic quotient.
No arbitrary quotient function, representative selector, or descent axiom is used. -/
noncomputable def classTheta (f : HeckeAdeles K → ℂ) : HeckeIdeleClasses K → ℂ :=
  Quotient.lift (ideleTheta K f) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    change ideleTheta K f x = ideleTheta K f y
    rw [hy, ideleTheta_principal])

/-- Exact original series formula, with the actual number-field embedding. -/
theorem classTheta_mk (f : HeckeAdeles K → ℂ) (x : HeckeIdeles K) :
    classTheta K f (QuotientGroup.mk x) =
      ∑' u : Kˣ, f (algebraMap K (HeckeAdeles K) (u : K) * x.val) := rfl

/-- The convergence hypothesis is independent of the representative. -/
theorem theta_summable_principal_iff (f : HeckeAdeles K → ℂ)
    (v : Kˣ) (x : HeckeIdeles K) :
    Summable (fun u : Kˣ => f ((principalIdele K u * (principalIdele K v * x)).val)) ↔
      Summable (fun u : Kˣ => f ((principalIdele K u * x).val)) := by
  have h := (Equiv.mulRight v).summable_iff
    (f := fun u : Kˣ => f ((principalIdele K u * x).val))
  change Summable (fun u : Kˣ => f ((principalIdele K (u*v) * x).val)) ↔ _ at h
  simpa only [map_mul, mul_assoc] using h

end Masullo.IdeleTheta
/- Appended to the exact arithmetic/convolution source prefix in JOriginalTheta.lean.
   No imports: this fragment is compiled as part of that standalone unit. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Masullo.GenuineMellinJet Masullo.IdeleTheta
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped BigOperators NumberField
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The original Schwartz--Bruhat space, described by finite tensor sums. -/
def IsOriginalBruhat (f : HeckeAdeles K → ℂ) : Prop :=
  ∃ n : ℕ, ∃ p : Fin n → SchwartzMap (mixedSpace K) ℂ,
    ∃ q : Fin n → FiniteAdeleRing (𝓞 K) K → ℂ,
      (∀ i, IsLocallyConstant (q i) ∧ HasCompactSupport (q i)) ∧
      ∀ x, f x = ∑ i, p i (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q i x.2

/-- Full principal sum, with the original twist and native half-weight. -/
def normalizedTheta (a alpha s : ℝ) (f : HeckeAdeles K → ℂ)
    (x : HeckeIdeleClasses K) : ℂ :=
  (nativeHalfWeight alpha s (classLog K x) : ℂ) *
    (Real.exp (a * classLog K x) : ℂ) * classTheta K f x

variable [MeasurableSpace (HeckeAdeles K)]

/-- Explicit admission obligations: original tests, BOTH moments, convergence,
    the actual compact-character isotype, and membership in the native Hilbert space.
    In particular, totalized `tsum` is never used to assert theta convergence. -/
structure AdmittedSource (addHaar : Measure (HeckeAdeles K))
    (nu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (a alpha s : ℝ) where
  test : HeckeAdeles K → ℂ
  bruhat : IsOriginalBruhat K test
  zero_value : test 0 = 0
  integrable : Integrable test addHaar
  zero_integral : ∫ x, test x ∂addHaar = 0
  summable : ∀ x : HeckeIdeles K,
    Summable (fun u : Kˣ => test ((principalIdele K u * x).val))
  character : ∀ b x : HeckeIdeleClasses K, classLog K b = 0 →
    classTheta K test (b*x) = (classCharacter K chi b : ℂ) * classTheta K test x
  memLp : MemLp (normalizedTheta K a alpha s test) 2 nu

def sourceVector {addHaar : Measure (HeckeAdeles K)}
    {nu : Measure (HeckeIdeleClasses K)} {chi : UnitaryHeckeCharacter K}
    {a alpha s : ℝ} (f : AdmittedSource K addHaar nu chi a alpha s) : Lp ℂ 2 nu :=
  f.memLp.toLp (normalizedTheta K a alpha s f.test)

def sourceSpan (addHaar : Measure (HeckeAdeles K))
    (nu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (a alpha s : ℝ) : Submodule ℂ (Lp ℂ 2 nu) :=
  Submodule.span ℂ (Set.range (sourceVector K (addHaar := addHaar)
    (nu := nu) (chi := chi) (a := a) (alpha := alpha) (s := s)))

/-- Closure of the actual admitted BOTH-moment principal-series sources. -/
def thetaClosure (addHaar : Measure (HeckeAdeles K))
    (nu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (a alpha s : ℝ) : Submodule ℂ (Lp ℂ 2 nu) :=
  (sourceSpan K addHaar nu chi a alpha s).topologicalClosure

theorem sourceVector_mem_closure {addHaar : Measure (HeckeAdeles K)}
    {nu : Measure (HeckeIdeleClasses K)} {chi : UnitaryHeckeCharacter K}
    {a alpha s : ℝ} (f : AdmittedSource K addHaar nu chi a alpha s) :
    sourceVector K f ∈ thetaClosure K addHaar nu chi a alpha s := by
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)

/-- Haar rescaling is exact; there is no probability normalization in A_mu. -/
theorem original_haar_convolution (nu : Measure (HeckeIdeleClasses K))
    (V : ℝ) (hV : 0 ≤ V) (h f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    (∫ g, h g * f (g⁻¹*x) ∂(ENNReal.ofReal V • nu)) =
      (V : ℂ) * (∫ g, h g * f (g⁻¹*x) ∂nu) := by
  simp only [integral_smul_measure, ENNReal.toReal_ofReal hV, Complex.real_smul]

def dilateTest (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ) :
    HeckeAdeles K → ℂ := fun x => f (g.val * x)

theorem actual_theta_dilate (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (x : HeckeIdeleClasses K) :
    classTheta K (dilateTest K g f) x = classTheta K f (QuotientGroup.mk g * x) := by
  induction x using Quotient.inductionOn with
  | h y =>
    change (∑' u : Kˣ, f (g.val * (principalIdele K u * y).val)) =
      ∑' u : Kˣ, f ((principalIdele K u * (g*y)).val)
    apply tsum_congr
    intro u
    congr 1
    simp only [Units.val_mul]
    ring

theorem dilation_preserves_zero_value (g : HeckeIdeles K)
    (f : HeckeAdeles K → ℂ) (hf : f 0 = 0) : dilateTest K g f 0 = 0 := by
  simpa [dilateTest] using hf

end
end JThetaAttachment



/- Append after JThetaAttachment definitions and the checked OSourceClosure block.
   This fragment uses the actual principal-idele theta vectors. -/
namespace OArithmeticClosure
open MeasureTheory MasulloGRH JThetaAttachment OSourceClosure Filter
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable (chi : UnitaryHeckeCharacter K) (a alpha s : ℝ)

instance thetaClosure_hasOrthogonalProjection :
    (thetaClosure K addHaar mu chi a alpha s).HasOrthogonalProjection := by
  unfold thetaClosure
  infer_instance

/-- A presentation of the already admitted theta span in the common linear-map
interface. Its domain is the actual theta span, not the original Bruhat space.
Both original moments are imposed in `AdmittedSource` before taking this span. -/
def arithmeticSourceMap :
    twoMomentSource
      (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0 →ₗ[ℂ] Lp ℂ 2 mu :=
  (sourceSpan K addHaar mu chi a alpha s).subtype.comp
    (twoMomentSource
      (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0).subtype

theorem arithmeticSourceMap_range :
    LinearMap.range (arithmeticSourceMap K addHaar mu chi a alpha s) =
      sourceSpan K addHaar mu chi a alpha s := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact v.val.property
  · intro hx
    refine ⟨⟨⟨x, hx⟩, ?_⟩, rfl⟩
    constructor <;> rfl

/-- This equality discharges the common closure interface for the chosen
arithmetic theta family; it assumes neither density nor spectral completeness. -/
theorem arithmetic_sourceClosure_eq :
    sourceClosure
      (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi a alpha s) =
      thetaClosure K addHaar mu chi a alpha s := by
  change (LinearMap.range (arithmeticSourceMap K addHaar mu chi a alpha s)).topologicalClosure = _
  rw [arithmeticSourceMap_range]
  rfl

/-- The geometric projection fixes every actual admitted principal theta
vector. This is an application theorem on J's arithmetic definitions. -/
theorem actual_theta_projected
    (f : AdmittedSource K addHaar mu chi a alpha s) :
    (thetaClosure K addHaar mu chi a alpha s).starProjection (sourceVector K f) =
      sourceVector K f :=
  Submodule.starProjection_eq_self_iff.mpr (sourceVector_mem_closure K f)

/-- Finite subsets of the actual principal-theta family recover the genuine
geometric and complementary projections on every vector. The result is strong
convergence, with no assertion of a trace or nuclear-norm limit. -/
theorem actual_theta_source_exhaustion (y : Lp ℂ 2 mu) :
    let F := fun T : Finset (Lp ℂ 2 mu) => Submodule.span ℂ
      ((T : Set (Lp ℂ 2 mu)) ∩ Set.range
        (sourceVector K (addHaar := addHaar) (nu := mu) (chi := chi)
          (a := a) (alpha := alpha) (s := s)))
    ∃ p : Finset (Lp ℂ 2 mu) → Lp ℂ 2 mu,
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (F T) hp y) ∧
      Tendsto p atTop (𝓝 ((thetaClosure K addHaar mu chi a alpha s).starProjection y)) ∧
      Tendsto (fun T => y - p T) atTop
        (𝓝 (y - (thetaClosure K addHaar mu chi a alpha s).starProjection y)) := by
  obtain ⟨p, hp, ht⟩ := Masullo.NestedProjection.actual_family_projection_tendsto
    (Set.range (sourceVector K (addHaar := addHaar) (nu := mu) (chi := chi)
      (a := a) (alpha := alpha) (s := s))) y
  exact ⟨p, hp, ht, tendsto_const_nhds.sub ht⟩

/-- Closure invariance from a proved action on the concrete admitted generators.
The displayed generator action is an application obligation, not its proof. -/
theorem actual_theta_closure_invariant
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (hgen : ∀ f : AdmittedSource K addHaar mu chi a alpha s,
      A (sourceVector K f) ∈ sourceSpan K addHaar mu chi a alpha s) :
    ∀ x ∈ thetaClosure K addHaar mu chi a alpha s,
      A x ∈ thetaClosure K addHaar mu chi a alpha s := by
  have hspan : ∀ x ∈ sourceSpan K addHaar mu chi a alpha s,
      A x ∈ sourceSpan K addHaar mu chi a alpha s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨f, rfl⟩ := hx; exact hgen f
    | zero => simp
    | add x y hx hy hpx hpy =>
      simpa only [map_add] using
        (sourceSpan K addHaar mu chi a alpha s).add_mem hpx hpy
    | smul c x hx hpx =>
      simpa only [map_smul] using
        (sourceSpan K addHaar mu chi a alpha s).smul_mem c hpx
  intro x hx
  exact map_mem_closure A.continuous hx hspan

end
end OArithmeticClosure


/- Insert after JThetaDefinitions.lean and the common Masullo.NativeRep block. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Masullo.GenuineMellinJet Masullo.IdeleTheta Masullo.NativeHalfWeightAddLe
open Masullo.NativeRep
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

theorem classTheta_const_mul (c : ℂ) (f : HeckeAdeles K → ℂ)
    (x : HeckeIdeleClasses K) :
    classTheta K (fun y => c * f y) x = c * classTheta K f x := by
  induction x using Quotient.inductionOn with
  | h y => exact tsum_mul_left

theorem theta_classLog_one : classLog K (1 : HeckeIdeleClasses K) = 0 := by
  have h := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h
  linarith

theorem theta_classLog_inv (g : HeckeIdeleClasses K) :
    classLog K g⁻¹ = -classLog K g := by
  have h := classLog_mul K g⁻¹ g
  rw [inv_mul_cancel, theta_classLog_one] at h
  linarith

/-- The actual original test action realizing weighted left translation.
The minus sign and inverse dilation follow from g⁻¹x in convolution. -/
def originalAction (a : ℝ) (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ) :
    HeckeAdeles K → ℂ :=
  fun y => (Real.exp (-a * classLog K (QuotientGroup.mk g)) : ℂ) *
    dilateTest K g⁻¹ f y

theorem normalizedTheta_originalAction (a alpha s : ℝ) (g : HeckeIdeles K)
    (f : HeckeAdeles K → ℂ) (x : HeckeIdeleClasses K) :
    normalizedTheta K a alpha s (originalAction K a g f) x =
      (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        ((Real.exp (a * classLog K ((QuotientGroup.mk g)⁻¹*x)) : ℂ) *
          classTheta K f ((QuotientGroup.mk g)⁻¹*x)) := by
  unfold normalizedTheta originalAction
  rw [classTheta_const_mul, actual_theta_dilate]
  change _ = (nativeHalfWeight alpha s (classLog K x) : ℂ) *
    ((Real.exp (a * classLog K ((QuotientGroup.mk g⁻¹)*x)) : ℂ) * _)
  rw [classLog_mul]
  have hinv : classLog K (QuotientGroup.mk g⁻¹) =
      -classLog K (QuotientGroup.mk g) := by
    simpa only [QuotientGroup.mk_inv] using
      theta_classLog_inv K (QuotientGroup.mk g)
  rw [hinv]
  have hexp : Real.exp (a * (-classLog K (QuotientGroup.mk g) + classLog K x)) =
      Real.exp (a * classLog K x) * Real.exp (-a * classLog K (QuotientGroup.mk g)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, Complex.ofReal_mul, QuotientGroup.mk_inv]
  ring

theorem originalAction_zero (a : ℝ) (g : HeckeIdeles K)
    (f : HeckeAdeles K → ℂ) (hf : f 0 = 0) : originalAction K a g f 0 = 0 := by
  simp [originalAction, dilateTest, hf]

theorem originalAction_summable (a : ℝ) (g : HeckeIdeles K)
    (f : HeckeAdeles K → ℂ)
    (hf : ∀ x : HeckeIdeles K,
      Summable (fun u : Kˣ => f ((principalIdele K u*x).val)))
    (x : HeckeIdeles K) :
    Summable (fun u : Kˣ => originalAction K a g f ((principalIdele K u*x).val)) := by
  have he (u : Kˣ) : g⁻¹.val * (principalIdele K u*x).val =
      (principalIdele K u*(g⁻¹*x)).val := by
    simp only [Units.val_mul]
    ring
  simpa only [originalAction, dilateTest, he] using
    (hf (g⁻¹*x)).mul_left (Real.exp (-a * classLog K (QuotientGroup.mk g)) : ℂ)

theorem originalAction_character (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (hf : ∀ b x : HeckeIdeleClasses K, classLog K b = 0 →
      classTheta K f (b*x) = (classCharacter K chi b : ℂ) * classTheta K f x)
    (b x : HeckeIdeleClasses K) (hb : classLog K b = 0) :
    classTheta K (originalAction K a g f) (b*x) =
      (classCharacter K chi b : ℂ) * classTheta K (originalAction K a g f) x := by
  unfold originalAction
  rw [classTheta_const_mul, classTheta_const_mul, actual_theta_dilate, actual_theta_dilate]
  rw [← mul_assoc, mul_comm (QuotientGroup.mk g⁻¹) b, mul_assoc, hf b _ hb]
  ring

variable [MeasurableMul (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (a alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

include ha hs in
theorem originalAction_memLp (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (hf : MemLp (normalizedTheta K a alpha s f) 2 mu) :
    MemLp (normalizedTheta K a alpha s (originalAction K a g f)) 2 mu := by
  have h := actual_weighted_translation_memLp K mu alpha s ha hs
    (fun x => (Real.exp (a * classLog K x) : ℂ) * classTheta K f x)
    (by
      have he : normalizedTheta K a alpha s f =
          (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
            ((Real.exp (a * classLog K x) : ℂ) * classTheta K f x)) := by
        funext x
        exact mul_assoc _ _ _
      rwa [← he]) (QuotientGroup.mk g)
  have he : normalizedTheta K a alpha s (originalAction K a g f) =
      (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        ((Real.exp (a * classLog K ((QuotientGroup.mk g)⁻¹*x)) : ℂ) *
          classTheta K f ((QuotientGroup.mk g)⁻¹*x))) :=
    funext (normalizedTheta_originalAction K a alpha s g f)
  rw [he]
  exact h

/-- Exact arithmetic application of the assembly's normalized L² translation.
The transformed L² membership is proved from hf, not separately assumed. -/
theorem sourceVector_translation (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (hf : MemLp (normalizedTheta K a alpha s f) 2 mu) :
    nativeTranslationCLM K mu alpha s ha hs (QuotientGroup.mk g)
      (hf.toLp (normalizedTheta K a alpha s f)) =
      (originalAction_memLp K mu a alpha s ha hs g f hf).toLp
        (normalizedTheta K a alpha s (originalAction K a g f)) := by
  apply Lp.ext
  have ht := (measurePreserving_mul_left mu (QuotientGroup.mk g)⁻¹).quasiMeasurePreserving.ae hf.coeFn_toLp
  filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs (QuotientGroup.mk g)
      (hf.toLp (normalizedTheta K a alpha s f)), ht,
    (originalAction_memLp K mu a alpha s ha hs g f hf).coeFn_toLp] with x h1 h2 h3
  rw [h1, h3, h2, normalizedTheta_originalAction]
  unfold normalizedTheta
  have hw : (nativeHalfWeight alpha s (classLog K ((QuotientGroup.mk g)⁻¹*x)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  field_simp

end
end JThetaAttachment


set_option maxHeartbeats 1200000
/- Insert after JThetaDefinitions and JThetaEquivariance. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Masullo.GenuineMellinJet Masullo.IdeleTheta Masullo.NativeRep
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped NumberField NNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- Original archimedean multiplication, used to pull back Schwartz functions. -/
def thetaArchDilation (g : HeckeIdeles K) : mixedSpace K ≃ₗ[ℝ] mixedSpace K where
  toFun x := InfiniteAdeleRing.ringEquiv_mixedSpace K g.val.1 * x
  invFun x := InfiniteAdeleRing.ringEquiv_mixedSpace K g.inv.1 * x
  left_inv x := by
    dsimp only
    rw [← mul_assoc, ← map_mul]
    have h : g.inv.1 * g.val.1 = 1 := congrArg Prod.fst g.inv_val
    rw [h, map_one, one_mul]
  right_inv x := by
    dsimp only
    rw [← mul_assoc, ← map_mul]
    have h : g.val.1 * g.inv.1 = 1 := congrArg Prod.fst g.val_inv
    rw [h, map_one, one_mul]
  map_add' x y := mul_add _ x y
  map_smul' c x := mul_smul_comm c _ x

/-- Explicit continuity avoids the generic finite-dimensional conversion. -/
def thetaArchDilationContinuous (g : HeckeIdeles K) :
    mixedSpace K ≃L[ℝ] mixedSpace K where
  toLinearEquiv := thetaArchDilation K g
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

/-- Original finite multiplication is a homeomorphism, with actual inverse. -/
def thetaFiniteDilation (g : HeckeIdeles K) :
    FiniteAdeleRing (𝓞 K) K ≃ₜ FiniteAdeleRing (𝓞 K) K where
  toFun x := g.val.2*x
  invFun x := g.inv.2*x
  left_inv x := by
    dsimp only
    rw [← mul_assoc, show g.inv.2*g.val.2 = 1 from congrArg Prod.snd g.inv_val, one_mul]
  right_inv x := by
    dsimp only
    rw [← mul_assoc, show g.val.2*g.inv.2 = 1 from congrArg Prod.snd g.val_inv, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem originalBruhat_dilate (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) : IsOriginalBruhat K (dilateTest K g f) := by
  rcases hf with ⟨n, p, q, hq, he⟩
  refine ⟨n, (fun i => SchwartzMap.compCLMOfContinuousLinearEquiv (F := ℂ) ℂ
    (thetaArchDilationContinuous K g) (p i)),
    (fun i => q i ∘ thetaFiniteDilation K g), ?_, ?_⟩
  · intro i
    exact ⟨(hq i).1.comp_continuous (thetaFiniteDilation K g).continuous,
      (hq i).2.comp_homeomorph (thetaFiniteDilation K g)⟩
  · intro x
    rw [dilateTest, he]
    apply Finset.sum_congr rfl
    intro i hi
    rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    change p i (InfiniteAdeleRing.ringEquiv_mixedSpace K (g.val.1*x.1)) * q i (g.val.2*x.2) =
      p i (InfiniteAdeleRing.ringEquiv_mixedSpace K g.val.1 *
        InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q i (g.val.2*x.2)
    rw [map_mul]

theorem originalBruhat_const_mul (c : ℂ) (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) : IsOriginalBruhat K (fun y => c*f y) := by
  rcases hf with ⟨n, p, q, hq, he⟩
  refine ⟨n, (fun i => c • p i), q, hq, ?_⟩
  intro x
  change c * f x = _
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change c * (p i _ * q i _) = (c * p i _) * q i _
  ring

theorem originalAction_bruhat (a : ℝ) (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) : IsOriginalBruhat K (originalAction K a g f) :=
  originalBruhat_const_mul K _ _ (originalBruhat_dilate K g⁻¹ f hf)

/-- The full original additive adele action; no product normalization is imposed. -/
def thetaAdeleDilation (g : HeckeIdeles K) : HeckeAdeles K ≃ₜ+ HeckeAdeles K where
  toFun x := g.val*x
  invFun x := g.inv*x
  left_inv x := by dsimp only; rw [← mul_assoc, g.inv_val, one_mul]
  right_inv x := by dsimp only; rw [← mul_assoc, g.val_inv, one_mul]
  map_add' x y := mul_add _ _ _
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

variable [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]

instance thetaAdeleDilation_map_isAddHaar (g : HeckeIdeles K) :
    (addHaar.map (thetaAdeleDilation K g)).IsAddHaarMeasure :=
  ContinuousAddEquiv.isAddHaarMeasure_map _ _

/-- Haar multiplier is constructed from the original measure, not postulated. -/
def thetaAddHaarScalar (g : HeckeIdeles K) : ℝ≥0 :=
  Measure.addHaarScalarFactor (addHaar.map (thetaAdeleDilation K g)) addHaar

theorem thetaAdeleDilation_map (g : HeckeIdeles K) :
    addHaar.map (thetaAdeleDilation K g) = thetaAddHaarScalar K addHaar g • addHaar :=
  Measure.isAddLeftInvariant_eq_smul _ _

theorem original_dilation_integrable (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (hf : Integrable f addHaar) : Integrable (dilateTest K g f) addHaar := by
  have h : Integrable f (addHaar.map (thetaAdeleDilation K g)) := by
    rw [thetaAdeleDilation_map]
    exact hf.smul_measure_nnreal
  exact (thetaAdeleDilation K g).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mp h

theorem original_dilation_integral (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ) :
    (∫ y, dilateTest K g f y ∂addHaar) =
      (thetaAddHaarScalar K addHaar g : ℝ) • ∫ y, f y ∂addHaar := by
  calc
    _ = ∫ y, f y ∂(addHaar.map (thetaAdeleDilation K g)) :=
      ((thetaAdeleDilation K g).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map f).symm
    _ = _ := by rw [thetaAdeleDilation_map, integral_smul_nnreal_measure]; rfl

variable [MeasurableMul (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (chi : UnitaryHeckeCharacter K) (a alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- Translation acts on every admitted ORIGINAL source. Bruhat membership,
both moments, convergence, character and native L² admission are all proved. -/
def translatedSource (g : HeckeIdeles K)
    (f : AdmittedSource K addHaar mu chi a alpha s) :
    AdmittedSource K addHaar mu chi a alpha s where
  test := originalAction K a g f.test
  bruhat := originalAction_bruhat K a g f.test f.bruhat
  zero_value := originalAction_zero K a g f.test f.zero_value
  integrable := (original_dilation_integrable K addHaar g⁻¹ f.test f.integrable).const_mul _
  zero_integral := by
    change (∫ y, (Real.exp (-a * classLog K (QuotientGroup.mk g)) : ℂ) *
      dilateTest K g⁻¹ f.test y ∂addHaar) = 0
    rw [integral_const_mul, original_dilation_integral, f.zero_integral, smul_zero, mul_zero]
  summable := originalAction_summable K a g f.test f.summable
  character := originalAction_character K chi a g f.test f.character
  memLp := originalAction_memLp K mu a alpha s ha hs g f.test f.memLp

/-- Exact generator-level arithmetic application, suitable for O's closure proof. -/
theorem translatedSource_equivariance (g : HeckeIdeles K)
    (f : AdmittedSource K addHaar mu chi a alpha s) :
    nativeTranslationCLM K mu alpha s ha hs (QuotientGroup.mk g) (sourceVector K f) =
      sourceVector K (translatedSource K addHaar mu chi a alpha s ha hs g f) :=
  sourceVector_translation K mu a alpha s ha hs g f.test f.memLp

end
end JThetaAttachment

/- Append after OThetaClosure, JThetaEquivariance and JOriginalSourceAction.
   This discharges the concrete generator-invariance application. -/
namespace OArithmeticClosure
open MeasureTheory MasulloGRH JThetaAttachment Masullo.NativeRep
open Masullo.IdeleClassGeometry PIntervalConvolution
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (chi : UnitaryHeckeCharacter K) (a alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- Native translation preserves the actual admitted theta closure. Original
test preservation and weighted intertwining are discharged by J's construction. -/
theorem arithmetic_theta_translation_invariant (g : HeckeIdeleClasses K) :
    ∀ x ∈ thetaClosure K addHaar mu chi a alpha s,
      nativeTranslationCLM K mu alpha s ha hs g x ∈
        thetaClosure K addHaar mu chi a alpha s := by
  apply actual_theta_closure_invariant K addHaar mu chi a alpha s
    (nativeTranslationCLM K mu alpha s ha hs g)
  intro f
  induction g using Quotient.inductionOn with
  | h u =>
    rw [translatedSource_equivariance K addHaar mu chi a alpha s ha hs u f]
    exact Submodule.subset_span
      ⟨translatedSource K addHaar mu chi a alpha s ha hs u f, rfl⟩

variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both convolution-first spectral operators kill the actual geometric
source input. The theorem has no theta-equivariance or source-invariance
hypothesis: their arithmetic applications have been proved above. -/
theorem both_tests_arithmetic_PA_source_zero
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let S := (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - S
    (P.comp A0).comp S = 0 ∧ (P.comp A1).comp S = 0 := by
  have hE : ∀ g x, x ∈ thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →
      nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g x ∈
        thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s := by
    intro g
    exact arithmetic_theta_translation_invariant K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s (by linarith) hs g
  have tests := DReview.both_sharp_tests_compact K phi hh hc
  exact ⟨interval_PA_source_zero K mu l r s hlr hs _ tests.1.1 tests.1.2 _ hE,
    interval_PA_source_zero K mu l r s hlr hs _ tests.2.1 tests.2.2 _ hE⟩

end
end OArithmeticClosure


/- Insert after JThetaDefinitions, JThetaEquivariance and JOriginalSourceAction.
   O owns the closed-span/projection application of this exact family. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.IdeleTheta Masullo.NativeRep
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- Original two-moment tests with explicit analytic admission, without a
fixed compact-character restriction. Admission of all original tests is a
separate theorem; no completeness claim is hidden in this structure. -/
structure AdmittedOriginalSource (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ) where
  test : HeckeAdeles K → ℂ
  bruhat : IsOriginalBruhat K test
  zero_value : test 0 = 0
  integrable : Integrable test addHaar
  zero_integral : ∫ x, test x ∂addHaar = 0
  summable : ∀ x : HeckeIdeles K,
    Summable (fun u : Kˣ => test ((principalIdele K u * x).val))
  memLp : MemLp (normalizedTheta K a alpha s test) 2 mu

def originalSourceVector {addHaar : Measure (HeckeAdeles K)}
    {mu : Measure (HeckeIdeleClasses K)} {a alpha s : ℝ}
    (f : AdmittedOriginalSource K addHaar mu a alpha s) : Lp ℂ 2 mu :=
  f.memLp.toLp (normalizedTheta K a alpha s f.test)

/-- Every previously chosen character source belongs to the same unrestricted
original-source family, with exactly the same arithmetic theta vector. -/
def forgetCharacter {addHaar : Measure (HeckeAdeles K)}
    {mu : Measure (HeckeIdeleClasses K)} {chi : UnitaryHeckeCharacter K}
    {a alpha s : ℝ} (f : AdmittedSource K addHaar mu chi a alpha s) :
    AdmittedOriginalSource K addHaar mu a alpha s where
  test := f.test
  bruhat := f.bruhat
  zero_value := f.zero_value
  integrable := f.integrable
  zero_integral := f.zero_integral
  summable := f.summable
  memLp := f.memLp

theorem sourceVector_forgetCharacter {addHaar : Measure (HeckeAdeles K)}
    {mu : Measure (HeckeIdeleClasses K)} {chi : UnitaryHeckeCharacter K}
    {a alpha s : ℝ} (f : AdmittedSource K addHaar mu chi a alpha s) :
    originalSourceVector K (forgetCharacter K f) = sourceVector K f := rfl

/-- P's common full-domain name is an alias of the checked unrestricted
domain, so the source objects and their admission proofs are not duplicated. -/
abbrev AdmittedFullSource (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ) :=
  AdmittedOriginalSource K addHaar mu a alpha s

abbrev fullSourceVector {addHaar : Measure (HeckeAdeles K)}
    {mu : Measure (HeckeIdeleClasses K)} {a alpha s : ℝ}
    (f : AdmittedFullSource K addHaar mu a alpha s) : Lp ℂ 2 mu :=
  originalSourceVector K f

def fullSourceSpan (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ) :
    Submodule ℂ (Lp ℂ 2 mu) :=
  Submodule.span ℂ (Set.range (fullSourceVector K (addHaar := addHaar)
    (mu := mu) (a := a) (alpha := alpha) (s := s)))

/-- The literal unrestricted admitted theta closure for the common operator. -/
def fullThetaClosure (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ) :
    Submodule ℂ (Lp ℂ 2 mu) :=
  (fullSourceSpan K addHaar mu a alpha s).topologicalClosure

theorem fullSourceVector_mem_closure {addHaar : Measure (HeckeAdeles K)}
    {mu : Measure (HeckeIdeleClasses K)} {a alpha s : ℝ}
    (f : AdmittedFullSource K addHaar mu a alpha s) :
    fullSourceVector K f ∈ fullThetaClosure K addHaar mu a alpha s :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)

theorem sourceSpan_le_fullSourceSpan (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (a alpha s : ℝ) :
    sourceSpan K addHaar mu chi a alpha s ≤ fullSourceSpan K addHaar mu a alpha s := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f, rfl⟩
  exact Submodule.subset_span ⟨forgetCharacter K f, rfl⟩

theorem thetaClosure_le_fullThetaClosure (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (a alpha s : ℝ) :
    thetaClosure K addHaar mu chi a alpha s ≤ fullThetaClosure K addHaar mu a alpha s := by
  change closure (sourceSpan K addHaar mu chi a alpha s : Set (Lp ℂ 2 mu)) ⊆
    closure (fullSourceSpan K addHaar mu a alpha s : Set (Lp ℂ 2 mu))
  exact closure_mono (sourceSpan_le_fullSourceSpan K addHaar mu chi a alpha s)

variable [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (a alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- The same manuscript action on original tests preserves all admission
fields; no transformed-source or character-completeness premise is supplied. -/
def translateOriginalSource (g : HeckeIdeles K)
    (f : AdmittedOriginalSource K addHaar mu a alpha s) :
    AdmittedOriginalSource K addHaar mu a alpha s where
  test := originalAction K a g f.test
  bruhat := originalAction_bruhat K a g f.test f.bruhat
  zero_value := originalAction_zero K a g f.test f.zero_value
  integrable := (original_dilation_integrable K addHaar g⁻¹ f.test f.integrable).const_mul _
  zero_integral := by
    change (∫ y, (Real.exp (-a * classLog K (QuotientGroup.mk g)) : ℂ) *
      dilateTest K g⁻¹ f.test y ∂addHaar) = 0
    rw [integral_const_mul, original_dilation_integral, f.zero_integral, smul_zero, mul_zero]
  summable := originalAction_summable K a g f.test f.summable
  memLp := originalAction_memLp K mu a alpha s ha hs g f.test f.memLp

/-- Exact unrestricted-source equivariance for O's closure application. -/
theorem translateOriginalSource_equivariance (g : HeckeIdeles K)
    (f : AdmittedOriginalSource K addHaar mu a alpha s) :
    nativeTranslationCLM K mu alpha s ha hs (QuotientGroup.mk g)
      (originalSourceVector K f) =
      originalSourceVector K (translateOriginalSource K addHaar mu a alpha s ha hs g f) :=
  sourceVector_translation K mu a alpha s ha hs g f.test f.memLp

end
end JThetaAttachment

/- Insert after JAllCharacterSource and the existing O/source-exhaustion core.
   This uses the actual unrestricted admitted original theta family, without
   identifying analytic admission with a theorem about all manuscript tests. -/
namespace OAllCharacterClosure
open MeasureTheory MasulloGRH JThetaAttachment OSourceClosure Filter
open Masullo.NativeRep Masullo.IdeleClassGeometry PIntervalConvolution
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable (a alpha s : ℝ)

instance fullThetaClosure_hasOrthogonalProjection :
    (fullThetaClosure K addHaar mu a alpha s).HasOrthogonalProjection := by
  unfold fullThetaClosure
  infer_instance

/-- Presentation of the actual admitted span in the existing linear interface.
The zero maps impose no new conditions: both moments were imposed on each test. -/
def fullSourceMap :
    twoMomentSource (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0 →ₗ[ℂ] Lp ℂ 2 mu :=
  (fullSourceSpan K addHaar mu a alpha s).subtype.comp
    (twoMomentSource (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0).subtype

theorem fullSourceMap_range :
    LinearMap.range (fullSourceMap K addHaar mu a alpha s) =
      fullSourceSpan K addHaar mu a alpha s := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact v.val.property
  · intro hx
    refine ⟨⟨⟨x, hx⟩, ?_⟩, rfl⟩
    constructor <;> rfl

theorem full_sourceClosure_eq :
    sourceClosure (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu a alpha s) =
      fullThetaClosure K addHaar mu a alpha s := by
  change (LinearMap.range (fullSourceMap K addHaar mu a alpha s)).topologicalClosure = _
  rw [fullSourceMap_range]
  rfl

/-- Exact dependent projection transport, following the repaired P interface. -/
theorem full_sourceProjection_eq :
    (sourceClosure (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu a alpha s)).starProjection =
      (fullThetaClosure K addHaar mu a alpha s).starProjection := by
  exact congrArg
    (fun W : Submodule ℂ (Lp ℂ 2 mu) => W.topologicalClosure.starProjection)
    (fullSourceMap_range K addHaar mu a alpha s)

theorem actual_full_theta_projected
    (f : AdmittedOriginalSource K addHaar mu a alpha s) :
    (fullThetaClosure K addHaar mu a alpha s).starProjection (originalSourceVector K f) =
      originalSourceVector K f :=
  Submodule.starProjection_eq_self_iff.mpr
    (fullSourceVector_mem_closure K f)

/-- Directed finite original-theta projection exhaustion on every completed input. -/
theorem actual_full_theta_source_exhaustion (y : Lp ℂ 2 mu) :
    let F := fun T : Finset (Lp ℂ 2 mu) => Submodule.span ℂ
      ((T : Set (Lp ℂ 2 mu)) ∩ Set.range (originalSourceVector K
        (addHaar := addHaar) (mu := mu) (a := a) (alpha := alpha) (s := s)))
    ∃ p : Finset (Lp ℂ 2 mu) → Lp ℂ 2 mu,
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (F T) hp y) ∧
      Tendsto p atTop (𝓝 ((fullThetaClosure K addHaar mu a alpha s).starProjection y)) ∧
      Tendsto (fun T => y-p T) atTop
        (𝓝 (y-(fullThetaClosure K addHaar mu a alpha s).starProjection y)) := by
  obtain ⟨p, hp, ht⟩ := Masullo.NestedProjection.actual_family_projection_tendsto
    (Set.range (originalSourceVector K (addHaar := addHaar) (mu := mu)
      (a := a) (alpha := alpha) (s := s))) y
  exact ⟨p, hp, ht, tendsto_const_nhds.sub ht⟩

variable [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable [mu.IsMulLeftInvariant]
variable (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- Source invariance is proved on the actual unrestricted arithmetic family. -/
theorem fullTheta_translation_invariant (g : HeckeIdeleClasses K) :
    ∀ x ∈ fullThetaClosure K addHaar mu a alpha s,
      nativeTranslationCLM K mu alpha s ha hs g x ∈
        fullThetaClosure K addHaar mu a alpha s := by
  have hgen : ∀ f : AdmittedOriginalSource K addHaar mu a alpha s,
      nativeTranslationCLM K mu alpha s ha hs g (originalSourceVector K f) ∈
        fullSourceSpan K addHaar mu a alpha s := by
    intro f
    induction g using Quotient.inductionOn with
    | h u =>
      rw [translateOriginalSource_equivariance K addHaar mu a alpha s ha hs u f]
      exact Submodule.subset_span ⟨translateOriginalSource K addHaar mu a alpha s ha hs u f, rfl⟩
  have hspan : ∀ x ∈ fullSourceSpan K addHaar mu a alpha s,
      nativeTranslationCLM K mu alpha s ha hs g x ∈
        fullSourceSpan K addHaar mu a alpha s := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨f, rfl⟩ := hx; exact hgen f
    | zero => simp
    | add x y hx hy hpx hpy =>
      simpa only [map_add] using (fullSourceSpan K addHaar mu a alpha s).add_mem hpx hpy
    | smul c x hx hpx =>
      simpa only [map_smul] using (fullSourceSpan K addHaar mu a alpha s).smul_mem c hpx
  intro x hx
  exact map_mem_closure (nativeTranslationCLM K mu alpha s ha hs g).continuous hx hspan

variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both actual convolution-first residuals kill every geometric source input.
No fixed character or free equivariance hypothesis occurs in this statement. -/
theorem both_tests_full_PA_source_zero
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ)*phi x)) tests.2.1 tests.2.2
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S
    (P.comp A0).comp S = 0 ∧ (P.comp A1).comp S = 0 := by
  have hE : ∀ g x, x ∈ fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s →
      nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g x ∈
        fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s := by
    intro g
    exact fullTheta_translation_invariant K addHaar mu (a+(l+r)/2) ((r-l)/2) s
      (by linarith) hs g
  have tests := DReview.both_sharp_tests_compact K phi hh hc
  exact ⟨interval_PA_source_zero K mu l r s hlr hs _ tests.1.1 tests.1.2 _ hE,
    interval_PA_source_zero K mu l r s hlr hs _ tests.2.1 tests.2.2 _ hE⟩

end
end OAllCharacterClosure
set_option pp.proofs false


-- Exact dependency block: L checked required-test block
namespace LIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OSourceClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The two required tests, without changing their complex conjugation convention. -/
def requiredTest (phi : HeckeIdeleClasses K → ℂ) (q : Fin 2) :
    HeckeIdeleClasses K → ℂ :=
  if q = 0 then DReview.sharp K phi
  else DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)

@[simp] theorem requiredTest_zero (phi : HeckeIdeleClasses K → ℂ) :
    requiredTest K phi 0 = DReview.sharp K phi := by simp [requiredTest]

@[simp] theorem requiredTest_one (phi : HeckeIdeleClasses K → ℂ) :
    requiredTest K phi 1 = DReview.sharp K (fun x => (classLog K x : ℂ) * phi x) := by
  simp [requiredTest]

theorem requiredTest_log_sign (phi : HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K) :
    requiredTest K phi 1 x = -(classLog K x : ℂ) * requiredTest K phi 0 x := by
  simpa only [requiredTest_zero, requiredTest_one] using DReview.sharp_log K phi x

theorem requiredTest_compact (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi) (q : Fin 2) :
    Continuous (requiredTest K phi q) ∧ HasCompactSupport (requiredTest K phi q) := by
  have ht := DReview.both_sharp_tests_compact K phi hh hc
  fin_cases q
  · simpa only [requiredTest_zero] using ht.1
  · simpa only [requiredTest_one] using ht.2

/-- The full norm-one vanishing assumption of 12.5.1.1 is discharged for both tests. -/
theorem requiredTest_vanishes_normOne (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (x : HeckeIdeleClasses K) (hx : classLog K x = 0) :
    requiredTest K phi q x = 0 := by
  fin_cases q
  · exact DReview.sharp_vanishes_normOne K phi hphi x hx
  · change requiredTest K phi 1 x = 0
    rw [requiredTest_log_sign, hx]
    simp

/-- Consequently both free convolution diagonals vanish at the group identity. -/
theorem requiredTest_at_one (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) :
    requiredTest K phi q 1 = 0 := by
  apply requiredTest_vanishes_normOne K phi hphi q
  have h := Masullo.WeightedIdeleClass.classLog_mul K
    (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h
  linarith

/-- The geometric-minus-spectral diagonal sign is pointwise, on a chosen kernel.
This avoids restricting an arbitrary product-a.e. representative to the diagonal. -/
theorem both_kernel_diagonal_sign (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (spectralKernel : Fin 2 → HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (q : Fin 2) (x : HeckeIdeleClasses K) :
    requiredTest K phi q (x * x⁻¹) - spectralKernel q x x = -spectralKernel q x x := by
  rw [mul_inv_cancel, requiredTest_at_one K phi hphi q, zero_sub]

section ActualConvolution
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The actual interval convolutions for both sharp families retain their signed
order remainder.  The displayed theta equivariance has exactly the seed's scope. -/
theorem both_tests_order_remainder
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (B : HeckeIdeleClasses K → V →ₗ[ℂ] V)
    (c0 cF : HeckeIdeleClasses K → ℂ)
    (h0 : ∀ g f, e0 (B g f) = c0 g * e0 f)
    (hF : ∀ g f, eF (B g f) = cF g * eF f)
    (hint : ∀ g f,
      Masullo.NativeRep.nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g
        (Theta f) = Theta (restrictedAction e0 eF (B g) (c0 g) (cF g) (h0 g) (hF g) f))
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (x : Lp ℂ 2 mu) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) ht.1 ht.2
    let S := (sourceClosure e0 eF Theta).starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - S
    P (A x) = P (A (P x)) ∧ A (P x) - P (A x) = S (A (P x)) := by
  let ht := requiredTest_compact K phi hh hc q
  let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) ht.1 ht.2
  let S := (sourceClosure e0 eF Theta).starProjection
  have hE : ∀ g F, F ∈ sourceClosure e0 eF Theta →
      Masullo.NativeRep.nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g F ∈
        sourceClosure e0 eF Theta := by
    intro g
    exact theta_closure_invariant e0 eF Theta _ (B g) (c0 g) (cF g)
      (h0 g) (hF g) (hint g)
  have hz := interval_PA_source_zero K mu l r s hlr hs
    (requiredTest K phi q) ht.1 ht.2 (sourceClosure e0 eF Theta) hE
  have he : A (S x) - S (A (S x)) = 0 := by
    have he := DFunLike.congr_fun hz x
    exact he
  have hfix : S (A (S x)) = A (S x) := (sub_eq_zero.mp he).symm
  change (A x - S (A x) = A (x-S x) - S (A (x-S x))) ∧
    (A (x-S x) - (A x-S (A x)) = S (A (x-S x)))
  simp only [map_sub, hfix]
  constructor <;> abel
end ActualConvolution
end
end LIntegrated

-- Exact dependency block: D checked nuclear-kernel/trace context
-- CHECK CONTEXT: DNuclearKernelMeasurableCheck exact proof context
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace GPointwiseCore
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integral_norm_product_le (mu : Measure X) (V W : Lp ℂ 2 mu) :
    (∫ x, ‖V x‖ * ‖W x‖ ∂mu) ≤ ‖V‖ * ‖W‖ := by
  let v : Lp ℝ 2 mu := (Lp.memLp V).norm.toLp (fun x => ‖V x‖)
  let w : Lp ℝ 2 mu := (Lp.memLp W).norm.toLp (fun x => ‖W x‖)
  have hv : ‖v‖ = ‖V‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hw : ‖w‖ = ‖W‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hi : (∫ x, ‖V x‖ * ‖W x‖ ∂mu) = inner ℝ v w := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp V).norm.coeFn_toLp, (Lp.memLp W).norm.coeFn_toLp]
      with x hx hy
    change ‖V x‖ * ‖W x‖ = inner ℝ (v x) (w x)
    rw [hx, hy]
    simp [RCLike.inner_apply, mul_comm]
  calc
    _ = inner ℝ v w := hi
    _ ≤ ‖inner ℝ v w‖ := le_abs_self _
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ = _ := by rw [hv, hw]


end GPointwiseCore

namespace ReviewM
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]
theorem integrable_complex_series (mu : Measure X) (F : ι → X → ℂ)
    (hi : ∀ i, Integrable (F i) mu)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂mu)) :
    Integrable (fun x => ∑' i, F i x) mu ∧
      (∫ x, ‖∑' i, F i x‖ ∂mu) ≤ ∑' i, ∫ x, ‖F i x‖ ∂mu := by
  classical
  have hm (i : ι) : AEMeasurable (fun x => ‖F i x‖ₑ) mu :=
    (hi i).aemeasurable.enorm
  have he : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) =
      ENNReal.ofReal (∑' i, ∫ x, ‖F i x‖ ∂mu) := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun x => norm_nonneg _) hs).symm
  have hlin : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) ≠ ⊤ := by rw [he]; exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ x ∂mu, ∑' i, ‖F i x‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlin
  have hsum : ∀ᵐ x ∂mu, Summable (fun i => F i x) := by
    filter_upwards [hae] with x hx
    apply Summable.of_norm
    have hn : (∑' i, (‖F i x‖₊ : ENNReal)) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)
  have htotal : Integrable (fun x => ∑' i, F i x) mu := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae
      (atTop : Filter (Finset ι)) (f := fun S x => ∑ i ∈ S, F i x)
      (fun S => Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hi i).1) ?_, ?_⟩
    · filter_upwards [hsum] with x hx
      exact hx.hasSum
    · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm)
        (lt_top_iff_ne_top.mpr hlin)
  refine ⟨htotal, ?_⟩
  have hbound : (∫⁻ x, ‖∑' i, F i x‖ₑ ∂mu) ≤
      ENNReal.ofReal (∑' i, ∫ x, ‖F i x‖ ∂mu) := by
    rw [← he]
    exact lintegral_mono fun x => enorm_tsum_le_tsum_enorm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [← ofReal_integral_norm_eq_lintegral_enorm htotal,
    ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _),
    ENNReal.toReal_ofReal (tsum_nonneg fun i => integral_nonneg fun x => norm_nonneg _)] at hreal
  exact hreal

theorem complex_series_ae_summable (mu : Measure X) (F : ι → X → ℂ)
    (hi : ∀ i, Integrable (F i) mu)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂mu)) :
    ∀ᵐ x ∂mu, Summable (fun i => F i x) := by
  have hm (i : ι) : AEMeasurable (fun x => ‖F i x‖ₑ) mu :=
    (hi i).aemeasurable.enorm
  have hlin : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) ≠ ⊤ := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun x => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlin
  filter_upwards [hae] with x hx
  apply Summable.of_norm
  have hn : (∑' i, (‖F i x‖₊ : ENNReal)) ≠ ⊤ := hx.ne
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)

end
end ReviewM
set_option linter.unusedSectionVars false
namespace HNormalizedKernel
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]

def haarKernel (b : X → ℝ) (V : ℝ) (U R : X → ℂ) (x y : X) : ℂ :=
  (U x / (b x : ℂ)) * ((b y : ℂ) * star (R y) / (V : ℂ))

theorem diagonal_formula (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : X → ℂ) (x : X) :
    haarKernel b V U R x x = (V : ℂ)⁻¹ * (U x * star (R x)) := by
  have hb0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  unfold haarKernel
  field_simp

theorem l2_inner_formula (nu : Measure X) (U R : Lp ℂ 2 nu) :
    (∫ x, U x * star (R x) ∂nu) = inner ℂ R U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [RCLike.inner_apply]

/-- Correct original-Haar diagonal density; no lower bound on b is needed. -/
theorem diagonal_integrable (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : Lp ℂ 2 nu) :
    Integrable (fun x => haarKernel b V U R x x) (ENNReal.ofReal V • nu) := by
  simp_rw [diagonal_formula b hb]
  exact (((Lp.memLp U).integrable_mul (Lp.memLp R).star).const_mul _).smul_measure
    (by simp)

/-- The Haar factor cancels exactly once in the diagonal trace coefficient. -/
theorem diagonal_integral (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu) :
    (∫ x, haarKernel b V U R x x ∂(ENNReal.ofReal V • nu)) = inner ℂ R U := by
  simp_rw [diagonal_formula b hb]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le, integral_const_mul,
    Complex.real_smul, l2_inner_formula]
  have hv0 : (V : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hV)
  rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]

/-- Full-input kernel action, not merely agreement on a theta core. -/
theorem kernel_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R F : Lp ℂ 2 nu) (x : X) :
    (b x : ℂ) * (∫ y, haarKernel b V U R x y * (F y / (b y : ℂ))
      ∂(ENNReal.ofReal V • nu)) = inner ℂ R F * U x := by
  have bx0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  have v0 : (V : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hV)
  have he (y : X) : haarKernel b V U R x y * (F y / (b y : ℂ)) =
      (U x / (b x : ℂ) / (V : ℂ)) * (F y * star (R y)) := by
    have by0 : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    unfold haarKernel
    field_simp
  simp_rw [he]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le, integral_const_mul,
    Complex.real_smul, l2_inner_formula]
  field_simp

/-- Contractive physical masks remove the cutoff from this canonical diagonal. -/
theorem diagonal_cutoff_limit (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu)
    (omega : ℕ → X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) (ENNReal.ofReal V • nu))
    (hbound : ∀ n, ∀ᵐ x ∂(ENNReal.ofReal V • nu), ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂(ENNReal.ofReal V • nu), Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, omega n x * haarKernel b V U R x x
      ∂(ENNReal.ofReal V • nu)) atTop (𝓝 (inner ℂ R U)) := by
  rw [← diagonal_integral nu b hb V hV U R]
  have hi := diagonal_integrable nu b hb V U R
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖haarKernel b V U R x x‖)
  · intro n
    exact (hm n).mul hi.aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa only [one_mul] using hx.mul
      (tendsto_const_nhds (x := haarKernel b V U R x x))

end
end HNormalizedKernel

/- Insert after GPointwiseCore, ReviewM.integrable_complex_series,
   ReviewM.complex_series_ae_summable and HNormalizedKernel. -/
namespace DNuclearKernel
open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

theorem tested_integrable (nu : Measure X) (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (V : Lp ℂ 2 nu) (i : ι) :
    Integrable (fun x => c i * v i x * star (V x)) nu := by
  simpa only [Pi.mul_apply, mul_assoc] using
    (((Lp.memLp (v i)).integrable_mul (Lp.memLp V).star).const_mul (c i))

theorem tested_integral_norm_le (nu : Measure X) (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (V : Lp ℂ 2 nu) (i : ι) :
    (∫ x, ‖c i * v i x * star (V x)‖ ∂nu) ≤ ‖c i‖ * ‖v i‖ * ‖V‖ := by
  simp only [norm_mul, norm_star, mul_assoc]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (GPointwiseCore.integral_norm_product_le nu (v i) V) (norm_nonneg _)

theorem tested_cost (nu : Measure X) (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖c i‖ * ‖v i‖))
    (V : Lp ℂ 2 nu) :
    Summable (fun i => ∫ x, ‖c i * v i x * star (V x)‖ ∂nu) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (tested_integral_norm_le nu c v V) (hc.mul_right ‖V‖)

/-- Absolute Hilbert-space cost gives pointwise absolute column convergence.
The finite-measure test functions are constructed from sigma-finiteness. -/
theorem ae_column_cost (nu : Measure X) [SigmaFinite nu] (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖c i‖ * ‖v i‖)) :
    ∀ᵐ x ∂nu, Summable (fun i => ‖c i‖ * ‖v i x‖) := by
  have hn (n : ℕ) : ∀ᵐ x ∂nu, x ∈ spanningSets nu n →
      Summable (fun i => ‖c i‖ * ‖v i x‖) := by
    let A := spanningSets nu n
    have hA := measurableSet_spanningSets nu n
    have hmu := measure_spanningSets_lt_top nu n
    let V : Lp ℂ 2 nu := indicatorConstLp 2 hA hmu.ne 1
    have hv : (V : X → ℂ) =ᵐ[nu] A.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have hs := ReviewM.complex_series_ae_summable nu
      (fun i x => c i * v i x * star (V x))
      (tested_integrable nu c v V) (tested_cost nu c v hc V)
    filter_upwards [hs, hv] with x hx hvx
    intro hax
    have hz := summable_norm_iff.mpr hx
    simpa [hvx, A, hax, norm_mul] using hz
  filter_upwards [ae_all_iff.mpr hn] with x hx
  have hall : x ∈ ⋃ n, spanningSets nu n := by rw [iUnion_spanningSets]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hall
  exact hx n hn

/-- The pointwise series represents the given Hilbert-space sum on all inputs. -/
theorem series_representation (nu : Measure X) [SigmaFinite nu]
    (c : ι → ℂ) (v : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖c i‖ * ‖v i‖))
    (out : Lp ℂ 2 nu) (hout : HasSum (fun i => c i • v i) out) :
    (out : X → ℂ) =ᵐ[nu] (fun x => ∑' i, c i * v i x) := by
  have hlocal (A : Set X) (hA : MeasurableSet A) (hmu : nu A < ⊤) :
      Integrable (A.indicator (fun x => ∑' i, c i * v i x)) nu ∧
      (∫ x in A, out x ∂nu) = ∫ x in A, (∑' i, c i * v i x) ∂nu := by
    let V : Lp ℂ 2 nu := indicatorConstLp 2 hA hmu.ne 1
    have hi := tested_integrable nu c v V
    have hs := tested_cost nu c v hc V
    have hv : (V : X → ℂ) =ᵐ[nu] A.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have he : (fun x => ∑' i, c i * v i x * star (V x)) =ᵐ[nu]
        A.indicator (fun x => ∑' i, c i * v i x) := by
      filter_upwards [hv] with x hx
      rw [tsum_mul_right, hx]
      by_cases ha : x ∈ A <;> simp [ha]
    refine ⟨(ReviewM.integrable_complex_series nu _ hi hs).1.congr he, ?_⟩
    have hp := (innerSL ℂ V).hasSum hout
    change HasSum (fun i => inner ℂ V (c i • v i)) (inner ℂ V out) at hp
    have hp' : HasSum (fun i => c i * inner ℂ V (v i)) (inner ℂ V out) := by
      simpa only [inner_smul_right] using hp
    rw [← L2.inner_indicatorConstLp_one hA hmu.ne, ← hp'.tsum_eq]
    have hcalc (i : ι) : (∫ x, c i * v i x * star (V x) ∂nu) =
        c i * inner ℂ V (v i) := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, mul_assoc])
    calc
      _ = ∑' i, ∫ x, c i * v i x * star (V x) ∂nu :=
        tsum_congr fun i => (hcalc i).symm
      _ = ∫ x, ∑' i, c i * v i x * star (V x) ∂nu :=
        (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq
      _ = _ := by rw [integral_congr_ae he, integral_indicator hA]
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hmu => integrableOn_Lp_of_measure_ne_top out one_le_two hmu.ne)
    (fun A hA hmu => (integrable_indicator_iff hA).mp (hlocal A hA hmu).1)
  exact fun A hA hmu => (hlocal A hA hmu).2

/-- The same original-Haar series whose diagonal is used by HOperatorTrace.
Rows are precomposed with the operator; columns carry any left projection. -/
def kernel (nu : Measure X) (b : X → ℝ) (u v : ι → Lp ℂ 2 nu)
    (x y : X) : ℂ :=
  ∑' i, HNormalizedKernel.haarKernel b 1 (v i) (u i) x y

theorem kernel_eq (nu : Measure X) (b : X → ℝ) (u v : ι → Lp ℂ 2 nu)
    (x y : X) : kernel nu b u v x y =
      (∑' i, v i x * star (u i y)) * ((b y : ℂ) / (b x : ℂ)) := by
  unfold kernel
  rw [← tsum_mul_right]
  apply tsum_congr
  intro i
  simp only [HNormalizedKernel.haarKernel, Complex.ofReal_one, div_eq_mul_inv]
  ring

theorem row_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (u v : ι → Lp ℂ 2 nu) (F : Lp ℂ 2 nu) (x : X)
    (hx : Summable (fun i => ‖u i‖ * ‖v i x‖)) :
    Integrable (fun y => kernel nu b u v x y * (F y / (b y : ℂ))) nu ∧
    (b x : ℂ) * (∫ y, kernel nu b u v x y * (F y / (b y : ℂ)) ∂nu) =
      ∑' i, inner ℂ (u i) F * v i x := by
  let f : ι → X → ℂ := fun i y => v i x * star (u i y) * F y
  have hi (i : ι) : Integrable (f i) nu := by
    simpa only [f, Pi.mul_apply, mul_assoc] using
      (((Lp.memLp (u i)).star.integrable_mul (Lp.memLp F)).const_mul (v i x))
  have hbound (i : ι) : (∫ y, ‖f i y‖ ∂nu) ≤ (‖u i‖ * ‖v i x‖) * ‖F‖ := by
    simp only [f, norm_mul, norm_star, mul_assoc]
    rw [integral_const_mul]
    calc
      _ ≤ ‖v i x‖ * (‖u i‖ * ‖F‖) := mul_le_mul_of_nonneg_left
        (GPointwiseCore.integral_norm_product_le nu (u i) F) (norm_nonneg _)
      _ = _ := by ring
  have hs : Summable (fun i => ∫ y, ‖f i y‖ ∂nu) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hbound (hx.mul_right ‖F‖)
  have hsum := ReviewM.integrable_complex_series nu f hi hs
  have hf (i : ι) : (∫ y, f i y ∂nu) = inner ℂ (u i) F * v i x := by
    have he : f i = fun y => v i x * (F y * star (u i y)) := by
      funext y
      dsimp only [f]
      ring
    rw [he, integral_const_mul, HNormalizedKernel.l2_inner_formula]
    ring
  have hk (y : X) : kernel nu b u v x y * (F y / (b y : ℂ)) =
      (b x : ℂ)⁻¹ * (∑' i, f i y) := by
    have hy0 : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    rw [kernel_eq]
    dsimp only [f]
    rw [tsum_mul_right]
    field_simp
  simp_rw [hk]
  refine ⟨hsum.1.const_mul _, ?_⟩
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
  · exact (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq.symm.trans
      (tsum_congr hf)
  · exact_mod_cast (ne_of_gt (hb x))

/-- Full-input integral action of a nuclear factor series. Scalar integrability
and the representative identity are proved from the same two hypotheses used
by H's operator-trace theorem. -/
theorem kernel_action (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hT : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i) (T F))
    (F : Lp ℂ 2 nu) :
    (∀ᵐ x ∂nu, Integrable
      (fun y => kernel nu b u v x y * (F y / (b y : ℂ))) nu) ∧
    (T F : X → ℂ) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, kernel nu b u v x y * (F y / (b y : ℂ)) ∂nu) := by
  have hcx : Summable (fun i => ‖(‖u i‖ : ℂ)‖ * ‖v i‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hc
  have hx := ae_column_cost nu (fun i => (‖u i‖ : ℂ)) v hcx
  have hx' : ∀ᵐ x ∂nu, Summable (fun i => ‖u i‖ * ‖v i x‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hx
  have hcF : Summable (fun i => ‖inner ℂ (u i) F‖ * ‖v i‖) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ (hc.mul_right ‖F‖)
    intro i
    calc
      _ ≤ (‖u i‖ * ‖F‖) * ‖v i‖ := mul_le_mul_of_nonneg_right
        (norm_inner_le_norm (u i) F) (norm_nonneg _)
      _ = _ := by ring
  have hout := series_representation nu (fun i => inner ℂ (u i) F) v hcF (T F) (hT F)
  constructor
  · filter_upwards [hx'] with x hx
    exact (row_action nu b hb u v F x hx).1
  · filter_upwards [hx', hout] with x hx hox
    exact hox.trans (row_action nu b hb u v F x hx).2.symm

/-- Admission and identification of the actual integral output in the completed
space follow from its proved action; they are not additional hypotheses. -/
theorem kernel_toLp (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hT : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i) (T F))
    (F : Lp ℂ 2 nu) :
    let kF := fun x => (b x : ℂ) *
      ∫ y, kernel nu b u v x y * (F y / (b y : ℂ)) ∂nu
    ∃ hm : MemLp kF 2 nu, hm.toLp kF = T F := by
  dsimp only
  have hact := (kernel_action nu b hb T u v hc hT F).2
  have hm := (Lp.memLp (T F)).ae_eq hact
  refine ⟨hm, ?_⟩
  apply Lp.ext
  exact hm.coeFn_toLp.trans hact.symm

end
end DNuclearKernel


/- Insert after DNuclearKernelActionFragment. -/
namespace DNuclearKernel
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The nuclear cost proves convergence on the product measure, separately
from the direct diagonal series used for the trace. -/
theorem kernel_series_ae_summable (nu : Measure X) [SigmaFinite nu]
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    ∀ᵐ p : X × X ∂nu.prod nu,
      Summable (fun i => v i p.1 * star (u i p.2)) := by
  have hm (i : ι) : Measurable
      (fun p : X × X => ‖v i p.1 * star (u i p.2)‖ₑ) :=
    (((Lp.stronglyMeasurable (v i)).comp_measurable measurable_fst).mul
      ((Lp.stronglyMeasurable (u i)).star.comp_measurable measurable_snd)).measurable.enorm
  have hx : ∀ᵐ x ∂nu, Summable (fun i => ‖u i‖ * ‖v i x‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      ae_column_cost nu (fun i => (‖u i‖ : ℂ)) v
        (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hc)
  have hxy : ∀ᵐ x ∂nu, ∀ᵐ y ∂nu,
      (∑' i, ‖v i x * star (u i y)‖ₑ) < ⊤ := by
    filter_upwards [hx] with x hxc
    have hxc' : Summable (fun i => ‖v i x‖ * ‖u i‖) := by
      simpa only [mul_comm] using hxc
    filter_upwards [ae_column_cost nu (fun i => v i x) u hxc'] with y hy
    have hn : Summable (fun i => ‖v i x * star (u i y)‖) := by
      simpa only [norm_mul, norm_star] using hy
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _) hn]
    exact ENNReal.ofReal_lt_top
  have hprod : ∀ᵐ p : X × X ∂nu.prod nu,
      (∑' i, ‖v i p.1 * star (u i p.2)‖ₑ) < ⊤ :=
    (Measure.ae_prod_iff_ae_ae
      (measurableSet_lt (Measurable.ennreal_tsum hm) measurable_const)).mpr hxy
  filter_upwards [hprod] with p hp
  apply Summable.of_norm
  have hn : (∑' i, (‖v i p.1 * star (u i p.2)‖₊ : ENNReal)) ≠ ⊤ := hp.ne
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)

/-- The full weighted kernel is measurable for the product of the original
Haar measure. Its action and diagonal are identified separately. -/
theorem kernel_aestronglyMeasurable (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hbm : Measurable b)
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    AEStronglyMeasurable (fun p : X × X => kernel nu b u v p.1 p.2) (nu.prod nu) := by
  have hraw : AEStronglyMeasurable
      (fun p : X × X => ∑' i, v i p.1 * star (u i p.2)) (nu.prod nu) := by
    apply aestronglyMeasurable_of_tendsto_ae
      (atTop : Filter (Finset ι))
      (f := fun S p => ∑ i ∈ S, v i p.1 * star (u i p.2))
    · intro S
      apply Finset.aestronglyMeasurable_fun_sum
      intro i _
      exact (((Lp.stronglyMeasurable (v i)).comp_measurable measurable_fst).mul
        ((Lp.stronglyMeasurable (u i)).star.comp_measurable measurable_snd)).aestronglyMeasurable
    · filter_upwards [kernel_series_ae_summable nu u v hc] with p hp
      exact hp.hasSum
  simp_rw [kernel_eq]
  exact hraw.mul
    (((hbm.complex_ofReal.comp measurable_snd).div
      (hbm.complex_ofReal.comp measurable_fst)).aestronglyMeasurable)

end
end DNuclearKernel


-- CHECK CONTEXT: HCompressionTraceCheck exact proof context
set_option linter.unusedSectionVars false

namespace Masullo.TraceClass
open scoped InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def stdHilbertBasis (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    HilbertBasis (exists_hilbertBasis 𝕜 E).choose 𝕜 E :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose
/-- Hilbert-basis trace, used below only after proving its HasSum statement. -/
def trace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (stdHilbertBasis ℂ H i) (T (stdHilbertBasis ℂ H i))
end
end Masullo.TraceClass



-- EXACT FRAGMENT: HNuclearSupportFragment.lean
/- Source proof blocks generalized only in the nuclear index type from Masullo/Spectral/NuclearTrace.lean,
   through nuclear_diagonal_hasSum. Insert after HTraceFragment; no imports. -/
open scoped InnerProductSpace
namespace Masullo.NuclearDiagonal
variable {κ : Type*}

theorem rankOne_diagonal_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : ι → H) (hb : Orthonormal ℂ b) (u v : H) :
    Summable (fun i => ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ∧
    (∑' i, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
  have key (S : Finset ι) :
      ∑ i ∈ S, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
    have hn (i : ι) : ‖⟪u, b i⟫_ℂ‖ = ‖⟪b i, u⟫_ℂ‖ := norm_inner_symm _ _
    simp only [norm_mul, hn]
    calc
      _ ≤ Real.sqrt (∑ i ∈ S, ‖⟪b i, u⟫_ℂ‖ ^ 2) *
          Real.sqrt (∑ i ∈ S, ‖⟪b i, v⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (‖u‖ ^ 2) * Real.sqrt (‖v‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt (hb.sum_inner_products_le u))
          (Real.sqrt_le_sqrt (hb.sum_inner_products_le v))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖u‖ * ‖v‖ := by simp
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) key,
    le_of_tendsto (summable_of_sum_le (fun _ => norm_nonneg _) key).hasSum
      (Filter.Eventually.of_forall key)⟩

theorem nuclear_diagonal_interchange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun p : κ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) ∧
    (∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) =
      ∑' n, ⟪u n, v n⟫_ℂ := by
  have hf (n : κ) := rankOne_diagonal_bound b b.orthonormal (u n) (v n)
  have hs : Summable (fun n => ∑' i, ‖⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ‖) :=
    Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun n => (hf n).2) hc
  have hp : Summable (fun p : κ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) := by
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun n => (hf n).1, hs⟩
  refine ⟨hp, ?_⟩
  calc
    _ = ∑' n, ∑' i, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ := hp.of_norm.tsum_comm
    _ = _ := tsum_congr (fun n => (b.hasSum_inner_mul_inner (u n) (v n)).tsum_eq)


theorem nuclear_operator_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : κ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' n, ⟪u n, v n⟫_ℂ := by
  have hd (i : ι) :
      (∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [inner_smul_right] using hh.tsum_eq
  calc
    _ = ∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ :=
      tsum_congr (fun i => (hd i).symm)
    _ = _ := (nuclear_diagonal_interchange b u v hc).2

end Masullo.NuclearDiagonal

set_option maxHeartbeats 400000
namespace Masullo.NuclearSeries
variable {κ : Type*}
open scoped InnerProductSpace

/-- Absolute convergence is derived from the existing operator expansion.
Both summable costs and the genuine HasSum equation are indispensable. -/
theorem nuclear_diagonal_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : κ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    Summable (fun i => ‖⟪b i, T (b i)⟫_ℂ‖) := by
  let c : κ → ι → ℂ := fun n i => ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ
  have hp : Summable (fun p : κ × ι => ‖c p.1 p.2‖) :=
    (Masullo.NuclearDiagonal.nuclear_diagonal_interchange b u v hc).1
  have hs : Summable (fun p : ι × κ => ‖c p.2 p.1‖) := hp.prod_symm
  have hr : (∀ i, Summable (fun n => ‖c n i‖)) ∧
      Summable (fun i => ∑' n, ‖c n i‖) :=
    (summable_prod_of_nonneg (fun p : ι × κ => norm_nonneg (c p.2 p.1))).1 hs
  have hd (i : ι) : (∑' n, c n i) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [c, inner_smul_right] using hh.tsum_eq
  have hbound (i : ι) : ‖⟪b i, T (b i)⟫_ℂ‖ ≤ ∑' n, ‖c n i‖ := by
    calc
      ‖⟪b i, T (b i)⟫_ℂ‖ = ‖∑' n, c n i‖ := congrArg norm (hd i).symm
      _ ≤ ∑' n, ‖c n i‖ := norm_tsum_le_tsum_norm (hr.1 i)
  exact Summable.of_nonneg_of_le
    (fun i => norm_nonneg (⟪b i, T (b i)⟫_ℂ)) hbound hr.2

/-- The native application sets T = P.comp (A h). The theorem does not
assume summability of a prescribed zero sum or reverse the operator order. -/
theorem nuclear_diagonal_hasSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : κ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪u n, v n⟫_ℂ) := by
  have hs := (nuclear_diagonal_summable b T u v hc hT).of_norm.hasSum
  rwa [Masullo.NuclearDiagonal.nuclear_operator_diagonal b T u v hc hT] at hs


end Masullo.NuclearSeries


-- EXACT FRAGMENT: HNuclearTraceFragment.lean
/- Append after HTraceFragment and HNuclearSupportFragment. -/
namespace HOperatorTrace
open ContinuousLinearMap Filter
open scoped InnerProductSpace Topology
noncomputable section
variable {κ : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical Hilbert-basis trace of the actual completed operator.
Both the norm cost and the equation on every input are retained explicitly. -/
theorem nuclear_trace (T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) :
    Masullo.TraceClass.trace T = ∑' n, inner ℂ (u n) (v n) :=
  Masullo.NuclearDiagonal.nuclear_operator_diagonal
    (Masullo.TraceClass.stdHilbertBasis ℂ H) T u v hc hT

/-- The same trace is an absolutely convergent diagonal in every Hilbert basis. -/
theorem nuclear_trace_basis (T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x))
    {ι : Type*} (e : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (e i) (T (e i))‖) ∧
    HasSum (fun i => inner ℂ (e i) (T (e i))) (Masullo.TraceClass.trace T) := by
  rw [nuclear_trace T u v hc hT]
  exact ⟨Masullo.NuclearSeries.nuclear_diagonal_summable e T u v hc hT,
    Masullo.NuclearSeries.nuclear_diagonal_hasSum e T u v hc hT⟩

/-- Any bounded left factor acts on the output columns, with its actual norm. -/
theorem nuclear_left_cost (P : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun n => ‖u n‖ * ‖P (v n)‖) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) (hc.mul_left ‖P‖)
  calc
    ‖u n‖ * ‖P (v n)‖ ≤ ‖u n‖ * (‖P‖ * ‖v n‖) :=
      mul_le_mul_of_nonneg_left (P.le_opNorm (v n)) (norm_nonneg _)
    _ = ‖P‖ * (‖u n‖ * ‖v n‖) := by ring

theorem nuclear_left_factor (P T : H →L[ℂ] H) (u v : κ → H)
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) (x : H) :
    HasSum (fun n => inner ℂ (u n) x • P (v n)) ((P.comp T) x) := by
  have h := P.hasSum (hT x)
  simpa only [map_smul, ContinuousLinearMap.comp_apply] using h

/-- Convolution-first order is preserved by construction; no cyclicity is used. -/
theorem nuclear_left_trace (P T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) :
    Masullo.TraceClass.trace (P.comp T) = ∑' n, inner ℂ (u n) (P (v n)) :=
  nuclear_trace (P.comp T) u (fun n => P (v n))
    (nuclear_left_cost P u v hc) (nuclear_left_factor P T u v hT)

/-- Projection-complement trace with the literal minus sign. -/
theorem nuclear_complement_trace (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) :
    Masullo.TraceClass.trace (((1 : H →L[ℂ] H) - S.starProjection).comp T) =
      ∑' n, inner ℂ (u n) (v n - S.starProjection (v n)) := by
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
    nuclear_left_trace ((1 : H →L[ℂ] H) - S.starProjection) T u v hc hT

end
end HOperatorTrace


-- EXACT FRAGMENT: HCompressionExtensionFragment.lean
/- Append after HNuclearTraceFragment. This transfers a nuclear expansion on
   the actual geometric spectral subspace to the ambient PA operator. -/
namespace HOperatorTrace
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compressed operator extends to exactly PA when the already-proved
source-invariance equation PA S=0 is supplied. No AP commutation is used. -/
theorem source_compression_extension (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0) :
    Sᗮ.subtypeL.comp ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)).comp
      Sᗮ.orthogonalProjection) = ((1 : H →L[ℂ] H)-S.starProjection).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  have hz' : A (S.starProjection x) - S.starProjection (A (S.starProjection x)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply] using
        congrArg (fun T : H →L[ℂ] H => T x) hz
  change Sᗮ.starProjection (A (Sᗮ.starProjection x)) = A x-S.starProjection (A x)
  simp only [Submodule.starProjection_orthogonal_val, map_sub]
  rw [(sub_eq_zero.mp hz').symm]
  abel

end
end HOperatorTrace


-- EXACT FRAGMENT: HCompressionTraceFragment.lean
/- Append after HNuclearTraceFragment and HCompressionExtensionFragment. This transfers a nuclear expansion on
   the actual geometric spectral subspace to the ambient PA operator. -/
namespace HOperatorTrace
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extend a nuclear expansion from the actual geometric subspace to its
ambient orthogonal extension. This generic intermediate keeps subtype
elaboration separate from the concrete PA compression. -/
theorem orthogonal_extension_factor (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (B : E →L[ℂ] E) (u v : κ → E)
    (hB : ∀ y : E, HasSum (fun i => inner ℂ (u i) y • v i) (B y)) (x : H) :
    HasSum (fun i => inner ℂ (u i : H) x • (v i : H))
      ((E.subtypeL.comp (B.comp E.orthogonalProjection)) x) := by
  have h := E.subtypeL.hasSum (hB (E.orthogonalProjection x))
  have hi (i : κ) : inner ℂ (u i) (E.orthogonalProjection x) =
      inner ℂ (u i : H) x := by
    change inner ℂ (u i : H) (E.starProjection x) = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (u i).property]
  simpa only [map_smul, hi, ContinuousLinearMap.comp_apply] using h

/-- A proved nuclear factorization of the compression yields a nuclear
factorization of the actual ambient PA, with the same norm-product cost. -/
theorem source_compression_factor (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0)
    (u v : κ → Sᗮ)
    (hB : ∀ y : Sᗮ, HasSum (fun i => inner ℂ (u i) y • v i)
      ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) y)) (x : H) :
    HasSum (fun i => inner ℂ (u i : H) x • (v i : H))
      ((((1 : H →L[ℂ] H)-S.starProjection).comp A) x) := by
  have h := orthogonal_extension_factor Sᗮ
    (Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) u v hB x
  rw [source_compression_extension S A hz] at h
  exact h

/-- The global ambient PA trace is the trace of its actual compression,
with nuclearity witnessed by the supplied summable factorization there. -/
theorem source_compression_trace (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0)
    (u v : κ → Sᗮ) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hB : ∀ y : Sᗮ, HasSum (fun i => inner ℂ (u i) y • v i)
      ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) y)) :
    Masullo.TraceClass.trace (((1 : H →L[ℂ] H)-S.starProjection).comp A) =
      Masullo.TraceClass.trace (Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) := by
  rw [nuclear_trace _ (fun i => (u i : H)) (fun i => (v i : H)) hc
    (source_compression_factor S A hz u v hB), nuclear_trace _ u v hc hB]
  rfl

end
end HOperatorTrace

-- CHECK CONTEXT: MSeriesFragment through diagonal_series
/- Insert after HNormalizedKernel and ReviewM's partition fragment. -/
namespace HNormalizedKernel
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Explicit Holder cost of the two normalized L2 rows. -/
def diagonalL2Cost (nu : Measure X) (U R : Lp ℂ 2 nu) : ℝ :=
  (∫ x, ‖U x‖ ^ (2 : ℝ) ∂nu) ^ (1 / (2 : ℝ)) *
    (∫ x, ‖R x‖ ^ (2 : ℝ) ∂nu) ^ (1 / (2 : ℝ))

/-- The original-Haar volume cancels in the absolute diagonal estimate too. -/
theorem diagonal_integral_norm_le (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu) :
    (∫ x, ‖haarKernel b V U R x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      diagonalL2Cost nu U R := by
  simp_rw [diagonal_formula b hb, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hV, norm_star]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le]
  rw [integral_const_mul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hV), one_mul]
  have hU : MemLp (fun x => (U x : ℂ)) (ENNReal.ofReal (2 : ℝ)) nu := by
    simpa using Lp.memLp U
  have hR : MemLp (fun x => (R x : ℂ)) (ENNReal.ofReal (2 : ℝ)) nu := by
    simpa using Lp.memLp R
  exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hU hR

/-- The SAME Haar kernel rows have the expected diagonal coefficient series.
The summability of their explicit L2 costs is the remaining analytic input. -/
theorem diagonal_series (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => diagonalL2Cost nu (U i) (R i))) :
    HasSum (fun i => inner ℂ (R i) (U i))
      (∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu)) := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hs : Summable (fun i => ∫ x,
      ‖haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _))
      (fun i => diagonal_integral_norm_le nu b hb V hV (U i) (R i)) hcost
  simpa only [diagonal_integral nu b hb V hV] using
    hasSum_integral_of_summable_integral_norm hi hs


end
end HNormalizedKernel

-- CHECK CONTEXT: MNormCostFragment
/- Insert after MSeriesFragment; uses H's exact original-Haar rows. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The integral Holder cost is exactly the Hilbert norm-product nuclear cost. -/
theorem diagonalL2Cost_eq_norm_mul (nu : Measure X) (U R : Lp ℂ 2 nu) :
    diagonalL2Cost nu U R = ‖U‖ * ‖R‖ := by
  have hsq (F : Lp ℂ 2 nu) :
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂nu) = ‖F‖ ^ 2 := by
    calc
      _ = ∫ x, inner ℝ (F x) (F x) ∂nu := by
        simp only [real_inner_self_eq_norm_sq, Real.rpow_two]
      _ = inner ℝ F F := (L2.inner_def F F).symm
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  unfold diagonalL2Cost
  rw [hsq U, hsq R, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg U), Real.sqrt_sq (norm_nonneg R)]

/-- Summable Hilbert factors discharge the original-Haar diagonal cost. -/
theorem diagonal_series_of_norm_cost {ι : Type*} [Countable ι]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    HasSum (fun i => inner ℂ (R i) (U i))
      (∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu)) := by
  apply diagonal_series nu b hb V hV U R
  simpa only [diagonalL2Cost_eq_norm_mul] using hcost

end
end HNormalizedKernel

-- CHECK CONTEXT: MNuclearDiagonalFragment nuclear_diagonal_integrable only
namespace HNormalizedKernel
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The actual original-Haar row series has an integrable diagonal with the
same total nuclear cost, without any further weight or volume factor. -/
theorem nuclear_diagonal_integrable (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    Integrable (fun x => ∑' i, haarKernel b V (U i) (R i) x x)
      (ENNReal.ofReal V • nu) ∧
    (∫ x, ‖∑' i, haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      ∑' i, ‖U i‖ * ‖R i‖ := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hmajor (i : ι) : (∫ x, ‖haarKernel b V (U i) (R i) x x‖
      ∂(ENNReal.ofReal V • nu)) ≤ ‖U i‖ * ‖R i‖ := by
    simpa only [diagonalL2Cost_eq_norm_mul] using
      diagonal_integral_norm_le nu b hb V hV (U i) (R i)
  have hs := Summable.of_nonneg_of_le
    (fun i => integral_nonneg fun x => norm_nonneg _) hmajor hc
  have h := ReviewM.integrable_complex_series (ENNReal.ofReal V • nu) _ hi hs
  exact ⟨h.1, h.2.trans (hs.tsum_le_tsum hmajor hc)⟩


end
end HNormalizedKernel

-- CHECK CONTEXT: HNuclearKernelFragment nuclear_kernel_trace only
/- Append after HNuclearTraceFragment and MNormCostFragment. -/
namespace HOperatorTrace
open MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section
variable {κ : Type*} [Countable κ]
variable {X : Type*} [MeasurableSpace X]

/-- The original-Haar diagonal of the very same nuclear rows is the actual
completed operator trace. The two analytic assumptions have distinct roles:
`hT` attaches the rows to T, and `hc` provides absolute convergence. -/
theorem nuclear_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : κ → Lp ℂ 2 nu)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ F, HasSum (fun n => inner ℂ (u n) F • v n) (T F)) :
    (∫ x, ∑' n, HNormalizedKernel.haarKernel b V (v n) (u n) x x
      ∂(ENNReal.ofReal V • nu)) = Masullo.TraceClass.trace T := by
  rw [nuclear_trace T u v hc hT]
  exact (HNormalizedKernel.diagonal_series_of_norm_cost nu b hb V hV v u
    (by simpa only [mul_comm] using hc)).tsum_eq.symm


end
end HOperatorTrace

-- CHECK CONTEXT: DNuclearCompressionFragment
/- Insert after DNuclearKernelMeasurableFragment and the H nuclear diagonal,
   trace and compression fragments. The arithmetic factor estimate remains an
   explicit application obligation; this theorem only transports proved factors. -/
namespace DNuclearKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Compression factors produce one measurable original-Haar kernel of the
genuine left projected operator, with full-input action and its actual trace.
No nuclearity hypothesis about the free convolution is used. -/
theorem source_compression_kernel (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (hbm : Measurable b)
    (S : Submodule ℂ (Lp ℂ 2 nu)) [S.HasOrthogonalProjection]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (hz : ((((1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)-S.starProjection).comp A).comp
      S.starProjection) = 0)
    (u v : ι → Sᗮ) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hB : ∀ y : Sᗮ, HasSum (fun i => inner ℂ (u i) y • v i)
      ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) y)) :
    let k := kernel nu b (fun i => (u i : Lp ℂ 2 nu)) (fun i => (v i : Lp ℂ 2 nu))
    let PA := Sᗮ.starProjection.comp A
    AEStronglyMeasurable (fun p : X × X => k p.1 p.2) (nu.prod nu) ∧
    (∀ F : Lp ℂ 2 nu,
      (∀ᵐ x ∂nu, Integrable (fun y => k x y * (F y / (b y : ℂ))) nu) ∧
      (PA F : X → ℂ) =ᵐ[nu]
        (fun x => (b x : ℂ) * ∫ y, k x y * (F y / (b y : ℂ)) ∂nu)) ∧
    Integrable (fun x => k x x) nu ∧
    (∫ x, k x x ∂nu) = Masullo.TraceClass.trace PA := by
  dsimp only
  have hcost : Summable (fun i => ‖(u i : Lp ℂ 2 nu)‖ * ‖(v i : Lp ℂ 2 nu)‖) := hc
  have hfactor (F : Lp ℂ 2 nu) :
      HasSum (fun i => inner ℂ (u i : Lp ℂ 2 nu) F • (v i : Lp ℂ 2 nu))
        ((Sᗮ.starProjection.comp A) F) := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.starProjection_orthogonal_val,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
      HOperatorTrace.source_compression_factor S A hz u v hB F
  refine ⟨kernel_aestronglyMeasurable nu b hbm _ _ hcost,
    (fun F => kernel_action nu b hb (Sᗮ.starProjection.comp A) _ _ hcost hfactor F), ?_, ?_⟩
  · simpa only [kernel, ENNReal.ofReal_one, one_smul] using
      (HNormalizedKernel.nuclear_diagonal_integrable nu b hb 1 (by norm_num)
        (fun i => (v i : Lp ℂ 2 nu)) (fun i => (u i : Lp ℂ 2 nu))
        (by simpa only [mul_comm] using hcost)).1
  · simpa only [kernel, ENNReal.ofReal_one, one_smul] using
      HOperatorTrace.nuclear_kernel_trace nu b hb 1 (by norm_num)
        (Sᗮ.starProjection.comp A) (fun i => (u i : Lp ℂ 2 nu))
        (fun i => (v i : Lp ℂ 2 nu)) hcost hfactor

end
end DNuclearKernel


-- Exact dependency block: E unchanged actual complementary projection cost
/- E source residual estimate. Append anywhere after Mathlib.
The projection minimality argument is adapted from ALPO's
GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PHadamardMean.lean:16.
Unlike a bound by 2, this gives the unit constant needed by (34.10). -/
namespace ESourceResidual
open Filter
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Every genuine orthogonal complementary projection is a contraction. -/
theorem complementary_projection_bound (E : Submodule ℂ H)
    [E.HasOrthogonalProjection] (x : H) :
    ‖x - E.starProjection x‖ ≤ ‖x‖ := by
  calc
    ‖x - E.starProjection x‖ ≤ ‖x - ((0 : E) : H)‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ norm_nonneg _⟩ (0 : E)
    _ = ‖x‖ := by simp

/-- The finite-source residual is controlled by the original input residual. -/
theorem nested_source_residual_bound (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (x : H) :
    ‖S.starProjection x - E.starProjection x‖ ≤ ‖x - E.starProjection x‖ := by
  have he : S.starProjection (E.starProjection x) = E.starProjection x :=
    Submodule.starProjection_eq_self_iff.mpr (hES (E.starProjection_apply_mem x))
  calc
    ‖S.starProjection x - E.starProjection x‖ =
        ‖S.starProjection (x - E.starProjection x)‖ := by rw [map_sub, he]
    _ ≤ ‖x - E.starProjection x‖ := S.norm_starProjection_apply_le _

/-- Unit-constant whole-column bound, uniform in the finite source set. -/
theorem nested_source_residual_contraction (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (x : H) :
    ‖E.starProjection x - S.starProjection x‖ ≤ ‖x‖ := by
  rw [norm_sub_rev]
  exact (nested_source_residual_bound S E hES x).trans
    (complementary_projection_bound E x)

/-- This discharges Q's projection-dependent summability from its nuclear
factor cost. The actual operator factorization is still a separate premise. -/
theorem source_factor_cost_summable (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Summable (fun j => ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) := by
  exact Summable.of_nonneg_of_le (fun j => by positivity)
    (fun j => mul_le_mul_of_nonneg_left
      (nested_source_residual_contraction S E hES (v j)) (norm_nonneg _)) hc

/-- Whole source-factor tail is no larger than the supplied factor cost. -/
theorem source_factor_cost_le (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    (∑' j, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) ≤
      ∑' j, ‖u j‖ * ‖v j‖ := by
  apply Summable.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left
      (nested_source_residual_contraction S E hES (v j)) (norm_nonneg _))
    (source_factor_cost_summable S E hES u v hc) hc

end
end ESourceResidual

-- Exact dependency block: Q unchanged AP to PA factor transport
/- Insert after HNuclearTraceFragment and E SourceResidualFragment.
   This consumes the literal AP order of manuscript 10.4.2.25--34. -/
namespace Q.OrderedNuclear
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
variable {H κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source invariance permits left projection of AP onto the requested PA.
It is not a commutation statement for A and P. -/
theorem project_AP_eq_PA (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0) :
    ((1 : H →L[ℂ] H)-S.starProjection).comp
      (A.comp ((1 : H →L[ℂ] H)-S.starProjection)) =
      ((1 : H →L[ℂ] H)-S.starProjection).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  have hz' : A (S.starProjection x)-S.starProjection (A (S.starProjection x)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply] using
      congrArg (fun T : H →L[ℂ] H => T x) hz
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, map_sub]
  calc
    A x-S.starProjection (A x)-
        (A (S.starProjection x)-S.starProjection (A (S.starProjection x))) =
        A x-S.starProjection (A x) := by rw [hz', sub_zero]

/-- Project the actual output columns; all inputs remain ambient inputs. -/
theorem AP_factors_to_PA (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0)
    (u v : κ → H)
    (hAP : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j)
      ((A.comp ((1 : H →L[ℂ] H)-S.starProjection)) x)) (x : H) :
    HasSum (fun j => inner ℂ (u j) x • (v j-S.starProjection (v j)))
      ((((1 : H →L[ℂ] H)-S.starProjection).comp A) x) := by
  have h := HOperatorTrace.nuclear_left_factor ((1 : H →L[ℂ] H)-S.starProjection)
    (A.comp ((1 : H →L[ℂ] H)-S.starProjection)) u v hAP x
  rw [project_AP_eq_PA S A hz] at h
  exact h

/-- The genuine orthogonal complement increases no norm-product cost. -/
theorem AP_cost_to_PA (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (u v : κ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Summable (fun j => ‖u j‖ * ‖v j-S.starProjection (v j)‖) ∧
    (∑' j, ‖u j‖ * ‖v j-S.starProjection (v j)‖) ≤ ∑' j, ‖u j‖ * ‖v j‖ := by
  have hb (j : κ) : ‖u j‖ * ‖v j-S.starProjection (v j)‖ ≤ ‖u j‖ * ‖v j‖ :=
    mul_le_mul_of_nonneg_left (ESourceResidual.complementary_projection_bound S (v j))
      (norm_nonneg _)
  have hs := Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb hc
  exact ⟨hs, hs.tsum_le_tsum hb hc⟩

end
end Q.OrderedNuclear

-- Exact dependency block: H unchanged actual source-zero application
/- Append after OAllCharacterClosure, LIntegrated, HCompressionExtension,
HCompressionTrace and HCompressionRows. All arithmetic application data are
the existing common definitions. -/
namespace HArithmeticTrace
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SFinite mu] [IsLocallyFiniteMeasure mu]

theorem full_arithmetic_PA_source_zero
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) :
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (LIntegrated.requiredTest K phi q) ht.1 ht.2
    let S := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    ((((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S.starProjection).comp A).comp
      S.starProjection) = 0 := by
  have h := OAllCharacterClosure.both_tests_full_PA_source_zero K addHaar mu
    a l r s hlr hs phi hh hc
  fin_cases q
  · simpa only [LIntegrated.requiredTest_zero] using h.1
  · simpa only [LIntegrated.requiredTest_one] using h.2


end
end HArithmeticTrace

-- Exact dependency block: G unchanged interval-weight application
/- Insert after GPointwiseConvolutionFragment. This uses the same physical
   kernel and interval weight; it introduces no new arithmetic operator. -/
namespace GPointwiseConvolution
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet PIntervalConvolution
noncomputable section

/-- A compact convolution test supplies an actual L2 row at every output
point for any continuous, nowhere-zero physical weight. -/
theorem compact_kernel_row_memLp
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [IsLocallyFiniteMeasure mu]
    (b : G → ℂ) (hbc : Continuous b) (hb : ∀ y, b y ≠ 0)
    (h : G → ℂ) (hh : Continuous h) (hc : HasCompactSupport h) (x : G) :
    MemLp (fun y => h (x*y⁻¹) / b y) 2 mu := by
  have hrow : Continuous (fun y => h (x*y⁻¹) / b y) :=
    (hh.comp (continuous_const.mul continuous_inv)).div hbc hb
  have hsupport : HasCompactSupport (fun y => h (x*y⁻¹)) :=
    hc.comp_homeomorph ((Homeomorph.inv G).trans (Homeomorph.mulLeft x))
  exact hrow.memLp_of_hasCompactSupport (by
    simp only [div_eq_mul_inv]
    exact hsupport.mul_right)

variable (K : Type*) [Field K] [NumberField K]

/-- The literal nonsymmetric interval weight is continuous and positive. -/
theorem intervalHalfWeight_continuous_pos
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s) :
    Continuous (fun x : HeckeIdeleClasses K =>
      (intervalHalfWeight l r s (classLog K x) : ℂ)) ∧
    (∀ x : HeckeIdeleClasses K, 0 < intervalHalfWeight l r s (classLog K x)) := by
  constructor
  · have he : (fun x : HeckeIdeleClasses K =>
        (intervalHalfWeight l r s (classLog K x) : ℂ)) =
        (fun x => radialTwist K ((l+r)/2) x *
          (nativeHalfWeight ((r-l)/2) s (classLog K x) : ℂ)) := by
      funext x
      rw [interval_halfWeight l r s _ hlr]
      simp only [Complex.ofReal_mul, Complex.ofReal_exp, radialTwist]
    rw [he]
    exact (radialTwist_continuous K _).mul
      (Masullo.NativeHalfWeightAddLe.actual_halfWeight_continuous K _ s hs)
  · intro x
    rw [interval_halfWeight l r s _ hlr]
    exact mul_pos (Real.exp_pos _) (nativeHalfWeight_pos _ _ _)


end
end GPointwiseConvolution


/- Concrete local compactness dependencies, adapted from ALPO GroundTheory/GlobalFields/LocalAtPlace.lean. -/

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
open MasulloGRH NumberField IsDedekindDomain Topology
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

instance finiteAdeleLocallyCompact :
    LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) := by
  letI : Fact (∀ v : HeightOneSpectrum (𝓞 K),
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
      ⟨fun v => isOpen_adicCompletionIntegers v⟩
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (B := fun v => v.adicCompletionIntegers K)
    (.of_forall fun v => isCompact_adicCompletionIntegers v)

instance adeleLocallyCompact : LocallyCompactSpace (HeckeAdeles K) :=
  inferInstanceAs (LocallyCompactSpace
    (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance finiteAdeleT2 : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs (T2Space (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => (v.adicCompletionIntegers K : Set (v.adicCompletion K))) Filter.cofinite))

instance infiniteAdeleT2 : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))

instance adeleT2 : T2Space (HeckeAdeles K) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))

instance ideleLocallyCompact : LocallyCompactSpace (HeckeIdeles K) := inferInstance

theorem coe_mem_adicCompletionIntegers_iff (v : HeightOneSpectrum (𝓞 K)) (k : K) :
    (k : v.adicCompletion K) ∈ v.adicCompletionIntegers K ↔ v.valuation K k ≤ 1 := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation']

/-- The actual principal additive subgroup is discrete; this is the explicit
small archimedean box/integral finite-adele proof in ALPO Adele/Discrete. -/
theorem principalAdeles_discrete :
    DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) := by
  let H := AdeleRing.principalSubgroup (𝓞 K) K
  let U : Set (HeckeAdeles K) :=
    {x : InfiniteAdeleRing K | ∀ w, ‖x w‖ < 1} ×ˢ
      {a : FiniteAdeleRing (𝓞 K) K | ∀ v,
        a v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K))}
  have ho : IsOpen U := by
    apply IsOpen.prod _ (MasulloGRH.integralFiniteSet_open K)
    have he : {x : InfiniteAdeleRing K | ∀ w, ‖x w‖ < 1} =
        ⋂ w : InfinitePlace K, {x : InfiniteAdeleRing K | ‖x w‖ < 1} := by
      ext x; simp
    rw [he]
    exact isOpen_iInter_of_finite fun w =>
      isOpen_lt (continuous_apply w).norm continuous_const
  have h0 : (0 : HeckeAdeles K) ∈ U := by
    constructor
    · intro w; change ‖(0 : w.Completion)‖ < 1; simp
    · intro v; exact (v.adicCompletionIntegers K).zero_mem
  have hh : ∀ x ∈ H, x ∈ U → x = 0 := by
    rintro x ⟨k, rfl⟩ ⟨hi, hf⟩
    have hv : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K k ≤ 1 :=
      fun v => (coe_mem_adicCompletionIntegers_iff K v k).mp (hf v)
    obtain ⟨z, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K k hv
    have hz (w : InfinitePlace K) : w (z : K) < 1 := by
      have he : ‖(algebraMap K (HeckeAdeles K) (z : K)).1 w‖ = w (z : K) :=
        NumberField.InfinitePlace.Completion.norm_coe w
          ((WithAbs.equiv _).symm (z : K))
      exact he ▸ hi w
    have hz0 : z = 0 := by
      by_contra hn
      obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
      exact (one_le_of_lt_one hn (fun w' _ => hz w')).not_gt (hz w)
    rw [hz0]; simp
  rw [discreteTopology_iff_isOpen_singleton_zero]
  convert ho.preimage (continuous_subtype_val : Continuous (fun x : H => (x : HeckeAdeles K)))
  ext ⟨x, hx⟩
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  constructor
  · intro h
    have hx0 : x = 0 := congrArg Subtype.val h
    rw [hx0]; exact h0
  · intro h
    exact Subtype.ext (hh x hx h)

/-- Discreteness is transported by the actual units-to-adeles inclusion. -/
instance principalIdeles_discrete : DiscreteTopology (principalIdeles K) := by
  let f : principalIdeles K → AdeleRing.principalSubgroup (𝓞 K) K := fun x =>
    ⟨((x : HeckeIdeles K) : HeckeAdeles K), by
      obtain ⟨k, hk⟩ := x.2
      exact ⟨(k : K), by rw [← hk]; rfl⟩⟩
  letI := principalAdeles_discrete K
  exact DiscreteTopology.of_continuous_injective (f := f)
    ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _)
    (fun x y h => Subtype.ext (Units.ext (congrArg Subtype.val h)))

theorem principalIdeles_closed : IsClosed (principalIdeles K : Set (HeckeIdeles K)) :=
  Subgroup.isClosed_of_discrete

theorem principalIdele_injective : Function.Injective (principalIdele K) := by
  intro x y h
  apply Units.ext
  apply NumberField.AdeleRing.algebraMap_injective (𝓞 K) K
  exact congrArg Units.val h

end
end NIdelicTopology

/- Exact constructive ALPO Bruhat proof with renamed namespace and explicit theorem type. -/
universe u

namespace NIndentation

open MeasureTheory Pointwise in
private lemma exists_nonneg_continuous_ne_zero_on_cosets {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ f : G → ℝ, Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport f ∩ (K * (H : Set G)))) ∧
      ∀ x, ∃ h : H, f (x * h) ≠ 0 := by

  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hVc, hVn, hVinv⟩ : ∃ V : Set G, IsCompact V ∧ V ∈ nhds (1 : G) ∧ V⁻¹ = V :=
    ⟨V₀ ∩ V₀⁻¹, hV₀c.inter_right hV₀c.inv.isClosed, Filter.inter_mem hV₀n (inv_mem_nhds_one G hV₀n),
      by rw [Set.inter_inv, inv_inv, Set.inter_comm]⟩
  have hPc : ∀ n : ℕ, IsCompact (V ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, ← Set.singleton_one]; exact isCompact_singleton
    | succ n ih => rw [pow_succ]; exact ih.mul hVc
  have h1V : (1 : G) ∈ interior V := mem_interior_iff_mem_nhds.2 hVn
  have hPint : ∀ n : ℕ, V ^ n ⊆ interior (V ^ (n + 1)) := by
    intro n x hx
    have hx' : x ∈ V ^ n * interior V := by simpa using Set.mul_mem_mul hx h1V
    refine interior_maximal ?_ (isOpen_interior.mul_left) hx'
    rw [pow_succ]
    exact Set.mul_subset_mul subset_rfl interior_subset
  have hPinv : ∀ n : ℕ, (V ^ n)⁻¹ = V ^ n := fun n => by rw [← inv_pow, hVinv]

  obtain ⟨Rel, hRel⟩ : ∃ Rel : G → G → Prop, ∀ y z,
      Rel y z ↔ ∃ n : ℕ, ∃ a ∈ V ^ n, ∃ h ∈ H, z = a * y * h := ⟨_, fun _ _ => Iff.rfl⟩
  have hrefl : ∀ y, Rel y y := fun y =>
    (hRel y y).2 ⟨0, 1, by simp, 1, H.one_mem, by simp⟩
  have hsymm : ∀ y z, Rel y z → Rel z y := by
    intro y z hyz
    obtain ⟨n, a, ha, h, hh, rfl⟩ := (hRel y z).1 hyz
    refine (hRel _ _).2 ⟨n, a⁻¹, ?_, h⁻¹, H.inv_mem hh, by group⟩
    rw [← hPinv n]
    exact Set.inv_mem_inv.2 ha
  have htrans : ∀ y z w, Rel y z → Rel z w → Rel y w := by
    intro y z w hyz hzw
    obtain ⟨n, a, ha, h, hh, rfl⟩ := (hRel y z).1 hyz
    obtain ⟨m, b, hb, k, hk, rfl⟩ := (hRel _ w).1 hzw
    refine (hRel _ _).2 ⟨m + n, b * a, ?_, h * k, H.mul_mem hh hk, by group⟩
    rw [pow_add]
    exact Set.mul_mem_mul hb ha

  let σ : G → G := fun y => Classical.epsilon (Rel y)
  have hσ : ∀ y, Rel y (σ y) := fun y => Classical.epsilon_spec ⟨y, hrefl y⟩
  have hσeq : ∀ y z, Rel y z → σ z = σ y := by
    intro y z hyz
    change Classical.epsilon (Rel z) = Classical.epsilon (Rel y)
    congr 1
    funext w
    exact propext ⟨fun h => htrans _ _ _ hyz h, fun h => htrans _ _ _ (hsymm _ _ hyz) h⟩

  let U : G → ℕ → Set G := fun r m => interior (V ^ (m + 1)) * {r} * (H : Set G)
  have hUo : ∀ r m, IsOpen (U r m) := fun r m => isOpen_interior.mul_right.mul_right
  have hUrel : ∀ r m z, z ∈ U r m → Rel r z := by
    rintro r m z ⟨_, ⟨a, ha, _, rfl, rfl⟩, h, hh, rfl⟩
    exact (hRel _ _).2 ⟨m + 1, a, interior_subset ha, h, hh, rfl⟩
  have hUH : ∀ r m z, z ∈ U r m → ∀ h ∈ H, z * h ∈ U r m := by
    rintro r m z ⟨x, hx, k, hk, rfl⟩ h hh
    exact ⟨x, hx, k * h, H.mul_mem hk hh, by rw [mul_assoc]⟩
  have hUsub : ∀ r m, U r m ⊆ V ^ (m + 1) * {r} * (H : Set G) := fun r m =>
    Set.mul_subset_mul (Set.mul_subset_mul interior_subset subset_rfl) subset_rfl
  have hexh : ∀ r z, Rel r z → ∃ m, z ∈ U r m := by
    intro r z hz
    obtain ⟨n, a, ha, h, hh, rfl⟩ := (hRel r z).1 hz
    exact ⟨n, Set.mul_mem_mul (Set.mul_mem_mul (hPint n ha) rfl) hh⟩

  let C : G → ℕ → Set G := fun r n => (V ^ (n + 1) * {r}) \ ⋃ k, ⋃ (_ : k < n), U r k
  let D : G → ℕ → Set G := fun r n => ⋃ k, ⋃ (_ : k < n), V ^ k * {r} * (H : Set G)
  have hCc : ∀ r n, IsCompact (C r n) := fun r n =>
    ((hPc _).mul isCompact_singleton).diff (isOpen_iUnion fun k => isOpen_iUnion fun _ => hUo r k)
  have hDc : ∀ r n, IsClosed (D r n) := by
    intro r n
    have : D r n = ⋃ k ∈ {k : ℕ | k < n}, V ^ k * {r} * (H : Set G) := rfl
    rw [this]
    exact (Set.finite_lt_nat n).isClosed_biUnion fun k _ =>
      hH.mul_left_of_isCompact ((hPc k).mul isCompact_singleton)
  have hCD : ∀ r n, Disjoint (C r n) (D r n) := by
    intro r n
    rw [Set.disjoint_left]
    rintro x ⟨-, hxU⟩ hxD
    simp only [D, Set.mem_iUnion] at hxD
    obtain ⟨k, hk, hx⟩ := hxD
    exact hxU (Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk,
      Set.mul_subset_mul (Set.mul_subset_mul (hPint k) subset_rfl) subset_rfl hx⟩⟩)
  choose φ hφ1 hφ0 hφcs hφI using fun r n =>
    exists_continuous_one_zero_of_isCompact (hCc r n) (hDc r n) (hCD r n)

  have hDU : ∀ r m n, m + 2 ≤ n → U r m ⊆ D r n := by
    intro r m n hmn z hz
    exact Set.mem_iUnion.2 ⟨m + 1, Set.mem_iUnion.2 ⟨by omega, hUsub r m hz⟩⟩
  have hloc : ∀ r m z, z ∈ U r m →
      ∑ᶠ n, φ r n z = ∑ n ∈ Finset.range (m + 2), φ r n z := by
    intro r m z hz
    apply finsum_eq_sum_of_support_subset
    intro n hn
    by_contra hn'
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn'
    exact hn (hφ0 r n (hDU r m n hn' hz))
  have hσU : ∀ y m z, z ∈ U (σ y) m → σ z = σ y := fun y m z hz =>
    (hσeq y z (htrans _ _ _ (hσ y) (hUrel _ m z hz)))
  have hyU : ∀ y, ∃ m, y ∈ U (σ y) m := fun y => hexh _ _ (hsymm _ _ (hσ y))
  have hfeq : ∀ y m z, z ∈ U (σ y) m →
      ∑ᶠ n, φ (σ z) n z = ∑ n ∈ Finset.range (m + 2), φ (σ y) n z := by
    intro y m z hz
    rw [hσU y m z hz]
    exact hloc _ m z hz
  refine ⟨fun y => ∑ᶠ n, φ (σ y) n y, ?_, fun y => finsum_nonneg fun n => (hφI _ _ y).1, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro y
    obtain ⟨m, hm⟩ := hyU y
    have hc : Continuous fun z => ∑ n ∈ Finset.range (m + 2), φ (σ y) n z :=
      continuous_finset_sum _ fun n _ => (φ (σ y) n).continuous
    refine hc.continuousAt.congr ?_
    filter_upwards [(hUo _ m).mem_nhds hm] with z hz
    exact (hfeq y m z hz).symm
  ·
    have hloc' : ∀ y, ∃ O Q : Set G, IsOpen O ∧ y ∈ O ∧ (∀ z ∈ O, ∀ h ∈ H, z * h ∈ O) ∧
        IsCompact Q ∧ tsupport (fun y => ∑ᶠ n, φ (σ y) n y) ∩ O ⊆ Q := by
      intro y
      obtain ⟨m, hm⟩ := hyU y
      refine ⟨U (σ y) m, ⋃ n ∈ Finset.range (m + 2), tsupport (φ (σ y) n), hUo _ m, hm,
        hUH _ m, (Finset.range (m + 2)).isCompact_biUnion fun n _ => hφcs _ n, ?_⟩
      intro x hx
      rw [Set.inter_comm] at hx
      refine closure_minimal ?_ ((Finset.range (m + 2)).isCompact_biUnion
        fun n _ => hφcs _ n).isClosed ((hUo _ m).inter_closure hx)
      rintro z ⟨hzU, hz⟩
      rw [Function.mem_support, hfeq y m z hzU] at hz
      obtain ⟨n, hn, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
      exact Set.mem_biUnion hn (subset_tsupport _ hne)
    choose O Q hOo hyO hOH hQc hOQ using hloc'
    intro K hK
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun y : K => O y) (fun y => hOo y)
      fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyO y⟩
    refine ((t.isCompact_biUnion fun i _ => hQc i)).of_isClosed_subset
      ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_
    rintro x ⟨hxs, _, hk, h, hh, rfl⟩
    obtain ⟨i, hi, hkO⟩ := Set.mem_iUnion₂.1 (ht hk)
    exact Set.mem_biUnion hi (hOQ i ⟨hxs, hOH i _ hkO h hh⟩)
  · intro y
    set r := σ y with hr
    have hex : ∃ m, y ∈ U r m := hyU y
    classical
    let m := Nat.find hex
    have hm : y ∈ U r m := Nat.find_spec hex
    obtain ⟨_, ⟨a, ha, _, rfl, rfl⟩, h, hh, hya⟩ := hm
    refine ⟨⟨h, hh⟩⁻¹, ?_⟩
    have hz : y * ((⟨h, hh⟩ : H)⁻¹ : H) = a * r := by
      rw [← hya]; simp
    rw [hz]
    have hzU : a * r ∈ U r m := ⟨a * r, Set.mul_mem_mul ha rfl, 1, H.one_mem, mul_one _⟩
    have hzC : a * r ∈ C r m := by
      refine ⟨Set.mul_mem_mul (interior_subset ha) rfl, ?_⟩
      simp only [Set.mem_iUnion]
      rintro ⟨k, hk, hkU⟩
      exact Nat.find_min hex hk (hya ▸ hUH r k _ hkU h hh)
    change ∑ᶠ n, φ (σ (a * r)) n (a * r) ≠ 0
    rw [hfeq y m _ hzU]
    refine (lt_of_lt_of_le ?_ (Finset.single_le_sum (fun n _ => (hφI _ n _).1)
      (Finset.mem_range.2 (by omega : m < m + 2)))).ne'
    rw [hφ1 _ m hzC]
    norm_num

open MeasureTheory Pointwise in
private lemma exists_bruhat_function_of_positive_on_cosets {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ : Measure H) [μ.IsHaarMeasure]
    (f : G → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hfK : ∀ K : Set G, IsCompact K → IsCompact (tsupport f ∩ (K * (H : Set G))))
    (hpos : ∀ x, ∃ h : H, f (x * h) ≠ 0) :
    ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ K : Set G, IsCompact K → IsCompact (tsupport β ∩ (K * (H : Set G)))) ∧
      ∀ x, ∫ h : H, β (x * h) ∂μ = 1 := by
  have hemb : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal

  have hsupp : ∀ K : Set G, IsCompact K → ∃ S : Set H, IsCompact S ∧
      ∀ x ∈ K, ∀ h : H, h ∉ S → f (x * h) = 0 := by
    intro K hK
    refine ⟨(↑) ⁻¹' (K⁻¹ * (tsupport f ∩ (K * (H : Set G)))),
      hemb.isCompact_preimage (hK.inv.mul (hfK K hK)), ?_⟩
    intro x hx h hS
    by_contra hne
    apply hS
    refine ⟨x⁻¹, by simpa using hx, x * h, ⟨subset_tsupport _ hne, x, hx, h, h.2, rfl⟩, ?_⟩
    simp
  have hcont_h : ∀ x, Continuous fun h : H => f (x * h) :=
    fun x => hf.comp (continuous_const.mul continuous_subtype_val)
  have hcs : ∀ x, HasCompactSupport fun h : H => f (x * h) := by
    intro x
    obtain ⟨S, hS, hSf⟩ := hsupp {x} isCompact_singleton
    exact HasCompactSupport.intro hS fun h hh => hSf x rfl h hh
  set F : G → ℝ := fun x => ∫ h : H, f (x * h) ∂μ with hFdef
  have hFpos : ∀ x, 0 < F x := by
    intro x
    obtain ⟨h, hh⟩ := hpos x
    exact (hcont_h x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun h => hf0 _) hh
  have hFinv : ∀ x (h : H), F (x * h) = F x := by
    intro x h
    simp only [hFdef]
    have := integral_mul_left_eq_self (μ := μ) (fun k : H => f (x * k)) h
    rw [← this]
    congr 1
    ext k
    simp [mul_assoc]
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
    obtain ⟨S, hS, hSf⟩ := hsupp K hK
    have hc : ContinuousOn F K :=
      continuousOn_integral_of_compact_support (f := fun x (h : H) => f (x * h)) hS
        (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd))).continuousOn
        fun x h hx hh => hSf x hx h hh
    exact hc.continuousAt hKn
  refine ⟨fun x => f x / F x, hf.div hFcont fun x => (hFpos x).ne',
    fun x => div_nonneg (hf0 x) (hFpos x).le, ?_, ?_⟩
  · intro K hK
    have hsub : tsupport (fun x => f x / F x) ⊆ tsupport f := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      simp [h0] at hx
    refine ((hfK K hK).inter_right (isClosed_tsupport (fun x => f x / F x))).of_isClosed_subset
      ((isClosed_tsupport _).inter (hH.mul_left_of_isCompact hK)) ?_
    rintro y ⟨hy1, hy2⟩
    exact ⟨⟨hsub hy1, hy2⟩, hy1⟩
  · intro x
    simp only [hFinv]
    rw [integral_div]
    exact div_self (hFpos x).ne'

open MeasureTheory Pointwise in

theorem exists_bruhat_function {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G)) (μ : Measure H) [μ.IsHaarMeasure] :
    ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧
      (∀ C : Set G, IsCompact C → IsCompact (tsupport β ∩ (C * (H : Set G)))) ∧
      ∀ x : G, ∫ h : H, β (x * (h : G)) ∂μ = 1 := by
  obtain ⟨f, hf, hf0, hfK, hpos⟩ := exists_nonneg_continuous_ne_zero_on_cosets H hH
  exact exists_bruhat_function_of_positive_on_cosets H hH μ f hf hf0 hfK hpos

end NIndentation

/- Append after NIdelicTopologyFragment and NBruhatExistenceFragment. -/
namespace NIndentation
open MasulloGRH MeasureTheory Pointwise
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The principal subgroup has exactly the arithmetic indexing by K units. -/
def principalEquiv : Kˣ ≃ principalIdeles K :=
  Equiv.ofBijective (fun q => ⟨principalIdele K q, ⟨q, rfl⟩⟩)
    ⟨fun _x _y h => NIdelicTopology.principalIdele_injective K (congrArg Subtype.val h),
      fun ⟨_x, q, hq⟩ => ⟨q, Subtype.ext hq⟩⟩

/-- Existence of the manuscript indentation on the actual ideles. No
normalization, quotient measurability or principal-lattice premise is assumed. -/
theorem exists_arithmetic_indentation :
    ∃ b : HeckeIdeles K → ℝ, Continuous b ∧ (∀ x, 0 ≤ b x) ∧
      ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1 := by
  classical
  letI : MeasurableSpace (HeckeIdeles K) := borel (HeckeIdeles K)
  letI : BorelSpace (HeckeIdeles K) := ⟨rfl⟩
  letI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  letI : Countable (principalIdeles K) :=
    Function.Injective.countable (principalEquiv K).symm.injective
  letI : (Measure.count : Measure (principalIdeles K)).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        ⟨fun C hC => Measure.count_apply_lt_top.2 hC.finite_of_discrete⟩,
      toIsMulLeftInvariant := inferInstance,
      open_pos := fun U _ hU h => hU.ne_empty (Measure.count_eq_zero_iff.1 h) }
  obtain ⟨b, hb, hb0, hbK, hnorm⟩ := exists_bruhat_function
    (principalIdeles K) (NIdelicTopology.principalIdeles_closed K) Measure.count
  refine ⟨b, hb, hb0, fun x => ?_⟩
  have hemb : Topology.IsClosedEmbedding
      ((↑) : principalIdeles K → HeckeIdeles K) :=
    (NIdelicTopology.principalIdeles_closed K).isClosedEmbedding_subtypeVal
  let C : Set (HeckeIdeles K) := {x}
  let S : Set (principalIdeles K) :=
    (↑) ⁻¹' (C⁻¹ * (tsupport b ∩ (C * (principalIdeles K : Set (HeckeIdeles K)))))
  have hS : IsCompact S := hemb.isCompact_preimage
    (isCompact_singleton.inv.mul (hbK C isCompact_singleton))
  have hcs : HasCompactSupport (fun h : principalIdeles K => b (x * h)) := by
    apply HasCompactSupport.intro hS
    intro h hh
    by_contra hn
    apply hh
    exact ⟨x⁻¹, by simp [C], x * h,
      ⟨subset_tsupport _ hn, x, rfl, h, h.2, rfl⟩, by simp⟩
  have hi : Integrable (fun h : principalIdeles K => b (x * h)) Measure.count :=
    (hb.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport hcs
  have hs : HasSum (fun h : principalIdeles K => b (x * h)) 1 := by
    have heq : (∑' h : principalIdeles K, b (x * h)) = 1 := by
      simpa only [integral_countable' hi, Measure.real, Measure.count_singleton,
        ENNReal.toReal_one, one_smul] using hnorm x
    exact heq ▸ (integrable_count_iff.mp hi).of_norm.hasSum
  have hre := (principalEquiv K).hasSum_iff.mpr hs
  simpa only [Function.comp_def, principalEquiv, Equiv.ofBijective_apply,
    mul_comm] using hre

end
end NIndentation

noncomputable section
namespace ReviewMPartition

/-- An indentation averages a positive partition; the resulting masks may overlap. -/
theorem averaged_partition {U I : Type*} (b : U → ℝ) (d : I → U → ℝ)
    (hb : ∀ u, 0 ≤ b u) (hbs : HasSum b 1)
    (hd : ∀ i u, 0 ≤ d i u) (hds : ∀ u, HasSum (fun i => d i u) 1) :
    (∀ i, Summable (fun u => b u * d i u)) ∧
    (∀ i, 0 ≤ ∑' u, b u * d i u) ∧
    HasSum (fun i => ∑' u, b u * d i u) 1 := by
  have hle (i : I) (u : U) : d i u ≤ 1 := by
    simpa only [Finset.sum_singleton, (hds u).tsum_eq] using
      (hds u).summable.sum_le_tsum {i} (fun j _ => hd j u)
  have hs (i : I) : Summable (fun u => b u * d i u) :=
    Summable.of_nonneg_of_le (fun u => mul_nonneg (hb u) (hd i u))
      (fun u => mul_le_of_le_one_right (hb u) (hle i u)) hbs.summable
  have hrow (u : U) : Summable (fun i => b u * d i u) :=
    (hds u).summable.mul_left (b u)
  have hrowval (u : U) : (∑' i, b u * d i u) = b u := by
    rw [tsum_mul_left, (hds u).tsum_eq, mul_one]
  have hall : Summable (fun ui : U × I => b ui.1 * d ui.2 ui.1) := by
    apply (summable_prod_of_nonneg (fun ui => mul_nonneg (hb ui.1) (hd ui.2 ui.1))).2
    exact ⟨hrow, by simpa only [hrowval] using hbs.summable⟩
  have hmass : (∑' i, ∑' u, b u * d i u) = 1 := by
    calc
      _ = ∑' u, ∑' i, b u * d i u := hall.tsum_comm
      _ = 1 := by simpa only [hrowval] using hbs.tsum_eq
  have houter : Summable (fun i => ∑' u, b u * d i u) := by
    exact ((summable_prod_of_nonneg (fun iu : I × U =>
      mul_nonneg (hb iu.2) (hd iu.1 iu.2))).1 hall.prod_symm).2
  exact ⟨hs, fun i => tsum_nonneg (fun u => mul_nonneg (hb u) (hd i u)),
    hmass ▸ houter.hasSum⟩

end ReviewMPartition

end
/- Append after ReviewMPartition.averaged_partition and the seed arithmetic definitions. -/
noncomputable section
open scoped BigOperators
namespace NDivisorialShells
open MasulloGRH NumberField
variable (K : Type*) [Field K] [NumberField K]

/-- The manuscript's nested finite-place unit strata live on ideles. -/
def stratum (v : ℕ → FinitePlace K) (n : ℕ) : Set (HeckeIdeles K) :=
  {x | ∀ k < n, ‖x.val.2 (v k).maximalIdeal‖ = 1}

/-- `none` is the residual S-part; `some n` is the first nonunit place. -/
def shellIndex (v : ℕ → FinitePlace K) (x : HeckeIdeles K) : Option ℕ :=
  if hx : ∃ n, ‖x.val.2 (v n).maximalIdeal‖ ≠ 1 then some (Nat.find hx) else none

def upstairsMask (v : ℕ → FinitePlace K) (e : Option ℕ) (x : HeckeIdeles K) : ℝ :=
  if shellIndex K v x = e then 1 else 0

theorem stratum_antitone (v : ℕ → FinitePlace K) : Antitone (stratum K v) := by
  intro n m hnm x hx k hk
  exact hx k (lt_of_lt_of_le hk hnm)

theorem first_nonunit_shell (v : ℕ → FinitePlace K) (x : HeckeIdeles K)
    (hx : ∃ n, ‖x.val.2 (v n).maximalIdeal‖ ≠ 1) :
    shellIndex K v x = some (Nat.find hx) ∧
      x ∈ stratum K v (Nat.find hx) ∧ x ∉ stratum K v (Nat.find hx + 1) := by
  refine ⟨by simp [shellIndex, hx], ?_, ?_⟩
  · intro k hk
    exact not_not.mp (Nat.find_min hx hk)
  · intro hu
    exact Nat.find_spec hx (hu _ (Nat.lt_succ_self _))

theorem residual_shell (v : ℕ → FinitePlace K) (x : HeckeIdeles K)
    (hx : ∀ n, ‖x.val.2 (v n).maximalIdeal‖ = 1) : shellIndex K v x = none := by
  simp [shellIndex, hx]

theorem upstairs_nonneg (v : ℕ → FinitePlace K) (e : Option ℕ) (x : HeckeIdeles K) :
    0 ≤ upstairsMask K v e x := by
  unfold upstairsMask
  split <;> norm_num

theorem upstairs_mass (v : ℕ → FinitePlace K) (x : HeckeIdeles K) :
    HasSum (fun e => upstairsMask K v e x) 1 := by
  classical
  simpa only [upstairsMask, eq_comm] using
    (hasSum_ite_eq (shellIndex K v x) (1 : ℝ))

/-- Orbit averaging by the fixed manuscript indentation. -/
def orbitMask (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (x : HeckeIdeles K) : ℝ :=
  ∑' q : Kˣ, b (principalIdele K q * x) * upstairsMask K v e (principalIdele K q * x)

theorem orbitMask_principal (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (q : Kˣ) (x : HeckeIdeles K) :
    orbitMask K v b e (principalIdele K q * x) = orbitMask K v b e x := by
  have ht := (Equiv.mulRight q).tsum_eq (fun u : Kˣ =>
    b (principalIdele K u * x) * upstairsMask K v e (principalIdele K u * x))
  change (∑' u : Kˣ, b (principalIdele K (u*q) * x) *
    upstairsMask K v e (principalIdele K (u*q) * x)) = _ at ht
  simpa only [orbitMask, map_mul, mul_assoc] using ht

/-- Actual quotient descent; no representative selector or invariance premise. -/
def descendedMask (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (orbitMask K v b e) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K := QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, orbitMask_principal])

theorem descendedMask_mk (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (x : HeckeIdeles K) :
    descendedMask K v b e (QuotientGroup.mk x) = orbitMask K v b e x := rfl

/-- Positivity and total mass are proved for these actual arithmetic masks.
The indentation normalization is displayed, not claimed to be constructed here. -/
theorem descended_partition_mass (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (x : HeckeIdeleClasses K) :
    (∀ e, 0 ≤ descendedMask K v b e x) ∧
      HasSum (fun e => descendedMask K v b e x) 1 := by
  refine Quotient.inductionOn x ?_
  intro y
  have ht := ReviewMPartition.averaged_partition
    (fun q : Kˣ => b (principalIdele K q * y))
    (fun e q => upstairsMask K v e (principalIdele K q * y))
    (fun q => hb _) (hbs y)
    (fun e q => upstairs_nonneg K v e _) (fun q => upstairs_mass K v _)
  exact ⟨ht.2.1, ht.2.2⟩

/-- The two repairs use the same actual idelic shell and the same quotient mask.
The incoming point is x*t⁻¹ because convolution acts before projection. -/
theorem actual_shell_boundary_split (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (y : HeckeIdeles K) (t : HeckeIdeleClasses K) (amp : ℂ) :
    let x : HeckeIdeleClasses K := QuotientGroup.mk y
    ((upstairsMask K v e y : ℂ) - (descendedMask K v b e (x*t⁻¹) : ℂ)) * amp =
      ((upstairsMask K v e y : ℂ) - (descendedMask K v b e x : ℂ)) * amp +
      ((descendedMask K v b e x : ℂ) - (descendedMask K v b e (x*t⁻¹) : ℂ)) * amp := by
  dsimp
  ring

/-- The corrected finite regularizer retains the narrow compensator with PLUS sign. -/
theorem regularizer_plus {X : Type*} (wide narrow sandwich regNarrow : X → ℂ) :
    (fun x => wide x - narrow x - (sandwich x - regNarrow x) +
      (narrow x - regNarrow x)) = (fun x => wide x - sandwich x) := by
  funext x
  ring
end NDivisorialShells
end

/- Append after NShellFragment. Uses the seed's concrete finite-adele open set. -/
namespace NDivisorialShells
open MasulloGRH NumberField Filter
open scoped Topology Valued
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Unit finite-idele perturbations preserve each local norm, hence every
individual and residual divisorial indicator. This proves the continuity
hypothesis for the actual masks used in M's quotient descent. -/
theorem upstairsMask_continuous (v : ℕ → FinitePlace K) (e : Option ℕ) :
    Continuous (upstairsMask K v e) := by
  let U : Set (HeckeIdeles K) := {a | (∀ w : FinitePrime K, Valued.v (a.val.2 w) ≤ 1) ∧
    (∀ w : FinitePrime K, Valued.v ((a⁻¹).val.2 w) ≤ 1)}
  have ho : IsOpen U := (integralFiniteSet_open K).preimage
    (continuous_snd.comp Units.continuous_val) |>.inter
      ((integralFiniteSet_open K).preimage (continuous_snd.comp Units.continuous_coe_inv))
  have h1 : (1 : HeckeIdeles K) ∈ U := by
    constructor <;> intro w <;> change Valued.v (1 : LocalField K w) ≤ 1 <;> simp
  have hu (a : HeckeIdeles K) (ha : a ∈ U) (w : FinitePrime K) :
      ‖a.val.2 w‖ = 1 := by
    have hp : a.val.2 w * (a⁻¹).val.2 w = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 w) a.val_inv
    have hpv : Valued.v (a.val.2 w) * Valued.v ((a⁻¹).val.2 w) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv : Valued.v (a.val.2 w) = 1 := by
      apply le_antisymm (ha.1 w)
      calc
        1 = Valued.v (a.val.2 w) * Valued.v ((a⁻¹).val.2 w) := hpv.symm
        _ ≤ Valued.v (a.val.2 w) * 1 := mul_le_mul_right (ha.2 w) _
        _ = _ := mul_one _
    change Valued.norm (a.val.2 w) = 1
    rw [Valued.norm_def, hv, map_one]
    rfl
  rw [continuous_iff_continuousAt]
  intro x
  have hV : ∀ᶠ y in 𝓝 x, x⁻¹*y ∈ U :=
    ((ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1))
  apply (continuous_const : Continuous (fun _ : HeckeIdeles K => upstairsMask K v e x)).continuousAt.congr_of_eventuallyEq
  filter_upwards [hV] with y hy
  have hn (n : ℕ) : ‖y.val.2 (v n).maximalIdeal‖ = ‖x.val.2 (v n).maximalIdeal‖ := by
    have he := hu (x⁻¹*y) hy (v n).maximalIdeal
    have hm : x.val.2 (v n).maximalIdeal * (x⁻¹*y).val.2 (v n).maximalIdeal =
        y.val.2 (v n).maximalIdeal :=
      congrArg (fun a : HeckeIdeles K => a.val.2 (v n).maximalIdeal) (mul_inv_cancel_left x y)
    rw [← hm, norm_mul, he, mul_one]
  simp only [upstairsMask, shellIndex, hn]
end
end NDivisorialShells

/-! Positive descended shells of the original Haar diagonal, M36 (36.1)-(36.3).
No disjointness assumption is used. Arithmetic identification of the density
is deliberately a separate obligation, not a new axiom. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ReviewM

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The masks are the nonnegative descended indentation weights. -/
structure PositivePartition (p : ι → X → ℝ) : Prop where
  measurable : ∀ i, Measurable (p i)
  nonneg : ∀ i x, 0 ≤ p i x
  mass : ∀ x, HasSum (fun i => p i x) 1

theorem partition_partial_le (p : ι → X → ℝ) (hp : PositivePartition p)
    (s : Finset ι) (x : X) : ∑ i ∈ s, p i x ≤ 1 := by
  simpa only [(hp.mass x).tsum_eq] using
    (hp.mass x).summable.sum_le_tsum s (fun i _ => hp.nonneg i x)

theorem partition_le_one (p : ι → X → ℝ) (hp : PositivePartition p)
    (i : ι) (x : X) : p i x ≤ 1 := by
  simpa using partition_partial_le p hp {i} x

/-- Multiplication by any descended shell preserves L1. -/
theorem shell_integrable (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (i : ι) :
    Integrable (fun x => (p i x : ℂ) * d x) μ := by
  apply hd.norm.mono' ((hp.measurable i).complex_ofReal.aestronglyMeasurable.mul
    hd.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p i x : ℂ) * d x‖ ≤ ‖d x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg i x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (partition_le_one p hp i x)

/-- Every finite family of shell integrals is bounded by the SAME L1 mass. -/
theorem finite_shell_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (s : Finset ι) :
    ∑ i ∈ s, ‖∫ x, (p i x : ℂ) * d x ∂μ‖ ≤ ∫ x, ‖d x‖ ∂μ := by
  have hi := fun i => shell_integrable μ p hp d hd i
  calc
    _ ≤ ∑ i ∈ s, ∫ x, ‖(p i x : ℂ) * d x‖ ∂μ :=
      Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ x, ∑ i ∈ s, ‖(p i x : ℂ) * d x‖ ∂μ :=
      (integral_finset_sum s (fun i _ => (hi i).norm)).symm
    _ ≤ ∫ x, ‖d x‖ ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => (hi i).norm)) hd.norm
      intro x
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp.nonneg _ x)]
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp s x)

/-- Countably many shells cost no factor equal to the number of shells. -/
theorem positive_shell_l1 (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) :
    Summable (fun i => ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ∧
    (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ≤ ∫ x, ‖d x‖ ∂μ := by
  have hs := summable_of_sum_le (fun i => norm_nonneg
    (∫ x, (p i x : ℂ) * d x ∂μ)) (finite_shell_bound μ p hp d hd)
  exact ⟨hs, le_of_tendsto hs.hasSum
    (Eventually.of_forall (finite_shell_bound μ p hp d hd))⟩

/-- The same estimate pays the entire shell-vector error. -/
theorem shell_difference_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d e : X → ℂ) (hd : Integrable d μ) (he : Integrable e μ) :
    (∑' i, ‖(∫ x, (p i x : ℂ) * d x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) ≤ ∫ x, ‖d x - e x‖ ∂μ := by
  have h := (positive_shell_l1 μ p hp (fun x => d x - e x) (hd.sub he)).2
  simpa only [mul_sub, integral_sub (shell_integrable μ p hp d hd _)
    (shell_integrable μ p hp e he _)] using h

/-- L1 convergence of the original Haar densities gives simultaneous shell convergence. -/
theorem shell_l1_limit (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : ℕ → X → ℂ) (e : X → ℂ) (hd : ∀ n, Integrable (d n) μ)
    (he : Integrable e μ)
    (hlim : Tendsto (fun n => ∫ x, ‖d n x - e x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, ‖(∫ x, (p i x : ℂ) * d n x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => tsum_nonneg (fun i => norm_nonneg _))
    (fun n => shell_difference_bound μ p hp (d n) e (hd n) he) hlim

/-- Relative to μ=V_K ν the density is w/V_K, not w. -/
def haarRankOneKernel (V : ℝ) (w : X → ℝ) (u v : X → ℂ) (x y : X) : ℂ :=
  ((w y / V : ℝ) : ℂ) * u x * star (v y)

omit [MeasurableSpace X] in
theorem haarRankOne_diagonal (V : ℝ) (w : X → ℝ) (u v : X → ℂ) (x : X) :
    haarRankOneKernel V w u v x x = ((w x / V : ℝ) : ℂ) * u x * star (v x) := rfl

/-- The manuscript's geometric kernel has the negative spectral diagonal. -/
theorem geometric_diagonal {G : Type*} [Group G] (h : G → ℂ)
    (k : G → G → ℂ) (hunit : h 1 = 0) (x : G) :
    h (x * x⁻¹) - k x x = -k x x := by simp [hunit]

/-- The finite narrow source compensator has the plus sign. -/
theorem finite_source_compensator (wide narrow sandwich regularized : ℂ) :
    wide - narrow - (sandwich - regularized) + (narrow - regularized) =
      wide - sandwich := by ring

/-- Neither the endpoint term nor the omitted-zero remainder disappears. -/
theorem retained_remainder (trace orbital boundary omitted : ℂ)
    (h : trace = orbital + boundary - omitted) :
    orbital = trace - boundary + omitted := by rw [h]; ring

end ReviewM

namespace ReviewM
variable {X ι U : Type*} [MeasurableSpace X]

/-- Apply the checked orbit-average normalization at every quotient point.
Measurability is stated for the descended functions, as required for Haar integration. -/
theorem averaged_positivePartition
    (b : X → U → ℝ) (d : ι → X → U → ℝ)
    (hb : ∀ x u, 0 ≤ b x u) (hbs : ∀ x, HasSum (b x) 1)
    (hd : ∀ i x u, 0 ≤ d i x u)
    (hds : ∀ x u, HasSum (fun i => d i x u) 1)
    (hm : ∀ i, Measurable (fun x => ∑' u, b x u * d i x u)) :
    PositivePartition (fun i x => ∑' u, b x u * d i x u) := by
  refine ⟨hm, ?_, ?_⟩
  · intro i x
    exact (ReviewMPartition.averaged_partition (b x) (fun i => d i x)
      (hb x) (hbs x) (fun i => hd i x) (hds x)).2.1 i
  · intro x
    exact (ReviewMPartition.averaged_partition (b x) (fun i => d i x)
      (hb x) (hbs x) (fun i => hd i x) (hds x)).2.2

/-- The positive descended shells reconstruct the ORIGINAL-measure diagonal.
This is B's checked reconstruction argument, using the common partition structure. -/
theorem shell_reconstruction [Countable ι] (μ : Measure X)
    (p : ι → X → ℝ) (hp : PositivePartition p)
    (f : X → ℂ) (hf : Integrable f μ) :
    HasSum (fun i => ∫ x, (p i x : ℂ) * f x ∂μ) (∫ x, f x ∂μ) := by
  classical
  have hi (i : ι) := shell_integrable μ p hp f hf i
  have hb (F : Finset ι) :
      (∑ i ∈ F, ∫ x, ‖(p i x : ℂ) * f x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
    rw [← integral_finset_sum F (fun i _ => (hi i).norm)]
    apply integral_mono (integrable_finset_sum F (fun i _ => (hi i).norm)) hf.norm
    intro x
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp.nonneg _ _)]
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp F x)
  have hs : Summable (fun i => ∫ x, ‖(p i x : ℂ) * f x‖ ∂μ) :=
    summable_of_sum_le (fun i => integral_nonneg (fun x => norm_nonneg _)) hb
  have he (x : X) : (∑' i, (p i x : ℂ) * f x) = f x := by
    have ht := ((Complex.ofRealCLM.hasSum (hp.mass x)).mul_right (f x)).tsum_eq
    simpa using ht
  simpa only [he] using hasSum_integral_of_summable_integral_norm hi hs

end ReviewM

/- Append after NShellFragment, NUpstairsContinuityFragment, and ReviewM's
   common PositivePartition. No local-finite-support assumption is needed. -/
namespace NDivisorialShells
open MasulloGRH NumberField Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section

/-- A finite partial sum witnesses every strict lower bound on a nonnegative
continuous summable family, uniformly in a neighborhood of the chosen point. -/
theorem eventually_lt_tsum_of_nonneg
    {X ι : Type*} [TopologicalSpace X] (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) (hpos : ∀ i x, 0 ≤ f i x)
    (hs : ∀ x, Summable (fun i => f i x)) (x : X) (a : ℝ)
    (ha : a < ∑' i, f i x) :
    ∀ᶠ y in 𝓝 x, a < ∑' i, f i y := by
  classical
  have he : ∀ᶠ S : Finset ι in atTop, a < ∑ i ∈ S, f i x :=
    (hs x).hasSum.eventually (Ioi_mem_nhds ha)
  obtain ⟨S, hS⟩ := he.exists
  have hn : ∀ᶠ y in 𝓝 x, a < ∑ i ∈ S, f i y :=
    (continuous_finset_sum S (fun i _ => hf i)).continuousAt.eventually
      (Ioi_mem_nhds hS)
  filter_upwards [hn] with y hy
  exact hy.trans_le ((hs y).sum_le_tsum S (fun i _ => hpos i y))

/-- Normalization controls both the sum and its complementary sum. Thus a
continuous family dominated by continuous probability weights has continuous
total mass, without an independent local-finite-support hypothesis. -/
theorem continuous_tsum_of_normalized_domination
    {X ι : Type*} [TopologicalSpace X] (w f : ι → X → ℝ)
    (hw : ∀ i, Continuous (w i)) (hf : ∀ i, Continuous (f i))
    (hpos : ∀ i x, 0 ≤ f i x) (hle : ∀ i x, f i x ≤ w i x)
    (hmass : ∀ x, HasSum (fun i => w i x) 1) :
    Continuous (fun x => ∑' i, f i x) := by
  have hs (x : X) : Summable (fun i => f i x) :=
    Summable.of_nonneg_of_le (fun i => hpos i x) (fun i => hle i x)
      (hmass x).summable
  have hc (x : X) : Summable (fun i => w i x - f i x) :=
    (hmass x).summable.sub (hs x)
  have hct (x : X) : (∑' i, (w i x - f i x)) = 1 - ∑' i, f i x :=
    ((hmass x).sub (hs x).hasSum).tsum_eq
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_order.2
  constructor
  · intro a ha
    exact eventually_lt_tsum_of_nonneg f hf hpos hs x a ha
  · intro a ha
    have hlt : 1 - a < ∑' i, (w i x - f i x) := by rw [hct]; linarith
    have he := eventually_lt_tsum_of_nonneg (fun i y => w i y - f i y)
      (fun i => (hw i).sub (hf i)) (fun i y => sub_nonneg.mpr (hle i y))
      hc x (1-a) hlt
    filter_upwards [he] with y hy
    rw [hct] at hy
    linarith

variable (K : Type*) [Field K] [NumberField K]

/-- Concrete orbit-average continuity from the manuscript indentation's
nonnegativity, continuity and normalization on the actual principal orbit. -/
theorem orbitMask_continuous_of_indentation
    (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : Continuous b) (hb0 : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (e : Option ℕ) : Continuous (orbitMask K v b e) := by
  apply continuous_tsum_of_normalized_domination
    (fun q x => b (principalIdele K q * x))
    (fun q x => b (principalIdele K q * x) *
      upstairsMask K v e (principalIdele K q * x))
  · intro q
    exact hb.comp (continuous_const.mul continuous_id)
  · intro q
    exact (hb.comp (continuous_const.mul continuous_id)).mul
      ((upstairsMask_continuous K v e).comp (continuous_const.mul continuous_id))
  · intro q x
    exact mul_nonneg (hb0 _) (upstairs_nonneg K v e _)
  · intro q x
    apply mul_le_of_le_one_right (hb0 _)
    unfold upstairsMask
    split <;> norm_num
  · exact hbs

/-- The actual arithmetic quotient masks are continuous; representative
independence is the already proved principal-idele reindexing. -/
theorem descendedMask_continuous_of_indentation
    (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : Continuous b) (hb0 : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (e : Option ℕ) : Continuous (descendedMask K v b e) :=
  (orbitMask_continuous_of_indentation K v b hb hb0 hbs e).quotient_lift _

/-- All common partition fields are proved on the actual idelic shells.
Existence of a continuous normalized indentation remains a construction
obligation; measurable descent and local finite orbit support are not premises. -/
theorem descended_positivePartition_of_indentation
    (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : Continuous b) (hb0 : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1) :
    ReviewM.PositivePartition (descendedMask K v b) := by
  refine ⟨fun e => (descendedMask_continuous_of_indentation K v b hb hb0 hbs e).measurable,
    ?_, ?_⟩
  · intro e x
    exact (descended_partition_mass K v b hb0 hbs x).1 e
  · intro x
    exact (descended_partition_mass K v b hb0 hbs x).2

end
end NDivisorialShells

/- Append after NIndentationApplicationFragment and NNormalizedDescentFragment. -/
namespace NDivisorialShells
open MasulloGRH MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- A fixed indentation provided by the proved actual arithmetic existence. -/
def arithmeticIndentation : HeckeIdeles K → ℝ :=
  Classical.choose (NIndentation.exists_arithmetic_indentation K)

theorem arithmeticIndentation_continuous : Continuous (arithmeticIndentation K) :=
  (Classical.choose_spec (NIndentation.exists_arithmetic_indentation K)).1

theorem arithmeticIndentation_nonneg (x : HeckeIdeles K) :
    0 ≤ arithmeticIndentation K x :=
  (Classical.choose_spec (NIndentation.exists_arithmetic_indentation K)).2.1 x

theorem arithmeticIndentation_hasSum (x : HeckeIdeles K) :
    HasSum (fun q : Kˣ => arithmeticIndentation K (principalIdele K q * x)) 1 :=
  (Classical.choose_spec (NIndentation.exists_arithmetic_indentation K)).2.2 x

/-- The concrete arithmetic partition has no indentation or descent hypotheses. -/
theorem arithmetic_positivePartition (v : ℕ → NumberField.FinitePlace K) :
    ReviewM.PositivePartition (descendedMask K v (arithmeticIndentation K)) :=
  descended_positivePartition_of_indentation K v (arithmeticIndentation K)
    (arithmeticIndentation_continuous K) (arithmeticIndentation_nonneg K)
    (arithmeticIndentation_hasSum K)

end
end NDivisorialShells
/- Insert after NShellFragment and MPartitionFragment. The signed differences
are the actual manuscript alpha_(n+1)-alpha_n, not positive shell indicators. -/
namespace NDivisorialShells
open MasulloGRH NumberField MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def stratumMask (v : ℕ → FinitePlace K) (n : ℕ) (x : HeckeIdeles K) : ℝ :=
  if x ∈ stratum K v n then 1 else 0

theorem shellIndex_some_iff (v : ℕ → FinitePlace K) (x : HeckeIdeles K) (n : ℕ) :
    shellIndex K v x = some n ↔
      x ∈ stratum K v n ∧ ‖x.val.2 (v n).maximalIdeal‖ ≠ 1 := by
  classical
  constructor
  · intro h
    by_cases he : ∃ k, ‖x.val.2 (v k).maximalIdeal‖ ≠ 1
    · have hn : Nat.find he = n := by simpa [shellIndex, he] using h
      subst n
      exact ⟨(first_nonunit_shell K v x he).2.1, Nat.find_spec he⟩
    · simp [shellIndex, he] at h
  · rintro ⟨hu, hn⟩
    have he : ∃ k, ‖x.val.2 (v k).maximalIdeal‖ ≠ 1 := ⟨n, hn⟩
    have hfind : Nat.find he = n := by
      apply le_antisymm (Nat.find_min' he hn)
      by_contra hlt
      exact Nat.find_spec he (hu _ (lt_of_not_ge hlt))
    simp [shellIndex, he, hfind]

theorem stratum_succ_iff (v : ℕ → FinitePlace K) (x : HeckeIdeles K) (n : ℕ) :
    x ∈ stratum K v (n+1) ↔
      x ∈ stratum K v n ∧ ‖x.val.2 (v n).maximalIdeal‖ = 1 := by
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h n (by omega)⟩
  · rintro ⟨h, hn⟩ k hk
    by_cases he : k = n
    · subst k
      exact hn
    · exact h k (by omega)

/-- The printed successive difference is the negative of the disjoint shell. -/
theorem stratumMask_step (v : ℕ → FinitePlace K) (n : ℕ) (x : HeckeIdeles K) :
    stratumMask K v (n+1) x - stratumMask K v n x =
      -upstairsMask K v (some n) x := by
  classical
  unfold stratumMask upstairsMask
  simp only [stratum_succ_iff, shellIndex_some_iff]
  by_cases hu : x ∈ stratum K v n <;>
    by_cases hn : ‖x.val.2 (v n).maximalIdeal‖ = 1 <;> simp [hu, hn]

/-- The nested quotient mask uses the same actual descended disjoint pieces. -/
def descendedStratumMask (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (n : ℕ) (x : HeckeIdeleClasses K) : ℝ :=
  1 - ∑ k ∈ Finset.range n, descendedMask K v b (some k) x

theorem descendedStratumMask_step (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (n : ℕ) (x : HeckeIdeleClasses K) :
    descendedStratumMask K v b (n+1) x - descendedStratumMask K v b n x =
      -descendedMask K v b (some n) x := by
  simp only [descendedStratumMask, Finset.sum_range_succ]
  ring

/-- This quotient mask equals the orbit average of the literal nested stratum. -/
theorem descendedStratumMask_mk (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q*x)) 1)
    (n : ℕ) (x : HeckeIdeles K) :
    descendedStratumMask K v b n (QuotientGroup.mk x) =
      ∑' q : Kˣ, b (principalIdele K q*x) * stratumMask K v n (principalIdele K q*x) := by
  have hs (m : ℕ) : Summable (fun q : Kˣ =>
      b (principalIdele K q*x) * stratumMask K v m (principalIdele K q*x)) := by
    apply Summable.of_nonneg_of_le _ _ (hbs x).summable
    · intro q
      exact mul_nonneg (hb _) (by unfold stratumMask; split <;> norm_num)
    · intro q
      exact mul_le_of_le_one_right (hb _) (by unfold stratumMask; split <;> norm_num)
  have hp (m : ℕ) : Summable (fun q : Kˣ =>
      b (principalIdele K q*x) * upstairsMask K v (some m) (principalIdele K q*x)) := by
    apply Summable.of_nonneg_of_le _ _ (hbs x).summable
    · intro q
      exact mul_nonneg (hb _) (upstairs_nonneg K v _ _)
    · intro q
      exact mul_le_of_le_one_right (hb _)
        (by unfold upstairsMask; split <;> norm_num)
  induction n with
  | zero =>
      simpa [descendedStratumMask, stratumMask, stratum] using (hbs x).tsum_eq.symm
  | succ n ih =>
      have he (y : HeckeIdeles K) : stratumMask K v (n+1) y =
          stratumMask K v n y - upstairsMask K v (some n) y := by
        linarith [stratumMask_step K v n y]
      simp_rw [he, mul_sub]
      rw [(hs n).tsum_sub (hp n), ← ih]
      simp only [descendedStratumMask, Finset.sum_range_succ, descendedMask_mk, orbitMask]
      ring

/-- The residual piece is precisely the ideles integral and invertible outside
S when the supplied place sequence has that exact range. -/
theorem residual_shell_iff_outside (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Set.range v = Sᶜ) (x : HeckeIdeles K) :
    shellIndex K v x = none ↔ ∀ w ∉ S, ‖x.val.2 w.maximalIdeal‖ = 1 := by
  have hnone : shellIndex K v x = none ↔ ∀ n, ‖x.val.2 (v n).maximalIdeal‖ = 1 := by
    classical
    by_cases he : ∃ n, ‖x.val.2 (v n).maximalIdeal‖ ≠ 1
    · simp [shellIndex, he]
    · simp only [not_exists, not_not] at he
      simp [shellIndex, he]
  rw [hnone]
  constructor
  · intro h w hw
    have hm : w ∈ Set.range v := by rw [hv]; exact hw
    obtain ⟨n, rfl⟩ := hm
    exact h n
  · intro h n
    exact h (v n) (by have hm : v n ∈ Set.range v := ⟨n,rfl⟩; rwa [hv] at hm)

private theorem tsum_option_complex (f : Option ℕ → ℂ) (hf : Summable f) :
    (∑' e, f e) = f none + ∑' n, f (some n) := by
  let g : ℕ ⊕ PUnit → ℂ := f ∘ (Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm
  have hg : Summable g := (Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm.summable_iff.2 hf
  calc
    (∑' e, f e) = ∑' t, g t := ((Equiv.optionEquivSumPUnit.{0, 0} ℕ).symm.tsum_eq f).symm
    _ = (∑' n, g (Sum.inl n)) + ∑' u, g (Sum.inr u) :=
      (hg.comp_injective Sum.inl_injective).tsum_sum (hg.comp_injective Sum.inr_injective)
    _ = f none + ∑' n, f (some n) := by simp [g, tsum_fintype, add_comm]


/-- Original-Haar reconstruction for the signed differences alpha_(n+1)-alpha_n.
The residual S-piece MINUS this signed series is the full diagonal integral. -/
theorem signed_shell_reconstruction (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hp : ReviewM.PositivePartition (descendedMask K v b))
    (mu : Measure (HeckeIdeleClasses K)) (d : HeckeIdeleClasses K → ℂ)
    (hd : Integrable d mu) :
    HasSum (fun n => ∫ x,
      ((descendedStratumMask K v b (n+1) x - descendedStratumMask K v b n x : ℝ) : ℂ) *
        d x ∂mu)
      ((∫ x, (descendedMask K v b none x : ℂ)*d x ∂mu) - ∫ x, d x ∂mu) ∧
    Summable (fun n => ‖∫ x,
      ((descendedStratumMask K v b (n+1) x - descendedStratumMask K v b n x : ℝ) : ℂ) *
        d x ∂mu‖) := by
  let f : Option ℕ → ℂ := fun e => ∫ x, (descendedMask K v b e x : ℂ)*d x ∂mu
  have hs : HasSum f (∫ x, d x ∂mu) := ReviewM.shell_reconstruction mu _ hp d hd
  have hsome : Summable (fun n => f (some n)) := hs.summable.comp_injective (Option.some_injective ℕ)
  have he : (∑' n, f (some n)) = (∫ x, d x ∂mu) - f none := by
    have hh := tsum_option_complex f hs.summable
    rw [hs.tsum_eq] at hh
    linear_combination -hh
  have hid (n : ℕ) : (∫ x,
      ((descendedStratumMask K v b (n+1) x - descendedStratumMask K v b n x : ℝ) : ℂ) *
        d x ∂mu) = -f (some n) := by
    simp only [descendedStratumMask_step, Complex.ofReal_neg, neg_mul, integral_neg, f]
  simp_rw [hid]
  constructor
  · have hh := hsome.hasSum.neg
    rw [he] at hh
    simpa only [neg_sub] using hh
  · have hh := (ReviewM.positive_shell_l1 mu _ hp d hd).1.comp_injective (Option.some_injective ℕ)
    simpa only [norm_neg, f] using hh

end
end NDivisorialShells
/- Insert after NSignedShellFragment and NCanonicalShellPartitionFragment. -/
namespace NDivisorialShells
open MasulloGRH NumberField MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Canonical arithmetic application: no free indentation, positivity,
normalization, or measurability premises remain. -/
theorem canonical_signed_shell_reconstruction (v : ℕ → FinitePlace K)
    (mu : Measure (HeckeIdeleClasses K)) (d : HeckeIdeleClasses K → ℂ)
    (hd : Integrable d mu) :
    HasSum (fun n => ∫ x,
      ((descendedStratumMask K v (arithmeticIndentation K) (n+1) x -
        descendedStratumMask K v (arithmeticIndentation K) n x : ℝ) : ℂ) * d x ∂mu)
      ((∫ x, (descendedMask K v (arithmeticIndentation K) none x : ℂ)*d x ∂mu) -
        ∫ x, d x ∂mu) ∧
    Summable (fun n => ‖∫ x,
      ((descendedStratumMask K v (arithmeticIndentation K) (n+1) x -
        descendedStratumMask K v (arithmeticIndentation K) n x : ℝ) : ℂ) * d x ∂mu‖) :=
  signed_shell_reconstruction K v (arithmeticIndentation K)
    (arithmetic_positivePartition K v) mu d hd

end
end NDivisorialShells




/- Insert after NCanonicalShellPartitionFragment. The common ideles,
quotient and constructed indentation are reused verbatim. -/
namespace NArithmeticUnfolding
open MeasureTheory MasulloGRH NDivisorialShells
open scoped ENNReal BigOperators
noncomputable section

/-- Tonelli and Haar translation unfold a normalized principal-orbit sum.
The equality is nonnegative, so it requires no finite-integral assumption. -/
theorem lintegral_bruhat_unfold {G Γ : Type*} [CommGroup G] [Group Γ]
    [MeasurableSpace G] [MeasurableMul G] [Countable Γ]
    (j : Γ →* G) (mu : Measure G) [mu.IsMulLeftInvariant]
    (b : G → ℝ≥0∞) (hb : Measurable b)
    (hmass : ∀ x, ∑' q : Γ, b (j q * x) = 1)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, b x * (∑' q : Γ, f (j q * x)) ∂mu) = ∫⁻ x, f x ∂mu := by
  calc
    _ = ∫⁻ x, ∑' q : Γ, b x * f (j q * x) ∂mu := by
      simp only [ENNReal.tsum_mul_left]
    _ = ∑' q : Γ, ∫⁻ x, b x * f (j q * x) ∂mu :=
      lintegral_tsum (fun q => (hb.mul (hf.comp (measurable_const_mul _))).aemeasurable)
    _ = ∑' q : Γ, ∫⁻ x, b (j (q⁻¹) * x) * f x ∂mu := by
      apply tsum_congr
      intro q
      have ht := lintegral_mul_left_eq_self
        (μ := mu) (fun x => b (j (q⁻¹) * x) * f x) (j q)
      simpa only [map_inv, inv_mul_cancel_left] using ht
    _ = ∫⁻ x, ∑' q : Γ, b (j (q⁻¹) * x) * f x ∂mu :=
      (lintegral_tsum (fun q =>
        ((hb.comp (measurable_const_mul _)).mul hf).aemeasurable)).symm
    _ = ∫⁻ x, (∑' q : Γ, b (j (q⁻¹) * x)) * f x ∂mu := by
      simp only [ENNReal.tsum_mul_right]
    _ = ∫⁻ x, f x ∂mu := by
      apply lintegral_congr
      intro x
      have he : (∑' q : Γ, b (j (q⁻¹) * x)) = 1 := by
        change (∑' q : Γ, b (j ((Equiv.inv Γ) q) * x)) = 1
        rw [(Equiv.inv Γ).tsum_eq (fun q => b (j q * x))]
        exact hmass x
      rw [he, one_mul]

/-- Real-valued normalized indentations use the same Tonelli identity. -/
theorem lintegral_real_bruhat_unfold {G Γ : Type*} [CommGroup G] [Group Γ]
    [MeasurableSpace G] [MeasurableMul G] [Countable Γ]
    (j : Γ →* G) (mu : Measure G) [mu.IsMulLeftInvariant]
    (b : G → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (hmass : ∀ x, HasSum (fun q : Γ => b (j q * x)) 1)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (b x) * (∑' q : Γ, f (j q * x)) ∂mu) =
      ∫⁻ x, f x ∂mu := by
  apply lintegral_bruhat_unfold j mu (fun x => ENNReal.ofReal (b x)) hb.ennreal_ofReal
    (fun x => ?_) f hf
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => hb0 _) (hmass x).summable,
    (hmass x).tsum_eq, ENNReal.ofReal_one]

variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

/-- The same fixed arithmetic indentation normalized as a nonnegative density. -/
def indentationDensity (x : HeckeIdeles K) : ℝ≥0∞ :=
  ENNReal.ofReal (arithmeticIndentation K x)

theorem indentationDensity_measurable : Measurable (indentationDensity K) :=
  (arithmeticIndentation_continuous K).measurable.ennreal_ofReal

omit [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)] in
theorem indentationDensity_mass (x : HeckeIdeles K) :
    (∑' q : Kˣ, indentationDensity K (principalIdele K q * x)) = 1 := by
  have hm := arithmeticIndentation_hasSum K x
  simp only [indentationDensity]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun q => arithmeticIndentation_nonneg K _) hm.summable, hm.tsum_eq,
    ENNReal.ofReal_one]

/-- Actual arithmetic application: the normalized density is constructed,
not supplied as an application premise. -/
theorem lintegral_arithmetic_unfold
    (lambda : Measure (HeckeIdeles K)) [lambda.IsMulLeftInvariant]
    (f : HeckeIdeles K → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, indentationDensity K x *
      (∑' q : Kˣ, f (principalIdele K q * x)) ∂lambda) = ∫⁻ x, f x ∂lambda := by
  letI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  exact lintegral_bruhat_unfold (principalIdele K) lambda (indentationDensity K)
    (indentationDensity_measurable K) (indentationDensity_mass K) f hf

/-- The counting-normalized quotient measure induced by the actual idelic
measure and the constructed indentation. Its comparison with another Haar
measure is a separate normalization statement. -/
def quotientMeasure (lambda : Measure (HeckeIdeles K)) :
    Measure (HeckeIdeleClasses K) :=
  (lambda.withDensity (indentationDensity K)).map QuotientGroup.mk

theorem lintegral_quotientMeasure
    (lambda : Measure (HeckeIdeles K))
    (F : HeckeIdeleClasses K → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂quotientMeasure K lambda) =
      ∫⁻ y, indentationDensity K y * F (QuotientGroup.mk y) ∂lambda := by
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  rw [quotientMeasure, lintegral_map hF hq]
  exact lintegral_withDensity_eq_lintegral_mul lambda (indentationDensity_measurable K)
    (hF.comp hq)

end
end NArithmeticUnfolding

/- Insert after NIndentationApplicationFragment. This retains the proper-support
part of N's already used Bruhat construction for the quotient measure proof. -/
namespace MQuotientHaar
open MasulloGRH MeasureTheory Pointwise NIndentation
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem exists_proper_arithmetic_indentation :
    ∃ b : HeckeIdeles K → ℝ, Continuous b ∧ (∀ x, 0 ≤ b x) ∧
      (∀ C : Set (HeckeIdeles K), IsCompact C →
        IsCompact (tsupport b ∩ (C * (principalIdeles K : Set (HeckeIdeles K))))) ∧
      ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1 := by
  classical
  letI : MeasurableSpace (HeckeIdeles K) := borel (HeckeIdeles K)
  letI : BorelSpace (HeckeIdeles K) := ⟨rfl⟩
  letI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  letI : Countable (principalIdeles K) :=
    Function.Injective.countable (principalEquiv K).symm.injective
  letI : (Measure.count : Measure (principalIdeles K)).IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        ⟨fun C hC => Measure.count_apply_lt_top.2 hC.finite_of_discrete⟩,
      toIsMulLeftInvariant := inferInstance,
      open_pos := fun U _ hU h => hU.ne_empty (Measure.count_eq_zero_iff.1 h) }
  obtain ⟨b, hb, hb0, hbK, hnorm⟩ := exists_bruhat_function
    (principalIdeles K) (NIdelicTopology.principalIdeles_closed K) Measure.count
  refine ⟨b, hb, hb0, hbK, fun x => ?_⟩
  have hemb : Topology.IsClosedEmbedding
      ((↑) : principalIdeles K → HeckeIdeles K) :=
    (NIdelicTopology.principalIdeles_closed K).isClosedEmbedding_subtypeVal
  let C : Set (HeckeIdeles K) := {x}
  let S : Set (principalIdeles K) :=
    (↑) ⁻¹' (C⁻¹ * (tsupport b ∩ (C * (principalIdeles K : Set (HeckeIdeles K)))))
  have hS : IsCompact S := hemb.isCompact_preimage
    (isCompact_singleton.inv.mul (hbK C isCompact_singleton))
  have hcs : HasCompactSupport (fun h : principalIdeles K => b (x * h)) := by
    apply HasCompactSupport.intro hS
    intro h hh
    by_contra hn
    apply hh
    exact ⟨x⁻¹, by simp [C], x * h,
      ⟨subset_tsupport _ hn, x, rfl, h, h.2, rfl⟩, by simp⟩
  have hi : Integrable (fun h : principalIdeles K => b (x * h)) Measure.count :=
    (hb.comp (continuous_const.mul continuous_subtype_val)).integrable_of_hasCompactSupport hcs
  have hs : HasSum (fun h : principalIdeles K => b (x * h)) 1 := by
    have heq : (∑' h : principalIdeles K, b (x * h)) = 1 := by
      simpa only [integral_countable' hi, Measure.real, Measure.count_singleton,
        ENNReal.toReal_one, one_smul] using hnorm x
    exact heq ▸ (integrable_count_iff.mp hi).of_norm.hasSum
  have hre := (principalEquiv K).hasSum_iff.mpr hs
  simpa only [Function.comp_def, principalEquiv, Equiv.ofBijective_apply,
    mul_comm] using hre

end
end MQuotientHaar

/- Insert after Mathlib. This is the compact-lift step in manuscript 12.2.1.2. -/
namespace MQuotientHaar
open Topology Set
noncomputable section

theorem compact_lift {G Q : Type*} [TopologicalSpace G] [LocallyCompactSpace G]
    [TopologicalSpace Q] (q : G → Q) (ho : IsOpenMap q) (hs : Function.Surjective q)
    (K : Set Q) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ K ⊆ q '' C := by
  classical
  choose C hC hCn using (fun x : G => exists_compact_mem_nhds x)
  have hcover : ∀ y ∈ K, y ∈ ⋃ x : G, q '' interior (C x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hs y
    exact Set.mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hCn x), rfl⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun x => q '' interior (C x)) (fun x => ho _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ t, C x, ?_, ?_⟩
  · exact t.finite_toSet.isCompact_biUnion (fun x _ => hC x)
  · intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact ⟨z, Set.mem_iUnion₂.mpr ⟨x, hx, interior_subset hz⟩, rfl⟩

end
end MQuotientHaar

/- Insert after NArithmeticUnfoldingFragment and MCompactLiftFragment. -/
namespace MQuotientHaar
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped ENNReal Pointwise Topology
noncomputable section

private theorem measure_eq_of_lintegral {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X)
    (h : ∀ f : X → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂mu = ∫⁻ x, f x ∂nu) :
    mu = nu := by
  ext s hs
  have he := h (s.indicator (fun _ => 1)) (measurable_const.indicator hs)
  simpa only [lintegral_indicator hs, setLIntegral_one] using he

variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

omit [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)] in
theorem quotient_principal_mul (q : Kˣ) (x : HeckeIdeles K) :
    (QuotientGroup.mk (principalIdele K q * x) : HeckeIdeleClasses K) =
      QuotientGroup.mk x := by
  apply QuotientGroup.eq.mpr
  have hm : principalIdele K (q⁻¹) ∈ principalIdeles K := ⟨q⁻¹, rfl⟩
  have he : (principalIdele K q * x)⁻¹ * x = principalIdele K (q⁻¹) := by
    simp [mul_inv_rev, mul_comm]
  rw [he]
  exact hm

/-- The quotient measure is independent of the normalized indentation.
The change of density is proved by N's Tonelli identity. -/
theorem lintegral_density_change
    (lambda : Measure (HeckeIdeles K)) [lambda.IsMulLeftInvariant]
    (rho : HeckeIdeles K → ℝ≥0∞) (hr : Measurable rho)
    (hrmass : ∀ x, ∑' q : Kˣ, rho (principalIdele K q * x) = 1)
    (F : HeckeIdeleClasses K → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂quotientMeasure K lambda) =
      ∫⁻ x, rho x * F (QuotientGroup.mk x) ∂lambda := by
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  rw [lintegral_quotientMeasure K lambda F hF]
  have h := lintegral_arithmetic_unfold K lambda
    (fun x => rho x * F (QuotientGroup.mk x)) (hr.mul (hF.comp hq))
  convert h using 1
  apply lintegral_congr
  intro x
  simp_rw [quotient_principal_mul, ENNReal.tsum_mul_right, hrmass, one_mul]

/-- Haar translation invariance is proved for the actual weighted pushforward. -/
theorem quotientMeasure_leftInvariant
    (lambda : Measure (HeckeIdeles K)) [lambda.IsMulLeftInvariant] :
    (quotientMeasure K lambda).IsMulLeftInvariant := by
  refine ⟨fun z => ?_⟩
  obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective z
  apply measure_eq_of_lintegral
  intro F hF
  rw [lintegral_map hF (measurable_const_mul _)]
  rw [lintegral_quotientMeasure K lambda (fun z => F (QuotientGroup.mk t * z))
    (hF.comp (measurable_const_mul _))]
  let rho := fun x => indentationDensity K (t⁻¹ * x)
  have hr : Measurable rho := (indentationDensity_measurable K).comp (measurable_const_mul _)
  have hm (x : HeckeIdeles K) : (∑' q : Kˣ, rho (principalIdele K q * x)) = 1 := by
    dsimp only [rho]
    simpa only [mul_left_comm] using indentationDensity_mass K (t⁻¹*x)
  rw [lintegral_density_change K lambda rho hr hm F hF]
  have ht := lintegral_mul_left_eq_self (μ := lambda)
    (fun x => rho x * F (QuotientGroup.mk x)) t
  convert ht using 1
  apply lintegral_congr
  intro x
  dsimp only [rho]
  rw [inv_mul_cancel_left]
  rfl

end
end MQuotientHaar

/- Append after MQuotientHaarFragment and MProperIndentationFragment. -/
namespace MQuotientHaar
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped ENNReal Pointwise Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

/-- Proper Bruhat support and a compact lift prove finite quotient mass on
compact sets for the already-fixed arithmetic indentation. -/
theorem quotientMeasure_finite_compacts
    (lambda : Measure (HeckeIdeles K)) [lambda.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts lambda] :
    IsFiniteMeasureOnCompacts (quotientMeasure K lambda) := by
  classical
  letI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  obtain ⟨b, hb, hb0, hbK, hbm⟩ := exists_proper_arithmetic_indentation K
  refine ⟨fun B hB => ?_⟩
  let q : HeckeIdeles K → HeckeIdeleClasses K := QuotientGroup.mk
  have hq : Continuous q := QuotientGroup.continuous_mk
  obtain ⟨C, hC, hBC⟩ := compact_lift q QuotientGroup.isOpenMap_coe
    QuotientGroup.mk_surjective B hB
  let T := tsupport b ∩ (C * (principalIdeles K : Set (HeckeIdeles K)))
  have hT : IsCompact T := hbK C hC
  have hBmeas : MeasurableSet B := hB.measurableSet
  have hpre : MeasurableSet (q ⁻¹' B) := hq.measurable hBmeas
  have hsupport (x : HeckeIdeles K) (hx : x ∈ q ⁻¹' B) (hz : b x ≠ 0) : x ∈ T := by
    refine ⟨subset_tsupport _ hz, ?_⟩
    obtain ⟨c, hc, he⟩ := hBC hx
    have hm : c⁻¹ * x ∈ principalIdeles K := QuotientGroup.eq.mp he
    exact ⟨c, hc, c⁻¹*x, hm, mul_inv_cancel_left c x⟩
  have hi : Integrable ((q ⁻¹' B).indicator b) lambda := by
    have hiT : Integrable (T.indicator b) lambda :=
      (hb.continuousOn.integrableOn_compact hT).integrable_indicator hT.measurableSet
    apply (hiT.indicator hpre).congr
    filter_upwards [] with x
    by_cases hx : x ∈ q ⁻¹' B
    · by_cases hz : b x = 0
      · simp [Set.indicator_of_mem hx, hz]
      · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (hsupport x hx hz)]
    · simp [Set.indicator_of_notMem hx]
  have hmass (x : HeckeIdeles K) : (∑' t : Kˣ,
      ENNReal.ofReal (b (principalIdele K t*x))) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => hb0 _) (hbm x).summable,
      (hbm x).tsum_eq, ENNReal.ofReal_one]
  have he := lintegral_density_change K lambda (fun x => ENNReal.ofReal (b x))
    hb.measurable.ennreal_ofReal hmass (B.indicator (fun _ => 1))
    (measurable_const.indicator hBmeas)
  have he' : quotientMeasure K lambda B =
      ∫⁻ x, ENNReal.ofReal ((q ⁻¹' B).indicator b x) ∂lambda := by
    simpa only [lintegral_indicator hBmeas, setLIntegral_one] using he.trans (by
      apply lintegral_congr
      intro x
      by_cases hx : q x ∈ B
      · simp [q, hx]
      · simp [q, hx])
  rw [he']
  apply lt_top_iff_ne_top.mpr
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hb.measurable.indicator hpre).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => Set.indicator_nonneg (fun _ _ => hb0 _) x))).2
  exact hi

end
end MQuotientHaar

/-! C measure/type interface. Insert after the seed arithmetic quotient and
its Borel measurable-space instances. No measure is redefined or rescaled. -/
namespace CNormalization
open MeasureTheory MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [SecondCountableTopology (HeckeIdeles K)]

/-- Local finiteness implies sigma-finiteness on the actual arithmetic quotient,
once second countability of the ideles is supplied. -/
theorem ideleClass_locallyFinite_sigmaFinite
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] :
    SigmaFinite mu := by
  infer_instance

variable [LocallyCompactSpace (HeckeIdeles K)]

/-- A genuine original Haar on the commutative quotient is inversion invariant.
This supplies the input substitution needed for h(x*y⁻¹). -/
theorem ideleClass_haar_invInvariant
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure] :
    mu.IsInvInvariant := by
  infer_instance

end
end CNormalization

/- C -> P/G/N: insert after CArithmeticMeasure and NIdelicTopology.
   The original Haar is not redefined or rescaled. -/
namespace CNormalization
open MeasureTheory MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [SecondCountableTopology (HeckeAdeles K)]

/-- The topology on the actual ideles is induced by their product embedding. -/
theorem idele_secondCountable : SecondCountableTopology (HeckeIdeles K) := by
  letI : SecondCountableTopology (HeckeAdeles K)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : HeckeAdeles K ≃ₜ (HeckeAdeles K)ᵐᵒᵖ).symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

/-- For the original arithmetic Haar, the topology already used in the common
assembly supplies sigma-finiteness and inversion invariance. N's actual idelic
local-compactness proof discharges the remaining topology application. -/
theorem originalHaar_kernel_requirements
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure] :
    SigmaFinite mu ∧ mu.IsInvInvariant := by
  letI : SecondCountableTopology (HeckeIdeles K) := idele_secondCountable K
  constructor
  · exact ideleClass_locallyFinite_sigmaFinite K mu
  · exact ideleClass_haar_invInvariant K mu

end
end CNormalization

/- Append after MQuotientFiniteFragment and CAdelicMeasure. -/
namespace MQuotientHaar
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

/-- The normalized orbit mass makes the quotient measure nonzero. The
application uses positivity of the actual upstairs Haar on open sets. -/
theorem quotientMeasure_ne_zero
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure] :
    quotientMeasure K lambda ≠ 0 := by
  intro hz
  have he := lintegral_quotientMeasure K lambda (fun _ => 1) measurable_const
  rw [hz] at he
  have hi : (∫⁻ x, indentationDensity K x ∂lambda) = 0 := by
    simpa using he.symm
  have hae : indentationDensity K =ᵐ[lambda] 0 :=
    (lintegral_eq_zero_iff (indentationDensity_measurable K)).mp hi
  have hreal : arithmeticIndentation K =ᵐ[lambda] (fun _ => 0) := by
    filter_upwards [hae] with x hx
    apply le_antisymm _ (arithmeticIndentation_nonneg K x)
    exact ENNReal.ofReal_eq_zero.mp hx
  have heq : arithmeticIndentation K = (fun _ => 0) :=
    ((arithmeticIndentation_continuous K).ae_eq_iff_eq lambda continuous_const).mp hreal
  have hm := (arithmeticIndentation_hasSum K (1 : HeckeIdeles K)).tsum_eq
  simp only [heq, tsum_zero] at hm
  exact zero_ne_one hm

attribute [local instance] quotientMeasure_finite_compacts quotientMeasure_leftInvariant

variable [SecondCountableTopology (HeckeAdeles K)]

/-- The counting-normalized arithmetic quotient is an explicitly positive
multiple of the SAME original Haar used in the operator and diagonal. -/
theorem quotientMeasure_eq_scaled_originalHaar
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure] :
    let c := (quotientMeasure K lambda).haarScalarFactor mu
    0 < c ∧ quotientMeasure K lambda = c • mu := by
  letI : SecondCountableTopology (HeckeIdeles K) := CNormalization.idele_secondCountable K
  letI := quotientMeasure_leftInvariant K lambda
  letI := quotientMeasure_finite_compacts K lambda
  have he := Measure.isMulLeftInvariant_eq_smul (quotientMeasure K lambda) mu
  refine ⟨?_, he⟩
  apply pos_iff_ne_zero.mpr
  intro hc
  apply quotientMeasure_ne_zero K lambda
  rw [he, hc, zero_smul]

/-- Original-Haar nonnegative integration with its determined normalization.
No equality of independently normalized measures is assumed. -/
theorem lintegral_originalHaar_normalization
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
    (F : HeckeIdeleClasses K → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, indentationDensity K x * F (QuotientGroup.mk x) ∂lambda) =
      ∫⁻ y, F y ∂((quotientMeasure K lambda).haarScalarFactor mu • mu) := by
  rw [← (quotientMeasure_eq_scaled_originalHaar K lambda mu).2]
  exact (lintegral_quotientMeasure K lambda F hF).symm

end
end MQuotientHaar

/- Insert after NArithmeticUnfoldingFragment. This is the Bochner adapter for
   N's exact constructed counting-normalized quotientMeasure; no second
   measure or assumed Haar comparison is introduced. -/
namespace ReviewI.QuotientIntegration
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped NNReal ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

/-- Absolute integrability and the complex integral both transfer to the
actual indentation-weighted idelic integral. Only the genuine quotient L1
admission is used, so finite kernel diagonals can discharge it directly. -/
theorem integrable_integral_quotientMeasure
    (lambda : Measure (HeckeIdeles K))
    (F : HeckeIdeleClasses K → ℂ) (hF : Integrable F (quotientMeasure K lambda)) :
    Integrable (fun y => (arithmeticIndentation K y : ℂ) *
      F (QuotientGroup.mk y)) lambda ∧
    (∫ x, F x ∂quotientMeasure K lambda) =
      ∫ y, (arithmeticIndentation K y : ℂ) * F (QuotientGroup.mk y) ∂lambda := by
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  let w : HeckeIdeles K → ℝ≥0 := fun y => Real.toNNReal (arithmeticIndentation K y)
  have hw : Measurable w :=
    (arithmeticIndentation_continuous K).measurable.real_toNNReal
  have he (y : HeckeIdeles K) : w y • F (QuotientGroup.mk y) =
      (arithmeticIndentation K y : ℂ) * F (QuotientGroup.mk y) := by
    change ((w y : ℝ) : ℂ) * F (QuotientGroup.mk y) = _
    have hv : (w y : ℝ) = arithmeticIndentation K y :=
      ENNReal.toReal_ofReal (arithmeticIndentation_nonneg K y)
    rw [hv]
  have hi : Integrable (fun y => F (QuotientGroup.mk y))
      (lambda.withDensity (fun y => (w y : ℝ≥0∞))) :=
    hF.comp_aemeasurable hq.aemeasurable
  have hwi := (integrable_withDensity_iff_integrable_smul hw).1 hi
  refine ⟨hwi.congr (Filter.Eventually.of_forall he), ?_⟩
  calc
    _ = ∫ y, F (QuotientGroup.mk y) ∂lambda.withDensity (fun y => (w y : ℝ≥0∞)) :=
      integral_map hq.aemeasurable hF.aestronglyMeasurable
    _ = ∫ y, w y • F (QuotientGroup.mk y) ∂lambda :=
      integral_withDensity_eq_integral_smul hw _
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall he)

end
end ReviewI.QuotientIntegration

/- Append after MOriginalHaarFragment and IQuotientIntegralFragment.
I owns the complex withDensity adapter; M supplies the original-Haar scale. -/
namespace MQuotientHaar
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]
attribute [local instance] quotientMeasure_finite_compacts quotientMeasure_leftInvariant
variable [SecondCountableTopology (HeckeAdeles K)]

/-- Haar invariance, compact-finiteness and nonzero mass have all been proved
for the constructed quotient measure on the actual arithmetic objects. -/
theorem quotientMeasure_isHaar
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure] :
    (quotientMeasure K lambda).IsHaarMeasure := by
  have h := quotientMeasure_eq_scaled_originalHaar K lambda mu
  rw [h.2]
  exact Measure.IsHaarMeasure.nnreal_smul _ h.1.ne'

/-- Original-Haar L1 admission is transported using the proved exact scale,
then I's checked adapter gives the indented complex integral upstairs. -/
theorem integrable_integral_originalHaar
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
    (F : HeckeIdeleClasses K → ℂ) (hF : Integrable F mu) :
    Integrable (fun x => (arithmeticIndentation K x : ℂ) *
      F (QuotientGroup.mk x)) lambda ∧
    (∫ x, (arithmeticIndentation K x : ℂ) * F (QuotientGroup.mk x) ∂lambda) =
      (((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ) * ∫ z, F z ∂mu := by
  have hs := (quotientMeasure_eq_scaled_originalHaar K lambda mu).2
  have hqF : Integrable F (quotientMeasure K lambda) := by
    rw [hs]
    exact hF.smul_measure_nnreal
  have hi := ReviewI.QuotientIntegration.integrable_integral_quotientMeasure K lambda F hqF
  refine ⟨hi.1, hi.2.symm.trans ?_⟩
  calc
    (∫ z, F z ∂quotientMeasure K lambda) =
        ∫ z, F z ∂((quotientMeasure K lambda).haarScalarFactor mu • mu) :=
      congrArg (fun eta : Measure (HeckeIdeleClasses K) => ∫ z, F z ∂eta) hs
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

end
end MQuotientHaar

/- Append after NCanonicalShellPartitionFragment and ReviewMPartition.
This is the tensor indentation identity in manuscript (12.2.2.1)--(12.2.2.4).
It constructs no alternative kernel and assumes no quotient Haar equality. -/
namespace HOrbitalDiagonal
open MasulloGRH NDivisorialShells
open scoped BigOperators
noncomputable section

/-- Both tensor factors of the indentation are retained. The principal-orbit
sum of their correlation has mass one, with absolute convergence supplied by
the already proved positive-partition interchange. -/
theorem correlated_indentation_partition
    {G Γ : Type*} [CommGroup G] [Group Γ]
    (j : Γ →* G) (b : G → ℝ) (hb : ∀ x, 0 ≤ b x)
    (hmass : ∀ x, HasSum (fun q : Γ => b (j q * x)) 1) (x : G) :
    (∀ q : Γ, Summable (fun t : Γ => b (j t * x) * b (j t * (j q⁻¹ * x)))) ∧
    (∀ q : Γ, 0 ≤ ∑' t : Γ, b (j t * x) * b (j t * (j q⁻¹ * x))) ∧
    HasSum (fun q : Γ => ∑' t : Γ, b (j t * x) * b (j t * (j q⁻¹ * x))) 1 := by
  apply ReviewMPartition.averaged_partition
    (fun t : Γ => b (j t * x))
    (fun q t : Γ => b (j t * (j q⁻¹ * x)))
    (fun t => hb _) (hmass x) (fun q t => hb _)
  intro t
  have h := (Equiv.inv Γ).hasSum_iff.mpr (hmass (j t * x))
  simpa only [Function.comp_def, Equiv.inv_apply, mul_left_comm] using h

variable (K : Type*) [Field K] [NumberField K]

/-- Application to the actual arithmetic indentation: no mass or positivity
hypothesis remains to be proved by the caller. -/
theorem arithmetic_correlated_partition (x : HeckeIdeles K) :
    (∀ q : Kˣ, Summable (fun t : Kˣ =>
      arithmeticIndentation K (principalIdele K t * x) *
      arithmeticIndentation K (principalIdele K t * (principalIdele K q⁻¹ * x)))) ∧
    (∀ q : Kˣ, 0 ≤ ∑' t : Kˣ,
      arithmeticIndentation K (principalIdele K t * x) *
      arithmeticIndentation K (principalIdele K t * (principalIdele K q⁻¹ * x))) ∧
    HasSum (fun q : Kˣ => ∑' t : Kˣ,
      arithmeticIndentation K (principalIdele K t * x) *
      arithmeticIndentation K (principalIdele K t * (principalIdele K q⁻¹ * x))) 1 :=
  correlated_indentation_partition (principalIdele K) (arithmeticIndentation K)
    (arithmeticIndentation_nonneg K) (arithmeticIndentation_hasSum K) x

/-- The indented principal-orbit values reconstruct the diagonal of the
same quotient kernel, including its exact absolute mass. This identity is
pointwise; the separate quotient Haar normalization must still be applied
before changing the measure of a diagonal integral. -/
theorem arithmetic_orbital_kernel_diagonal
    (k : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ) (x : HeckeIdeles K) :
    let w := fun q : Kˣ => ∑' t : Kˣ,
      arithmeticIndentation K (principalIdele K t * x) *
      arithmeticIndentation K (principalIdele K t * (principalIdele K q⁻¹ * x))
    let z : HeckeIdeleClasses K := QuotientGroup.mk x
    HasSum (fun q : Kˣ => (w q : ℂ) *
      k (QuotientGroup.mk (principalIdele K q⁻¹ * x)) z) (k z z) ∧
    HasSum (fun q : Kˣ => ‖(w q : ℂ) *
      k (QuotientGroup.mk (principalIdele K q⁻¹ * x)) z‖) ‖k z z‖ := by
  dsimp only
  have hp := arithmetic_correlated_partition K x
  have hq (q : Kˣ) :
      (QuotientGroup.mk (principalIdele K q⁻¹ * x) : HeckeIdeleClasses K) =
        QuotientGroup.mk x := by
    rw [QuotientGroup.mk_mul]
    have hz : (QuotientGroup.mk (principalIdele K q⁻¹) : HeckeIdeleClasses K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨q⁻¹, rfl⟩
    rw [hz, one_mul]
  constructor
  · simpa only [hq, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul] using
      (Complex.ofRealCLM.hasSum hp.2.2).mul_right
        (k (QuotientGroup.mk x) (QuotientGroup.mk x))
  · simpa only [hq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp.2.1 _), one_mul] using
      hp.2.2.mul_right ‖k (QuotientGroup.mk x) (QuotientGroup.mk x)‖

end
end HOrbitalDiagonal

/- Insert after HOrbitalDiagonal and MComplexQuotient.  This is the
original-Haar integration step in manuscript (12.2.2.4), applied pointwise
before taking the quotient measure.  The comparison scalar is retained. -/
namespace HOrbitalDiagonal
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]
variable [SecondCountableTopology (HeckeAdeles K)]
attribute [local instance] MQuotientHaar.quotientMeasure_finite_compacts
  MQuotientHaar.quotientMeasure_leftInvariant

/-- Integrability of the specified quotient diagonal gives absolute orbital
mass upstairs and the exact positive Haar scale.  No product-a.e. identity is
restricted to the diagonal. -/
theorem kernel_originalHaar_orbital_integral
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
    (k : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hk : Integrable (fun x => k x x) mu) :
    let c := (quotientMeasure K lambda).haarScalarFactor mu
    let orbit := fun (q : Kˣ) (x : HeckeIdeles K) =>
      Complex.ofReal (∑' t : Kˣ, arithmeticIndentation K (principalIdele K t * x) *
        arithmeticIndentation K (principalIdele K t * (principalIdele K q⁻¹ * x))) *
      k (QuotientGroup.mk (principalIdele K q⁻¹ * x)) (QuotientGroup.mk x)
    0 < c ∧
    Integrable (fun x => (arithmeticIndentation K x : ℂ) * ∑' q : Kˣ, orbit q x) lambda ∧
    Integrable (fun x => arithmeticIndentation K x * ∑' q : Kˣ, ‖orbit q x‖) lambda ∧
    (∫ x, (arithmeticIndentation K x : ℂ) * ∑' q : Kˣ, orbit q x ∂lambda) =
      ((c : ℝ) : ℂ) * ∫ x, k x x ∂mu := by
  dsimp only
  have hc := (MQuotientHaar.quotientMeasure_eq_scaled_originalHaar K lambda mu).1
  have hi := MQuotientHaar.integrable_integral_originalHaar K lambda mu
    (fun z => k z z) hk
  simp_rw [(arithmetic_orbital_kernel_diagonal K k _).1.tsum_eq,
    (arithmetic_orbital_kernel_diagonal K k _).2.tsum_eq]
  refine ⟨hc, hi.1, ?_, hi.2⟩
  convert hi.1.norm using 1
  ext x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (arithmeticIndentation_nonneg K x)]

end
end HOrbitalDiagonal

/- Insert after DNuclearKernelMeasurable, HNuclearKernel, MNuclearDiagonal,
   QAPToPAFactor, HArithmeticCompression, GKernelRows, CArithmeticMeasure
   NIdelicTopology and CAdelicMeasure. This consumes the AP factors of manuscript
   10.4.2.25--34; it does not prove their arithmetic summability. -/
namespace DNuclearKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The literal AP expansion gives a kernel of PA by projecting its output
columns. The source-zero application, factor equation and cost have separate
roles; no commutation of A with the orthogonal projector is asserted. -/
theorem AP_projected_kernel (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (hbm : Measurable b)
    (S : Submodule ℂ (Lp ℂ 2 nu)) [S.HasOrthogonalProjection]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (hz : ((((1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)-S.starProjection).comp A).comp
      S.starProjection) = 0)
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hAP : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i)
      ((A.comp Sᗮ.starProjection) F)) :
    let P := Sᗮ.starProjection
    let k := kernel nu b u (fun i => P (v i))
    AEStronglyMeasurable (fun p : X × X => k p.1 p.2) (nu.prod nu) ∧
    (∀ F : Lp ℂ 2 nu,
      (∀ᵐ x ∂nu, Integrable (fun y => k x y * (F y / (b y : ℂ))) nu) ∧
      ((P.comp A) F : X → ℂ) =ᵐ[nu]
        (fun x => (b x : ℂ) * ∫ y, k x y * (F y / (b y : ℂ)) ∂nu)) ∧
    (∀ F : Lp ℂ 2 nu,
      ∃ hi : MemLp (fun x => (b x : ℂ) *
        ∫ y, k x y * (F y / (b y : ℂ)) ∂nu) 2 nu,
      hi.toLp _ = (P.comp A) F) ∧
    Integrable (fun x => k x x) nu ∧
    (∫ x, k x x ∂nu) = Masullo.TraceClass.trace (P.comp A) ∧
    (∫ x, ‖k x x‖ ∂nu) ≤ ∑' i, ‖u i‖ * ‖v i‖ := by
  dsimp only
  have hP : Sᗮ.starProjection =
      (1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)-S.starProjection := by
    apply ContinuousLinearMap.ext
    intro F
    simp only [Submodule.starProjection_orthogonal_val,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  have hAP' : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i)
      ((A.comp ((1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)-S.starProjection)) F) := by
    simpa only [hP] using hAP
  have hf : ∀ F, HasSum (fun i => inner ℂ (u i) F • Sᗮ.starProjection (v i))
      ((Sᗮ.starProjection.comp A) F) := by
    simpa only [hP, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
      Q.OrderedNuclear.AP_factors_to_PA S A hz u v hAP'
  have hbound := Q.OrderedNuclear.AP_cost_to_PA S u v hc
  have hc' : Summable (fun i => ‖u i‖ * ‖Sᗮ.starProjection (v i)‖) := by
    simpa only [Submodule.starProjection_orthogonal_val] using hbound.1
  have hdiag := HNormalizedKernel.nuclear_diagonal_integrable nu b hb 1 (by norm_num)
    (fun i => Sᗮ.starProjection (v i)) u (by simpa only [mul_comm] using hc')
  simp only [ENNReal.ofReal_one, one_smul] at hdiag
  have hact (F : Lp ℂ 2 nu) := kernel_action nu b hb
    (Sᗮ.starProjection.comp A) u (fun i => Sᗮ.starProjection (v i)) hc' hf F
  refine ⟨kernel_aestronglyMeasurable nu b hbm _ _ hc', hact, ?_, hdiag.1, ?_, ?_⟩
  · intro F
    have hi := (Lp.memLp ((Sᗮ.starProjection.comp A) F)).ae_eq (hact F).2
    refine ⟨hi, ?_⟩
    apply Lp.ext
    exact hi.coeFn_toLp.trans (hact F).2.symm
  · simpa only [kernel, ENNReal.ofReal_one, one_smul] using
      HOperatorTrace.nuclear_kernel_trace nu b hb 1 (by norm_num)
        (Sᗮ.starProjection.comp A) u (fun i => Sᗮ.starProjection (v i)) hc' hf
  · apply hdiag.2.trans
    simpa only [mul_comm, Submodule.starProjection_orthogonal_val] using hbound.2

end
end DNuclearKernel

namespace DAllSourceKernel
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]

local instance AP_kernel_sigmaFinite : SigmaFinite mu := by
  letI : SecondCountableTopology (HeckeIdeles K) := CNormalization.idele_secondCountable K
  exact CNormalization.ideleClass_locallyFinite_sigmaFinite K mu

/-- Application to both literal tests and the original arithmetic Haar.
The supplied AP expansion/cost remain explicit analytic inputs. Positivity,
measurability, source invariance, PA factor transport, full-input kernel
admission and the diagonal trace identification are proved applications. -/
theorem both_tests_originalHaar_projected_kernel_of_AP
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (u v : ℕ → Lp ℂ 2 mu)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hAP : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i)
      (((intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2).comp
          (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s)ᗮ.starProjection) F)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let W := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let P := Wᗮ.starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let k := DNuclearKernel.kernel mu b u (fun i => P (v i))
    AEStronglyMeasurable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      k p.1 p.2) (mu.prod mu) ∧
    (∀ F : Lp ℂ 2 mu,
      (∀ᵐ x ∂mu, Integrable (fun y => k x y * (F y / (b y : ℂ))) mu) ∧
      ((P.comp A) F : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
        (fun x => (b x : ℂ) * ∫ y, k x y * (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ F : Lp ℂ 2 mu,
      ∃ hi : MemLp (fun x => (b x : ℂ) *
        ∫ y, k x y * (F y / (b y : ℂ)) ∂mu) 2 mu,
      hi.toLp _ = (P.comp A) F) ∧
    Integrable (fun x => k x x) mu ∧
    (∫ x, k x x ∂mu) = Masullo.TraceClass.trace (P.comp A) ∧
    (∫ x, ‖k x x‖ ∂mu) ≤ ∑' i, ‖u i‖ * ‖v i‖ := by
  dsimp only
  have hb := GPointwiseConvolution.intervalHalfWeight_continuous_pos K l r s hlr hs
  have hbm : Measurable (fun x : HeckeIdeleClasses K =>
      intervalHalfWeight l r s (classLog K x)) := by
    simpa only [Complex.ofReal_re] using hb.1.measurable.re
  exact DNuclearKernel.AP_projected_kernel mu _ hb.2 hbm _ _
    (HArithmeticTrace.full_arithmetic_PA_source_zero K addHaar mu a l r s hlr hs phi hh hc q)
    u v hcost hAP

end
end DAllSourceKernel

/- Insert after DAPProjectedKernelFragment and HOriginalHaarOrbitalIntegral.
The actual AP factor construction is an explicit dependency. This applies
its proved PA kernel and diagonal to the SAME original-Haar orbital measure. -/
namespace HArithmeticTrace
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment NDivisorialShells NArithmeticUnfolding
open scoped InnerProductSpace BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
variable (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
attribute [local instance] MQuotientHaar.quotientMeasure_finite_compacts
  MQuotientHaar.quotientMeasure_leftInvariant
local instance PA_orbital_originalHaar_sigmaFinite : SigmaFinite mu :=
  (CNormalization.originalHaar_kernel_requirements K mu).1

/-- The actual PA kernel has its original-Haar diagonal trace and an
absolutely integrable tensor-orbit trace with the exact positive scalar.
The literal AP expansion and summable cost remain explicit analytic inputs;
source invariance, projection order, diagonal admission and measure transport
are all proved on the arithmetic objects for both test families. -/
theorem both_tests_PA_originalHaar_orbital_trace_of_AP
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (u v : ℕ → Lp ℂ 2 mu)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hAP : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i)
      (((intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2).comp
          (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s)ᗮ.starProjection) F)) :
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (LIntegrated.requiredTest K phi q) ht.1 ht.2
    let W := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let P := Wᗮ.starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let k := DNuclearKernel.kernel mu b u (fun i => P (v i))
    let c := (quotientMeasure K lambda).haarScalarFactor mu
    let orbit := fun (j : Kˣ) (x : HeckeIdeles K) =>
      Complex.ofReal (∑' t : Kˣ, arithmeticIndentation K (principalIdele K t * x) *
        arithmeticIndentation K (principalIdele K t * (principalIdele K j⁻¹ * x))) *
      k (QuotientGroup.mk (principalIdele K j⁻¹ * x)) (QuotientGroup.mk x)
    (∀ F : Lp ℂ 2 mu,
      (∀ᵐ x ∂mu, Integrable (fun y => k x y * (F y / (b y : ℂ))) mu) ∧
      ((P.comp A) F : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
        (fun x => (b x : ℂ) * ∫ y, k x y * (F y / (b y : ℂ)) ∂mu)) ∧
    Integrable (fun x => k x x) mu ∧
    (∫ x, k x x ∂mu) = Masullo.TraceClass.trace (P.comp A) ∧
    0 < c ∧
    Integrable (fun x => (arithmeticIndentation K x : ℂ) * ∑' j : Kˣ, orbit j x) lambda ∧
    Integrable (fun x => arithmeticIndentation K x * ∑' j : Kˣ, ‖orbit j x‖) lambda ∧
    (∫ x, (arithmeticIndentation K x : ℂ) * ∑' j : Kˣ, orbit j x ∂lambda) =
      ((c : ℝ) : ℂ) * Masullo.TraceClass.trace (P.comp A) := by
  have hd := DAllSourceKernel.both_tests_originalHaar_projected_kernel_of_AP
    K addHaar mu a l r s hlr hs phi hh hc q u v hcost hAP
  dsimp only at hd ⊢
  have ho := HOrbitalDiagonal.kernel_originalHaar_orbital_integral K lambda mu _ hd.2.2.2.1
  dsimp only at ho
  rw [hd.2.2.2.2.1] at ho
  exact ⟨hd.2.1, hd.2.2.2.1, hd.2.2.2.2.1, ho⟩

end
end HArithmeticTrace

#check HArithmeticTrace.both_tests_PA_originalHaar_orbital_trace_of_AP
#print axioms HArithmeticTrace.both_tests_PA_originalHaar_orbital_trace_of_AP
