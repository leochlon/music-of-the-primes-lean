
-- Exact source: inputs/exchange/F/submissions/febc436fd63242cd85ed65d00f3dc9f2/FConcretePhysicalCheck.lean
import Mathlib
set_option linter.unusedSectionVars false
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

end PIntervalConvolution


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


namespace OSourceClosure
open Filter
open scoped Topology
noncomputable section
variable {V H : Type*} [AddCommGroup V] [Module ℂ V]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def twoMomentSource (e0 eF : V →ₗ[ℂ] ℂ) : Submodule ℂ V := e0.ker ⊓ eF.ker

end
end OSourceClosure


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

end
end OArithmeticClosure


namespace HNormalizedKernel
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]

def haarKernel (b : X → ℝ) (V : ℝ) (U R : X → ℂ) (x y : X) : ℂ :=
  (U x / (b x : ℂ)) * ((b y : ℂ) * star (R y) / (V : ℂ))

omit [MeasurableSpace X] in
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


/-! F contribution. Insert after PIntervalConvolution and HNormalizedKernel.
    Uses the canonical interval half-weight and the original-Haar kernel. -/
namespace FIntervalPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet PIntervalConvolution
open scoped Topology
noncomputable section

/-- The manuscript's full weight (9.2.2.41), in logarithmic coordinates. -/
def intervalWeight (l r s t : ℝ) : ℝ :=
  max (Real.exp (2*l*t)) (Real.exp (2*r*t)) * (1+t^2)^(s/2)

theorem intervalHalfWeight_pos (l r s t : ℝ) :
    0 < PIntervalConvolution.intervalHalfWeight l r s t := by
  unfold PIntervalConvolution.intervalHalfWeight
  positivity

/-- Squaring the seed's actual normalization gives exactly the original weight. -/
theorem intervalHalfWeight_sq (l r s t : ℝ) :
    PIntervalConvolution.intervalHalfWeight l r s t *
      PIntervalConvolution.intervalHalfWeight l r s t = intervalWeight l r s t := by
  have he : Real.exp (max (l*t) (r*t)) * Real.exp (max (l*t) (r*t)) =
      max (Real.exp (2*l*t)) (Real.exp (2*r*t)) := by
    rw [← Real.exp_add]
    by_cases h : l*t ≤ r*t
    · rw [max_eq_right h, max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
      congr 1
      ring
    · have h' : r*t ≤ l*t := le_of_not_ge h
      rw [max_eq_left h', max_eq_left (Real.exp_le_exp.mpr (by nlinarith))]
      congr 1
      ring
  unfold PIntervalConvolution.intervalHalfWeight intervalWeight
  calc
    _ = (Real.exp (max (l*t) (r*t)) * Real.exp (max (l*t) (r*t))) *
      ((1+t^2)^(s/4) * (1+t^2)^(s/4)) := by ring
    _ = _ := by
      rw [he, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
      congr 2
      ring

theorem strict_admission_recenter (l r a : ℝ) (z : ℂ) :
    |(z-(((l+r)/2 : ℝ) : ℂ)).re-a| < (r-l)/2 ↔
      a+l < z.re ∧ z.re < a+r := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Both endpoints survive recentering; admissible boundary degree is separate. -/
theorem boundary_admission_recenter (l r a : ℝ) (hlr : l ≤ r) (z : ℂ) :
    |(z-(((l+r)/2 : ℝ) : ℂ)).re-a| = (r-l)/2 ↔
      z.re = a+l ∨ z.re = a+r := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  constructor
  · intro h
    by_cases hz : 0 ≤ z.re-(l+r)/2-a
    · rw [abs_of_nonneg hz] at h
      right
      linarith
    · rw [abs_of_neg (lt_of_not_ge hz)] at h
      left
      linarith
  · rintro (hz | hz)
    · rw [hz, show a+l-(l+r)/2-a = -((r-l)/2) by ring, abs_neg]
      exact abs_of_nonneg (by linarith)
    · rw [hz, show a+r-(l+r)/2-a = (r-l)/2 by ring]
      exact abs_of_nonneg (by linarith)

/-- The manuscript's epsilon*Lambda regime supplies epsilon -> 0. -/
theorem epsilon_tendsto_zero (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0)) :
    Tendsto epsilon atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (Lambda n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hLambda
  have hp := hprod.mul hi
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [hLambda.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  field_simp [ne_of_gt hn]

/-- The actual (Lambda,epsilon) plateau eventually contains every positive norm.
No relation between the source index and the physical index is used. -/
theorem plateau_eventually (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (t : ℝ) (ht : 0 < t) :
    ∀ᶠ n in atTop, (Lambda n)⁻¹ + epsilon n ≤ t ∧ t ≤ Lambda n - epsilon n := by
  have he := epsilon_tendsto_zero Lambda epsilon hLambda hprod
  have hi : Tendsto (fun n => (Lambda n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hLambda
  have hlo : Tendsto (fun n => (Lambda n)⁻¹ + epsilon n) atTop (𝓝 (0 : ℝ)) := by
    simpa using hi.add he
  filter_upwards [hlo.eventually (gt_mem_nhds ht),
    he.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hLambda.eventually (eventually_ge_atTop (t+1))] with n hn heps hL
  exact ⟨le_of_lt hn, by linarith⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The midpoint multiplication preserves the minus sign in the logged test. -/
theorem logged_test_recenter (b : ℝ) (h : HeckeIdeleClasses K → ℂ) :
    (fun x => radialTwist K b x * (-(classLog K x : ℂ) * h x)) =
      (fun x => -(classLog K x : ℂ) * (radialTwist K b x * h x)) := by
  funext x
  ring

/-- Pointwise mask convergence is proved from the manuscript cutoff plateau. -/
theorem manuscript_mask_tendsto (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1)
    (x : HeckeIdeleClasses K) :
    Tendsto (fun n => omega n x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [plateau_eventually Lambda epsilon hLambda hprod
    (Real.exp (classLog K x)) (Real.exp_pos _)] with n hn
  exact (hplateau n x hn.1 hn.2).symm

/-- Original-Haar cutoff removal on the interval-normalized kernel. All mask
convergence and diagonal integrability hypotheses are discharged here from
the manuscript plateau and the actual completed L2 columns respectively. -/
theorem interval_diagonal_cutoff_limit
    (nu : Measure (HeckeIdeleClasses K)) (l r s V : ℝ) (hV : 0 < V)
    (U R : Lp ℂ 2 nu) (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) (ENNReal.ofReal V • nu))
    (hb : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    Tendsto (fun n => ∫ x, omega n x * HNormalizedKernel.haarKernel
      (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y))
      V U R x x ∂(ENNReal.ofReal V • nu)) atTop (𝓝 (inner ℂ R U)) := by
  apply HNormalizedKernel.diagonal_cutoff_limit nu
    (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y))
    (fun y => intervalHalfWeight_pos l r s (classLog K y)) V hV U R omega hm
  · intro n
    exact Filter.Eventually.of_forall (hb n)
  · exact Filter.Eventually.of_forall
      (manuscript_mask_tendsto K Lambda epsilon hLambda hprod omega hplateau)

end
end FIntervalPhysical


set_option linter.unusedSectionVars false
/- Exact Hilbert-basis trace definitions from Masullo/Analysis/TraceClass.lean.
   The theorems below prove convergence for the finite-rank operators used here. -/
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

namespace HOperatorTrace
open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace BigOperators
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The trace sum of an actual finite-rank operator, in every Hilbert basis. -/
theorem finite_rank_hasSum (U R : ι → H) {κ : Type*} (e : HilbertBasis κ ℂ H) :
    HasSum (fun k => inner ℂ (e k) ((∑ i, rankOne ℂ (U i) (R i)) (e k)))
      (∑ i, inner ℂ (R i) (U i)) := by
  have he : (fun k => inner ℂ (e k) ((∑ i, rankOne ℂ (U i) (R i)) (e k))) =
      fun k => ∑ i, inner ℂ (R i) (e k) * inner ℂ (e k) (U i) := by
    funext k
    simp only [ContinuousLinearMap.sum_apply, rankOne_apply, inner_sum, inner_smul_right]
  rw [he]
  exact hasSum_sum fun i _ => e.hasSum_inner_mul_inner (R i) (U i)

theorem finite_rank_trace (U R : ι → H) :
    Masullo.TraceClass.trace (∑ i, rankOne ℂ (U i) (R i)) =
      ∑ i, inner ℂ (R i) (U i) :=
  (finite_rank_hasSum U R (Masullo.TraceClass.stdHilbertBasis ℂ H)).tsum_eq

/-- Adjoint rows enforce convolution first, left projection second. -/
theorem finite_projection_comp (u : ι → H) (A : H →L[ℂ] H) :
    (∑ i, rankOne ℂ (u i) (u i)).comp A =
      ∑ i, rankOne ℂ (u i) (A.adjoint (u i)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    rankOne_apply, adjoint_inner_left]

/-- The finite-rank sum really is the geometric orthogonal projection. -/
theorem finite_orthogonal_projection (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (u : ι → H) (hu : Orthonormal ℂ u)
    (hspan : Submodule.span ℂ (Set.range u) = E) :
    E.starProjection = ∑ i, rankOne ℂ (u i) (u i) := by
  ext x
  have hp : (∑ i, inner ℂ (u i) x • u i) ∈ E := by
    rw [← hspan]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have ho : ∀ w ∈ E, inner ℂ w (x - ∑ i, inner ℂ (u i) x • u i) = 0 := by
    intro w hw
    rw [← hspan] at hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    rw [sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, inner_sub_right, hu.inner_right_fintype, sub_self, mul_zero]
  simpa only [ContinuousLinearMap.sum_apply, rankOne_apply] using
    (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp
      (fun w hw => inner_eq_zero_symm.mpr (ho w hw)))

variable {X : Type*} [MeasurableSpace X]

/-- An original-Haar diagonal integral is the actual operator trace. -/
theorem finite_kernel_trace (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu) :
    (∫ x, ∑ i, HNormalizedKernel.haarKernel b V (U i) (R i) x x
      ∂(ENNReal.ofReal V • nu)) =
      Masullo.TraceClass.trace (∑ i, rankOne ℂ (U i) (R i)) := by
  rw [integral_finset_sum _ (fun i _ =>
    HNormalizedKernel.diagonal_integrable nu b hb V (U i) (R i))]
  simp_rw [HNormalizedKernel.diagonal_integral nu b hb V hV]
  exact (finite_rank_trace U R).symm

/-- Trace/diagonal attachment for a genuine orthogonal projection after any
completed bounded operator A, hence for the constructed arithmetic convolution. -/
theorem projected_operator_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [E.HasOrthogonalProjection]
    (u : ι → Lp ℂ 2 nu) (hu : Orthonormal ℂ u)
    (hspan : Submodule.span ℂ (Set.range u) = E)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    (∫ x, ∑ i, HNormalizedKernel.haarKernel b V (u i) (A.adjoint (u i)) x x
      ∂(ENNReal.ofReal V • nu)) =
      Masullo.TraceClass.trace (E.starProjection.comp A) := by
  rw [finite_orthogonal_projection E u hu hspan, finite_projection_comp]
  exact finite_kernel_trace nu b hb V hV u (fun i => A.adjoint (u i))

end
end HOperatorTrace

/- Append after HNormalizedKernel and OSourceClosure.actual_source_family_exhaustion.
   The finite spans below are literally the common theta-source finite spans. -/
namespace DSourceKernel
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology BigOperators InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Integrability of the actual full-input rank-one kernel integrand. -/
theorem rank_integrable (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (U R F : Lp ℂ 2 nu) (x : X) :
    Integrable (fun y => HNormalizedKernel.haarKernel b 1 U R x y *
      (F y / (b y : ℂ))) nu := by
  have he (y : X) : HNormalizedKernel.haarKernel b 1 U R x y *
      (F y / (b y : ℂ)) = (U x / (b x : ℂ)) * (F y * star (R y)) := by
    have hy : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    simp only [HNormalizedKernel.haarKernel, Complex.ofReal_one, div_one]
    field_simp
  simp_rw [he]
  exact ((Lp.memLp F).integrable_mul (Lp.memLp R).star).const_mul _

/-- Finite source projection expressed with its actual orthonormal basis. -/
theorem projection_expansion (nu : Measure X)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (v : Lp ℂ 2 nu) :
    E.starProjection v = ∑ i,
      inner ℂ ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu) v •
        ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu) := by
  let e := stdOrthonormalBasis ℂ E
  let w : E := ⟨E.starProjection v, E.starProjection_apply_mem v⟩
  have hw : (w : Lp ℂ 2 nu) = ∑ i, inner ℂ (e i) w • (e i : Lp ℂ 2 nu) := by
    conv_lhs => rw [← e.sum_repr' w]
    simp
  have hi (i) : inner ℂ (e i) w = inner ℂ (e i : Lp ℂ 2 nu) v := by
    change inner ℂ (e i : Lp ℂ 2 nu) (E.starProjection v) = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (e i).property]
  simpa only [hi] using hw

/-- Every row is precomposed with A, implemented by A.adjoint. -/
def finiteKernel (nu : Measure X) (b : X → ℝ)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (x y : X) : ℂ :=
  ∑ i, HNormalizedKernel.haarKernel b 1
    ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
    (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) x y

/-- The canonical finite-source kernel acts on every completed input. -/
theorem finiteKernel_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    (fun x => (E.starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, finiteKernel nu b E A x y *
        (F y / (b y : ℂ)) ∂nu) := by
  classical
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  let c : Fin (Module.finrank ℂ E) → ℂ := fun i => inner ℂ (e i) (A F)
  have he (T : Finset (Fin (Module.finrank ℂ E))) :
      (fun x => (∑ i ∈ T, c i • e i) x) =ᵐ[nu]
      (fun x => ∑ i ∈ T, c i * e i x) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 nu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • e i) (∑ j ∈ T, c j • e j),
        Lp.coeFn_smul (c i) (e i), ih] with x hx hs ht
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, ht] using hx
  rw [projection_expansion]
  filter_upwards [he Finset.univ] with x hx
  change (∑ i, c i • e i) x = _ at hx ⊢
  rw [hx]
  unfold finiteKernel
  simp only [Finset.sum_mul]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h := HNormalizedKernel.kernel_action nu b hb 1 (by norm_num)
      (e i) (A.adjoint (e i)) F x
    rw [adjoint_inner_left] at h
    simpa only [ENNReal.ofReal_one, one_smul] using h.symm
  · intro i hi
    exact rank_integrable nu b hb _ _ F x

/-- This is a direct Haar diagonal calculation for the specified finite kernel. -/
theorem finiteKernel_diagonal (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    Integrable (fun x => finiteKernel nu b E A x x) nu ∧
    (∫ x, finiteKernel nu b E A x x ∂nu) =
      ∑ i, inner ℂ ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
        (A ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) := by
  have hi (i) : Integrable (fun x => HNormalizedKernel.haarKernel b 1
      ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
      (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) x x) nu := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      HNormalizedKernel.diagonal_integrable nu b hb 1
        ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
        (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu))
  constructor
  · exact integrable_finset_sum _ (fun i _ => hi i)
  · unfold finiteKernel
    rw [integral_finset_sum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hmem
    have h := HNormalizedKernel.diagonal_integral nu b hb 1 (by norm_num)
      ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
      (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu))
    rw [adjoint_inner_left] at h
    simpa only [ENNReal.ofReal_one, one_smul] using h

end
end DSourceKernel

/- Append after DSourceKernel and HOperatorTrace. -/
namespace DSourceKernel
open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped BigOperators Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The specified finite source kernel has the trace of the actual source
orthogonal projection after the bounded completed operator A. All finite-frame
hypotheses are discharged by the canonical orthonormal basis of the source span. -/
theorem finiteKernel_trace (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    (∫ x, finiteKernel nu b E A x x ∂nu) =
      Masullo.TraceClass.trace (E.starProjection.comp A) := by
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have he : E.starProjection = ∑ i, rankOne ℂ (e i) (e i) := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.sum_apply, rankOne_apply] using
      projection_expansion nu E v
  rw [he, HOperatorTrace.finite_projection_comp]
  simpa only [finiteKernel, e, ENNReal.ofReal_one, one_smul] using
    HOperatorTrace.finite_kernel_trace nu b hb 1 (by norm_num) e
      (fun i => A.adjoint (e i))

end
end DSourceKernel

/-! F: physical cutoff for D's genuine finite source projection after A.
Insert after HSourceTraceFragment (DSourceKernel.finiteKernel_trace) and FIntervalPhysical. -/
namespace FSourcePhysical
open MeasureTheory Filter ContinuousLinearMap MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology BigOperators InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The radial quantity in the cutoff is the actual arithmetic idele modulus. -/
theorem actual_norm_positive (g : HeckeIdeles K) : 0 < genuineIdeleModulus K g := by
  have hn : 0 ≤ genuineIdeleModulus K g := by
    unfold genuineIdeleModulus
    exact mul_nonneg (Finset.prod_nonneg (fun w _ => pow_nonneg (norm_nonneg _) _))
      (finprod_nonneg (fun v => norm_nonneg _))
  exact lt_of_le_of_ne hn (Ne.symm (genuineIdeleModulus_ne_zero K g))

theorem exp_classLog_mk (g : HeckeIdeles K) :
    Real.exp (classLog K (QuotientGroup.mk g)) = genuineIdeleModulus K g := by
  change Real.exp (Real.log (genuineIdeleModulus K g)) = _
  exact Real.exp_log (actual_norm_positive K g)

/-- Physical cutoff passage for D's actual finite projection AFTER the completed
operator A. The diagonal is the specified kernel and the endpoint is its actual
Hilbert-basis trace. The source span stays fixed throughout this limit. -/
theorem interval_source_kernel_cutoff_trace
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hb : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    Tendsto (fun n => ∫ x, omega n x * DSourceKernel.finiteKernel mu
      (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y))
      E A x x ∂mu) atTop (𝓝 (Masullo.TraceClass.trace (E.starProjection.comp A))) := by
  let b := fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y)
  have bpos : ∀ x, 0 < b x := fun x =>
    FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)
  have hd := (DSourceKernel.finiteKernel_diagonal mu b bpos E A).1
  rw [← DSourceKernel.finiteKernel_trace mu b bpos E A]
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖DSourceKernel.finiteKernel mu b E A x x‖)
  · intro n
    exact (hm n).mul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb n x))
  · exact Filter.Eventually.of_forall (fun x => by
      have hx := FIntervalPhysical.manuscript_mask_tendsto K Lambda epsilon
        hLambda hprod omega hplateau x
      simpa only [one_mul] using hx.mul
        (tendsto_const_nhds (x := DSourceKernel.finiteKernel mu b E A x x)))

end
end FSourcePhysical


namespace DSourceKernel
open MeasureTheory OSourceClosure
noncomputable section
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def sourceSpan (nu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (T : Finset (Lp ℂ 2 nu)) : Submodule ℂ (Lp ℂ 2 nu) :=
  Submodule.span ℂ ((T : Set (Lp ℂ 2 nu)) ∩ Set.range Theta)

instance sourceSpan_finiteDim (nu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu) (T : Finset (Lp ℂ 2 nu)) :
    FiniteDimensional ℂ (sourceSpan nu e0 eF Theta T) :=
  FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet T).inter_of_left _)

end
end DSourceKernel


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


end
end LIntegrated


/-! F: apply the fixed-source physical limit to both actual arithmetic tests.
Insert after LIntegrated.requiredTest, OArithmeticClosure, DSourceKernel, and FSourcePhysical. -/
namespace FArithmeticPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OArithmeticClosure LIntegrated
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Every actual finite theta-source cutoff has the original-Haar physical
trace limit for both sharp tests, with the required midpoint shift in a. -/
theorem both_tests_arithmetic_physical_trace
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hb : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    let tests := requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    ∀ T, Tendsto (fun n => ∫ x, omega n x * DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  exact FSourcePhysical.interval_source_kernel_cutoff_trace K mu l r s _ _
    Lambda epsilon hLambda hprod omega hm hb hplateau

end
end FArithmeticPhysical


namespace DSourceKernel
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]
/-- Removal of any contractive physical mask, with the finite source held fixed.
The limit is the genuine completed-operator trace in the same original Haar. -/
theorem finiteKernel_cutoff_trace_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (omega : ℕ → X → ℂ) (hm : ∀ n, AEStronglyMeasurable (omega n) nu)
    (hbound : ∀ n, ∀ᵐ x ∂nu, ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂nu, Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, omega n x * finiteKernel nu b E A x x ∂nu)
      atTop (𝓝 (Masullo.TraceClass.trace (E.starProjection.comp A))) := by
  rw [← finiteKernel_trace nu b hb E A]
  have hi := (finiteKernel_diagonal nu b hb E A).1
  apply tendsto_integral_of_dominated_convergence (fun x => ‖finiteKernel nu b E A x x‖)
  · intro n
    exact (hm n).mul hi.aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa only [one_mul] using hx.mul
      (tendsto_const_nhds (x := finiteKernel nu b E A x x))

end
end DSourceKernel

namespace DSourceKernel
open MeasureTheory Filter ContinuousLinearMap OSourceClosure
open scoped Topology BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The actual integrand of the finite source kernel is integrable on every input. -/
theorem finiteKernel_integrable (nu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (E : Submodule ℂ (Lp ℂ 2 nu))
    [FiniteDimensional ℂ E] (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (F : Lp ℂ 2 nu) (x : X) :
    Integrable (fun y => finiteKernel nu b E A x y * (F y / (b y : ℂ))) nu := by
  simp only [finiteKernel, Finset.sum_mul]
  exact integrable_finset_sum _ (fun i _ => rank_integrable nu b hb _ _ F x)

/-- Free convolution minus the literal finite source-projection kernel. -/
def residualKernel (nu : Measure X) (b : X → ℝ)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (freeKernel : X → X → ℂ) (x y : X) : ℂ :=
  freeKernel x y - finiteKernel nu b E A x y

/-- Subtraction preserves the actual full-input action. The free action and
its integrability are stated separately so their arithmetic application cannot
be concealed in a kernel-representation definition. -/
theorem residualKernel_action (nu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (E : Submodule ℂ (Lp ℂ 2 nu))
    [FiniteDimensional ℂ E] (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (freeKernel : X → X → ℂ) (F : Lp ℂ 2 nu)
    (hfree : (fun x => A F x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, freeKernel x y * (F y / (b y : ℂ)) ∂nu))
    (hint : ∀ᵐ x ∂nu, Integrable
      (fun y => freeKernel x y * (F y / (b y : ℂ))) nu) :
    (fun x => (A F - E.starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, residualKernel nu b E A freeKernel x y *
        (F y / (b y : ℂ)) ∂nu) := by
  filter_upwards [hfree, hint, finiteKernel_action nu b hb E A F,
    Lp.coeFn_sub (A F) (E.starProjection (A F))] with x hA hi hE hsub
  simp only [Pi.sub_apply] at hsub
  rw [hsub, hA, hE]
  simp only [residualKernel, sub_mul]
  rw [integral_sub hi (finiteKernel_integrable nu b hb E A F x), mul_sub]

/-- When the free diagonal vanishes, the residual diagonal is exactly the
negative finite source diagonal. This does not assert that the residual
operator is trace class. -/
theorem residualKernel_diagonal (nu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (E : Submodule ℂ (Lp ℂ 2 nu))
    [FiniteDimensional ℂ E] (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (freeKernel : X → X → ℂ) (hdiag : ∀ x, freeKernel x x = 0) :
    Integrable (fun x => residualKernel nu b E A freeKernel x x) nu ∧
    (∫ x, residualKernel nu b E A freeKernel x x ∂nu) =
      -Masullo.TraceClass.trace (E.starProjection.comp A) := by
  have he (x : X) : residualKernel nu b E A freeKernel x x =
      -finiteKernel nu b E A x x := by simp [residualKernel, hdiag x]
  simp_rw [he]
  exact ⟨(finiteKernel_diagonal nu b hb E A).1.neg,
    by rw [integral_neg, finiteKernel_trace nu b hb E A]⟩

/-- Fixed-source physical cutoff passage for this same specified residual
kernel. The target is minus the source trace, with no global trace inference. -/
theorem residualKernel_cutoff_limit (nu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (E : Submodule ℂ (Lp ℂ 2 nu))
    [FiniteDimensional ℂ E] (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (freeKernel : X → X → ℂ) (hdiag : ∀ x, freeKernel x x = 0)
    (omega : ℕ → X → ℂ) (hm : ∀ n, AEStronglyMeasurable (omega n) nu)
    (hbound : ∀ n, ∀ᵐ x ∂nu, ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂nu, Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, omega n x * residualKernel nu b E A freeKernel x x ∂nu)
      atTop (𝓝 (-Masullo.TraceClass.trace (E.starProjection.comp A))) := by
  have he (x : X) : residualKernel nu b E A freeKernel x x =
      -finiteKernel nu b E A x x := by simp [residualKernel, hdiag x]
  simp_rw [he, mul_neg, integral_neg]
  exact (finiteKernel_cutoff_trace_limit nu b hb E A omega hm hbound hl).neg

end
end DSourceKernel
/-! F: actual arithmetic application of D's residual kernel cutoff.
Insert after FArithmeticPhysical, LIntegrated, and DResidualKernelFragment.
D owns the residual kernel and its generic diagonal/cutoff identities. -/
namespace FArithmeticPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OArithmeticClosure LIntegrated
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Both required arithmetic residual kernels have the manuscript smooth
physical limit in the original Haar measure. Norm-one vanishing supplies the
diagonal sign. The source cutoff is fixed; the endpoint is minus its source
trace, not an assertion of global residual trace class. -/
theorem both_tests_arithmetic_residual_physical
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hb : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    let tests := requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    let kernel := fun T => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => requiredTest K phi q (x*y⁻¹))
    ∀ T, Integrable (fun x => kernel T x x) mu ∧
      (∫ x, kernel T x x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, omega n x * kernel T x x ∂mu) atTop
        (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  have hbpos : ∀ x, 0 < intervalHalfWeight l r s (classLog K x) :=
    fun x => FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)
  have hdiag : ∀ x : HeckeIdeleClasses K, requiredTest K phi q (x*x⁻¹) = 0 := by
    intro x
    rw [mul_inv_cancel]
    exact requiredTest_at_one K phi hphi q
  refine ⟨(DSourceKernel.residualKernel_diagonal mu _ hbpos _ _ _ hdiag).1,
    (DSourceKernel.residualKernel_diagonal mu _ hbpos _ _ _ hdiag).2, ?_⟩
  apply DSourceKernel.residualKernel_cutoff_limit mu _ hbpos _ _
    (fun x y => requiredTest K phi q (x*y⁻¹)) hdiag omega hm
  · intro n
    exact Filter.Eventually.of_forall (hb n)
  · exact Filter.Eventually.of_forall
      (FIntervalPhysical.manuscript_mask_tendsto K Lambda epsilon hLambda hprod omega hplateau)

end
end FArithmeticPhysical

/-! F: the actual two-parameter physical regime, beyond a chosen sequence.
Insert after FIntervalPhysical, HSourceTraceFragment, and DResidualKernelFragment. -/
namespace FPhysicalFilter
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology
noncomputable section

/-- Coordinates are (Lambda, delta), with delta = epsilon * Lambda.
The product filter is nontrivial and permits independent rates of approach. -/
def cutoffRegime : Filter (ℝ × ℝ) :=
  (atTop : Filter ℝ) ×ˢ (𝓝[>] (0 : ℝ))

instance cutoffRegime_countablyGenerated : cutoffRegime.IsCountablyGenerated := by
  unfold cutoffRegime
  infer_instance

instance cutoffRegime_neBot : cutoffRegime.NeBot := by
  unfold cutoffRegime
  infer_instance

theorem cutoffRegime_Lambda : Tendsto (fun p : ℝ × ℝ => p.1) cutoffRegime atTop :=
  tendsto_fst

/-- In these coordinates epsilon = delta / Lambda, so the manuscript's
product condition follows without tying the two parameters to a sequence. -/
theorem cutoffRegime_product :
    Tendsto (fun p : ℝ × ℝ => (p.2 / p.1) * p.1) cutoffRegime (𝓝 (0 : ℝ)) := by
  have hd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝 (0 : ℝ)) :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝[>] (0 : ℝ))).mono_right
      nhdsWithin_le_nhds
  apply hd.congr'
  filter_upwards [cutoffRegime_Lambda.eventually (eventually_gt_atTop (0 : ℝ))]
    with p hp
  simp [ne_of_gt hp]

/-- The scalar parameter restrictions from manuscript Definition 9.3.3.1. -/
def ValidCutoff (L e : ℝ) : Prop :=
  0 < L ∧ 0 < e ∧ 0 < L⁻¹-e ∧ L⁻¹-e < L-e

theorem cutoffRegime_admissible :
    ∀ᶠ p : ℝ × ℝ in cutoffRegime, ValidCutoff p.1 (p.2/p.1) := by
  have hd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝 (0 : ℝ)) :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝[>] (0 : ℝ))).mono_right
      nhdsWithin_le_nhds
  have hdpos : ∀ᶠ p : ℝ × ℝ in cutoffRegime, 0 < p.2 :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝[>] (0 : ℝ))).eventually
      self_mem_nhdsWithin
  filter_upwards [cutoffRegime_Lambda.eventually (eventually_gt_atTop (1 : ℝ)),
    hdpos, hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with p hL hd0 hd1
  have hL0 : 0 < p.1 := lt_trans zero_lt_one hL
  have he : p.2/p.1 < p.1⁻¹ := by
    rw [div_lt_iff₀ hL0, inv_mul_cancel₀ (ne_of_gt hL0)]
    exact hd1
  have hi : p.1⁻¹ < p.1 := by
    rw [← one_div, div_lt_iff₀ hL0]
    nlinarith
  exact ⟨hL0, div_pos hd0 hL0, sub_pos.mpr he, sub_lt_sub_right hi _⟩

theorem epsilon_tendsto_zero {ι : Type*} (f : Filter ι) (Lambda epsilon : ι → ℝ)
    (hLambda : Tendsto Lambda f atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) f (𝓝 0)) :
    Tendsto epsilon f (𝓝 0) := by
  have hi : Tendsto (fun n => (Lambda n)⁻¹) f (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hLambda
  have hp := hprod.mul hi
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [hLambda.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  field_simp [ne_of_gt hn]

theorem plateau_eventually {ι : Type*} (f : Filter ι) (Lambda epsilon : ι → ℝ)
    (hLambda : Tendsto Lambda f atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) f (𝓝 0))
    (t : ℝ) (ht : 0 < t) :
    ∀ᶠ n in f, (Lambda n)⁻¹ + epsilon n ≤ t ∧ t ≤ Lambda n - epsilon n := by
  have he := epsilon_tendsto_zero f Lambda epsilon hLambda hprod
  have hi : Tendsto (fun n => (Lambda n)⁻¹) f (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hLambda
  have hlo : Tendsto (fun n => (Lambda n)⁻¹ + epsilon n) f (𝓝 (0 : ℝ)) := by
    simpa using hi.add he
  filter_upwards [hlo.eventually (gt_mem_nhds ht),
    he.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hLambda.eventually (eventually_ge_atTop (t+1))] with n hn heps hL
  exact ⟨le_of_lt hn, by linarith⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The filter form of the manuscript's dominated physical passage. The
integrability premise is discharged for the actual source kernel below. -/
theorem manuscript_integral_limit {ι : Type*} (f : Filter ι) [f.IsCountablyGenerated]
    (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu)
    (Lambda epsilon : ι → ℝ) (hLambda : Tendsto Lambda f atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) f (𝓝 0))
    (omega : ι → HeckeIdeleClasses K → ℂ)
    (hm : ∀ᶠ n in f, AEStronglyMeasurable (omega n) mu)
    (hb : ∀ᶠ n in f, ∀ x, ‖omega n x‖ ≤ 1)
    (hp : ∀ᶠ n in f, ∀ x, (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    Tendsto (fun n => ∫ x, omega n x * d x ∂mu) f (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖d x‖)
  · exact hm.mono (fun n hn => hn.mul hd.aestronglyMeasurable)
  · exact hb.mono (fun n hn => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hn x)))
  · exact hd.norm
  · exact Eventually.of_forall (fun x => by
      have hx : Tendsto (fun n => omega n x) f (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hp, plateau_eventually f Lambda epsilon hLambda hprod
          (Real.exp (classLog K x)) (Real.exp_pos _)] with n hpn hn
        exact (hpn x hn.1 hn.2).symm
      simpa only [one_mul] using hx.mul (tendsto_const_nhds (x := d x)))

/-- The same finite source kernel converges in the genuine two-parameter
regime; its actual trace and diagonal integrability are proved suppliers. -/
theorem interval_source_kernel_cutoff_net
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ L e, ValidCutoff L e → AEStronglyMeasurable (omega L e) mu)
    (hb : ∀ L e, ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1)
    (hp : ∀ L e, ValidCutoff L e → ∀ x, L⁻¹ + e ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ L-e → omega L e x = 1) :
    Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x *
      DSourceKernel.finiteKernel mu
        (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y)) E A x x ∂mu)
      cutoffRegime (𝓝 (Masullo.TraceClass.trace (E.starProjection.comp A))) := by
  let b := fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y)
  have bpos : ∀ x, 0 < b x := fun x =>
    FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)
  rw [← DSourceKernel.finiteKernel_trace mu b bpos E A]
  exact manuscript_integral_limit K cutoffRegime mu _
    (DSourceKernel.finiteKernel_diagonal mu b bpos E A).1
    (fun p => p.1) (fun p => p.2/p.1) cutoffRegime_Lambda cutoffRegime_product
    (fun p => omega p.1 (p.2/p.1))
    (cutoffRegime_admissible.mono (fun p hp' => hm p.1 (p.2/p.1) hp'))
    (cutoffRegime_admissible.mono (fun p hp' => hb p.1 (p.2/p.1) hp'))
    (cutoffRegime_admissible.mono (fun p hp' => hp p.1 (p.2/p.1) hp'))

theorem interval_residual_kernel_cutoff_net
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (freeKernel : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hdiag : ∀ x, freeKernel x x = 0)
    (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ L e, ValidCutoff L e → AEStronglyMeasurable (omega L e) mu)
    (hb : ∀ L e, ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1)
    (hp : ∀ L e, ValidCutoff L e → ∀ x, L⁻¹ + e ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ L-e → omega L e x = 1) :
    Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x *
      DSourceKernel.residualKernel mu
        (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y))
        E A freeKernel x x ∂mu)
      cutoffRegime (𝓝 (-Masullo.TraceClass.trace (E.starProjection.comp A))) := by
  have he (x : HeckeIdeleClasses K) : DSourceKernel.residualKernel mu
      (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y)) E A freeKernel x x =
      -DSourceKernel.finiteKernel mu
        (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y)) E A x x := by
    simp [DSourceKernel.residualKernel, hdiag x]
  simp_rw [he, mul_neg, integral_neg]
  exact (interval_source_kernel_cutoff_net K mu l r s E A omega hm hb hp).neg

end
end FPhysicalFilter

/-! F: both actual arithmetic kernels in the two-parameter physical regime.
Insert after FPhysicalFilter, LIntegrated, and J/O arithmetic source definitions. -/
namespace FArithmeticPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OArithmeticClosure LIntegrated FPhysicalFilter
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Smooth cutoff limits for the actual arithmetic source and residual kernels,
with independently varying Lambda and epsilon*Lambda. Parameter validity is
proved eventually, so no conditions on invalid cutoffs are imposed. -/
theorem both_tests_arithmetic_physical_net
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2)
    (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ L e, ValidCutoff L e → AEStronglyMeasurable (omega L e) mu)
    (hb : ∀ L e, ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1)
    (hp : ∀ L e, ValidCutoff L e → ∀ x, L⁻¹ + e ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ L-e → omega L e x = 1) :
    let tests := requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    ∀ T,
      Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        cutoffRegime (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x *
        DSourceKernel.residualKernel mu b (E T) A
          (fun x y => requiredTest K phi q (x*y⁻¹)) x x ∂mu)
        cutoffRegime (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  constructor
  · exact interval_source_kernel_cutoff_net K mu l r s _ _ omega hm hb hp
  · apply interval_residual_kernel_cutoff_net K mu l r s _ _
      (fun x y => requiredTest K phi q (x*y⁻¹)) _ omega hm hb hp
    intro x
    change requiredTest K phi q (x*x⁻¹) = 0
    rw [mul_inv_cancel]
    exact requiredTest_at_one K phi hphi q

end
end FArithmeticPhysical


-- Exact supplier: inputs/exchange/H/HNuclearSupportFragment.lean
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

-- Exact supplier: inputs/exchange/H/HNuclearTraceFragment.lean
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

-- Exact supplier: inputs/exchange/H/HProjectedBasisFragment.lean
/- Append after HTraceFragment. No nuclear hypothesis is used in this factorization. -/
namespace HOperatorTrace
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual geometric left projection has this full-input rank-one expansion.
The output columns are its own Hilbert basis; adjoint rows enforce PA order. -/
theorem projected_basis_factor (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    {ι : Type*} (e : HilbertBasis ι ℂ E) (A : H →L[ℂ] H) (x : H) :
    HasSum (fun i => inner ℂ (A.adjoint (e i : H)) x • (e i : H))
      ((E.starProjection.comp A) x) := by
  have h := E.subtypeL.hasSum (e.hasSum_repr (E.orthogonalProjection (A x)))
  have hi (i : ι) : inner ℂ (e i) (E.orthogonalProjection (A x)) =
      inner ℂ (A.adjoint (e i : H)) x := by
    change inner ℂ (e i : H) (E.starProjection (A x)) = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (e i).property]
    exact (A.adjoint_inner_left x (e i : H)).symm
  simpa only [map_smul, HilbertBasis.repr_apply_apply, hi,
    ContinuousLinearMap.comp_apply, Submodule.starProjection_apply] using h

/-- Exact source-complement application; completeness comes from orthogonality. -/
theorem source_complement_basis_factor (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    {ι : Type*} (e : HilbertBasis ι ℂ Sᗮ) (A : H →L[ℂ] H) (x : H) :
    HasSum (fun i => inner ℂ (A.adjoint (e i : H)) x • (e i : H))
      ((((1 : H →L[ℂ] H) - S.starProjection).comp A) x) := by
  simpa only [ContinuousLinearMap.comp_apply, Submodule.starProjection_orthogonal_val,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
      projected_basis_factor Sᗮ e A x

end
end HOperatorTrace

-- Exact supplier: inputs/exchange/M/MPartitionFragment.lean
noncomputable section
open Filter
open scoped BigOperators Topology
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

-- Exact supplier: inputs/exchange/M/MSeriesFragment.lean
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

/-- Every descended shell may be taken through the same original-Haar series;
no factor depending on the number of shells is introduced. -/
theorem shell_diagonal_series {E : Type*} (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => diagonalL2Cost nu (U i) (R i)))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) (e : E) :
    HasSum (fun i => ∫ x, (p e x : ℂ) * haarKernel b V (U i) (R i) x x
      ∂(ENNReal.ofReal V • nu))
      (∫ x, ∑' i, (p e x : ℂ) * haarKernel b V (U i) (R i) x x
        ∂(ENNReal.ofReal V • nu)) := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hm (i : ι) := ReviewM.shell_integrable (ENNReal.ofReal V • nu) p hp
    (fun x => haarKernel b V (U i) (R i) x x) (hi i) e
  have hmajor (i : ι) : (∫ x,
      ‖(p e x : ℂ) * haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      diagonalL2Cost nu (U i) (R i) := by
    apply le_trans _ (diagonal_integral_norm_le nu b hb V hV (U i) (R i))
    apply integral_mono (hm i).norm (hi i).norm
    intro x
    change ‖(p e x : ℂ) * haarKernel b V (U i) (R i) x x‖ ≤
      ‖haarKernel b V (U i) (R i) x x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg e x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (ReviewM.partition_le_one p hp e x)
  exact hasSum_integral_of_summable_integral_norm hm
    (Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _))
      hmajor hcost)

end
end HNormalizedKernel

-- Exact supplier: inputs/exchange/M/MNormCostFragment.lean
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

-- Exact supplier: inputs/exchange/M/MNuclearDiagonalFragment.lean
/- Insert after MNormCostFragment. The series integrability proof adapts
   review_core/Masullo/Spectral/ComplexMellinMoments.lean:3654,
   itself the ALPO InterBridgeG argument, to an arbitrary countable index. -/
namespace ReviewM
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- An absolute integral row bound constructs an L1 series; pointwise
summability and integrability of the total diagonal are conclusions. -/
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

/-- The full shell vector is continuous under L1 convergence along any filter,
including the directed finite-theta source index used in Q. -/
theorem shell_filter_limit {E J : Type*} (mu : Measure X)
    (p : E → X → ℝ) (hp : PositivePartition p)
    (d : J → X → ℂ) (e : X → ℂ) (hd : ∀ j, Integrable (d j) mu)
    (he : Integrable e mu) (L : Filter J)
    (hlim : Tendsto (fun j => ∫ x, ‖d j x - e x‖ ∂mu) L (𝓝 0)) :
    Tendsto (fun j => ∑' i, ‖(∫ x, (p i x : ℂ) * d j x ∂mu) -
      (∫ x, (p i x : ℂ) * e x ∂mu)‖) L (𝓝 0) := by
  apply squeeze_zero (fun j => tsum_nonneg (fun i => norm_nonneg _))
    (fun j => shell_difference_bound mu p hp (d j) e (hd j) he) hlim

end
end ReviewM

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

/-- Reconstruct the actual L1 diagonal series by all descended shells.
Its entire shell vector is bounded by the single nuclear factor cost. -/
theorem nuclear_diagonal_shells {E : Type*} [Countable E] (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) :
    HasSum (fun e => ∫ x, (p e x : ℂ) *
      (∑' i, haarKernel b V (U i) (R i) x x) ∂(ENNReal.ofReal V • nu))
      (∑' i, inner ℂ (R i) (U i)) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) *
      (∑' i, haarKernel b V (U i) (R i) x x) ∂(ENNReal.ofReal V • nu)‖) ≤
      ∑' i, ‖U i‖ * ‖R i‖ := by
  have hd := nuclear_diagonal_integrable nu b hb V hV U R hc
  constructor
  · have h := ReviewM.shell_reconstruction (ENNReal.ofReal V • nu) p hp _ hd.1
    rw [← (diagonal_series_of_norm_cost nu b hb V hV U R hc).tsum_eq] at h
    exact h
  · exact (ReviewM.positive_shell_l1 (ENNReal.ofReal V • nu) p hp _ hd.1).2.trans hd.2

end
end HNormalizedKernel

-- Exact supplier: inputs/exchange/H/HNuclearKernelFragment.lean
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

/-- Bounded left projection is applied to the columns after convolution.
All resulting cost and expansion hypotheses are proved from the supplied rows. -/
theorem projected_nuclear_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [E.HasOrthogonalProjection]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : κ → Lp ℂ 2 nu)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hA : ∀ F, HasSum (fun n => inner ℂ (u n) F • v n) (A F)) :
    (∫ x, ∑' n, HNormalizedKernel.haarKernel b V
      (E.starProjection (v n)) (u n) x x ∂(ENNReal.ofReal V • nu)) =
        Masullo.TraceClass.trace (E.starProjection.comp A) :=
  nuclear_kernel_trace nu b hb V hV (E.starProjection.comp A) u
    (fun n => E.starProjection (v n)) (nuclear_left_cost E.starProjection u v hc)
      (nuclear_left_factor E.starProjection A u v hA)

/-- Actual source-complement operator; original Haar appears exactly once. -/
theorem complement_nuclear_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (S : Submodule ℂ (Lp ℂ 2 nu)) [S.HasOrthogonalProjection]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : κ → Lp ℂ 2 nu)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hA : ∀ F, HasSum (fun n => inner ℂ (u n) F • v n) (A F)) :
    (∫ x, ∑' n, HNormalizedKernel.haarKernel b V
      (v n - S.starProjection (v n) : Lp ℂ 2 nu) (u n) x x ∂(ENNReal.ofReal V • nu)) =
        Masullo.TraceClass.trace (((1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) -
          S.starProjection).comp A) := by
  have hS : Sᗮ.starProjection =
      (1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) - S.starProjection := by
    apply ContinuousLinearMap.ext
    intro F
    simp only [Submodule.starProjection_orthogonal_val,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  simpa only [hS, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
    projected_nuclear_kernel_trace nu b hb V hV Sᗮ A u v hc hA

/-- Application to the literal geometric projection basis. The actual operator
factor equation is proved, not assumed; only its row-norm summability remains. -/
theorem projected_basis_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [E.HasOrthogonalProjection]
    (e : HilbertBasis κ ℂ E) (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (hs : Summable (fun i => ‖A.adjoint (e i : Lp ℂ 2 nu)‖)) :
    (∫ x, ∑' i, HNormalizedKernel.haarKernel b V
      (e i : Lp ℂ 2 nu) (A.adjoint (e i : Lp ℂ 2 nu)) x x
      ∂(ENNReal.ofReal V • nu)) = Masullo.TraceClass.trace (E.starProjection.comp A) := by
  have hc : Summable (fun i => ‖A.adjoint (e i : Lp ℂ 2 nu)‖ *
      ‖(e i : Lp ℂ 2 nu)‖) := by
    have he (i : κ) : ‖(e i : Lp ℂ 2 nu)‖ = 1 := by
      change ‖e i‖ = 1
      exact e.orthonormal.norm_eq_one i
    simpa only [he, mul_one] using hs
  exact nuclear_kernel_trace nu b hb V hV (E.starProjection.comp A)
    (fun i => A.adjoint (e i : Lp ℂ 2 nu)) (fun i => (e i : Lp ℂ 2 nu)) hc
      (projected_basis_factor E e A)

end
end HOperatorTrace

/-! F: the physical limit for H/M's actual infinite kernel/trace interface.
Insert after FPhysicalFilter, HNuclearKernelFragment, and MNuclearDiagonalFragment.
Analytic row summability is explicit; it is not a proved arithmetic application. -/
namespace FGlobalPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution FPhysicalFilter
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {κ : Type*} [Countable κ]

/-- The original-Haar integral, actual operator trace, and full physical net
are connected for the same nuclear rows. Integrability and mask convergence
are proved from the norm cost and manuscript plateau, respectively. -/
theorem nuclear_kernel_physical_net
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : κ → Lp ℂ 2 mu)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ F, HasSum (fun n => inner ℂ (u n) F • v n) (T F))
    (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ L e, ValidCutoff L e → AEStronglyMeasurable (omega L e) mu)
    (hb : ∀ L e, ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1)
    (hp : ∀ L e, ValidCutoff L e → ∀ x, L⁻¹ + e ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ L-e → omega L e x = 1) :
    let d := fun x => ∑' n, HNormalizedKernel.haarKernel
      (fun y => intervalHalfWeight l r s (classLog K y)) 1 (v n) (u n) x x
    Integrable d mu ∧ (∫ x, d x ∂mu) = Masullo.TraceClass.trace T ∧
      Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x * d x ∂mu)
        cutoffRegime (𝓝 (Masullo.TraceClass.trace T)) := by
  dsimp only
  let b := fun y => intervalHalfWeight l r s (classLog K y)
  have bpos : ∀ x, 0 < b x := fun x =>
    FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)
  have hd := (HNormalizedKernel.nuclear_diagonal_integrable mu b bpos 1 (by norm_num)
    v u (by simpa only [mul_comm] using hc)).1
  simp only [ENNReal.ofReal_one, one_smul] at hd
  have ht := HOperatorTrace.nuclear_kernel_trace mu b bpos 1 (by norm_num) T u v hc hT
  simp only [ENNReal.ofReal_one, one_smul] at ht
  refine ⟨hd, ht, ?_⟩
  rw [← ht]
  exact manuscript_integral_limit K cutoffRegime mu _ hd
    (fun p => p.1) (fun p => p.2/p.1) cutoffRegime_Lambda cutoffRegime_product
    (fun p => omega p.1 (p.2/p.1))
    (cutoffRegime_admissible.mono (fun p hp' => hm p.1 (p.2/p.1) hp'))
    (cutoffRegime_admissible.mono (fun p hp' => hb p.1 (p.2/p.1) hp'))
    (cutoffRegime_admissible.mono (fun p hp' => hp p.1 (p.2/p.1) hp'))

/-- The PA factor equation is discharged for the literal source-complement
Hilbert basis. Only the displayed adjoint-row summability remains analytic. -/
theorem source_complement_basis_physical_net
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (S : Submodule ℂ (Lp ℂ 2 mu)) [S.HasOrthogonalProjection]
    (e : HilbertBasis κ ℂ Sᗮ) (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (hs : Summable (fun i => ‖A.adjoint (e i : Lp ℂ 2 mu)‖))
    (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ L e, ValidCutoff L e → AEStronglyMeasurable (omega L e) mu)
    (hb : ∀ L e, ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1)
    (hp : ∀ L e, ValidCutoff L e → ∀ x, L⁻¹ + e ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ L-e → omega L e x = 1) :
    let d := fun x => ∑' i, HNormalizedKernel.haarKernel
      (fun y => intervalHalfWeight l r s (classLog K y)) 1
      (e i : Lp ℂ 2 mu) (A.adjoint (e i : Lp ℂ 2 mu)) x x
    let PA := ((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S.starProjection).comp A
    Integrable d mu ∧ (∫ x, d x ∂mu) = Masullo.TraceClass.trace PA ∧
      Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x * d x ∂mu)
        cutoffRegime (𝓝 (Masullo.TraceClass.trace PA)) := by
  have hc : Summable (fun i => ‖A.adjoint (e i : Lp ℂ 2 mu)‖ *
      ‖(e i : Lp ℂ 2 mu)‖) := by
    have he (i : κ) : ‖(e i : Lp ℂ 2 mu)‖ = 1 := by
      change ‖e i‖ = 1
      exact e.orthonormal.norm_eq_one i
    simpa only [he, mul_one] using hs
  exact nuclear_kernel_physical_net K mu l r s _ _ _ hc
    (HOperatorTrace.source_complement_basis_factor S e A) omega hm hb hp

end
end FGlobalPhysical

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

end
end OAllCharacterClosure

/-! F: the unrestricted admitted original theta source in the same physical regime.
Insert after FPhysicalFilter, LIntegrated, JAllCharacterSource, and OAllCharacterClosure. -/
namespace FArithmeticPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure LIntegrated FPhysicalFilter
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Smooth cutoff limits for the unrestricted admitted original source and its residual,
with independently varying Lambda and epsilon*Lambda. Parameter validity is
proved eventually, so no conditions on invalid cutoffs are imposed. -/
theorem both_tests_original_physical_net
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2)
    (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ L e, ValidCutoff L e → AEStronglyMeasurable (omega L e) mu)
    (hb : ∀ L e, ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1)
    (hp : ∀ L e, ValidCutoff L e → ∀ x, L⁻¹ + e ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ L-e → omega L e x = 1) :
    let tests := requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    ∀ T,
      Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        cutoffRegime (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      Tendsto (fun p : ℝ × ℝ => ∫ x, omega p.1 (p.2/p.1) x *
        DSourceKernel.residualKernel mu b (E T) A
          (fun x y => requiredTest K phi q (x*y⁻¹)) x x ∂mu)
        cutoffRegime (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  constructor
  · exact interval_source_kernel_cutoff_net K mu l r s _ _ omega hm hb hp
  · apply interval_residual_kernel_cutoff_net K mu l r s _ _
      (fun x y => requiredTest K phi q (x*y⁻¹)) _ omega hm hb hp
    intro x
    change requiredTest K phi q (x*x⁻¹) = 0
    rw [mul_inv_cancel]
    exact requiredTest_at_one K phi hphi q

end
end FArithmeticPhysical


/-! F continuation: an explicit inversion-symmetric smooth radial cutoff.
Insert after FPhysicalFilter. The scalar construction uses the same smooth
transition argument as Masullo/Analysis/TestFunctions and ALPO ExphOn.shortCut.
No source, kernel, measure, or projection is redefined. -/
namespace FSmoothCutoff
open Set
open scoped ContDiff
noncomputable section

def stepBand (L e t : ℝ) : ℝ :=
  Real.smoothTransition ((Real.exp t - L⁻¹) / e) *
    Real.smoothTransition ((L - Real.exp t) / e)

/-- Smooth union with the inverse image preserves the plateau exactly and
enforces the manuscript's multiplicative symmetry. -/
def logCutoff (L e t : ℝ) : ℝ :=
  1 - (1 - stepBand L e t) * (1 - stepBand L e (-t))

theorem stepBand_bounds (L e t : ℝ) :
    0 ≤ stepBand L e t ∧ stepBand L e t ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem logCutoff_bounds (L e t : ℝ) :
    0 ≤ logCutoff L e t ∧ logCutoff L e t ≤ 1 := by
  obtain ⟨ha0, ha1⟩ := stepBand_bounds L e t
  obtain ⟨hb0, hb1⟩ := stepBand_bounds L e (-t)
  have hp0 : 0 ≤ (1 - stepBand L e t) * (1 - stepBand L e (-t)) :=
    mul_nonneg (by linarith) (by linarith)
  have hp1 : (1 - stepBand L e t) * (1 - stepBand L e (-t)) ≤ 1 :=
    mul_le_one₀ (by linarith) (by linarith) (by linarith)
  unfold logCutoff
  constructor <;> linarith

theorem logCutoff_neg (L e t : ℝ) : logCutoff L e (-t) = logCutoff L e t := by
  simp only [logCutoff, neg_neg]
  ring

theorem stepBand_smooth (L e : ℝ) : ContDiff ℝ ∞ (stepBand L e) := by
  exact (Real.smoothTransition.contDiff.comp
    ((Real.contDiff_exp.sub contDiff_const).div_const e)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub Real.contDiff_exp).div_const e))

theorem logCutoff_smooth (L e : ℝ) : ContDiff ℝ ∞ (logCutoff L e) := by
  exact contDiff_const.sub ((contDiff_const.sub (stepBand_smooth L e)).mul
    (contDiff_const.sub ((stepBand_smooth L e).comp contDiff_id.neg)))

theorem stepBand_eq_one (L e t : ℝ) (he : 0 < e)
    (hl : L⁻¹ + e ≤ Real.exp t) (hr : Real.exp t ≤ L - e) :
    stepBand L e t = 1 := by
  unfold stepBand
  rw [Real.smoothTransition.one_of_one_le ((one_le_div he).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div he).2 (by linarith))]
  exact one_mul 1

theorem logCutoff_eq_one (L e t : ℝ) (he : 0 < e)
    (hl : L⁻¹ + e ≤ Real.exp t) (hr : Real.exp t ≤ L - e) :
    logCutoff L e t = 1 := by
  simp [logCutoff, stepBand_eq_one L e t he hl hr]

theorem stepBand_zero_of_le (L e t : ℝ) (he : 0 < e)
    (ht : Real.exp t ≤ L⁻¹) : stepBand L e t = 0 := by
  unfold stepBand
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) he.le), zero_mul]

theorem stepBand_zero_of_ge (L e t : ℝ) (he : 0 < e)
    (ht : L ≤ Real.exp t) : stepBand L e t = 0 := by
  unfold stepBand
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) he.le), mul_zero]

theorem logCutoff_zero_of_ge (L e t : ℝ) (hL : 0 < L) (he : 0 < e)
    (ht : Real.log L ≤ t) : logCutoff L e t = 0 := by
  have hp : L ≤ Real.exp t := by
    simpa only [Real.exp_log hL] using Real.exp_le_exp.mpr ht
  have hn : Real.exp (-t) ≤ L⁻¹ := by
    calc
      Real.exp (-t) ≤ Real.exp (-Real.log L) := Real.exp_le_exp.mpr (neg_le_neg ht)
      _ = L⁻¹ := by rw [Real.exp_neg, Real.exp_log hL]
  simp [logCutoff, stepBand_zero_of_ge L e t he hp,
    stepBand_zero_of_le L e (-t) he hn]

theorem logCutoff_zero_of_le (L e t : ℝ) (hL : 0 < L) (he : 0 < e)
    (ht : t ≤ -Real.log L) : logCutoff L e t = 0 := by
  rw [← logCutoff_neg]
  exact logCutoff_zero_of_ge L e (-t) hL he (by linarith)

theorem logCutoff_support (L e : ℝ) (hL : 0 < L) (he : 0 < e) :
    Function.support (logCutoff L e) ⊆ Icc (-Real.log L) (Real.log L) := by
  intro t ht
  constructor
  · by_contra h
    exact ht (logCutoff_zero_of_le L e t hL he (le_of_not_ge h))
  · by_contra h
    exact ht (logCutoff_zero_of_ge L e t hL he (le_of_not_ge h))

theorem logCutoff_compact (L e : ℝ) (hL : 0 < L) (he : 0 < e) :
    HasCompactSupport (logCutoff L e) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact closure_minimal (logCutoff_support L e hL he) isClosed_Icc

end
end FSmoothCutoff


/-! F: attach the explicit scalar cutoff to the manuscript's class norm.
Insert after FSmoothCutoff, FPhysicalFilter, and DReview.classLog_inv. -/
namespace FSmoothCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def realMask (L e : ℝ) (x : HeckeIdeleClasses K) : ℝ :=
  logCutoff L e (classLog K x)

def mask (L e : ℝ) (x : HeckeIdeleClasses K) : ℂ :=
  (realMask K L e x : ℂ)

theorem realMask_bounds (L e : ℝ) (x : HeckeIdeleClasses K) :
    0 ≤ realMask K L e x ∧ realMask K L e x ≤ 1 :=
  logCutoff_bounds L e (classLog K x)

theorem realMask_continuous (L e : ℝ) : Continuous (realMask K L e) :=
  (logCutoff_smooth L e).continuous.comp (classLog_continuous K)

theorem mask_continuous (L e : ℝ) : Continuous (mask K L e) :=
  Complex.continuous_ofReal.comp (realMask_continuous K L e)

theorem mask_measurable (mu : Measure (HeckeIdeleClasses K)) (L e : ℝ) :
    AEStronglyMeasurable (mask K L e) mu :=
  (mask_continuous K L e).measurable.aestronglyMeasurable

theorem mask_norm_le (L e : ℝ) (x : HeckeIdeleClasses K) :
    ‖mask K L e x‖ ≤ 1 := by
  simp only [mask, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realMask_bounds K L e x).1]
  exact (realMask_bounds K L e x).2

theorem realMask_inv (L e : ℝ) (x : HeckeIdeleClasses K) :
    realMask K L e x⁻¹ = realMask K L e x := by
  simp only [realMask, DReview.classLog_inv, logCutoff_neg]

theorem mask_inv (L e : ℝ) (x : HeckeIdeleClasses K) :
    mask K L e x⁻¹ = mask K L e x := by
  rw [mask, mask, realMask_inv]

theorem mask_plateau (L e : ℝ) (hv : FPhysicalFilter.ValidCutoff L e)
    (x : HeckeIdeleClasses K)
    (hl : L⁻¹ + e ≤ Real.exp (classLog K x))
    (hr : Real.exp (classLog K x) ≤ L - e) : mask K L e x = 1 := by
  simp only [mask, realMask, logCutoff_eq_one L e (classLog K x) hv.2.1 hl hr,
    Complex.ofReal_one]

theorem mask_support (L e : ℝ) (hv : FPhysicalFilter.ValidCutoff L e) :
    Function.support (mask K L e) ⊆
      {x | L⁻¹ ≤ Real.exp (classLog K x) ∧ Real.exp (classLog K x) ≤ L} := by
  intro x hx
  have hx' : logCutoff L e (classLog K x) ≠ 0 := by
    intro hz
    exact hx (by simp [mask, realMask, hz])
  obtain ⟨hl, hr⟩ := logCutoff_support L e hv.1 hv.2.1 hx'
  constructor
  · have h := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_neg, Real.exp_log hv.1] using h
  · have h := Real.exp_le_exp.mpr hr
    simpa only [Real.exp_log hv.1] using h

/-- Every fixed class eventually lies on the plateau in the actual independent
two-parameter regime, including the identity where the mask attains norm one. -/
theorem mask_eventually_one (x : HeckeIdeleClasses K) :
    ∀ᶠ p : ℝ × ℝ in FPhysicalFilter.cutoffRegime,
      mask K p.1 (p.2 / p.1) x = 1 := by
  filter_upwards [FPhysicalFilter.cutoffRegime_admissible,
    FPhysicalFilter.plateau_eventually FPhysicalFilter.cutoffRegime
      (fun p : ℝ × ℝ => p.1) (fun p : ℝ × ℝ => p.2 / p.1)
      FPhysicalFilter.cutoffRegime_Lambda FPhysicalFilter.cutoffRegime_product
      (Real.exp (classLog K x)) (Real.exp_pos _)] with p hp hx
  exact mask_plateau K p.1 (p.2 / p.1) hp x hx.1 hx.2

/-- All cutoff hypotheses of the original-Haar dominated passage are now
proved for the explicit radial family. Integrability remains the supplied
diagonal theorem's obligation. -/
theorem integral_limit (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun p : ℝ × ℝ => ∫ x, mask K p.1 (p.2 / p.1) x * d x ∂mu)
      FPhysicalFilter.cutoffRegime (𝓝 (∫ x, d x ∂mu)) := by
  exact FPhysicalFilter.manuscript_integral_limit K FPhysicalFilter.cutoffRegime mu d hd
    (fun p : ℝ × ℝ => p.1) (fun p : ℝ × ℝ => p.2 / p.1)
    FPhysicalFilter.cutoffRegime_Lambda FPhysicalFilter.cutoffRegime_product
    (fun p => mask K p.1 (p.2 / p.1))
    (Eventually.of_forall (fun p => mask_measurable K mu p.1 (p.2 / p.1)))
    (Eventually.of_forall (fun p => mask_norm_le K p.1 (p.2 / p.1)))
    (FPhysicalFilter.cutoffRegime_admissible.mono (fun p hp =>
      mask_plateau K p.1 (p.2 / p.1) hp))

end
end FSmoothCutoff


/-! F: exact common-source application, with all smooth mask data discharged.
Insert after FSmoothCutoff, FSmoothRadial and FOriginalPhysicalNet. -/
namespace FArithmeticPhysical
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure LIntegrated FPhysicalFilter
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

theorem both_tests_original_smooth_physical_net
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) :
    let tests := requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    ∀ T,
      Tendsto (fun p : ℝ × ℝ => ∫ x, FSmoothCutoff.mask K p.1 (p.2/p.1) x *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        cutoffRegime (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      Tendsto (fun p : ℝ × ℝ => ∫ x, FSmoothCutoff.mask K p.1 (p.2/p.1) x *
        DSourceKernel.residualKernel mu b (E T) A
          (fun x y => requiredTest K phi q (x*y⁻¹)) x x ∂mu)
        cutoffRegime (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  exact both_tests_original_physical_net K addHaar mu a l r s hlr hs phi hh hc hphi q
    (FSmoothCutoff.mask K)
    (fun L e _ => FSmoothCutoff.mask_measurable K mu L e)
    (fun L e _ => FSmoothCutoff.mask_norm_le K L e)
    (FSmoothCutoff.mask_plateau K)

end
end FArithmeticPhysical



-- Exact source: inputs/exchange/K/KStrongPhysicalMask.lean
/-! Insert after KMaskFragment. Bounded physical multiplication on the common
completed L2 realization. The construction adapts the actual toLp/cutCLM proof
in review_core/Masullo/Geometry/WeightedCutoff.lean, without importing its
separate weighted measure or its conditional trace theorem. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory Filter
open scoped Topology ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem real_mask_mul_norm_le (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (z : ℂ) :
    ‖(r : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hr.2

theorem real_mask_sub_norm_le (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (z : ℂ) :
    ‖(r : ℂ) * z - z‖ ≤ ‖z‖ := by
  have heq : (r : ℂ) * z - z = ((r-1 : ℝ) : ℂ) * z := by push_cast; ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hr.2)]
  apply mul_le_of_le_one_left (norm_nonneg _)
  linarith [hr.1]

theorem realMask_memLp (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    MemLp (fun x => (rho x : ℂ) * f x) 2 mu := by
  refine ⟨hm.complex_ofReal.aestronglyMeasurable.mul (Lp.memLp f).1, ?_⟩
  apply lt_of_le_of_lt _ (Lp.memLp f).2
  exact eLpNorm_mono_ae (Eventually.of_forall (fun x => real_mask_mul_norm_le _ (hb x) _))

def realMask (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  (realMask_memLp mu rho hm hb f).toLp (fun x => (rho x : ℂ) * f x)

theorem realMask_ae (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    (realMask mu rho hm hb f : X → ℂ) =ᵐ[mu] fun x => (rho x : ℂ) * f x :=
  MemLp.coeFn_toLp _

theorem realMask_norm_le (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    ‖realMask mu rho hm hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [realMask_ae mu rho hm hb f] with x hx
  rw [hx]
  exact real_mask_mul_norm_le _ (hb x) _

/-- Literal multiplication by the manuscript real physical mask. -/
def realMaskCLM (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  LinearMap.mkContinuous
    { toFun := realMask mu rho hm hb
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [realMask_ae mu rho hm hb (f+g),
          realMask_ae mu rho hm hb f, realMask_ae mu rho hm hb g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (realMask mu rho hm hb f) (realMask mu rho hm hb g)]
          with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [realMask_ae mu rho hm hb (c • f), realMask_ae mu rho hm hb f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (realMask mu rho hm hb f)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4, Pi.smul_apply, h2, h3, Pi.smul_apply]
        simp only [smul_eq_mul]
        ring }
    1 (fun f => by simpa using realMask_norm_le mu rho hm hb f)

theorem realMaskCLM_complement_bound
    (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    ‖realMaskCLM mu rho hm hb f - f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (realMaskCLM mu rho hm hb f) f,
    realMask_ae mu rho hm hb f] with x h1 h2
  change (realMaskCLM mu rho hm hb f : X → ℂ) x = _ at h2
  rw [h1, Pi.sub_apply, h2]
  exact real_mask_sub_norm_le _ (hb x) _

/-- The entire L2 error is bounded with constant one by the original-measure
tail outside the physical plateau. No source index occurs in this estimate. -/
theorem real_mask_tail_eLpNorm (mu : Measure X) (band : Set X)
    (rho : X → ℝ) (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ band, rho x = 1) (f : X → ℂ) :
    eLpNorm (fun x => (rho x : ℂ) * f x - f x) 2 mu ≤
      eLpNorm (bandᶜ.indicator f) 2 mu := by
  apply eLpNorm_mono_ae
  filter_upwards [] with x
  by_cases hx : x ∈ band
  · simp [hp x hx, hx]
  · simpa [hx] using real_mask_sub_norm_le (rho x) (hb x) (f x)

/-- Strong convergence of the genuine bounded multiplication operators. The
plateau application, rather than an assumed Lp limit, supplies pointwise
eventual equality. This is a vector theorem, with no nuclearity conclusion. -/
theorem realMaskCLM_strong (mu : Measure X) (rho : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (rho n))
    (hb : ∀ n x, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (hp : ∀ x, ∀ᶠ n in atTop, rho n x = 1) (f : Lp ℂ 2 mu) :
    Tendsto (fun n => realMaskCLM mu (rho n) (hm n) (hb n) f) atTop (𝓝 f) := by
  let F : ℕ → X → ℂ := fun n x => (rho n x : ℂ) * f x
  have hF : ∀ n, MemLp (F n) 2 mu := fun n => realMask_memLp mu _ (hm n) (hb n) f
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ≠ ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Lp.memLp f).2).ne
  have hlim : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂mu)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖F n x - f x‖ₑ ^ (2 : ℝ))
      (fun x => ‖f x‖ₑ ^ (2 : ℝ))
      (fun n => by simpa using (((hF n).1.sub (Lp.memLp f).1).enorm.pow_const (2 : ℕ)))
      (fun n => Eventually.of_forall fun x => by
        apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (real_mask_sub_norm_le _ (hb n x) _)) hfin
      (f := fun _ => (0 : ℝ≥0∞))
      (Eventually.of_forall fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hp x] with n hn
        simp [F, hn])
    simpa using h
  have hnorm : Tendsto (fun n => eLpNorm (F n - (f : X → ℂ)) 2 mu)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hlim
    simpa only [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, Pi.sub_apply,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF (f : X → ℂ) (Lp.memLp f)).2 hnorm
  simpa only [Lp.toLp_coeFn] using h

end KPhysicalMask
end


-- Exact source: HMaskedDiagonalFragment.lean
/- Append after HSourceTrace and KStrongPhysicalMask. The mask is K's actual
completed multiplication operator; all measures and kernels are unchanged. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Multiplying the original-Haar diagonal is exactly multiplying the output
column in L2. The a.e. representative conversion is proved explicitly. -/
theorem realMask_diagonal (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (rho : X → ℝ) (hm : Measurable rho) (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (U R : Lp ℂ 2 nu) :
    Integrable (fun x => (rho x : ℂ) * haarKernel b 1 U R x x) nu ∧
    (∫ x, (rho x : ℂ) * haarKernel b 1 U R x x ∂nu) =
      inner ℂ R (KPhysicalMask.realMaskCLM nu rho hm hbound U) := by
  let M := KPhysicalMask.realMaskCLM nu rho hm hbound
  have he : (fun x => (rho x : ℂ) * haarKernel b 1 U R x x) =ᵐ[nu]
      (fun x => haarKernel b 1 (M U) R x x) := by
    filter_upwards [KPhysicalMask.realMask_ae nu rho hm hbound U] with x hx
    change (M U : X → ℂ) x = (rho x : ℂ) * U x at hx
    simp only [diagonal_formula b hb, Complex.ofReal_one, inv_one, one_mul, hx]
    ring
  have hi : Integrable (fun x => haarKernel b 1 (M U) R x x) nu := by
    simpa only [ENNReal.ofReal_one, one_smul] using diagonal_integrable nu b hb 1 (M U) R
  refine ⟨hi.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simpa only [ENNReal.ofReal_one, one_smul] using
    diagonal_integral nu b hb 1 (by norm_num) (M U) R

end
end HNormalizedKernel

namespace DSourceKernel
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The physical cutoff of the finite EA diagonal is the trace of EAM.
The equality uses adjoint rows and finite-dimensional trace, with no
commutation of E, A or M and no nuclearity assumption about A. -/
theorem finiteKernel_realMask_trace (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (rho : X → ℝ) (hm : Measurable rho) (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) :
    let M := KPhysicalMask.realMaskCLM nu rho hm hbound
    Integrable (fun x => (rho x : ℂ) * finiteKernel nu b E A x x) nu ∧
    (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x ∂nu) =
      (∫ x, finiteKernel nu b E (A.comp M) x x ∂nu) ∧
    (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x ∂nu) =
      Masullo.TraceClass.trace (E.starProjection.comp (A.comp M)) := by
  dsimp only
  let M := KPhysicalMask.realMaskCLM nu rho hm hbound
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have hr (i : Fin (Module.finrank ℂ E)) :=
    HNormalizedKernel.realMask_diagonal nu b hb rho hm hbound (e i) (A.adjoint (e i))
  have hi : Integrable (fun x => (rho x : ℂ) * finiteKernel nu b E A x x) nu := by
    simp only [finiteKernel, Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => (hr i).1)
  have he : (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x ∂nu) =
      (∫ x, finiteKernel nu b E (A.comp M) x x ∂nu) := by
    calc
      _ = ∑ i, inner ℂ (A.adjoint (e i)) (M (e i)) := by
        simp only [finiteKernel, Finset.mul_sum]
        rw [integral_finset_sum _ (fun i _ => (hr i).1)]
        exact Finset.sum_congr rfl (fun i _ => (hr i).2)
      _ = _ := by
        rw [(finiteKernel_diagonal nu b hb E (A.comp M)).2]
        apply Finset.sum_congr rfl
        intro i _
        exact A.adjoint_inner_left (M (e i)) (e i)
  exact ⟨hi, he, he.trans (finiteKernel_trace nu b hb E (A.comp M))⟩

end
end DSourceKernel


-- Exact source: HArithmeticMaskedDiagonalFragment.lean
/- Append after HMaskedDiagonal, FSmoothRadial and the shared full-source
kernel definitions. All mask hypotheses are discharged for F's constructed
smooth manuscript family. -/
namespace HArithmeticTrace
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment OAllCharacterClosure
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- For both actual interval convolutions and every finite full-theta source,
the literal smooth physical diagonal has the trace of the correctly ordered
E A M. The residual diagonal retains the negative source trace. -/
theorem both_tests_full_source_smooth_mask_trace
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) (L epsilon : ℝ) :
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (LIntegrated.requiredTest K phi q) ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let M := KPhysicalMask.realMaskCLM mu (FSmoothCutoff.realMask K L epsilon)
      (FSmoothCutoff.realMask_continuous K L epsilon).measurable
      (FSmoothCutoff.realMask_bounds K L epsilon)
    ∀ T,
      Integrable (fun x => FSmoothCutoff.mask K L epsilon x *
        DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, FSmoothCutoff.mask K L epsilon x * DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        (∫ x, DSourceKernel.finiteKernel mu b (E T) (A.comp M) x x ∂mu) ∧
      (∫ x, FSmoothCutoff.mask K L epsilon x * DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp (A.comp M)) ∧
      (∫ x, FSmoothCutoff.mask K L epsilon x * DSourceKernel.residualKernel mu b (E T) A
        (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) x x ∂mu) =
        -Masullo.TraceClass.trace ((E T).starProjection.comp (A.comp M)) := by
  dsimp only
  intro T
  have h := DSourceKernel.finiteKernel_realMask_trace mu
    (fun x => intervalHalfWeight l r s (classLog K x))
    (fun x => FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x))
    (DSourceKernel.sourceSpan mu
      (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) T)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    (FSmoothCutoff.realMask K L epsilon)
    (FSmoothCutoff.realMask_continuous K L epsilon).measurable
    (FSmoothCutoff.realMask_bounds K L epsilon)
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  simp only [DSourceKernel.residualKernel, mul_inv_cancel,
    LIntegrated.requiredTest_at_one K phi hphi q, zero_sub, mul_neg, integral_neg]
  exact congrArg Neg.neg h.2.2

end
end HArithmeticTrace
#check HArithmeticTrace.both_tests_full_source_smooth_mask_trace
#print axioms HArithmeticTrace.both_tests_full_source_smooth_mask_trace
