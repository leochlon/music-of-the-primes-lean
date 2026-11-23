
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

/- Append after HMaskedDiagonal. These are the same masks, finite source
kernel, original measure and genuine Hilbert-basis operator trace. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The two-sided physical diagonal has two mask factors. Its integral is
the L2 pairing with two successive applications of the actual mask. -/
theorem realMask_twosided_diagonal (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (rho : X → ℝ) (hm : Measurable rho) (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (U R : Lp ℂ 2 nu) :
    let M := KPhysicalMask.realMaskCLM nu rho hm hbound
    Integrable (fun x => (rho x : ℂ) * haarKernel b 1 U R x x * (rho x : ℂ)) nu ∧
    (∫ x, (rho x : ℂ) * haarKernel b 1 U R x x * (rho x : ℂ) ∂nu) =
      inner ℂ R (M (M U)) := by
  dsimp only
  let M := KPhysicalMask.realMaskCLM nu rho hm hbound
  have he : (fun x => (rho x : ℂ) * haarKernel b 1 U R x x * (rho x : ℂ)) =ᵐ[nu]
      (fun x => haarKernel b 1 (M (M U)) R x x) := by
    filter_upwards [KPhysicalMask.realMask_ae nu rho hm hbound U,
      KPhysicalMask.realMask_ae nu rho hm hbound (M U)] with x h1 h2
    change (M U : X → ℂ) x = (rho x : ℂ) * U x at h1
    change (M (M U) : X → ℂ) x = (rho x : ℂ) * (M U) x at h2
    simp only [diagonal_formula b hb, Complex.ofReal_one, inv_one, one_mul, h2, h1]
    ring
  have hi : Integrable (fun x => haarKernel b 1 (M (M U)) R x x) nu := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      diagonal_integrable nu b hb 1 (M (M U)) R
  refine ⟨hi.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simpa only [ENNReal.ofReal_one, one_smul] using
    diagonal_integral nu b hb 1 (by norm_num) (M (M U)) R

end
end HNormalizedKernel

namespace DSourceKernel
open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The literal two-sided finite source diagonal is the trace of M E A M.
The proof preserves convolution/projection order and uses no commutation or
nuclear hypothesis about the unprojected convolution. -/
theorem finiteKernel_twosided_realMask_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (rho : X → ℝ) (hm : Measurable rho) (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) :
    let M := KPhysicalMask.realMaskCLM nu rho hm hbound
    Integrable (fun x => (rho x : ℂ) * finiteKernel nu b E A x x * (rho x : ℂ)) nu ∧
    (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x * (rho x : ℂ) ∂nu) =
      Masullo.TraceClass.trace (M.comp (E.starProjection.comp (A.comp M))) := by
  dsimp only
  let M := KPhysicalMask.realMaskCLM nu rho hm hbound
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have hr (i : Fin (Module.finrank ℂ E)) :=
    HNormalizedKernel.realMask_twosided_diagonal nu b hb rho hm hbound
      (e i) (A.adjoint (e i))
  have hp : E.starProjection = ∑ i, rankOne ℂ (e i) (e i) := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.sum_apply, rankOne_apply, e] using
      projection_expansion nu E v
  have hf : M.comp (E.starProjection.comp (A.comp M)) =
      ∑ i, rankOne ℂ (M (e i)) ((A.comp M).adjoint (e i)) := by
    rw [hp, HOperatorTrace.finite_projection_comp]
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      rankOne_apply, map_sum, map_smul]
  refine ⟨?_, ?_⟩
  · simp only [finiteKernel, Finset.mul_sum, Finset.sum_mul]
    exact integrable_finset_sum _ (fun i _ => (hr i).1)
  · change (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x * (rho x : ℂ) ∂nu) =
      Masullo.TraceClass.trace (M.comp (E.starProjection.comp (A.comp M)))
    rw [hf, HOperatorTrace.finite_rank_trace]
    simp only [finiteKernel, Finset.mul_sum, Finset.sum_mul]
    rw [integral_finset_sum _ (fun i _ => (hr i).1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hr i).2]
    simp only [adjoint_inner_left, ContinuousLinearMap.comp_apply, M]

end
end DSourceKernel

/- Append after HTwosidedDiagonal and the shared full-source/smooth-mask
definitions. This specializes every finite-frame, weight and mask hypothesis. -/
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

/-- The diagonal of D's actual two-sided physical source kernel, for both
required tests, has the trace of M E A M in the original Haar measure.
The residual diagonal is the negative of this source correction. -/
theorem both_tests_full_source_twosided_smooth_trace
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
    let rho := FSmoothCutoff.mask K L epsilon
    let M := KPhysicalMask.realMaskCLM mu (FSmoothCutoff.realMask K L epsilon)
      (FSmoothCutoff.realMask_continuous K L epsilon).measurable
      (FSmoothCutoff.realMask_bounds K L epsilon)
    ∀ T,
      Integrable (fun x => rho x * DSourceKernel.finiteKernel mu b (E T) A x x * rho x) mu ∧
      (∫ x, rho x * DSourceKernel.finiteKernel mu b (E T) A x x * rho x ∂mu) =
        Masullo.TraceClass.trace (M.comp ((E T).starProjection.comp (A.comp M))) ∧
      (∫ x, rho x * DSourceKernel.residualKernel mu b (E T) A
        (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) x x * rho x ∂mu) =
        -Masullo.TraceClass.trace (M.comp ((E T).starProjection.comp (A.comp M))) := by
  dsimp only
  intro T
  have h := DSourceKernel.finiteKernel_twosided_realMask_trace mu
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
  refine ⟨h.1, h.2, ?_⟩
  simp only [DSourceKernel.residualKernel, mul_inv_cancel,
    LIntegrated.requiredTest_at_one K phi hphi q, zero_sub, mul_neg, neg_mul, integral_neg]
  exact congrArg Neg.neg h.2

end
end HArithmeticTrace

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

/- Insert after NArithmeticUnfoldingFragment. The original quotient masks and
constructed indentation are reused; no new shell or measure is defined. -/
namespace NArithmeticUnfolding
open MeasureTheory MasulloGRH NDivisorialShells NumberField
open scoped ENNReal BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem ofReal_descendedMask_mk (v : ℕ → FinitePlace K) (e : Option ℕ)
    (x : HeckeIdeles K) :
    ENNReal.ofReal (descendedMask K v (arithmeticIndentation K) e (QuotientGroup.mk x)) =
      ∑' q : Kˣ, indentationDensity K (principalIdele K q * x) *
        ENNReal.ofReal (upstairsMask K v e (principalIdele K q * x)) := by
  have hp (q : Kˣ) : 0 ≤ arithmeticIndentation K (principalIdele K q*x) *
      upstairsMask K v e (principalIdele K q*x) :=
    mul_nonneg (arithmeticIndentation_nonneg K _) (upstairs_nonneg K v e _)
  have hs : Summable (fun q : Kˣ => arithmeticIndentation K (principalIdele K q*x) *
      upstairsMask K v e (principalIdele K q*x)) := by
    apply Summable.of_nonneg_of_le hp _ (arithmeticIndentation_hasSum K x).summable
    intro q
    apply mul_le_of_le_one_right (arithmeticIndentation_nonneg K _)
    unfold upstairsMask
    split <;> norm_num
  rw [descendedMask_mk, orbitMask, ENNReal.ofReal_tsum_of_nonneg hp hs]
  apply tsum_congr
  intro q
  exact ENNReal.ofReal_mul (arithmeticIndentation_nonneg K _)

variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

/-- The actual descended arithmetic shell integral equals the literal upstairs
shell with the same indentation. All arithmetic mask/normalization hypotheses
are discharged. Comparison with another original quotient Haar is M's measure
normalization application. -/
theorem lintegral_arithmetic_shell_unfold
    (lambda : Measure (HeckeIdeles K)) [lambda.IsMulLeftInvariant]
    (v : ℕ → FinitePlace K) (e : Option ℕ)
    (F : HeckeIdeleClasses K → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, ENNReal.ofReal (descendedMask K v (arithmeticIndentation K) e x) * F x
      ∂quotientMeasure K lambda) =
      ∫⁻ y, indentationDensity K y * ENNReal.ofReal (upstairsMask K v e y) *
        F (QuotientGroup.mk y) ∂lambda := by
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  have hqp (q : Kˣ) (x : HeckeIdeles K) :
      (QuotientGroup.mk (principalIdele K q*x) : HeckeIdeleClasses K) =
        QuotientGroup.mk x := by
    apply QuotientGroup.eq.mpr
    have hm : principalIdele K (q⁻¹) ∈ principalIdeles K := ⟨q⁻¹, rfl⟩
    have he : (principalIdele K q * x)⁻¹ * x = principalIdele K (q⁻¹) := by
      simp [mul_inv_rev, mul_comm]
    rw [he]
    exact hm
  let f := fun y : HeckeIdeles K => indentationDensity K y *
    ENNReal.ofReal (upstairsMask K v e y) * F (QuotientGroup.mk y)
  have hf : Measurable f :=
    ((indentationDensity_measurable K).mul
      (upstairsMask_continuous K v e).measurable.ennreal_ofReal).mul (hF.comp hq)
  rw [lintegral_quotientMeasure K lambda _
    (((arithmetic_positivePartition K v).measurable e).ennreal_ofReal.mul hF)]
  have ht := lintegral_arithmetic_unfold K lambda f hf
  simpa only [f, hqp, ENNReal.tsum_mul_right, ← ofReal_descendedMask_mk K v e] using ht

end
end NArithmeticUnfolding

/- Insert after NShellUnfoldingFragment. This measure equality makes the
literal arithmetic shell identity available to complex integration. -/
namespace NArithmeticUnfolding
open MeasureTheory MasulloGRH NDivisorialShells NumberField
open scoped ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]

/-- The same quotient shell measure is the pushforward of the corresponding
literal upstairs shell, with counting-normalized arithmetic indentation. -/
theorem arithmetic_shell_measure
    (lambda : Measure (HeckeIdeles K)) [lambda.IsMulLeftInvariant]
    (v : ℕ → FinitePlace K) (e : Option ℕ) :
    (quotientMeasure K lambda).withDensity
      (fun x => ENNReal.ofReal (descendedMask K v (arithmeticIndentation K) e x)) =
    (lambda.withDensity (fun y => indentationDensity K y *
      ENNReal.ofReal (upstairsMask K v e y))).map QuotientGroup.mk := by
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  have hp := ((arithmetic_positivePartition K v).measurable e).ennreal_ofReal
  have hu := (indentationDensity_measurable K).mul
    (upstairsMask_continuous K v e).measurable.ennreal_ofReal
  ext s hs
  let F : HeckeIdeleClasses K → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have he : (∫⁻ x, F x ∂(quotientMeasure K lambda).withDensity
      (fun x => ENNReal.ofReal (descendedMask K v (arithmeticIndentation K) e x))) =
      ∫⁻ x, F x ∂(lambda.withDensity (fun y => indentationDensity K y *
        ENNReal.ofReal (upstairsMask K v e y))).map QuotientGroup.mk := by
    rw [lintegral_withDensity_eq_lintegral_mul _ hp hF, lintegral_map hF hq]
    exact (lintegral_arithmetic_shell_unfold K lambda v e F hF).trans
      (lintegral_withDensity_eq_lintegral_mul lambda hu (hF.comp hq)).symm
  simpa only [F, lintegral_indicator hs, setLIntegral_one] using he

end
end NArithmeticUnfolding

/- Insert after MComplexQuotientFragment and NShellMeasureFragment.
Manuscript Corollary 12.2.1.2 and (12.2.1.6)--(12.2.1.8), applied to
N's actual shell measure and the same original Haar mu as the operator. -/
namespace MQuotientHaar
open MeasureTheory MasulloGRH NDivisorialShells NArithmeticUnfolding
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]
variable [SecondCountableTopology (HeckeAdeles K)]
attribute [local instance] quotientMeasure_finite_compacts quotientMeasure_leftInvariant

/-- The actual indentation section scales the L1 norm by the proved positive
Haar comparison scalar. This applies to arbitrary L1 representatives. -/
theorem integral_norm_originalHaar
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
    (F : HeckeIdeleClasses K → ℂ) (hF : Integrable F mu) :
    (∫ y, ‖(arithmeticIndentation K y : ℂ) * F (QuotientGroup.mk y)‖ ∂lambda) =
      ((quotientMeasure K lambda).haarScalarFactor mu : ℝ) * ∫ z, ‖F z‖ ∂mu := by
  have hs := (quotientMeasure_eq_scaled_originalHaar K lambda mu).2
  have hFq : Integrable F (quotientMeasure K lambda) := by
    rw [hs]
    exact hF.smul_measure_nnreal
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  let w : HeckeIdeles K → ℝ≥0 := fun y => Real.toNNReal (arithmeticIndentation K y)
  have hw : Measurable w := (arithmeticIndentation_continuous K).measurable.real_toNNReal
  have he (y : HeckeIdeles K) :
      ‖(arithmeticIndentation K y : ℂ) * F (QuotientGroup.mk y)‖ =
        w y • ‖F (QuotientGroup.mk y)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (arithmeticIndentation_nonneg K y)]
    change _ = (w y : ℝ) * _
    rw [show (w y : ℝ) = arithmeticIndentation K y from
      ENNReal.toReal_ofReal (arithmeticIndentation_nonneg K y)]
  calc
    _ = ∫ y, w y • ‖F (QuotientGroup.mk y)‖ ∂lambda :=
      integral_congr_ae (Filter.Eventually.of_forall he)
    _ = ∫ y, ‖F (QuotientGroup.mk y)‖
        ∂lambda.withDensity (fun y => (w y : ℝ≥0∞)) :=
      (integral_withDensity_eq_integral_smul hw _).symm
    _ = ∫ z, ‖F z‖ ∂quotientMeasure K lambda :=
      (integral_map hq.aemeasurable hFq.norm.aestronglyMeasurable).symm
    _ = ∫ z, ‖F z‖ ∂((quotientMeasure K lambda).haarScalarFactor mu • mu) :=
      congrArg (fun eta : Measure (HeckeIdeleClasses K) => ∫ z, ‖F z‖ ∂eta) hs
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

/-- Every original-mu integrable diagonal has an integrable literal upstairs
shell. No pointwise measurability or extra induced-measure admission is assumed. -/
theorem integrable_integral_originalHaar_shell
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
    (v : ℕ → NumberField.FinitePlace K) (e : Option ℕ)
    (F : HeckeIdeleClasses K → ℂ) (hF : Integrable F mu) :
    Integrable (fun y => (arithmeticIndentation K y : ℂ) *
      (upstairsMask K v e y : ℂ) * F (QuotientGroup.mk y)) lambda ∧
    (∫ y, (arithmeticIndentation K y : ℂ) * (upstairsMask K v e y : ℂ) *
      F (QuotientGroup.mk y) ∂lambda) =
      (((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ) *
        ∫ z, (descendedMask K v (arithmeticIndentation K) e z : ℂ) * F z ∂mu := by
  have hs := (quotientMeasure_eq_scaled_originalHaar K lambda mu).2
  have hFq : Integrable F (quotientMeasure K lambda) := by
    rw [hs]
    exact hF.smul_measure_nnreal
  have hq : Measurable (QuotientGroup.mk : HeckeIdeles K → HeckeIdeleClasses K) :=
    QuotientGroup.continuous_mk.measurable
  let p : HeckeIdeleClasses K → ℝ≥0 := fun z =>
    Real.toNNReal (descendedMask K v (arithmeticIndentation K) e z)
  let w : HeckeIdeles K → ℝ≥0 := fun y =>
    Real.toNNReal (arithmeticIndentation K y) * Real.toNNReal (upstairsMask K v e y)
  have hp : Measurable p :=
    ((arithmetic_positivePartition K v).measurable e).real_toNNReal
  have hw : Measurable w :=
    (arithmeticIndentation_continuous K).measurable.real_toNNReal.mul
      (upstairsMask_continuous K v e).measurable.real_toNNReal
  have hpe (z : HeckeIdeleClasses K) : p z • F z =
      (descendedMask K v (arithmeticIndentation K) e z : ℂ) * F z := by
    change ((p z : ℝ) : ℂ) * F z = _
    rw [show (p z : ℝ) = descendedMask K v (arithmeticIndentation K) e z from
      ENNReal.toReal_ofReal ((arithmetic_positivePartition K v).nonneg e z)]
  have hwe (y : HeckeIdeles K) : w y • F (QuotientGroup.mk y) =
      (arithmeticIndentation K y : ℂ) * (upstairsMask K v e y : ℂ) *
        F (QuotientGroup.mk y) := by
    change (((Real.toNNReal (arithmeticIndentation K y) *
      Real.toNNReal (upstairsMask K v e y) : ℝ≥0) : ℝ) : ℂ) * _ = _
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (arithmeticIndentation_nonneg K y),
      Real.coe_toNNReal _ (upstairs_nonneg K v e y), Complex.ofReal_mul]
  have hmap : (quotientMeasure K lambda).withDensity (fun z => (p z : ℝ≥0∞)) =
      (lambda.withDensity (fun y => (w y : ℝ≥0∞))).map QuotientGroup.mk := by
    simpa only [p, w, ENNReal.coe_mul, indentationDensity] using
      arithmetic_shell_measure K lambda v e
  have hFp : Integrable F
      ((quotientMeasure K lambda).withDensity (fun z => (p z : ℝ≥0∞))) :=
    (integrable_withDensity_iff_integrable_smul hp).2
      ((ReviewM.shell_integrable (quotientMeasure K lambda) _
        (arithmetic_positivePartition K v) F hFq e).congr
          (Filter.Eventually.of_forall (fun z => (hpe z).symm)))
  have hFm : Integrable F
      ((lambda.withDensity (fun y => (w y : ℝ≥0∞))).map QuotientGroup.mk) := by
    rw [← hmap]
    exact hFp
  have hFu := hFm.comp_aemeasurable hq.aemeasurable
  have hwi := (integrable_withDensity_iff_integrable_smul hw).1 hFu
  refine ⟨hwi.congr (Filter.Eventually.of_forall hwe), ?_⟩
  calc
    _ = ∫ y, w y • F (QuotientGroup.mk y) ∂lambda :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => (hwe y).symm))
    _ = ∫ y, F (QuotientGroup.mk y) ∂lambda.withDensity (fun y => (w y : ℝ≥0∞)) :=
      (integral_withDensity_eq_integral_smul hw _).symm
    _ = ∫ z, F z ∂(quotientMeasure K lambda).withDensity (fun z => (p z : ℝ≥0∞)) := by
      rw [hmap]
      exact (integral_map hq.aemeasurable hFm.aestronglyMeasurable).symm
    _ = ∫ z, p z • F z ∂quotientMeasure K lambda :=
      integral_withDensity_eq_integral_smul hp _
    _ = ∫ z, (descendedMask K v (arithmeticIndentation K) e z : ℂ) * F z
        ∂quotientMeasure K lambda :=
      integral_congr_ae (Filter.Eventually.of_forall hpe)
    _ = ∫ z, (descendedMask K v (arithmeticIndentation K) e z : ℂ) * F z
        ∂((quotientMeasure K lambda).haarScalarFactor mu • mu) :=
      congrArg (fun eta : Measure (HeckeIdeleClasses K) =>
        ∫ z, (descendedMask K v (arithmeticIndentation K) e z : ℂ) * F z ∂eta) hs
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

end
end MQuotientHaar

/- Insert after MOriginalHaarShellFragment, MOriginalHaarFragment and HSourceTrace.
The actual operator and all Lp rows remain on the original mu. -/
namespace NArithmeticUnfolding
open MeasureTheory MasulloGRH NDivisorialShells NumberField
open scoped ENNReal NNReal BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]
variable [SecondCountableTopology (HeckeAdeles K)]
attribute [local instance] MQuotientHaar.quotientMeasure_finite_compacts
  MQuotientHaar.quotientMeasure_leftInvariant

/-- The literal upstairs arithmetic shells of the actual finite-source
kernel reconstruct its trace on the SAME original Haar, with the proved
comparison scalar. No diagonal admission or shell normalization premise
remains in this application. -/
theorem finiteKernel_originalHaar_shell_trace
    (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
    (v : ℕ → FinitePlace K)
    (b : HeckeIdeleClasses K → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :
    let c := (quotientMeasure K lambda).haarScalarFactor mu
    let k := DSourceKernel.finiteKernel mu b E A
    let d := fun e y => (arithmeticIndentation K y : ℂ) *
      (upstairsMask K v e y : ℂ) * k (QuotientGroup.mk y) (QuotientGroup.mk y)
    0 < c ∧ (∀ e, Integrable (d e) lambda) ∧
    (∀ e, (∫ y, d e y ∂lambda) = ((c : ℝ) : ℂ) *
      ∫ x, (descendedMask K v (arithmeticIndentation K) e x : ℂ) * k x x ∂mu) ∧
    HasSum (fun e => ∫ y, d e y ∂lambda)
      (((c : ℝ) : ℂ) * Masullo.TraceClass.trace (E.starProjection.comp A)) := by
  dsimp only
  have hc := MQuotientHaar.quotientMeasure_eq_scaled_originalHaar K lambda mu
  have hd := (DSourceKernel.finiteKernel_diagonal mu b hb E A).1
  have hi := fun e => MQuotientHaar.integrable_integral_originalHaar_shell K lambda mu v e
    (fun x => DSourceKernel.finiteKernel mu b E A x x) hd
  refine ⟨hc.1, fun e => (hi e).1, fun e => (hi e).2, ?_⟩
  have ht := ReviewM.shell_reconstruction mu _ (arithmetic_positivePartition K v)
    (fun x => DSourceKernel.finiteKernel mu b E A x x) hd
  rw [DSourceKernel.finiteKernel_trace mu b hb E A] at ht
  simp_rw [(hi _).2]
  exact ht.mul_left _

end
end NArithmeticUnfolding

/- Insert after MOriginalHaarShellFragment, NCanonicalSignedShellFragment,
HSourceTrace, DResidualKernel and the common full-source definitions.
Manuscript (11.3.1.4), (12.2.1.6)--(12.2.1.8), on the actual operator rows. -/
namespace NArithmeticUnfolding
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry NumberField
open PIntervalConvolution JThetaAttachment OAllCharacterClosure NDivisorialShells
open scoped BigOperators ENNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableSpace (HeckeIdeles K)] [BorelSpace (HeckeIdeles K)]
variable [SecondCountableTopology (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (lambda : Measure (HeckeIdeles K)) [lambda.IsHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]
attribute [local instance] MQuotientHaar.quotientMeasure_finite_compacts
  MQuotientHaar.quotientMeasure_leftInvariant
local instance shell_originalHaar_sigmaFinite : SigmaFinite mu :=
  (CNormalization.originalHaar_kernel_requirements K mu).1

/-- Both actual sharp tests have the literal upstairs arithmetic shell
unfolding and signed-stratum trace identity. Every diagonal admission and
normalization application is proved on the same original-mu E_T A; the
residual kernel is A minus its finite source projection after convolution. -/
theorem both_tests_full_originalHaar_signed_shells
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → FinitePlace K) (q : Fin 2) :
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (LIntegrated.requiredTest K phi q) ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let c := (quotientMeasure K lambda).haarScalarFactor mu
    let d := fun T x => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) x x
    let u := fun T e y => (arithmeticIndentation K y : ℂ) *
      (upstairsMask K v e y : ℂ) * d T (QuotientGroup.mk y)
    0 < c ∧ ∀ T,
      (∀ e, Integrable (u T e) lambda ∧
        (∫ y, u T e y ∂lambda) = ((c : ℝ) : ℂ) *
          ∫ x, (descendedMask K v (arithmeticIndentation K) e x : ℂ) * d T x ∂mu) ∧
      HasSum (fun e => ∫ y, u T e y ∂lambda)
        (-(((c : ℝ) : ℂ) * Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      HasSum (fun n => ∫ y, (arithmeticIndentation K y : ℂ) *
          ((stratumMask K v (n+1) y - stratumMask K v n y : ℝ) : ℂ) *
            d T (QuotientGroup.mk y) ∂lambda)
        ((∫ y, u T none y ∂lambda) +
          ((c : ℝ) : ℂ) * Masullo.TraceClass.trace ((E T).starProjection.comp A)) := by
  dsimp only
  refine ⟨(MQuotientHaar.quotientMeasure_eq_scaled_originalHaar K lambda mu).1, ?_⟩
  intro T
  let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let E := DSourceKernel.sourceSpan mu
    (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) T
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  let d := fun x => DSourceKernel.residualKernel mu b E A
    (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) x x
  have hb : ∀ x, 0 < b x := fun x =>
    FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)
  have hd : Integrable d mu := by
    simpa only [d, DSourceKernel.residualKernel, mul_inv_cancel,
      LIntegrated.requiredTest_at_one K phi hphi q, zero_sub] using
      (DSourceKernel.finiteKernel_diagonal mu b hb E A).1.neg
  have he : (∫ x, d x ∂mu) = -Masullo.TraceClass.trace (E.starProjection.comp A) := by
    simp only [d, DSourceKernel.residualKernel, mul_inv_cancel,
      LIntegrated.requiredTest_at_one K phi hphi q, zero_sub, integral_neg]
    rw [DSourceKernel.finiteKernel_trace mu b hb E A]
  have hi := fun e => MQuotientHaar.integrable_integral_originalHaar_shell
    K lambda mu v e d hd
  refine ⟨hi, ?_, ?_⟩
  · have ht := ReviewM.shell_reconstruction mu _ (arithmetic_positivePartition K v) d hd
    rw [he] at ht
    change HasSum (fun e => ∫ y, (arithmeticIndentation K y : ℂ) *
      (upstairsMask K v e y : ℂ) * d (QuotientGroup.mk y) ∂lambda)
      (-((((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ) *
        Masullo.TraceClass.trace (E.starProjection.comp A)))
    simp_rw [(hi _).2]
    simpa only [mul_neg] using ht.mul_left
      (((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ)
  · have ht := (canonical_signed_shell_reconstruction K v mu d hd).1
    rw [he, sub_neg_eq_add] at ht
    have hn (n : ℕ) :
        (∫ y, (arithmeticIndentation K y : ℂ) *
          ((stratumMask K v (n+1) y - stratumMask K v n y : ℝ) : ℂ) *
            d (QuotientGroup.mk y) ∂lambda) =
          (((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ) *
            ∫ x, ((descendedStratumMask K v (arithmeticIndentation K) (n+1) x -
              descendedStratumMask K v (arithmeticIndentation K) n x : ℝ) : ℂ) *
                d x ∂mu := by
      simp only [stratumMask_step, descendedStratumMask_step, Complex.ofReal_neg,
        mul_neg, neg_mul, integral_neg]
      exact congrArg Neg.neg (hi (some n)).2
    change HasSum (fun n => ∫ y, (arithmeticIndentation K y : ℂ) *
      ((stratumMask K v (n+1) y - stratumMask K v n y : ℝ) : ℂ) *
        d (QuotientGroup.mk y) ∂lambda)
      ((∫ y, (arithmeticIndentation K y : ℂ) * (upstairsMask K v none y : ℂ) *
        d (QuotientGroup.mk y) ∂lambda) +
        (((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ) *
          Masullo.TraceClass.trace (E.starProjection.comp A))
    simp_rw [hn, (hi none).2]
    simpa only [mul_add] using ht.mul_left
      (((quotientMeasure K lambda).haarScalarFactor mu : ℝ) : ℂ)

end
end NArithmeticUnfolding
#check NArithmeticUnfolding.both_tests_full_originalHaar_signed_shells
#print axioms NArithmeticUnfolding.both_tests_full_originalHaar_signed_shells
