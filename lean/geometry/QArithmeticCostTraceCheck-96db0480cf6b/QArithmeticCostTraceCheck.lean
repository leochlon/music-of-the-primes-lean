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

-- Check context: inputs/exchange/H/HKernelFragment.lean
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


-- Check context: inputs/exchange/H/HTraceFragment.lean
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

-- Check context: inputs/exchange/D/DSourceKernelFragment.lean
/- Append after HNormalizedKernel and OSourceClosure.actual_source_family_exhaustion.
   The finite spans below are literally the common theta-source finite spans. -/
namespace DSourceKernel
open MeasureTheory Filter ContinuousLinearMap OSourceClosure
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

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def sourceSpan (nu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (T : Finset (Lp ℂ 2 nu)) : Submodule ℂ (Lp ℂ 2 nu) :=
  Submodule.span ℂ ((T : Set (Lp ℂ 2 nu)) ∩ Set.range Theta)

instance sourceSpan_finiteDim (nu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu) (T : Finset (Lp ℂ 2 nu)) :
    FiniteDimensional ℂ (sourceSpan nu e0 eF Theta T) :=
  FiniteDimensional.span_of_finite ℂ ((Finset.finite_toSet T).inter_of_left _)

/-- The kernels use the literal theta-source spans. Their residual operators
converge to the full source-complement projection AFTER A on every input.
This is a strong operator statement; it makes no trace-limit assertion. -/
theorem source_kernel_global_connection (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    let E := sourceSpan nu e0 eF Theta
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, finiteKernel nu b (E T) A x y *
        (F y / (b y : ℂ)) ∂nu)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - (sourceClosure e0 eF Theta).starProjection (A F))) := by
  dsimp only
  refine ⟨fun T => finiteKernel_action nu b hb _ A F, ?_⟩
  obtain ⟨p, hp, ht⟩ := actual_source_family_exhaustion e0 eF Theta A F
  have he (T) : p T = (sourceSpan nu e0 eF Theta T).starProjection (A F) := by
    obtain ⟨inst, h⟩ := hp T
    exact h
  simpa only [he] using ht

end
end DSourceKernel

-- Check context: QSourceCutoffFragment.lean
/- Append after the seed's OSourceClosure.actual_source_family_exhaustion.
   No arithmetic or source definitions from the seed are duplicated. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Dominated nuclear representation cost for any directed source flag. -/
theorem directed_source_nuclear_cost_limit
    {N : Type*} [Nonempty N] [SemilatticeSup N]
    (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (E : N → Submodule ℂ H) [∀ n, (E n).HasOrthogonalProjection]
    (hmono : Monotone E) (hES : ∀ n, E n ≤ S)
    (hdense : (S : Set H) ⊆ closure (⋃ n, (E n : Set H)))
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun n => ∑' j, ‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖)
      atTop (𝓝 0) := by
  have hb (n : N) (j : ℕ) : ‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖ ≤
      2 * (‖u j‖ * ‖v j‖) := by
    have hp : ‖(E n).starProjection (v j)-S.starProjection (v j)‖ ≤ 2*‖v j‖ :=
      (norm_sub_le _ _).trans (by linarith [(E n).norm_starProjection_apply_le (v j),
        S.norm_starProjection_apply_le (v j)])
    exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring)
  have ht (j : ℕ) : Tendsto
      (fun n => ‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖) atTop (𝓝 0) := by
    have hh := (Masullo.NestedProjection.global_projection_tendsto S E hmono hES hdense (v j)).sub
      (tendsto_const_nhds (x := S.starProjection (v j)))
    simpa using hh.norm.const_mul ‖u j‖
  have he : ∀ᶠ n in atTop, ∀ j,
      ‖‖u j‖ * ‖(E n).starProjection (v j)-S.starProjection (v j)‖‖ ≤
      2*(‖u j‖*‖v j‖) := by
    apply Eventually.of_forall
    intro n j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb n j
  simpa using tendsto_tsum_of_dominated_convergence (hc.mul_left 2) ht he

/-- The seed's finite spans, with a named projection instance. -/
def finiteSourceSpan (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H) : Submodule ℂ H :=
  Submodule.span ℂ ((T : Set H) ∩ Set.range Theta)

instance finiteSourceSpan_finiteDimensional (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H) :
    FiniteDimensional ℂ (finiteSourceSpan e0 eF Theta T) :=
  FiniteDimensional.span_of_finite ℂ
    (T.finite_toSet.subset (show (T : Set H) ∩ Set.range Theta ⊆ (T : Set H)
      from Set.inter_subset_left))

theorem theta_span_eq (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) :
    Submodule.span ℂ (Set.range Theta) = LinearMap.range Theta := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  · rintro _ ⟨f, rfl⟩
    exact Submodule.subset_span ⟨f, rfl⟩

theorem finiteSourceSpan_monotone (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) :
    Monotone (finiteSourceSpan e0 eF Theta) := by
  intro T U hTU
  apply Submodule.span_mono
  intro y hy
  exact ⟨hTU hy.1, hy.2⟩

theorem finiteSourceSpan_le (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H) :
    finiteSourceSpan e0 eF Theta T ≤ sourceClosure e0 eF Theta := by
  have h := (Submodule.span_mono (R := ℂ)
    (show (T : Set H) ∩ Set.range Theta ⊆ Set.range Theta from Set.inter_subset_right)).trans
      (Submodule.le_topologicalClosure (Submodule.span ℂ (Set.range Theta)))
  simpa only [theta_span_eq, sourceClosure, finiteSourceSpan] using h

theorem finiteSourceSpan_dense (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) :
    (sourceClosure e0 eF Theta : Set H) ⊆
      closure (⋃ T, (finiteSourceSpan e0 eF Theta T : Set H)) := by
  have h := closure_mono (Masullo.NestedProjection.span_subset_finite_union (Set.range Theta))
  simpa only [theta_span_eq, sourceClosure, finiteSourceSpan] using h

/-- Density is proved for the actual theta image; only the nuclear factor
summability remains an analytic input. No countable source basis is imposed. -/
theorem actual_theta_nuclear_cost_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j, ‖u j‖ *
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) atTop (𝓝 0) := by
  classical
  exact directed_source_nuclear_cost_limit (sourceClosure e0 eF Theta)
    (finiteSourceSpan e0 eF Theta) (finiteSourceSpan_monotone e0 eF Theta)
    (finiteSourceSpan_le e0 eF Theta) (finiteSourceSpan_dense e0 eF Theta) u v hc

/-- A factorization of the fixed-input-mask convolution is carried through
both genuine left projections. The sign is global minus finite spectral part. -/
theorem actual_theta_factor_residual (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) (x : H) :
    HasSum (fun j => ⟪u j, x⟫_ℂ •
      ((finiteSourceSpan e0 eF Theta T).starProjection (v j) -
       (sourceClosure e0 eF Theta).starProjection (v j)))
      (((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A) (M x) -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A) (M x)) := by
  have he := (hfactor x).map (finiteSourceSpan e0 eF Theta T).starProjection.toAddMonoidHom
    (finiteSourceSpan e0 eF Theta T).starProjection.continuous
  have hs := (hfactor x).map (sourceClosure e0 eF Theta).starProjection.toAddMonoidHom
    (sourceClosure e0 eF Theta).starProjection.continuous
  change HasSum (fun j => (finiteSourceSpan e0 eF Theta T).starProjection (⟪u j, x⟫_ℂ • v j))
    ((finiteSourceSpan e0 eF Theta T).starProjection (A (M x))) at he
  change HasSum (fun j => (sourceClosure e0 eF Theta).starProjection (⟪u j, x⟫_ℂ • v j))
    ((sourceClosure e0 eF Theta).starProjection (A (M x))) at hs
  simp only [map_smul] at he hs
  convert he.sub hs using 1
  · funext j
    exact smul_sub _ _ _
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    abel

/-- Scalar coefficient series for the projected nuclear representation.
The operator-trace / diagonal identification is a separate theorem. -/
theorem actual_theta_trace_series_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j,
      ⟪u j, v j - (finiteSourceSpan e0 eF Theta T).starProjection (v j)⟫_ℂ)
      atTop (𝓝 (∑' j, ⟪u j, v j - (sourceClosure e0 eF Theta).starProjection (v j)⟫_ℂ)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence (hc.mul_left 2)
  · intro j
    have hp := Masullo.NestedProjection.global_projection_tendsto
      (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
      (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
      (finiteSourceSpan_dense e0 eF Theta) (v j)
    exact tendsto_const_nhds.inner (tendsto_const_nhds.sub hp)
  · apply Eventually.of_forall
    intro T j
    have hp : ‖v j - (finiteSourceSpan e0 eF Theta T).starProjection (v j)‖ ≤ 2 * ‖v j‖ :=
      (norm_sub_le _ _).trans (by linarith [(finiteSourceSpan e0 eF Theta T).norm_starProjection_apply_le (v j)])
    exact (norm_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by ring))

end
end Q.IntegratedSourceCutoff

-- Check context: QKernelFactorFragment.lean
/- Append after DSourceKernel. The actual operator factorization remains explicit. -/
namespace DSourceKernel
open MeasureTheory Filter
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The diagonal of the actual finite projected kernel is the projected
coefficient series of any proved factorization of its completed operator.
This identifies the coefficient series, rather than merely naming it a trace. -/
theorem finiteKernel_factor_series (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hfactor : ∀ F, HasSum (fun j => ⟪u j, F⟫_ℂ • v j) (A F)) :
    HasSum (fun j => ⟪u j, E.starProjection (v j)⟫_ℂ)
      (∫ x, finiteKernel nu b E A x x ∂nu) := by
  classical
  rw [(finiteKernel_diagonal nu b hb E A).2]
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have hi (i : Fin (Module.finrank ℂ E)) :
      HasSum (fun j => ⟪u j, e i⟫_ℂ * ⟪e i, v j⟫_ℂ) ⟪e i, A (e i)⟫_ℂ := by
    have h := (innerSL ℂ (e i)).hasSum (hfactor (e i))
    simpa only [innerSL_apply_apply, inner_smul_right] using h
  have hs : HasSum (fun j => ∑ i, ⟪u j, e i⟫_ℂ * ⟪e i, v j⟫_ℂ)
      (∑ i, ⟪e i, A (e i)⟫_ℂ) := hasSum_sum (fun i _ => hi i)
  convert hs using 1
  funext j
  rw [projection_expansion]
  simp only [inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end
end DSourceKernel

-- Check context: QSourceDiagonalLimitFragment.lean
/- Append after QSourceCutoffFragment and QKernelFactorFragment.
   These are the exact D finite kernels and the same genuine source projections. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The source coefficient series converges under the original nuclear factor
cost; the finite source sets are the canonical directed theta exhaustion. -/
theorem actual_theta_source_series_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j,
      inner ℂ (u j) ((finiteSourceSpan e0 eF Theta T).starProjection (v j)))
      atTop (𝓝 (∑' j, inner ℂ (u j) ((sourceClosure e0 eF Theta).starProjection (v j)))) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hc
  · intro j
    exact tendsto_const_nhds.inner
      (Masullo.NestedProjection.global_projection_tendsto
        (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
        (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
        (finiteSourceSpan_dense e0 eF Theta) (v j))
  · apply Eventually.of_forall
    intro T j
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left
        ((finiteSourceSpan e0 eF Theta T).norm_starProjection_apply_le (v j))
        (norm_nonneg _))

end
end Q.IntegratedSourceCutoff

namespace DSourceKernel
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Original-Haar diagonal integrals of the actual finite theta-source kernels
converge to the source-projected factor series. The HasSum hypothesis is an
identity for the completed operator on every input, not merely theta inputs. -/
theorem sourceKernel_diagonal_series_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) =>
      ∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu)
      atTop (𝓝 (∑' j, inner ℂ (u j)
        ((sourceClosure e0 eF Theta).starProjection (v j)))) := by
  have he (T : Finset (Lp ℂ 2 nu)) :
      (∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu) =
        ∑' j, inner ℂ (u j)
          ((finiteSourceSpan e0 eF Theta T).starProjection (v j)) :=
    (finiteKernel_factor_series nu b hb (sourceSpan nu e0 eF Theta T) A u v hfactor).tsum_eq.symm
  simp_rw [he]
  exact actual_theta_source_series_limit e0 eF Theta u v hc

/-- The source limit keeps the free diagonal term and its sign. In the actual
localized convolution application `free` is its separately proved trace. -/
theorem sourceKernel_complement_diagonal_series_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F))
    (free : ℂ) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) =>
      free - ∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu)
      atTop (𝓝 (free - ∑' j, inner ℂ (u j)
        ((sourceClosure e0 eF Theta).starProjection (v j)))) :=
  tendsto_const_nhds.sub
    (sourceKernel_diagonal_series_limit nu b hb e0 eF Theta A u v hc hfactor)

end
end DSourceKernel

-- Check context: inputs/exchange/H/HNuclearSupportFragment.lean
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

-- Check context: inputs/exchange/H/HNuclearTraceFragment.lean
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

-- Check context: QSourceTraceLimitFragment.lean
/- Append after QSourceDiagonalLimitFragment and HNuclearTraceFragment.
   This bridges the source limit to H's actual Hilbert-basis operator trace. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Actual operator traces of the left complementary source approximants
converge. The factorization is on every input of A, and remains explicit. -/
theorem actual_theta_operator_trace_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Tendsto (fun T : Finset H => Masullo.TraceClass.trace
      (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A))
      atTop (𝓝 (Masullo.TraceClass.trace
        (((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A))) := by
  simp_rw [HOperatorTrace.nuclear_complement_trace _ A u v hc hfactor]
  exact actual_theta_trace_series_limit e0 eF Theta u v hc

/-- Source and complementary traces add to the original trace, with all three
basis sums identified by the same proved factorization. -/
theorem nuclear_source_trace_sub (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Masullo.TraceClass.trace A - Masullo.TraceClass.trace (S.starProjection.comp A) =
      Masullo.TraceClass.trace (((1 : H →L[ℂ] H) - S.starProjection).comp A) := by
  have h0 : Summable (fun j => inner ℂ (u j) (v j)) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le
      (fun j => norm_nonneg (inner ℂ (u j) (v j)))
      (fun j => norm_inner_le_norm (u j) (v j)) hc
  have hS : Summable (fun j => inner ℂ (u j) (S.starProjection (v j))) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hc
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (S.norm_starProjection_apply_le (v j)) (norm_nonneg _))
  rw [HOperatorTrace.nuclear_trace A u v hc hfactor,
    HOperatorTrace.nuclear_left_trace S.starProjection A u v hc hfactor,
    HOperatorTrace.nuclear_complement_trace S A u v hc hfactor]
  simp_rw [inner_sub_right]
  exact (h0.tsum_sub hS).symm

end
end Q.IntegratedSourceCutoff

namespace DSourceKernel
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The actual finite source-kernel diagonals converge to the genuine source
operator trace, in the unchanged original Haar measure. -/
theorem sourceKernel_diagonal_trace_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) =>
      ∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu)
      atTop (𝓝 (Masullo.TraceClass.trace ((sourceClosure e0 eF Theta).starProjection.comp A))) := by
  rw [HOperatorTrace.nuclear_left_trace _ A u v hc hfactor]
  exact sourceKernel_diagonal_series_limit nu b hb e0 eF Theta A u v hc hfactor

/-- The sign and free term required by the geometric calculation are retained.
For the application A is the constructed convolution with a fixed input mask. -/
theorem sourceKernel_free_minus_diagonal_trace_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ℕ → Lp ℂ 2 nu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) => Masullo.TraceClass.trace A -
      ∫ x, finiteKernel nu b (sourceSpan nu e0 eF Theta T) A x x ∂nu)
      atTop (𝓝 (Masullo.TraceClass.trace
        (((1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) -
          (sourceClosure e0 eF Theta).starProjection).comp A))) := by
  rw [← nuclear_source_trace_sub (sourceClosure e0 eF Theta) A u v hc hfactor]
  exact tendsto_const_nhds.sub
    (sourceKernel_diagonal_trace_limit nu b hb e0 eF Theta A u v hc hfactor)

end
end DSourceKernel

-- Check context: QRightTraceLimitFragment.lean
/- Append after QRightCutoffFragment, QSourceTraceLimitFragment, and HNuclearTraceFragment.
   This is the operator-trace version of the manuscript's RIGHT source cutoff.
   The complementary-input remainder is kept throughout. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Bounded right composition acts on the dual rows by the adjoint. -/
theorem nuclear_right_trace (C A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Masullo.TraceClass.trace (A.comp C) = ∑' j, inner ℂ (C.adjoint (u j)) (v j) := by
  have hcost : Summable (fun j => ‖C.adjoint (u j)‖ * ‖v j‖) := by
    apply Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      (hc.mul_left ‖C.adjoint‖)
    calc
      ‖C.adjoint (u j)‖ * ‖v j‖ ≤ (‖C.adjoint‖ * ‖u j‖) * ‖v j‖ :=
        mul_le_mul_of_nonneg_right (C.adjoint.le_opNorm (u j)) (norm_nonneg _)
      _ = ‖C.adjoint‖ * (‖u j‖ * ‖v j‖) := by ring
  apply HOperatorTrace.nuclear_trace (A.comp C) (fun j => C.adjoint (u j)) v hcost
  intro x
  simpa only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply]
    using hfactor (C x)

/-- Trace cyclicity is proved from the same full-input factorization; it does
not identify the two ordered operators. -/
theorem nuclear_bounded_trace_cyclic (C A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Masullo.TraceClass.trace (A.comp C) = Masullo.TraceClass.trace (C.comp A) := by
  rw [nuclear_right_trace C A u v hc hfactor,
    HOperatorTrace.nuclear_left_trace C A u v hc hfactor]
  simp only [ContinuousLinearMap.adjoint_inner_left]

/-- The right source cutoff has the genuine operator trace limit Tr(A S).
For the manuscript application A is the masked geometric operator M S A_h. -/
theorem right_source_operator_trace_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Tendsto (fun T : Finset H => Masullo.TraceClass.trace
      (A.comp (finiteSourceSpan e0 eF Theta T).starProjection))
      atTop (𝓝 (Masullo.TraceClass.trace (A.comp (sourceClosure e0 eF Theta).starProjection))) := by
  simp_rw [nuclear_bounded_trace_cyclic _ A u v hc hfactor,
    HOperatorTrace.nuclear_left_trace _ A u v hc hfactor]
  exact actual_theta_source_series_limit e0 eF Theta u v hc

/-- Compensated right condensation retains precisely A(1-S). This statement
does not drop the term using source invariance P A_h S=0. -/
theorem right_source_operator_trace_with_remainder (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Tendsto (fun T : Finset H => Masullo.TraceClass.trace
        (A.comp (finiteSourceSpan e0 eF Theta T).starProjection) +
      Masullo.TraceClass.trace
        (A.comp ((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection)))
      atTop (𝓝 (Masullo.TraceClass.trace A)) := by
  have he : Masullo.TraceClass.trace (A.comp (sourceClosure e0 eF Theta).starProjection) +
      Masullo.TraceClass.trace
        (A.comp ((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection)) =
      Masullo.TraceClass.trace A := by
    rw [nuclear_bounded_trace_cyclic _ A u v hc hfactor,
      nuclear_bounded_trace_cyclic _ A u v hc hfactor]
    have h := nuclear_source_trace_sub (sourceClosure e0 eF Theta) A u v hc hfactor
    linear_combination -h
  simpa only [he] using
    (right_source_operator_trace_limit e0 eF Theta A u v hc hfactor).add
      (tendsto_const_nhds (x := Masullo.TraceClass.trace
        (A.comp ((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection))))

end
end Q.IntegratedSourceCutoff

-- Check context: inputs/exchange/L/LTestBoundary.fragment.lean
/-! Append after the checked seed.  Reuses DReview.sharp, the actual quotient,
its logarithm, and the constructed interval convolution. -/
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

-- Check context: QFullSourceTraceFragment.lean
/- Insert after JAllCharacterSource, OAllCharacterClosure, QSourceTraceLimitFragment,
   and LIntegrated.requiredTest. No source, projection, or convolution is redefined. -/
namespace Q.FullSourceCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open JThetaAttachment OSourceClosure OAllCharacterClosure
open Q.IntegratedSourceCutoff PIntervalConvolution
open scoped Topology InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable (a alpha s : ℝ)

/-- The existing finite-source construction on the full admitted theta span. -/
abbrev fullFiniteSpan (T : Finset (Lp ℂ 2 mu)) : Submodule ℂ (Lp ℂ 2 mu) :=
  finiteSourceSpan (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu a alpha s) T

/-- Directed density is discharged on the common full arithmetic source.
Only the explicitly displayed representation cost is an analytic input. -/
theorem full_source_nuclear_cost_limit
    (u v : ℕ → Lp ℂ 2 mu) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => ∑' j, ‖u j‖ *
      ‖(fullFiniteSpan K addHaar mu a alpha s T).starProjection (v j) -
        (fullThetaClosure K addHaar mu a alpha s).starProjection (v j)‖) atTop (𝓝 0) := by
  have h := actual_theta_nuclear_cost_limit
    (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu a alpha s) u v hc
  rw [full_sourceProjection_eq] at h
  exact h

/-- The actual full-source finite kernels converge to the genuine source trace,
with the unaltered original measure and every completed input in hfactor. -/
theorem full_source_diagonal_trace_limit
    (b : HeckeIdeleClasses K → ℝ) (hb : ∀ x, 0 < b x)
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ℕ → Lp ℂ 2 mu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun T : Finset (Lp ℂ 2 mu) =>
      ∫ x, DSourceKernel.finiteKernel mu b (fullFiniteSpan K addHaar mu a alpha s T) A x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace
        ((fullThetaClosure K addHaar mu a alpha s).starProjection.comp A))) := by
  have h := DSourceKernel.sourceKernel_diagonal_trace_limit mu b hb
    (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu a alpha s) A u v hc hfactor
  rw [full_sourceProjection_eq] at h
  exact h

variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both literal sharp convolutions, followed by the genuine full-source
complement, with a fixed incoming physical multiplier M. The free trace is
retained until the localized convolution diagonal formula proves its value.
This theorem does not assert the analytic factor hypotheses for every M. -/
theorem both_tests_full_source_trace_limit
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (u v : Fin 2 → ℕ → Lp ℂ 2 mu)
    (hcost : ∀ q, Summable (fun j => ‖u q j‖ * ‖v q j‖))
    (hfactor : ∀ q F, HasSum (fun j => inner ℂ (u q j) F • v q j)
      (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2 (M F)))
    (q : Fin 2) :
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2
    let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => Masullo.TraceClass.trace (A.comp M) -
      ∫ x, DSourceKernel.finiteKernel mu b (E T) (A.comp M) x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace
        (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S).comp (A.comp M)))) := by
  let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  have h := DSourceKernel.sourceKernel_free_minus_diagonal_trace_limit mu
    (fun x => intervalHalfWeight l r s (classLog K x))
    (fun x => by
      change 0 < intervalHalfWeight l r s (classLog K x)
      rw [interval_halfWeight l r s (classLog K x) hlr]
      exact mul_pos (Real.exp_pos _) (Masullo.GenuineMellinJet.nativeHalfWeight_pos _ _ _))
    (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    (A.comp M) (u q) (v q) (hcost q) (hfactor q)
  rw [full_sourceProjection_eq] at h
  exact h

end
end Q.FullSourceCutoff

set_option pp.proofs false

-- Check context: inputs/exchange/K/KStrongPhysicalMask.lean
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

-- Check context: QPhysicalOperatorTraceFragment.lean
/- Insert after KStrongPhysicalMask, QSourceTraceLimit and QRightTraceLimit.
   Q owns this source/physical trace composition; K owns the proved multiplier.
   F/H retain ownership of the original-Haar physical diagonal integral. -/
namespace Q.IntegratedSourceCutoff
open MeasureTheory Filter OSourceClosure KPhysicalMask
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Physical multiplication is on the right of the actual nuclear operator.
Its trace convergence follows from the constructed mask and proved factor
trace cyclicity, without assuming equality of the two ordered operators. -/
theorem physical_mask_operator_trace_limit (mu : Measure X)
    (rho : ℕ → X → ℝ) (hm : ∀ n, Measurable (rho n))
    (hb : ∀ n x, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (hp : ∀ x, ∀ᶠ n in atTop, rho n x = 1)
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ℕ → Lp ℂ 2 mu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun n => Masullo.TraceClass.trace
      (A.comp (realMaskCLM mu (rho n) (hm n) (hb n))))
      atTop (𝓝 (Masullo.TraceClass.trace A)) := by
  simp_rw [nuclear_bounded_trace_cyclic _ A u v hc hfactor,
    HOperatorTrace.nuclear_left_trace _ A u v hc hfactor]
  rw [HOperatorTrace.nuclear_trace A u v hc hfactor]
  apply tendsto_tsum_of_dominated_convergence hc
  · intro j
    exact tendsto_const_nhds.inner (realMaskCLM_strong mu rho hm hb hp (v j))
  · apply Eventually.of_forall
    intro n j
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left
        (realMask_norm_le mu (rho n) (hm n) (hb n) (v j)) (norm_nonneg _))

/-- The source cutoff is taken at each fixed physical mask. The second
statement then removes that physical mask from PA. There is no exchange of
limits or uniform-in-mask source bound. Local AM and global PA factors are
distinct actual operator equations, retained explicitly in this theorem. -/
theorem source_then_physical_operator_trace_limits (mu : Measure X)
    (b : X → ℝ) (hb0 : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (rho : ℕ → X → ℝ) (hm : ∀ n, Measurable (rho n))
    (hb : ∀ n x, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (hp : ∀ x, ∀ᶠ n in atTop, rho n x = 1)
    (u v : ℕ → ℕ → Lp ℂ 2 mu)
    (hcost : ∀ n, Summable (fun j => ‖u n j‖ * ‖v n j‖))
    (hlocal : ∀ n F, HasSum (fun j => inner ℂ (u n j) F • v n j)
      (A (realMaskCLM mu (rho n) (hm n) (hb n) F)))
    (U W : ℕ → Lp ℂ 2 mu)
    (hglobalCost : Summable (fun j => ‖U j‖ * ‖W j‖))
    (hglobal : ∀ F, HasSum (fun j => inner ℂ (U j) F • W j)
      ((((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
        (sourceClosure e0 eF Theta).starProjection).comp A) F)) :
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - (sourceClosure e0 eF Theta).starProjection
    let M := fun n => realMaskCLM mu (rho n) (hm n) (hb n)
    (∀ n, Tendsto (fun T : Finset (Lp ℂ 2 mu) => Masullo.TraceClass.trace (A.comp (M n)) -
        ∫ x, DSourceKernel.finiteKernel mu b (DSourceKernel.sourceSpan mu e0 eF Theta T)
          (A.comp (M n)) x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace ((P.comp A).comp (M n))))) ∧
    Tendsto (fun n => Masullo.TraceClass.trace ((P.comp A).comp (M n)))
      atTop (𝓝 (Masullo.TraceClass.trace (P.comp A))) := by
  dsimp only
  constructor
  · intro n
    simpa only [ContinuousLinearMap.comp_assoc] using
      DSourceKernel.sourceKernel_free_minus_diagonal_trace_limit mu b hb0 e0 eF Theta
        (A.comp (realMaskCLM mu (rho n) (hm n) (hb n)))
        (u n) (v n) (hcost n) (hlocal n)
  · exact physical_mask_operator_trace_limit mu rho hm hb hp
      (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
        (sourceClosure e0 eF Theta).starProjection).comp A) U W hglobalCost hglobal

end
end Q.IntegratedSourceCutoff

set_option pp.proofs false


namespace FIntervalPhysical
open Filter
open scoped Topology
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


end FIntervalPhysical

/- Insert after QPhysicalOperatorTraceFragment, QFullSourceTraceFragment and
   FIntervalPhysical.plateau_eventually. Uses the common source and operators. -/
namespace Q.FullSourceCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open JThetaAttachment OAllCharacterClosure PIntervalConvolution KPhysicalMask
open Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both literal test families with the manuscript physical plateau and the
actual full-source projection. All geometric/mask application hypotheses are
proved; local AM and global PA nuclear factor applications remain explicit. -/
theorem both_tests_full_source_physical_trace_limits
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℝ) (hm : ∀ n, Measurable (rho n))
    (hb : ∀ n x, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (hp : ∀ n x, (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → rho n x = 1)
    (u v : ℕ → ℕ → Lp ℂ 2 mu)
    (hcost : ∀ n, Summable (fun j => ‖u n j‖ * ‖v n j‖))
    (hlocal : ∀ n F, HasSum (fun j => inner ℂ (u n j) F • v n j)
      (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2
        (realMaskCLM mu (rho n) (hm n) (hb n) F)))
    (U W : ℕ → Lp ℂ 2 mu)
    (hglobalCost : Summable (fun j => ‖U j‖ * ‖W j‖))
    (hglobal : ∀ F, HasSum (fun j => inner ℂ (U j) F • W j)
      ((((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
        (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection).comp
        (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
          (LIntegrated.requiredTest_compact K phi hh hc q).1
          (LIntegrated.requiredTest_compact K phi hh hc q).2)) F)) :
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let M := fun n => realMaskCLM mu (rho n) (hm n) (hb n)
    let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    (∀ n, Tendsto (fun T : Finset (Lp ℂ 2 mu) => Masullo.TraceClass.trace (A.comp (M n)) -
      ∫ x, DSourceKernel.finiteKernel mu b (E T) (A.comp (M n)) x x ∂mu)
        atTop (𝓝 (Masullo.TraceClass.trace ((P.comp A).comp (M n))))) ∧
    Tendsto (fun n => Masullo.TraceClass.trace ((P.comp A).comp (M n)))
      atTop (𝓝 (Masullo.TraceClass.trace (P.comp A))) := by
  have hpoint : ∀ x, ∀ᶠ n in atTop, rho n x = 1 := by
    intro x
    filter_upwards [FIntervalPhysical.plateau_eventually Lambda epsilon hLambda hprod
      (Real.exp (classLog K x)) (Real.exp_pos _)] with n hn
    exact hp n x hn.1 hn.2
  have h := source_then_physical_operator_trace_limits mu
    (fun x => intervalHalfWeight l r s (classLog K x))
    (fun x => by
      change 0 < intervalHalfWeight l r s (classLog K x)
      rw [interval_halfWeight l r s (classLog K x) hlr]
      exact mul_pos (Real.exp_pos _) (Masullo.GenuineMellinJet.nativeHalfWeight_pos _ _ _))
    (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    rho hm hb hpoint u v hcost hlocal U W hglobalCost
    (by rw [full_sourceProjection_eq]; exact hglobal)
  rw [full_sourceProjection_eq] at h
  exact h

end
end Q.FullSourceCutoff

set_option pp.proofs false

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


end
end FPhysicalFilter


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


/- Append after DSourceKernel and HOperatorTrace. -/
namespace DSourceKernel
open MeasureTheory ContinuousLinearMap InnerProductSpace Filter OSourceClosure
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
    simpa only [ContinuousLinearMap.sum_apply, rankOne_apply, e] using
      projection_expansion nu E v
  rw [he, HOperatorTrace.finite_projection_comp]
  simpa only [finiteKernel, e, ENNReal.ofReal_one, one_smul] using
    HOperatorTrace.finite_kernel_trace nu b hb 1 (by norm_num) e
      (fun i => A.adjoint (e i))

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

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Full-input finite kernel action, genuine finite operator trace, and the
proved strong connection to the global source-complement operator, together.
No claim of trace convergence is inferred from the strong limit. -/
theorem source_kernel_trace_global_connection (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    let E := sourceSpan nu e0 eF Theta
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, finiteKernel nu b (E T) A x y *
        (F y / (b y : ℂ)) ∂nu)) ∧
    (∀ T, Integrable (fun x => finiteKernel nu b (E T) A x x) nu ∧
      (∫ x, finiteKernel nu b (E T) A x x ∂nu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - (sourceClosure e0 eF Theta).starProjection (A F))) := by
  dsimp only
  have hd := source_kernel_global_connection nu b hb e0 eF Theta A F
  exact ⟨hd.1, fun T => ⟨(finiteKernel_diagonal nu b hb _ A).1,
    finiteKernel_trace nu b hb _ A⟩, hd.2⟩
end
end DSourceKernel


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


noncomputable section
namespace KPhysicalMask
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment OAllCharacterClosure LIntegrated
open FPhysicalFilter
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- F's explicit smooth radial family acting on the common original-Haar L2. -/
def smoothMaskCLM (mu : Measure (HeckeIdeleClasses K)) (L e : ℝ) :
    Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  realMaskCLM mu (FSmoothCutoff.realMask K L e)
    (FSmoothCutoff.realMask_continuous K L e).measurable
    (FSmoothCutoff.realMask_bounds K L e)


end KPhysicalMask
end


/- Insert after QPhysicalOperatorTraceFragment. This preserves the genuine
   independent cutoff regime rather than choosing one physical sequence. -/
namespace Q.IntegratedSourceCutoff
open MeasureTheory Filter KPhysicalMask
open scoped Topology InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

theorem physical_mask_operator_trace_filter {ι : Type*} (f : Filter ι)
    [f.IsCountablyGenerated] (mu : Measure X)
    (rho : ι → X → ℝ) (hm : ∀ i, Measurable (rho i))
    (hb : ∀ i x, 0 ≤ rho i x ∧ rho i x ≤ 1)
    (hp : ∀ x, ∀ᶠ i in f, rho i x = 1)
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ℕ → Lp ℂ 2 mu)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j) (A F)) :
    Tendsto (fun i => Masullo.TraceClass.trace
      (A.comp (realMaskCLM mu (rho i) (hm i) (hb i)))) f
      (𝓝 (Masullo.TraceClass.trace A)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro z hz
  exact physical_mask_operator_trace_limit mu (fun n => rho (z n))
    (fun n => hm (z n)) (fun n => hb (z n)) (fun x => hz.eventually (hp x))
    A u v hc hfactor

end
end Q.IntegratedSourceCutoff


/- Insert after QPhysicalNetTrace, HMaskedDiagonal, FSmoothRadial,
   KConcretePhysical.smoothMaskCLM, and QFullSourceTrace.
   H owns the finite masked identity; Q owns the iterated trace passage. -/
namespace Q.FullSourceCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open JThetaAttachment OAllCharacterClosure PIntervalConvolution KPhysicalMask
open scoped Topology InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Source exhaustion of the literal smoothly masked original-Haar diagonal,
followed by the independent physical trace net. All cutoff data, source
projection transport and finite diagonal/trace attachments are proved.
Local AM and global PA factor-cost applications remain explicit. -/
theorem both_tests_concrete_masked_trace_limits
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (u v : (ℝ × ℝ) → ℕ → Lp ℂ 2 mu)
    (hcost : ∀ p, FPhysicalFilter.ValidCutoff p.1 (p.2/p.1) →
      Summable (fun j => ‖u p j‖ * ‖v p j‖))
    (hlocal : ∀ p, FPhysicalFilter.ValidCutoff p.1 (p.2/p.1) →
      ∀ F, HasSum (fun j => inner ℂ (u p j) F • v p j)
        (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
          (LIntegrated.requiredTest_compact K phi hh hc q).1
          (LIntegrated.requiredTest_compact K phi hh hc q).2
          (smoothMaskCLM K mu p.1 (p.2/p.1) F)))
    (U W : ℕ → Lp ℂ 2 mu)
    (hglobalCost : Summable (fun j => ‖U j‖ * ‖W j‖))
    (hglobal : ∀ F, HasSum (fun j => inner ℂ (U j) F • W j)
      ((((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-
        (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection).comp
        (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
          (LIntegrated.requiredTest_compact K phi hh hc q).1
          (LIntegrated.requiredTest_compact K phi hh hc q).2)) F)) :
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2
    let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-
      (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let M := fun p : ℝ × ℝ => smoothMaskCLM K mu p.1 (p.2/p.1)
    (∀ p T, Integrable (fun x => FSmoothCutoff.mask K p.1 (p.2/p.1) x *
      DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, FSmoothCutoff.mask K p.1 (p.2/p.1) x *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
          Masullo.TraceClass.trace ((E T).starProjection.comp (A.comp (M p)))) ∧
    (∀ p, FPhysicalFilter.ValidCutoff p.1 (p.2/p.1) →
      Tendsto (fun T : Finset (Lp ℂ 2 mu) => Masullo.TraceClass.trace (A.comp (M p)) -
        ∫ x, FSmoothCutoff.mask K p.1 (p.2/p.1) x *
          DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        atTop (𝓝 (Masullo.TraceClass.trace ((P.comp A).comp (M p))))) ∧
    Tendsto (fun p : ℝ × ℝ => Masullo.TraceClass.trace ((P.comp A).comp (M p)))
      FPhysicalFilter.cutoffRegime (𝓝 (Masullo.TraceClass.trace (P.comp A))) := by
  let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-
    (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  let M := fun p : ℝ × ℝ => smoothMaskCLM K mu p.1 (p.2/p.1)
  have hb : ∀ x, 0 < b x := by
    intro x
    unfold b intervalHalfWeight
    positivity
  have hd (p : ℝ × ℝ) (T : Finset (Lp ℂ 2 mu)) :=
    DSourceKernel.finiteKernel_realMask_trace mu b hb (E T) A
      (FSmoothCutoff.realMask K p.1 (p.2/p.1))
      (FSmoothCutoff.realMask_continuous K p.1 (p.2/p.1)).measurable
      (FSmoothCutoff.realMask_bounds K p.1 (p.2/p.1))
  refine ⟨fun p T => ⟨(hd p T).1, (hd p T).2.2⟩, ?_, ?_⟩
  · intro p hp
    have ht := DSourceKernel.sourceKernel_free_minus_diagonal_trace_limit mu b hb
      (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
      (A.comp (M p)) (u p) (v p) (hcost p hp) (hlocal p hp)
    rw [full_sourceProjection_eq] at ht
    have he (T : Finset (Lp ℂ 2 mu)) :
        (∫ x, FSmoothCutoff.mask K p.1 (p.2/p.1) x *
          DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
          ∫ x, DSourceKernel.finiteKernel mu b (E T) (A.comp (M p)) x x ∂mu :=
      (hd p T).2.1
    change Tendsto (fun T : Finset (Lp ℂ 2 mu) =>
      Masullo.TraceClass.trace (A.comp (M p)) -
        ∫ x, FSmoothCutoff.mask K p.1 (p.2/p.1) x *
          DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace ((P.comp A).comp (M p))))
    simp_rw [he]
    simpa only [ContinuousLinearMap.comp_assoc] using ht
  · apply Q.IntegratedSourceCutoff.physical_mask_operator_trace_filter
      FPhysicalFilter.cutoffRegime mu
      (fun p : ℝ × ℝ => FSmoothCutoff.realMask K p.1 (p.2/p.1))
      (fun p => (FSmoothCutoff.realMask_continuous K p.1 (p.2/p.1)).measurable)
      (fun p => FSmoothCutoff.realMask_bounds K p.1 (p.2/p.1)) _
      (P.comp A) U W hglobalCost hglobal
    intro x
    simpa only [FSmoothCutoff.mask, Complex.ofReal_eq_one] using
      FSmoothCutoff.mask_eventually_one K x

end
end Q.FullSourceCutoff

/- Shared definitions copied from Masullo/Nuclear/TraceExhaustion.lean,
   HasNuclearCost and nuclearNorm only. Insert once; no new trace definition. -/
noncomputable section
namespace Masullo.NuclearFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}

def HasNuclearCost (T : E →L[ℂ] E) (C : ℝ) : Prop :=
  ∃ (v : ι → E) (f : ι → E →L[ℂ] ℂ),
    (∀ x, HasSum (fun i => f i x • v i) (T x)) ∧
    Summable (fun i => ‖f i‖ * ‖v i‖) ∧
    (∑' i, ‖f i‖ * ‖v i‖) ≤ C

end Masullo.NuclearFactorization
namespace Masullo.NuclearFactorization
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The repository's norm from absolutely summable rank-one representations. -/
def nuclearNorm (T : H →L[ℂ] H) : ENNReal :=
  sInf {c | ∃ (κ : Type u) (C : ℝ), HasNuclearCost (ι := κ) T C ∧
    c = ENNReal.ofReal C}

theorem nuclearNorm_le_of_cost {κ : Type u} {T : H →L[ℂ] H} {C : ℝ}
    (h : HasNuclearCost (ι := κ) T C) : nuclearNorm T ≤ ENNReal.ofReal C := by
  exact sInf_le ⟨κ, C, h, rfl⟩

end Masullo.NuclearFactorization
end

/- Insert after QSourceCutoffFragment, E SourceResidualFragment, and
   QNuclearNormDefinitionsFragment. Uses exactly the existing source spans. -/
namespace Q.NuclearSourceCutoff
open Filter OSourceClosure Q.IntegratedSourceCutoff Masullo.NuclearFactorization
open scoped Topology InnerProductSpace
noncomputable section
universe w
variable {H κ : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The canonical theta-source cost works with the actual factor index,
including a Hilbert basis or a character-dependent sigma index. -/
theorem source_cost_tendsto (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : κ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j, ‖u j‖ *
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) atTop (𝓝 0) := by
  classical
  have hz : (∑' j : κ, (0 : ℝ)) = 0 := by simp
  rw [← hz]
  apply tendsto_tsum_of_dominated_convergence hc
  · intro j
    have hh := (Masullo.NestedProjection.global_projection_tendsto
      (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
      (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
      (finiteSourceSpan_dense e0 eF Theta) (v j)).sub
      (tendsto_const_nhds (x := (sourceClosure e0 eF Theta).starProjection (v j)))
    simpa using hh.norm.const_mul ‖u j‖
  · apply Eventually.of_forall
    intro T j
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (ESourceResidual.nested_source_residual_contraction
        (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta T)
        (finiteSourceSpan_le e0 eF Theta T) (v j)) (norm_nonneg _)

/-- Explicit rank-one cost of global PA M minus the finite-source PA M.
The factor application concerns the actual A M on every completed input. -/
theorem source_residual_hasNuclearCost (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x)))
    (T : Finset H) :
    HasNuclearCost (ι := κ)
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M)
      (∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) := by
  refine ⟨fun j => (finiteSourceSpan e0 eF Theta T).starProjection (v j) -
      (sourceClosure e0 eF Theta).starProjection (v j),
    fun j => innerSL ℂ (u j), ?_, ?_, ?_⟩
  · intro x
    have hh := ((finiteSourceSpan e0 eF Theta T).starProjection -
      (sourceClosure e0 eF Theta).starProjection).hasSum (hfactor x)
    convert hh using 1
    · funext j
      simp only [innerSL_apply_apply, ContinuousLinearMap.sub_apply, map_smul, smul_sub]
    · simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.one_apply]
      abel
  · simp only [innerSL_apply_norm]
    exact Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => mul_le_mul_of_nonneg_left
        (ESourceResidual.nested_source_residual_contraction
          (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta T)
          (finiteSourceSpan_le e0 eF Theta T) (v j)) (norm_nonneg _)) hc
  · simp only [innerSL_apply_norm, le_refl]

theorem source_residual_nuclearNorm_bound (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x)))
    (T : Finset H) :
    nuclearNorm
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M) ≤
      ENNReal.ofReal (∑' j, ‖u j‖ *
        ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
          (sourceClosure e0 eF Theta).starProjection (v j)‖) :=
  nuclearNorm_le_of_cost (source_residual_hasNuclearCost e0 eF Theta A M u v hc hfactor T)

/-- Source exhaustion in the repository's nuclear norm, with the actual
operator difference and convolution-first order. -/
theorem source_residual_nuclearNorm_tendsto (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A (M x))) :
    Tendsto (fun T : Finset H => nuclearNorm
      ((((1 : H →L[ℂ] H) - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
        (((1 : H →L[ℂ] H) - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M))
      atTop (𝓝 0) := by
  have hcost := source_cost_tendsto e0 eF Theta u v hc
  have hbound := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hcost
  simp only [ENNReal.ofReal_zero] at hbound
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ => zero_le _) (source_residual_nuclearNorm_bound e0 eF Theta A M u v hc hfactor)

end
end Q.NuclearSourceCutoff

/- Insert after QNuclearSourceCutoffFragment and QFullSourceTraceFragment.
   Applies the common source projection, actual convolution, and both tests. -/
namespace Q.FullSourceCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open JThetaAttachment OAllCharacterClosure PIntervalConvolution
open Masullo.NuclearFactorization
open scoped Topology InnerProductSpace
noncomputable section
universe w
variable (K : Type w) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- The common full-source theta exhaustion in nuclear norm for each literal
sharp test. The original measure and interval midpoint are retained. Only
the independent localized-convolution factor construction is an input. -/
theorem both_tests_full_source_nuclearNorm_tendsto {κ : Type w}
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (u v : κ → Lp ℂ 2 mu)
    (hcost : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j)
      (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2 (M F))) :
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2
    let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => nuclearNorm
      ((P.comp A).comp M -
        (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-(E T).starProjection).comp A).comp M))
      atTop (𝓝 0) := by
  have h := Q.NuclearSourceCutoff.source_residual_nuclearNorm_tendsto
    (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    M u v hcost hfactor
  rw [full_sourceProjection_eq] at h
  exact h

end
end Q.FullSourceCutoff

/- Insert after QNuclearSourceCutoff, HNuclearTrace and HMaskedDiagonal.
   C.3.5.5(2)-(3) / G32 (32.4): consume the repository's actual functional
   nuclear-cost interface without choosing a countable factor enumeration. -/
namespace Q.NuclearCostTrace
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open Masullo.NuclearFactorization
open scoped Topology InnerProductSpace
noncomputable section
universe w
variable {H κ : Type w} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Riesz conversion preserves the exact full-input expansion and cost.
This consumes a proved cost; it does not construct arithmetic nuclearity. -/
theorem vector_factors_of_cost {A : H →L[ℂ] H} {C : ℝ}
    (hA : HasNuclearCost (ι := κ) A C) :
    ∃ u v : κ → H,
      (∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) ∧
      Summable (fun j => ‖u j‖ * ‖v j‖) ∧
      (∑' j, ‖u j‖ * ‖v j‖) ≤ C := by
  rcases hA with ⟨v, f, hf, hc, hC⟩
  let u : κ → H := fun j => (InnerProductSpace.toDual ℂ H).symm (f j)
  have hu (j : κ) : ‖u j‖ = ‖f j‖ :=
    (InnerProductSpace.toDual ℂ H).symm.norm_map (f j)
  refine ⟨u, v, ?_, ?_, ?_⟩
  · intro x
    simpa only [u, InnerProductSpace.toDual_symm_apply] using hf x
  · simpa only [hu] using hc
  · simpa only [hu] using hC

/-- The actual basis trace is bounded by each supplied nuclear cost. -/
theorem trace_norm_le_cost {A : H →L[ℂ] H} {C : ℝ}
    (hA : HasNuclearCost (ι := κ) A C) :
    ‖Masullo.TraceClass.trace A‖ ≤ C := by
  rcases vector_factors_of_cost hA with ⟨u, v, hf, hc, hC⟩
  rw [HOperatorTrace.nuclear_trace A u v hc hf]
  have hi : Summable (fun j => inner ℂ (u j) (v j)) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun j : κ => norm_nonneg _)
      (fun j : κ => norm_inner_le_norm _ _) hc
  exact (hi.hasSum.norm_le_of_bounded hc.hasSum
    (fun j => norm_inner_le_norm _ _)).trans hC

/-- C.3.5.5 uses precisely this domination by the repository's nuclear norm. -/
theorem trace_norm_le_nuclearNorm (A : H →L[ℂ] H) :
    ENNReal.ofReal ‖Masullo.TraceClass.trace A‖ ≤ nuclearNorm A := by
  apply le_sInf
  rintro c ⟨ι, C, hC, rfl⟩
  exact ENNReal.ofReal_le_ofReal (trace_norm_le_cost hC)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The scalar source trace error has the SAME constant-one residual cost
as the actual ordered operator difference, for its actual factor index. -/
theorem source_trace_error_le (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hf : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x))
    (T : Finset H) :
    ‖Masullo.TraceClass.trace ((finiteSourceSpan e0 eF Theta T).starProjection.comp A) -
      Masullo.TraceClass.trace ((sourceClosure e0 eF Theta).starProjection.comp A)‖ ≤
      ∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ := by
  let E := finiteSourceSpan e0 eF Theta T
  let S := sourceClosure e0 eF Theta
  have hcost : Summable (fun j => ‖u j‖ * ‖E.starProjection (v j) -
      S.starProjection (v j)‖) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) hc
    exact mul_le_mul_of_nonneg_left
      (ESourceResidual.nested_source_residual_contraction S E
        (finiteSourceSpan_le e0 eF Theta T) (v j)) (norm_nonneg _)
  have hproj (W : Submodule ℂ H) [W.HasOrthogonalProjection] :
      Summable (fun j => inner ℂ (u j) (W.starProjection (v j))) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun j : κ => norm_nonneg _) (fun j => ?_) hc
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (W.norm_starProjection_apply_le _) (norm_nonneg _))
  rw [HOperatorTrace.nuclear_left_trace _ A u v hc hf,
    HOperatorTrace.nuclear_left_trace _ A u v hc hf]
  apply ((hproj E).hasSum.sub (hproj S).hasSum).norm_le_of_bounded hcost.hasSum
  intro j
  rw [← inner_sub_right]
  exact norm_inner_le_norm _ _

theorem source_trace_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hf : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Tendsto (fun T : Finset H => Masullo.TraceClass.trace
      ((finiteSourceSpan e0 eF Theta T).starProjection.comp A)) atTop
      (𝓝 (Masullo.TraceClass.trace ((sourceClosure e0 eF Theta).starProjection.comp A))) := by
  simp_rw [HOperatorTrace.nuclear_left_trace _ A u v hc hf]
  apply tendsto_tsum_of_dominated_convergence hc
  · intro j
    exact tendsto_const_nhds.inner
      (Masullo.NestedProjection.global_projection_tendsto
        (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
        (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
        (finiteSourceSpan_dense e0 eF Theta) (v j))
  · apply Eventually.of_forall
    intro T j
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left
        ((finiteSourceSpan e0 eF Theta T).norm_starProjection_apply_le _) (norm_nonneg _))

theorem source_trace_sub (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hf : ∀ x, HasSum (fun j => inner ℂ (u j) x • v j) (A x)) :
    Masullo.TraceClass.trace A - Masullo.TraceClass.trace (S.starProjection.comp A) =
      Masullo.TraceClass.trace (((1 : H →L[ℂ] H)-S.starProjection).comp A) := by
  have h0 : Summable (fun j => inner ℂ (u j) (v j)) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun j : κ => norm_nonneg _)
      (fun j : κ => norm_inner_le_norm _ _) hc
  have hS : Summable (fun j => inner ℂ (u j) (S.starProjection (v j))) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun j : κ => norm_nonneg _) (fun j => ?_) hc
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (S.norm_starProjection_apply_le _) (norm_nonneg _))
  rw [HOperatorTrace.nuclear_trace A u v hc hf,
    HOperatorTrace.nuclear_left_trace S.starProjection A u v hc hf,
    HOperatorTrace.nuclear_complement_trace S A u v hc hf]
  simp_rw [inner_sub_right]
  exact (h0.tsum_sub hS).symm

variable {X : Type w} [MeasurableSpace X]

/-- Direct application of a functional cost to the literal original-measure
masked finite kernel, retaining the free trace and the convolution-first order. -/
theorem masked_source_trace_limit_of_cost (mu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (rho : X → ℝ) (hm : Measurable rho)
    (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (C : ℝ)
    (hA : HasNuclearCost (ι := κ)
      (A.comp (KPhysicalMask.realMaskCLM mu rho hm hbound)) C) :
    let M := KPhysicalMask.realMaskCLM mu rho hm hbound
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-
      (sourceClosure e0 eF Theta).starProjection
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => Masullo.TraceClass.trace (A.comp M) -
      ∫ x, (rho x : ℂ) * DSourceKernel.finiteKernel mu b
        (finiteSourceSpan e0 eF Theta T) A x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace ((P.comp A).comp M))) := by
  dsimp only
  rcases vector_factors_of_cost hA with ⟨u, v, hf, hc, _⟩
  have he (T : Finset (Lp ℂ 2 mu)) :=
    (DSourceKernel.finiteKernel_realMask_trace mu b hb
      (finiteSourceSpan e0 eF Theta T) A rho hm hbound).2.2
  simp_rw [he]
  have ht := (tendsto_const_nhds (x := Masullo.TraceClass.trace
    (A.comp (KPhysicalMask.realMaskCLM mu rho hm hbound)))).sub (source_trace_limit e0 eF Theta
    (A.comp (KPhysicalMask.realMaskCLM mu rho hm hbound)) u v hc hf)
  rw [source_trace_sub _ _ u v hc hf] at ht
  simpa only [ContinuousLinearMap.comp_assoc] using ht

end
end Q.NuclearCostTrace

/- Insert after QCostTraceFragment and QArithmeticNuclearCutoffFragment.
   The source/diagonal/nuclear cutoff applications use exactly the common
   original Haar, full theta closure, interval weight and literal smooth mask.
   The actual localized-convolution nuclear cost remains an explicit input. -/
namespace Q.FullSourceCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open JThetaAttachment OAllCharacterClosure PIntervalConvolution KPhysicalMask
open Masullo.NuclearFactorization Q.NuclearCostTrace
open scoped Topology InnerProductSpace
noncomputable section
universe w
variable (K : Type w) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both G32 fixed-mask source passages consume the repository's native
functional cost directly. The actual source closure, mask, full-input action
and measured finite diagonal are applied, rather than new application premises. -/
theorem both_tests_smooth_source_trace_of_cost {κ : Type w}
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (Lambda epsilon C : ℝ)
    (hlocal : HasNuclearCost (ι := κ)
      ((intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2).comp
          (smoothMaskCLM K mu Lambda epsilon)) C) :
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2
    let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-
      (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let M := smoothMaskCLM K mu Lambda epsilon
    (∀ T, Integrable (fun x => FSmoothCutoff.mask K Lambda epsilon x *
      DSourceKernel.finiteKernel mu b (E T) A x x) mu) ∧
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => nuclearNorm
      ((P.comp A).comp M -
        (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-(E T).starProjection).comp A).comp M))
      atTop (𝓝 0) ∧
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => Masullo.TraceClass.trace (A.comp M) -
      ∫ x, FSmoothCutoff.mask K Lambda epsilon x *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
      atTop (𝓝 (Masullo.TraceClass.trace ((P.comp A).comp M))) := by
  let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let E := fullFiniteSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  let M := smoothMaskCLM K mu Lambda epsilon
  have hb : ∀ x, 0 < b x := by
    intro x
    unfold b intervalHalfWeight
    positivity
  rcases vector_factors_of_cost hlocal with ⟨u, v, hf, hcost, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro T
    exact (DSourceKernel.finiteKernel_realMask_trace mu b hb (E T) A
      (FSmoothCutoff.realMask K Lambda epsilon)
      (FSmoothCutoff.realMask_continuous K Lambda epsilon).measurable
      (FSmoothCutoff.realMask_bounds K Lambda epsilon)).1
  · exact both_tests_full_source_nuclearNorm_tendsto K addHaar mu a l r s hlr hs
      phi hh hc q M u v hcost hf
  · have ht := masked_source_trace_limit_of_cost mu b hb
      (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) A
      (FSmoothCutoff.realMask K Lambda epsilon)
      (FSmoothCutoff.realMask_continuous K Lambda epsilon).measurable
      (FSmoothCutoff.realMask_bounds K Lambda epsilon) C hlocal
    rw [full_sourceProjection_eq] at ht
    exact ht

end
end Q.FullSourceCutoff
#check Q.FullSourceCutoff.both_tests_smooth_source_trace_of_cost
#print axioms Q.FullSourceCutoff.both_tests_smooth_source_trace_of_cost
#print axioms Q.NuclearCostTrace.source_trace_error_le
#print axioms Q.NuclearCostTrace.trace_norm_le_nuclearNorm
