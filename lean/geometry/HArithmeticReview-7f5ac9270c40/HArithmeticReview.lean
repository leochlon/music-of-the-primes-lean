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

#print axioms nativeHalfWeight_add_le
#print axioms actual_halfWeight_continuous
#print axioms actual_weighted_translation_memLp
#print axioms actual_weighted_translation_eLpNorm
#print axioms actual_weighted_translation_norm
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

#print axioms nativeTranslationCLM
#print axioms nativeTranslationCLM_ae
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

#print axioms nativeTranslation_weaklyMeasurable
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

#print axioms native_convolution_scalar_integrable
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

#print axioms nativePettisLinear_bound
#print axioms nativePettisVector_pairing
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

#print axioms nativePettisVector_bound
#print axioms nativeConvolutionCLM
#print axioms nativeConvolutionCLM_pairing
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

#print axioms actual_closed_subspace_convolution
#print axioms actual_PAQ_zero
#print axioms actual_global_convolution_blocks
#print axioms actual_global_candidate_defect
end Masullo.ClosedSubspaceConvolution

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace Masullo.WeightedCutoff

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def cut (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator (f : X → ℂ))

theorem cut_ae (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    (cut μ s hs f : X → ℂ) =ᵐ[μ] s.indicator (f : X → ℂ) :=
  MemLp.coeFn_toLp _

theorem cut_norm_le (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖cut μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cut_ae μ s hs f] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

def cutCLM (s : Set X) (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := cut μ s hs
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [cut_ae μ s hs (f+g), cut_ae μ s hs f, cut_ae μ s hs g,
          Lp.coeFn_add f g, Lp.coeFn_add (cut μ s hs f) (cut μ s hs g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx]
          exact h4
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [cut_ae μ s hs (c • f), cut_ae μ s hs f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (cut μ s hs f)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h3] }
    1 (fun f => by simpa using cut_norm_le μ s hs f)

theorem cut_complement_bound (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖f - cutCLM μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub f (cutCLM μ s hs f), cut_ae μ s hs f] with x h1 h2
  change (cutCLM μ s hs f : X → ℂ) x = _ at h2
  rw [h1, Pi.sub_apply, h2]
  by_cases hx : x ∈ s <;> simp [hx]

def band (ell : X → ℝ) (n : ℕ) : Set X := {x | |ell x| ≤ (n : ℝ)}

theorem band_measurable (ell : X → ℝ) (hell : Measurable ell) (n : ℕ) :
    MeasurableSet (band ell n) := measurableSet_le hell.abs measurable_const

theorem eventually_mem_band (ell : X → ℝ) (x : X) :
    ∀ᶠ n in atTop, x ∈ band ell n := by
  obtain ⟨N, hN⟩ := exists_nat_ge |ell x|
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans (by exact_mod_cast hn)

theorem physical_band_strong (ell : X → ℝ) (hell : Measurable ell) (f : Lp ℂ 2 μ) :
    Tendsto (fun n => cutCLM μ (band ell n) (band_measurable ell hell n) f)
      atTop (𝓝 f) := by
  let F : ℕ → X → ℂ := fun n => (band ell n).indicator (f : X → ℂ)
  have hF : ∀ n, MemLp (F n) 2 μ := fun n =>
    (Lp.memLp f).indicator (band_measurable ell hell n)
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Lp.memLp f).2).ne
  have hlim : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂μ)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖F n x - f x‖ₑ ^ (2 : ℝ))
      (fun x => ‖f x‖ₑ ^ (2 : ℝ))
      (fun n => by simpa using (((hF n).1.sub (Lp.memLp f).1).enorm.pow_const (2 : ℕ)))
      (fun n => Eventually.of_forall fun x => by
        by_cases hx : x ∈ band ell n <;> simp [F, hx]) hfin
      (f := fun _ => (0 : ℝ≥0∞))
      (Eventually.of_forall fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_mem_band ell x] with n hn
        simp [F, hn])
    simpa using h
  have hnorm : Tendsto (fun n => eLpNorm (F n - (f : X → ℂ)) 2 μ)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hlim
    simpa only [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, Pi.sub_apply,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF (f : X → ℂ) (Lp.memLp f)).2 hnorm
  simpa only [Lp.toLp_coeFn] using h

end Masullo.WeightedCutoff
namespace Masullo.WeightedDiagonalFactorization
open MeasureTheory

/-- Weight and reciprocal weight cancel in the ORIGINAL-Haar diagonal. -/
theorem weighted_diagonal_factorization (u r : ℂ) (w : ℝ) (hw : 0 < w) :
    ((Real.sqrt w : ℂ) * u) * (r / (Real.sqrt w : ℂ)) = u * r := by
  have hs : (Real.sqrt w : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hw))
  field_simp

/-- Native primal and dual L2 rows give an integrable actual diagonal without
assuming the native weight is bounded below. The row r includes conjugation. -/
theorem native_diagonal_integrable {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (u r : X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 < w x)
    (hu : MemLp (fun x => (Real.sqrt (w x) : ℂ) * u x) 2 mu)
    (hr : MemLp (fun x => r x / (Real.sqrt (w x) : ℂ)) 2 mu) :
    Integrable (fun x => u x * r x) mu := by
  have hi := hu.integrable_mul hr
  have he : (fun x => (Real.sqrt (w x) : ℂ) * u x) *
      (fun x => r x / (Real.sqrt (w x) : ℂ)) = (fun x => u x*r x) := by
    funext x
    exact weighted_diagonal_factorization (u x) (r x) (w x) (hw x)
  rw [he] at hi
  exact hi

/-- An actual infinite row expansion, once its native norm estimates provide
one summable ORIGINAL-measure bound, has the rank-one trace coefficient sum.
No product-null-set diagonal restriction or invented spectral data occurs. -/
theorem native_diagonal_integral_series {X : Type*} [MeasurableSpace X]
    {ι : Type*} [Countable ι]
    (mu : Measure X) (u r : ι → X → ℂ) (w : X → ℝ)
    (hw : ∀ x, 0 < w x)
    (hu : ∀ i, MemLp (fun x => (Real.sqrt (w x) : ℂ) * u i x) 2 mu)
    (hr : ∀ i, MemLp (fun x => r i x / (Real.sqrt (w x) : ℂ)) 2 mu)
    (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i, (∫ x, ‖u i x * r i x‖ ∂mu) ≤ B i) :
    HasSum (fun i => ∫ x, u i x * r i x ∂mu)
      (∫ x, ∑' i, u i x * r i x ∂mu) := by
  have hi (i : ι) := native_diagonal_integrable mu (u i) (r i) w hw (hu i) (hr i)
  have hs : Summable (fun i => ∫ x, ‖u i x * r i x‖ ∂mu) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _)) hbound hB
  exact hasSum_integral_of_summable_integral_norm hi hs

#print axioms weighted_diagonal_factorization
#print axioms native_diagonal_integrable
#print axioms native_diagonal_integral_series
end Masullo.WeightedDiagonalFactorization



namespace Masullo.CoreInvarianceExtends
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 theorem core_invariance_extends (T : H →L[ℂ] H) (C : Submodule ℂ H)
    (hC : ∀ x ∈ C, T x ∈ C) :
    ∀ x ∈ C.topologicalClosure, T x ∈ C.topologicalClosure := by
  intro x hx
  exact map_mem_closure T.continuous hx hC

/-- With G the ACTUAL geometric closure, its orthogonal complement projector
is P=1-Q. Invariance of G gives a one-sided triangular block, not commutation. -/
 theorem projection_order_defect (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    T (P x) - P (T x) = Q (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

 theorem convolution_first_compression (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let P := ContinuousLinearMap.id ℂ H - G.starProjection
    P (T x) = P (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

/-- Both complementary printed-to-convolution-first changes have opposite
signs, for the SAME cutoff. Neither individual defect is set to zero. -/
 theorem paired_cutoff_order_defects (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T M : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    (M (T (P x)) - M (P (T x)) = M (Q (T (P x)))) ∧
    (M (T (Q x)) - M (Q (T x)) = -M (Q (T (P x)))) := by
  dsimp only
  have hh := congrArg M (projection_order_defect G T hG x)
  simp only [map_sub] at hh
  constructor
  · exact hh
  · have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
      Submodule.starProjection_eq_self_iff.mpr
        (hG _ (Submodule.starProjection_apply_mem G x))
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
    abel

#print axioms core_invariance_extends
#print axioms projection_order_defect
#print axioms convolution_first_compression
#print axioms paired_cutoff_order_defects
end Masullo.CoreInvarianceExtends


namespace NativePWTransportR35

variable {R : Type*} [Ring R]

-- Instantiate e with the actual residual W^N and et with its adjoint.
-- u and ut are the original source column operator and its adjoint.
theorem original_gram_expansion (u ut e et : R) :
    ut * (1 - et) * (1 - e) * u =
      ut * u - ut * e * u - ut * et * u + ut * et * e * u := by
  noncomm_ring

-- q is the projection onto the actual finite reconstructed sources.
theorem source_residual_decomposition (s q e b : R) (hs : s * s = s)
    (hqs : q * s = q) :
    (s - q) * b = (s - q) * ((s - e) * b) + (s - q) * e * b := by
  calc
    (s - q) * b = (s * s - q * s) * b := by rw [hs, hqs]
    _ = (s - q) * ((s - e) * b) + (s - q) * e * b := by noncomm_ring

theorem perturbation_lower_bound {E : Type*} [SeminormedAddCommGroup E]
    (v w : E) (rho : ℝ) (h : ‖w‖ ≤ rho * ‖v‖) :
    (1 - rho) * ‖v‖ ≤ ‖v - w‖ := by
  have ht : ‖v‖ - ‖w‖ ≤ ‖v - w‖ := norm_sub_norm_le v w
  nlinarith

theorem signed_correction_error (a b x y ea eb : ℝ)
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb) :
    |(a - b) - (x - y)| ≤ ea + eb := by
  have ht := abs_sub (a - x) (b - y)
  have he : (a - b) - (x - y) = (a - x) - (b - y) := by ring
  rw [he]
  linarith

theorem signed_complex_correction_error (a b x y : ℂ) (ea eb : ℝ)
    (ha : ‖a - x‖ ≤ ea) (hb : ‖b - y‖ ≤ eb) :
    ‖(a - b) - (x - y)‖ ≤ ea + eb := by
  have ht := norm_sub_le (a - x) (b - y)
  have he : (a - b) - (x - y) = (a - x) - (b - y) := by ring
  rw [he]
  linarith

end NativePWTransportR35


namespace HReview
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
  Masullo.WeightedIdeleClass Masullo.NativeRep Masullo.NativePettisVectorBound
open scoped Topology InnerProductSpace
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Arithmetic logarithm, including inversion, is inherited from the product formula. -/
theorem classLog_one : classLog K 1 = 0 := by
  have hh := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at hh
  linarith

theorem classLog_inv (x : HeckeIdeleClasses K) : classLog K x⁻¹ = -classLog K x := by
  have hh := classLog_mul K x⁻¹ x
  rw [inv_mul_cancel, classLog_one] at hh
  linarith

def sharp (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  star (phi x⁻¹)

/-- BOTH requested tests, with the conjugation and the negative logarithmic sign. -/
theorem logged_sharp (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    sharp K (fun y => (classLog K y : ℂ) * phi y) x =
      -(classLog K x : ℂ) * sharp K phi x := by
  simp [sharp, classLog_inv, star_mul, mul_comm]

theorem logged_test_compact (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Continuous (fun x => -(classLog K x : ℂ) * h x) ∧
    HasCompactSupport (fun x => -(classLog K x : ℂ) * h x) := by
  exact ⟨((Complex.continuous_ofReal.comp (classLog_continuous K)).neg).mul hh,
    hc.mul_left⟩

variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (nu : Measure (HeckeIdeleClasses K)) [nu.IsMulLeftInvariant] [SFinite nu]
variable [IsLocallyFiniteMeasure nu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)

/-- Native half-weight realization of W_I^s with Hilbert reference nu.
The convolution Haar is mu=V*nu; this scalar must not be silently dropped. -/
def originalConvolution (V : ℝ) : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu :=
  (V : ℂ) • nativeConvolutionCLM K nu alpha s ha hs h hh hc

theorem originalConvolution_pairing (V : ℝ) (hV : 0 ≤ V)
    (F U : Lp ℂ 2 nu) :
    inner ℂ U (originalConvolution K nu alpha s ha hs h hh hc V F) =
      ∫ g, h g * inner ℂ U (nativeTranslationCLM K nu alpha s ha hs g F)
        ∂(ENNReal.ofReal V • nu) := by
  simp only [originalConvolution, ContinuousLinearMap.smul_apply, inner_smul_right,
    nativeConvolutionCLM_pairing, integral_smul_measure, ENNReal.toReal_ofReal hV,
    Complex.real_smul]

/-- Source equivariance is needed only on the actual generating family.
Continuity then supplies invariance of its closed linear span. -/
theorem source_closure_translation_invariant {J : Type*}
    (theta : J → Lp ℂ 2 nu)
    (hsource : ∀ g j, nativeTranslationCLM K nu alpha s ha hs g (theta j) ∈
      Submodule.span ℂ (Set.range theta)) :
    ∀ g F, F ∈ (Submodule.span ℂ (Set.range theta)).topologicalClosure →
      nativeTranslationCLM K nu alpha s ha hs g F ∈
        (Submodule.span ℂ (Set.range theta)).topologicalClosure := by
  intro g F hF
  let T := nativeTranslationCLM K nu alpha s ha hs g
  let N := Submodule.span ℂ (Set.range theta)
  have hinv : N ≤ N.comap T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hsource g j
  exact map_mem_closure T.continuous hF (fun v hv => hinv hv)

/-- PA=PAP and AP-PA=QAP for the genuine source-closure projection.
The source family must be the original both-moment theta family in applications. -/
theorem original_source_PA_order {J : Type*}
    (theta : J → Lp ℂ 2 nu)
    (hsource : ∀ g j, nativeTranslationCLM K nu alpha s ha hs g (theta j) ∈
      Submodule.span ℂ (Set.range theta))
    (V : ℝ) (F : Lp ℂ 2 nu) :
    let E := (Submodule.span ℂ (Set.range theta)).topologicalClosure
    let Q := E.starProjection
    let P := ContinuousLinearMap.id ℂ (Lp ℂ 2 nu) - Q
    let A := originalConvolution K nu alpha s ha hs h hh hc V
    P (A F) = P (A (P F)) ∧ A (P F) - P (A F) = Q (A (P F)) := by
  let E := (Submodule.span ℂ (Set.range theta)).topologicalClosure
  let A := originalConvolution K nu alpha s ha hs h hh hc V
  have hE : ∀ x ∈ E, A x ∈ E := by
    intro x hx
    exact E.smul_mem (V : ℂ)
      (Masullo.ClosedSubspaceConvolution.actual_closed_subspace_convolution
        K nu alpha s ha hs h hh hc E
        (source_closure_translation_invariant K nu alpha s ha hs theta hsource) x hx)
  exact ⟨Masullo.CoreInvarianceExtends.convolution_first_compression E A hE F,
    Masullo.CoreInvarianceExtends.projection_order_defect E A hE F⟩

/-- Physical cutoff convergence on the actual arithmetic class group, in
native half-weight coordinates. No compact support of projected vectors. -/
theorem actual_physical_band_limit (F : Lp ℂ 2 nu) :
    Tendsto (fun n => Masullo.WeightedCutoff.cutCLM nu
      (Masullo.WeightedCutoff.band (classLog K) n)
      (Masullo.WeightedCutoff.band_measurable (classLog K)
        (classLog_continuous K).measurable n) F) atTop (𝓝 F) :=
  Masullo.WeightedCutoff.physical_band_strong nu (classLog K)
    (classLog_continuous K).measurable F

#print axioms originalConvolution_pairing
#print axioms original_source_PA_order
#print axioms actual_physical_band_limit
end
end HReview

set_option linter.unusedSectionVars false

/-! Original-Haar rank-one kernels in the native half-weight realization.
If H=L2(w nu), b=sqrt(w), mu=V nu, the ordinary function represented by
F in L2(nu) is F/b. The kernel below therefore contains b(y)/(V b(x)). -/
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
#print axioms HNormalizedKernel.kernel_action
#print axioms HNormalizedKernel.diagonal_integral
#print axioms HNormalizedKernel.diagonal_cutoff_limit

/- Peer N source reviewed and incorporated verbatim, except its import. -/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace NMeasuredShells

variable {X E : Type*} [MeasurableSpace X]

/-- Shell pairing always uses the original quotient Haar measure `mu`. -/
noncomputable def shell (mu : Measure X) (p : X → ℝ) (f : X → ℂ) : ℂ :=
  ∫ x, (p x : ℂ) * f x ∂mu

/-- Bounded measurable shell masks need no separate integrability assumption. -/
theorem masked_integrable (mu : Measure X) (p : X → ℝ) (f : X → ℂ)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => (p x : ℂ) * f x) mu := by
  apply hf.norm.mono'
    ((Complex.continuous_ofReal.measurable.comp hp).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
  simpa using mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg (f x))

/-- A finite set of positive descended masks may overlap. -/
theorem finite_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ)
    (hf : Integrable f mu)
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1)
    (hi : ∀ e ∈ F, Integrable (fun x => (p e x : ℂ) * f x) mu) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  calc
    _ ≤ ∑ e ∈ F, ∫ x, ‖(p e x : ℂ) * f x‖ ∂mu := by
      exact Finset.sum_le_sum (fun e he => norm_integral_le_integral_norm _)
    _ = ∫ x, ∑ e ∈ F, ‖(p e x : ℂ) * f x‖ ∂mu := by
      symm
      exact integral_finset_sum F (fun e he => (hi e he).norm)
    _ ≤ ∫ x, ‖f x‖ ∂mu := by
      apply integral_mono
        (integrable_finset_sum F (fun e he => (hi e he).norm)) hf.norm
      intro x
      calc
        (∑ e ∈ F, ‖(p e x : ℂ) * f x‖) = (∑ e ∈ F, p e x) * ‖f x‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e he
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp e he x)]
        _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hs x) (norm_nonneg _)
        _ = ‖f x‖ := one_mul _

/-- Discharges mask integrability for the positive overlapping partition. -/
theorem measurable_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ) (hf : Integrable f mu)
    (hm : ∀ e ∈ F, Measurable (p e))
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  apply finite_shell_contraction mu F p f hf hp hs
  intro e he
  apply masked_integrable mu (p e) f (hm e he) (hp e he) _ hf
  intro x
  exact (Finset.single_le_sum (fun j hj => hp j hj x) he).trans (hs x)

omit [MeasurableSpace X] in
/-- Exact finite regularizer: the narrow remainder has a PLUS sign. -/
theorem regularizer_plus (wide narrow sandwich regNarrow : X → ℂ) :
    (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) = (fun x => wide x - sandwich x) := by
  funext x
  ring

/-- The correction identity holds under every mask before any limit. -/
theorem regularized_shell_eq (mu : Measure X) (p : X → ℝ)
    (wide narrow sandwich regNarrow : X → ℂ) :
    shell mu p (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) =
      shell mu p (fun x => wide x - sandwich x) := by
  rw [regularizer_plus]

/-- A trace-zero transport has a retained masked boundary contribution. -/
theorem shell_sub (mu : Measure X) (p : X → ℝ) (f g : X → ℂ)
    (hf : Integrable (fun x => (p x : ℂ) * f x) mu)
    (hg : Integrable (fun x => (p x : ℂ) * g x) mu) :
    shell mu p (fun x => f x - g x) = shell mu p f - shell mu p g := by
  simp only [shell, mul_sub]
  exact integral_sub hf hg

/-- Original representative and incoming-mask boundaries telescope before integration. -/
theorem boundary_repairs (indicator outgoing incoming : ℂ) :
    indicator - incoming = (indicator - outgoing) + (outgoing - incoming) := by ring

/-- The omitted residue is bounded by every paid finite shell enclosure. -/
theorem finite_residue_certificate [Fintype E]
    (v w : E → ℂ) (m : ℕ) (err : ℝ)
    (hm : ∑ e, v e = (m : ℂ))
    (he : (∑ e, ‖v e - w e‖) ≤ err) :
    ‖(m : ℂ) - ∑ e, w e‖ ≤ err := by
  rw [← hm, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans he

end NMeasuredShells

#print axioms NMeasuredShells.finite_shell_contraction
#print axioms NMeasuredShells.regularizer_plus
#print axioms NMeasuredShells.boundary_repairs
#print axioms NMeasuredShells.finite_residue_certificate

namespace HReview
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet

/-- The constructed original-Haar kernel acts on every completed arithmetic input.
Here b is exactly the manuscript half-weight for I=[-alpha,alpha]. -/
theorem actual_original_Haar_kernel_action
    (K : Type*) [Field K] [NumberField K]
    (nu : Measure (HeckeIdeleClasses K)) (alpha s V : ℝ) (hV : 0 < V)
    (U R F : Lp ℂ 2 nu) (x : HeckeIdeleClasses K) :
    let b := fun y => nativeHalfWeight alpha s (classLog K y)
    (b x : ℂ) * (∫ y, HNormalizedKernel.haarKernel b V U R x y *
      (F y / (b y : ℂ)) ∂(ENNReal.ofReal V • nu)) = inner ℂ R F * U x := by
  exact HNormalizedKernel.kernel_action nu _
    (fun y => nativeHalfWeight_pos alpha s (classLog K y)) V hV U R F x

/-- Peer N's measured shell theorem applies to the canonical Haar diagonal.
The integrability hypothesis is discharged from the actual L2 columns. -/
theorem canonical_diagonal_shell_bound
    {X E : Type*} [MeasurableSpace X]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : Lp ℂ 2 nu) (F : Finset E) (p : E → X → ℝ)
    (hm : ∀ e ∈ F, Measurable (p e))
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1) :
    (∑ e ∈ F, ‖NMeasuredShells.shell (ENNReal.ofReal V • nu) (p e)
      (fun x => HNormalizedKernel.haarKernel b V U R x x)‖) ≤
    ∫ x, ‖HNormalizedKernel.haarKernel b V U R x x‖ ∂(ENNReal.ofReal V • nu) := by
  exact NMeasuredShells.measurable_shell_contraction _ F p _
    (HNormalizedKernel.diagonal_integrable nu b hb V U R) hm hp hs

#print axioms actual_original_Haar_kernel_action
#print axioms canonical_diagonal_shell_bound
end HReview

/- Peer P nonsymmetric interval extension; source and clean receipt reviewed. -/
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

#print axioms PIntervalConvolution.interval_convolution_conjugacy
#print axioms PIntervalConvolution.interval_memLp_iff
#print axioms PIntervalConvolution.interval_PA_source_zero

/- Peer I measured compensator, physical tail, and omitted-edge remainder. -/

/-! I35 (35.7)-(35.9): the finite source term and narrow compensator are
retained under the SAME original-Haar mask. No arithmetic density identity
or nuclearity is asserted by this analytic lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ReviewI
variable {X : Type*} [MeasurableSpace X]

def masked (mu : Measure X) (w f : X → ℂ) : ℂ := ∫ x, w x * f x ∂mu

theorem masked_integrable (mu : Measure X) (w f : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => w x * f x) mu := by
  apply hf.norm.mono' (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖w x * f x‖ ≤ ‖f x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

theorem masked_sub (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    masked mu w (fun x => f x-g x) = masked mu w f-masked mu w g := by
  simp only [masked, mul_sub]
  exact integral_sub (masked_integrable mu w f hw hb hf)
    (masked_integrable mu w g hw hb hg)

theorem masked_error_le (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    ‖masked mu w f-masked mu w g‖ ≤ ∫ x, ‖f x-g x‖ ∂mu := by
  rw [← masked_sub mu w f g hw hb hf hg]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (masked_integrable mu w _ hw hb (hf.sub hg)).norm (hf.sub hg).norm
  filter_upwards [hb] with x hx
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- `wide=d_beta(T_beta)`, `narrow=d_alpha(T_alpha)`,
`sandwich=d_beta(S_e T_beta S_e)`, `regularized=d_alpha(R_e T_alpha R_e)`.
The source transport is `sandwich-regularized`. -/
theorem finite_source_compensator_integral
    (mu : Measure X) (w wide narrow sandwich regularized : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hsand : Integrable sandwich mu) (hreg : Integrable regularized mu) :
    masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich x-regularized x)
      +masked mu w (fun x => narrow x-regularized x) =
    masked mu w (fun x => wide x-sandwich x) := by
  rw [masked_sub mu w sandwich regularized hw hb hsand hreg,
    masked_sub mu w narrow regularized hw hb hnarrow hreg,
    masked_sub mu w wide sandwich hw hb hwide hsand]
  ring

/-- The low-energy cutoff converges to the full-input LEFT correction under
any bounded physical/shell mask. The source identity is not replaced by
its total trace; the regularization compensator is present at every n. -/
theorem regularized_source_shell_limit
    (mu : Measure X) (w wide narrow full : X → ℂ)
    (sandwich regularized : ℕ → X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hfull : Integrable full mu)
    (hsand : ∀ n, Integrable (sandwich n) mu)
    (hreg : ∀ n, Integrable (regularized n) mu)
    (hlim : Tendsto (fun n => ∫ x, ‖sandwich n x-full x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) atTop
      (𝓝 (masked mu w (fun x => wide x-full x))) := by
  have ht : Tendsto (fun n => masked mu w (sandwich n)) atTop
      (𝓝 (masked mu w full)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => masked_error_le mu w (sandwich n) full hw hb (hsand n) hfull) hlim
  have he : (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) =
      (fun n => masked mu w wide-masked mu w (sandwich n)) := by
    funext n
    rw [finite_source_compensator_integral mu w wide narrow (sandwich n)
      (regularized n) hw hb hwide hnarrow (hsand n) (hreg n),
      masked_sub mu w wide (sandwich n) hw hb hwide (hsand n)]
  rw [he, masked_sub mu w wide full hw hb hwide hfull]
  exact tendsto_const_nhds.sub ht

/-- Physical exhaustion is justified from an actual integrable Haar density. -/
theorem physical_cutoff_limit (mu : Measure X) (d : X → ℂ) (w : ℕ → X → ℂ)
    (hd : Integrable d mu) (hw : ∀ n, AEStronglyMeasurable (w n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖w n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => w n x) atTop (𝓝 1)) :
    Tendsto (fun n => masked mu (w n) d) atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · intro n
    exact (hw n).mul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    filter_upwards [hb n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa using hx.mul (tendsto_const_nhds (x := d x))

/-- The physical tail is retained as an integral before taking a limit. -/
theorem physical_tail_identity (mu : Measure X) (w d : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hd : Integrable d mu) :
    (∫ x, d x ∂mu)-masked mu w d = ∫ x, (1-w x)*d x ∂mu := by
  simp only [sub_mul, one_mul, masked]
  exact (integral_sub hd (masked_integrable mu w d hw hb hd)).symm

/-- If the full explicit formula is pole - all zeros, and the native trace
is interior + admitted edge, the correction is omitted - admitted edge. -/
theorem omitted_edge_remainder (pole geometric interior edge omitted spectral : ℂ)
    (hfull : geometric = pole-(interior+omitted))
    (hspec : spectral = interior+edge) :
    pole-geometric-spectral = omitted-edge := by
  rw [hfull, hspec]
  ring

end ReviewI
#print axioms ReviewI.finite_source_compensator_integral
#print axioms ReviewI.regularized_source_shell_limit
#print axioms ReviewI.physical_cutoff_limit
#print axioms ReviewI.omitted_edge_remainder

namespace HReview
/-- Manuscript (11.3.1.4): positive strata have the opposite shell sign. -/
theorem printed_shell_sign (alphaNext alphaNow kernel : ℂ) :
    (alphaNext-alphaNow)*kernel = -((alphaNow-alphaNext)*kernel) := by ring
end HReview
#print axioms HReview.printed_shell_sign
