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


-- Integrated supplier: inputs/exchange/J/JThetaDefinitions.lean
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



-- Integrated supplier: inputs/exchange/H/HKernelFragment.lean
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



-- Integrated supplier: inputs/exchange/O/OThetaClosure.lean
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

/-- Projection equality is transported along the proved equality of source
submodules, with the canonical projection on each topological closure. -/
theorem arithmetic_sourceProjection_eq :
    (sourceClosure
      (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi a alpha s)).starProjection =
      (thetaClosure K addHaar mu chi a alpha s).starProjection := by
  exact congrArg
    (fun W : Submodule ℂ (Lp ℂ 2 mu) => W.topologicalClosure.starProjection)
    (arithmeticSourceMap_range K addHaar mu chi a alpha s)

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


-- Integrated supplier: inputs/exchange/D/DSourceKernelFragment.lean
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


-- Integrated supplier: inputs/exchange/H/HTraceFragment.lean
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


-- Integrated supplier: inputs/exchange/H/HSourceTraceFragment.lean
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


-- Integrated supplier: inputs/exchange/L/LTestBoundary.fragment.lean
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

/- B fragment: insert after DSourceKernel, HSourceTraceFragment and ReviewM.
   This attaches the actual finite theta-source kernels to trace and shells. -/
namespace BSourceShell
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The same actual finite-source diagonal reconstructs its operator trace
through every measurable positive partition on the original measure. -/
theorem finiteKernel_trace_shells {ι : Type*} [Countable ι]
    (mu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (p : ι → X → ℝ) (hp : ReviewM.PositivePartition p) :
    Integrable (fun x => DSourceKernel.finiteKernel mu b E A x x) mu ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) *
        DSourceKernel.finiteKernel mu b E A x x ∂mu)
        (Masullo.TraceClass.trace (E.starProjection.comp A)) := by
  have hd := (DSourceKernel.finiteKernel_diagonal mu b hb E A).1
  refine ⟨hd, ?_⟩
  rw [← DSourceKernel.finiteKernel_trace mu b hb E A]
  exact ReviewM.shell_reconstruction mu p hp _ hd

end
end BSourceShell

/- B continuation fragment. Insert after BSourceShellFragment and ReviewM.
   These are the SAME literal finite source kernels used by D and H.
   I owns their actual arithmetic/two-test/descended-partition instantiation. -/
namespace BSourceShell
open MeasureTheory ContinuousLinearMap Filter
open scoped Topology BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Contractive masks preserve the actual original-measure diagonal's L1 admission. -/
theorem masked_integrable (mu : Measure X) (d omega : X → ℂ)
    (hd : Integrable d mu) (hm : AEStronglyMeasurable omega mu)
    (hbound : ∀ᵐ x ∂mu, ‖omega x‖ ≤ 1) :
    Integrable (fun x => omega x * d x) mu := by
  apply hd.norm.mono' (hm.mul hd.aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖omega x * d x‖ ≤ ‖d x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- Original-measure L1 removal of physical masks, with the source cutoff fixed. -/
theorem masked_diagonal_L1 (mu : Measure X) (d : X → ℂ)
    (hd : Integrable d mu) (omega : ℕ → X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, ‖omega n x * d x - d x‖ ∂mu) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫ x, ‖omega n x * d x - d x‖ ∂mu)
      atTop (𝓝 (∫ _ : X, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 2 * ‖d x‖)
    · intro n
      exact (((hm n).mul hd.aestronglyMeasurable).sub hd.aestronglyMeasurable).norm
    · exact hd.norm.const_mul 2
    · intro n
      filter_upwards [hbound n] with x hx
      simp only [norm_norm]
      calc
        ‖omega n x * d x - d x‖ ≤ ‖omega n x * d x‖ + ‖d x‖ := norm_sub_le _ _
        _ ≤ ‖d x‖ + ‖d x‖ := by
          rw [norm_mul]
          exact add_le_add (mul_le_of_le_one_left (norm_nonneg (d x)) hx) le_rfl
        _ = 2 * ‖d x‖ := by ring
    · filter_upwards [hl] with x hx
      simpa only [one_mul, sub_self, norm_zero] using
        ((hx.mul (tendsto_const_nhds (x := d x))).sub
          (tendsto_const_nhds (x := d x))).norm
  simpa only [integral_zero] using ht

/-- Simultaneous shell convergence for the SAME finite source diagonal.
No Gram determinant, kernel-action, or diagonal-integrability premise is added. -/
theorem finiteKernel_shell_cutoff_trace {ι : Type*} [Countable ι]
    (mu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (p : ι → X → ℝ) (hp : ReviewM.PositivePartition p)
    (omega : ℕ → X → ℂ) (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    let d := fun x => DSourceKernel.finiteKernel mu b E A x x
    HasSum (fun i => ∫ x, (p i x : ℂ) * d x ∂mu)
      (Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
    Summable (fun i => ‖∫ x, (p i x : ℂ) * d x ∂mu‖) ∧
    (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' i, ‖(∫ x, (p i x : ℂ) * (omega n x * d x) ∂mu) -
      (∫ x, (p i x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let d := fun x => DSourceKernel.finiteKernel mu b E A x x
  have hd : Integrable d mu := (DSourceKernel.finiteKernel_diagonal mu b hb E A).1
  have ht := finiteKernel_trace_shells mu b hb E A p hp
  have ha := ReviewM.positive_shell_l1 mu p hp d hd
  refine ⟨ht.2, ha.1, ha.2, ?_⟩
  exact ReviewM.shell_l1_limit mu p hp (fun n x => omega n x * d x) d
    (fun n => masked_integrable mu d (omega n) hd (hm n) (hbound n)) hd
    (masked_diagonal_L1 mu d hd omega hm hbound hl)

/-- The complementary kernel's pointwise diagonal, under h(1)=0, has shell sum
minus the genuine finite SOURCE trace. This does not assert that the residual
operator is itself trace class or that its diagonal limit has been identified. -/
theorem finiteComplement_trace_shells [Group X] {ι : Type*} [Countable ι]
    (mu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (h : X → ℂ) (h1 : h 1 = 0)
    (p : ι → X → ℝ) (hp : ReviewM.PositivePartition p) :
    let d := fun x => h (x * x⁻¹) - DSourceKernel.finiteKernel mu b E A x x
    Integrable d mu ∧
    HasSum (fun i => ∫ x, (p i x : ℂ) * d x ∂mu)
      (-Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
    Summable (fun i => ‖∫ x, (p i x : ℂ) * d x ∂mu‖) ∧
    (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu := by
  dsimp only
  let d := fun x => h (x * x⁻¹) - DSourceKernel.finiteKernel mu b E A x x
  have he : d = fun x => -DSourceKernel.finiteKernel mu b E A x x := by
    funext x
    simp only [d, mul_inv_cancel, h1, zero_sub]
  have hd : Integrable d mu := by
    rw [he]
    exact (DSourceKernel.finiteKernel_diagonal mu b hb E A).1.neg
  have htrace : (∫ x, d x ∂mu) =
      -Masullo.TraceClass.trace (E.starProjection.comp A) := by
    rw [he, integral_neg, DSourceKernel.finiteKernel_trace mu b hb E A]
  have ht := ReviewM.shell_reconstruction mu p hp d hd
  rw [htrace] at ht
  have ha := ReviewM.positive_shell_l1 mu p hp d hd
  exact ⟨hd, ht, ha.1, ha.2⟩

end
end BSourceShell

/- Insert after DSourceKernel and HSourceTraceFragment. This algebraic bridge
   records the free-kernel obligations explicitly; G supplies their application
   to the constructed arithmetic convolution. -/
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

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Explicit residual-kernel actions and their strong operator limit.
The limit is projection after A; no commutation or trace convergence is used. -/
theorem residualKernel_global_connection (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (freeKernel : X → X → ℂ)
    (F : Lp ℂ 2 nu)
    (hfree : (fun x => A F x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, freeKernel x y * (F y / (b y : ℂ)) ∂nu))
    (hint : ∀ᵐ x ∂nu, Integrable
      (fun y => freeKernel x y * (F y / (b y : ℂ))) nu) :
    let E := sourceSpan nu e0 eF Theta
    let P := (1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) -
      (sourceClosure e0 eF Theta).starProjection
    (∀ T, (fun x => (A F - (E T).starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, residualKernel nu b (E T) A freeKernel x y *
        (F y / (b y : ℂ)) ∂nu)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 ((P.comp A) F)) := by
  dsimp only
  refine ⟨fun T => residualKernel_action nu b hb _ A freeKernel F hfree hint, ?_⟩
  exact (source_kernel_global_connection nu b hb e0 eF Theta A F).2

end
end DSourceKernel

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

/- Insert after DResidualKernelFragment, BSourceCutoffShellFragment,
   MPartitionFragment, NNormalizedDescentFragment and LIntegrated.requiredTest.
   The final arithmetic wrapper also uses JThetaAttachment/OArithmeticClosure.
   This is one application of the shared source kernel, not a new kernel. -/
namespace ReviewI.Integration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution
open scoped Topology BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- The actual interval convolution and finite source projection have a common
original-Haar diagonal and descended arithmetic shell expression. The residual
diagonal has the opposite sign; no residual-operator trace is asserted. -/
theorem finite_interval_source_shells
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (indent : HeckeIdeles K → ℝ)
    (hindcont : Continuous indent)
    (hind : ∀ x, 0 ≤ indent x)
    (hmass : ∀ x, HasSum (fun t : Kˣ => indent (principalIdele K t * x)) 1)
    (q : Fin 2) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v indent
    let ker := DSourceKernel.finiteKernel mu b E A
    let d := fun x => DSourceKernel.residualKernel mu b E A
      (fun x y => h (x*y⁻¹)) x x
    Integrable (fun x => ker x x) mu ∧
    (∫ x, ker x x ∂mu) = Masullo.TraceClass.trace (E.starProjection.comp A) ∧
    HasSum (fun e => ∫ x, (p e x : ℂ) * ker x x ∂mu)
      (Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
    Integrable d mu ∧
    (∫ x, d x ∂mu) = -Masullo.TraceClass.trace (E.starProjection.comp A) ∧
    HasSum (fun e => ∫ x, (p e x : ℂ) * d x ∂mu)
      (-Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
    Summable (fun e => ‖∫ x, (p e x : ℂ) * d x ∂mu‖) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p e x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  let A := intervalConvolutionCLM K mu l r s hlr hs h
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  let p := NDivisorialShells.descendedMask K v indent
  let d := fun x => DSourceKernel.residualKernel mu b E A
    (fun x y => h (x*y⁻¹)) x x
  have hb : ∀ x, 0 < b x := by
    intro x
    dsimp [b, intervalHalfWeight]
    positivity
  have hp : ReviewM.PositivePartition p :=
    NDivisorialShells.descended_positivePartition_of_indentation K v indent
      hindcont hind hmass
  have hpos := BSourceShell.finiteKernel_trace_shells mu b hb E A p hp
  have hneg := BSourceShell.finiteComplement_trace_shells mu b hb E A h
    (LIntegrated.requiredTest_at_one K phi hphi q) p hp
  have hdiag : ∀ x, h (x*x⁻¹) = 0 := by
    intro x
    rw [mul_inv_cancel]
    exact LIntegrated.requiredTest_at_one K phi hphi q
  have hd := DSourceKernel.residualKernel_diagonal mu b hb E A
    (fun x y => h (x*y⁻¹)) hdiag
  refine ⟨hpos.1, DSourceKernel.finiteKernel_trace mu b hb E A, hpos.2,
    hd.1, hd.2, hneg.2.1, hneg.2.2.1, hneg.2.2.2, ?_⟩
  let omega : ℕ → HeckeIdeleClasses K → ℂ := fun n =>
    (DReview.physicalBand K n).indicator (fun _ => 1)
  have hm : ∀ n, AEStronglyMeasurable (omega n) mu := by
    intro n
    exact aestronglyMeasurable_const.indicator (DReview.physicalBand_measurable K n)
  have hbound : ∀ n, ∀ᵐ x ∂mu, ‖omega n x‖ ≤ 1 := by
    intro n
    filter_upwards [] with x
    by_cases hx : x ∈ DReview.physicalBand K n <;> simp [omega, hx]
  have hl : ∀ᵐ x ∂mu, Tendsto (fun n => omega n x) atTop (𝓝 1) := by
    filter_upwards [] with x
    obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : x ∈ DReview.physicalBand K n := hN.trans (by exact_mod_cast hn)
    simp [omega, hx]
  have he (n : ℕ) (x : HeckeIdeleClasses K) :
      omega n x * d x = (DReview.physicalBand K n).indicator d x := by
    by_cases hx : x ∈ DReview.physicalBand K n <;> simp [omega, hx]
  apply ReviewM.shell_l1_limit mu p hp
    (fun n => (DReview.physicalBand K n).indicator d) d
    (fun n => hd.1.indicator (DReview.physicalBand_measurable K n)) hd.1
  simpa only [he] using BSourceShell.masked_diagonal_L1 mu d hd.1 omega hm hbound hl

variable [MeasurableSpace (HeckeAdeles K)]

/-- Application to the very finite theta-source spans used in the canonical
strong exhaustion. Both tests, the interval midpoint and original Haar survive.
The chosen chi-source remains explicit; this is not an all-character theorem. -/
theorem both_tests_arithmetic_source_shells
    (addHaar : Measure (HeckeAdeles K))
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (indent : HeckeIdeles K → ℝ)
    (hindcont : Continuous indent)
    (hind : ∀ x, 0 ≤ indent x)
    (hmass : ∀ x, HasSum (fun t : Kˣ => indent (principalIdele K t * x)) 1)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
    let Theta := OArithmeticClosure.arithmeticSourceMap K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let S := (JThetaAttachment.thetaClosure K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v indent
    let d := fun T x => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹)) x x
    (∀ T,
      HasSum (fun e => ∫ x, (p e x : ℂ) * DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        (Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) * d T x ∂mu)
        (-Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Summable (fun e => ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ∧
      (∑' e, ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ≤ ∫ x, ‖d T x‖ ∂mu ∧
      Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
        (DReview.physicalBand K n).indicator (d T) x ∂mu) -
        (∫ x, (p e x : ℂ) * d T x ∂mu)‖) atTop (𝓝 0)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  let A := intervalConvolutionCLM K mu l r s hlr hs h
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let V := JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
  let Theta := OArithmeticClosure.arithmeticSourceMap K addHaar mu chi
    (a+(l+r)/2) ((r-l)/2) s
  refine ⟨?_, ?_⟩
  · intro T
    obtain ⟨_, _, hsource, _, _, hresidual, hsum, hbound, hlim⟩ :=
      finite_interval_source_shells K mu l r s hlr hs
        (DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T)
        phi hh hc hphi v indent hindcont hind hmass q
    exact ⟨hsource, hresidual, hsum, hbound, hlim⟩
  · have hlim := (DSourceKernel.source_kernel_global_connection mu
      (fun x => intervalHalfWeight l r s (classLog K x))
      (fun x => by
        change 0 < intervalHalfWeight l r s (classLog K x)
        unfold intervalHalfWeight
        positivity)
      (0 : V →ₗ[ℂ] ℂ) 0 Theta A F).2
    have hp := OArithmeticClosure.arithmetic_sourceProjection_eq
      K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
    rw [hp] at hlim
    exact hlim

end
end ReviewI.Integration

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


end
end OAllCharacterClosure


/- Insert after the checked ISourceShellFragment and J/O's shared full-source
   definitions. No new source, kernel, test, trace or partition is defined. -/
namespace ReviewI.Integration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution
open scoped Topology BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu] [MeasurableSpace (HeckeAdeles K)]

/-- The signed arithmetic shell formula for the full admitted original source,
with the same finite kernels and strong convolution-first residual limit.
Admission of every manuscript source is not inferred from the source definition. -/
theorem both_tests_full_source_shells
    (addHaar : Measure (HeckeAdeles K))
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (indent : HeckeIdeles K → ℝ)
    (hindcont : Continuous indent)
    (hind : ∀ x, 0 ≤ indent x)
    (hmass : ∀ x, HasSum (fun t : Kˣ => indent (principalIdele K t * x)) 1)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let S := (JThetaAttachment.fullThetaClosure K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v indent
    let d := fun T x => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹)) x x
    (∀ chi : UnitaryHeckeCharacter K,
      JThetaAttachment.thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s ≤
        JThetaAttachment.fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s) ∧
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
      (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
        (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ T,
      Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) * DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        (Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) * d T x ∂mu)
        (-Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Summable (fun e => ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ∧
      (∑' e, ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ≤ ∫ x, ‖d T x‖ ∂mu ∧
      Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
        (DReview.physicalBand K n).indicator (d T) x ∂mu) -
        (∫ x, (p e x : ℂ) * d T x ∂mu)‖) atTop (𝓝 0)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  let A := intervalConvolutionCLM K mu l r s hlr hs h
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
    (a+(l+r)/2) ((r-l)/2) s
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro chi
    exact JThetaAttachment.thetaClosure_le_fullThetaClosure K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s
  · intro T
    exact DSourceKernel.finiteKernel_action mu
      (fun x => intervalHalfWeight l r s (classLog K x))
      (fun x => by
        change 0 < intervalHalfWeight l r s (classLog K x)
        unfold intervalHalfWeight
        positivity) _ A F
  · intro T
    obtain ⟨hki, hktrace, hsource, _, _, hresidual, hsum, hbound, hlim⟩ :=
      finite_interval_source_shells K mu l r s hlr hs
        (DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T)
        phi hh hc hphi v indent hindcont hind hmass q
    exact ⟨hki, hktrace, hsource, hresidual, hsum, hbound, hlim⟩
  · have hlim := (DSourceKernel.source_kernel_global_connection mu
      (fun x => intervalHalfWeight l r s (classLog K x))
      (fun x => by
        change 0 < intervalHalfWeight l r s (classLog K x)
        unfold intervalHalfWeight
        positivity)
      (0 : V →ₗ[ℂ] ℂ) 0 Theta A F).2
    have hp := OAllCharacterClosure.full_sourceProjection_eq
      K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    rw [hp] at hlim
    exact hlim


end
end ReviewI.Integration

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

namespace Masullo.InverseGramProjection
open scoped InnerProductSpace Matrix BigOperators
noncomputable instance finiteSpan_finiteDim
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] (r : ι → H) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range r)) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range r)

/-- Explicit inverse-Gram coefficients determine the genuine orthogonal
projection, with the complex inner product linear in the second argument. -/
theorem inverseGram_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → H)
    (hG : IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j)))) (v : H) :
    (Submodule.span ℂ (Set.range r)).starProjection v =
      ∑ j, (((fun i j => inner ℂ (r i) (r j)) : Matrix ι ι ℂ)⁻¹ *ᵥ
        (fun i => inner ℂ (r i) v)) j • r j := by
  classical
  let E := Submodule.span ℂ (Set.range r)
  let G : Matrix ι ι ℂ := fun i j => inner ℂ (r i) (r j)
  let c := G⁻¹ *ᵥ (fun i => inner ℂ (r i) v)
  let p := ∑ j, c j • r j
  have hp : p ∈ E := by
    apply Submodule.sum_mem
    intro j hj
    exact E.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have heq : G *ᵥ c = (fun i => inner ℂ (r i) v) := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hi : ∀ i, inner ℂ (r i) (v-p) = 0 := by
    intro i
    rw [inner_sub_right]
    apply sub_eq_zero.mpr
    have hh := congrFun heq i
    simpa [p, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, G, mul_comm] using hh.symm
  have ho : ∀ w ∈ E, inner ℂ w (v-p) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨i, rfl⟩ := hw; exact hi i
    | zero => simp
    | add x y hx hy hpx hpy => simp only [inner_add_left, hpx, hpy, add_zero]
    | smul a x hx hpx => simp only [inner_smul_left, hpx, mul_zero]
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp
    (fun w hw => inner_eq_zero_symm.mpr (ho w hw)))


end Masullo.InverseGramProjection

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


end KPhysicalMask
end

/- B source-Gram attachment. Insert after BProjection, DSourceKernel,
   HSourceTrace, ReviewM and KStrongPhysicalMask. Uses the existing kernel,
   trace and physical multiplication; no arithmetic object is redefined. -/
namespace BSourceGram
open MeasureTheory ContinuousLinearMap InnerProductSpace OSourceClosure
open scoped InnerProductSpace Matrix BigOperators ComplexOrder
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The finite source Gram matrix in the common Hilbert realization. A named
Matrix type also fixes matrix inversion, rather than pointwise function inversion. -/
def sourceGram (r : ι → H) : Matrix ι ι ℂ :=
  fun i j => inner ℂ (r i) (r j)

/-- Explicit matrix inversion avoids Lean's pointwise function inverse instance. -/
def sourceGramInverse (r : ι → H) : Matrix ι ι ℂ :=
  @Inv.inv (Matrix ι ι ℂ) Matrix.inv (sourceGram r)

/-- The source Gram determinant is proved invertible from the actual frame. -/
theorem source_Gram_isUnit (r : ι → H) (hr : LinearIndependent ℂ r) :
    IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j))) := by
  exact isUnit_iff_ne_zero.mpr
    (ne_of_gt (Matrix.posDef_gram_of_linearIndependent hr).det_pos)

/-- Full inverse-Gram contraction with an arbitrary output operator M.
The incoming row is A.adjoint r_i: convolution is performed before projection. -/
theorem source_Gram_rankOne (r : ι → H) (hr : LinearIndependent ℂ r)
    (A M : H →L[ℂ] H) :
    M.comp ((Submodule.span ℂ (Set.range r)).starProjection.comp A) =
      ∑ i, rankOne ℂ
        (M (∑ j, sourceGramInverse r j i • r j))
        (A.adjoint (r i)) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    rankOne_apply, adjoint_inner_left]
  rw [Masullo.InverseGramProjection.inverseGram_projection r (source_Gram_isUnit r hr)]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_smul,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  dsimp [sourceGramInverse, sourceGram]
  rw [mul_comm]
  rfl

/-- This trace keeps every off-diagonal inverse-Gram entry. -/
theorem source_Gram_trace (r : ι → H) (hr : LinearIndependent ℂ r)
    (A M : H →L[ℂ] H) :
    Masullo.TraceClass.trace
      (M.comp ((Submodule.span ℂ (Set.range r)).starProjection.comp A)) =
      ∑ i, ∑ j, sourceGramInverse r j i *
        inner ℂ (r i) (A (M (r j))) := by
  rw [source_Gram_rankOne r hr A M, HOperatorTrace.finite_rank_trace]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right, adjoint_inner_left]

variable {X : Type*} [MeasurableSpace X]

/-- The original weighted source Gram equals the Hilbert Gram. The original
measure is unchanged; b is the one half-weight relating physical and L2 vectors. -/
theorem source_Gram_original_measure (mu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (r : ι → Lp ℂ 2 mu) (i j : ι) :
    (∫ x, star (r i x / (b x : ℂ)) * (r j x / (b x : ℂ)) *
      (b x : ℂ)^2 ∂mu) = inner ℂ (r i) (r j) := by
  rw [← HNormalizedKernel.l2_inner_formula mu (r j) (r i)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hb0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]
  field_simp

theorem masked_rank_diagonal_integrable (mu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (rho : X → ℝ) (hm : Measurable rho)
    (hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (U R : Lp ℂ 2 mu) :
    Integrable (fun x => (rho x : ℂ) *
      HNormalizedKernel.haarKernel b 1 U R x x) mu := by
  have h := (Lp.memLp (KPhysicalMask.realMask mu rho hm hrho U)).integrable_mul
    (Lp.memLp R).star
  apply h.congr
  filter_upwards [KPhysicalMask.realMask_ae mu rho hm hrho U] with x hx
  change (KPhysicalMask.realMask mu rho hm hrho U) x * star (R x) = _
  rw [HNormalizedKernel.diagonal_formula b hb, hx]
  simp only [Complex.ofReal_one, inv_one, one_mul]
  ring

theorem masked_rank_diagonal_integral (mu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (rho : X → ℝ) (hm : Measurable rho)
    (hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (U R : Lp ℂ 2 mu) :
    (∫ x, (rho x : ℂ) * HNormalizedKernel.haarKernel b 1 U R x x ∂mu) =
      inner ℂ R (KPhysicalMask.realMaskCLM mu rho hm hrho U) := by
  rw [← HNormalizedKernel.l2_inner_formula]
  apply integral_congr_ae
  filter_upwards [KPhysicalMask.realMask_ae mu rho hm hrho U] with x hx
  change (KPhysicalMask.realMaskCLM mu rho hm hrho U : X → ℂ) x = _ at hx
  rw [HNormalizedKernel.diagonal_formula b hb, hx]
  simp only [Complex.ofReal_one, inv_one, one_mul]
  ring

/-- Every actual shell diagonal is a trace with the genuine output mask.
No diagonal/trace identity is assumed. All rank-one integrability is proved. -/
theorem finiteKernel_masked_trace (mu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (rho : X → ℝ) (hm : Measurable rho)
    (hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) :
    (∫ x, (rho x : ℂ) * DSourceKernel.finiteKernel mu b E A x x ∂mu) =
      Masullo.TraceClass.trace
        ((KPhysicalMask.realMaskCLM mu rho hm hrho).comp (E.starProjection.comp A)) := by
  classical
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 mu := fun i => stdOrthonormalBasis ℂ E i
  let M := KPhysicalMask.realMaskCLM mu rho hm hrho
  have he : M.comp (E.starProjection.comp A) =
      ∑ i, rankOne ℂ (M (e i)) (A.adjoint (e i)) := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      rankOne_apply, adjoint_inner_left]
    rw [DSourceKernel.projection_expansion]
    simp only [map_sum, map_smul, e]
  rw [he, HOperatorTrace.finite_rank_trace]
  simp only [DSourceKernel.finiteKernel, Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ =>
    masked_rank_diagonal_integrable mu b hb rho hm hrho _ _)]
  exact Finset.sum_congr rfl (fun i _ =>
    masked_rank_diagonal_integral mu b hb rho hm hrho _ _)

/-- The SAME D finite kernel has the full source-Gram shell contraction.
The source frame is arbitrary; its determinant application is proved internally. -/
theorem finiteKernel_masked_Gram (mu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x) (r : ι → Lp ℂ 2 mu) (hr : LinearIndependent ℂ r)
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (rho : X → ℝ) (hm : Measurable rho)
    (hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) :
    (∫ x, (rho x : ℂ) * DSourceKernel.finiteKernel mu b
      (Submodule.span ℂ (Set.range r)) A x x ∂mu) =
      ∑ i, ∑ j, sourceGramInverse r j i *
        inner ℂ (r i) (A (KPhysicalMask.realMaskCLM mu rho hm hrho (r j))) := by
  rw [finiteKernel_masked_trace mu b hb _ A rho hm hrho]
  exact source_Gram_trace r hr A _

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Every finite source cutoff has an independent frame selected from its
literal admitted theta generators. No independence or determinant premise is added.
The finite basis selection is the same constructive span argument used in ALPO
LatticeCovolumes/DegStA.lean, applied here to the actual source set. -/
theorem sourceSpan_frame (mu : Measure X) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (T : Finset (Lp ℂ 2 mu)) :
    ∃ n : ℕ, ∃ r : Fin n → Lp ℂ 2 mu,
      (∀ i, r i ∈ (T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta) ∧
      LinearIndependent ℂ r ∧
      Submodule.span ℂ (Set.range r) = DSourceKernel.sourceSpan mu e0 eF Theta T := by
  classical
  obtain ⟨U, hUT, hspan, hli⟩ := exists_linearIndependent ℂ
    ((T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta)
  have hfin : U.Finite := (Finset.finite_toSet T).subset (fun _ hx => (hUT hx).1)
  letI : Fintype U := hfin.fintype
  let r : Fin (Fintype.card U) → Lp ℂ 2 mu :=
    fun i => ((Fintype.equivFin U).symm i : Lp ℂ 2 mu)
  have hrange : Set.range r = U := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ((Fintype.equivFin U).symm i).2
    · intro hx
      exact ⟨Fintype.equivFin U ⟨x, hx⟩, by simp [r]⟩
  refine ⟨Fintype.card U, r, (fun i => hUT ((Fintype.equivFin U).symm i).2),
    hli.comp _ (Fintype.equivFin U).symm.injective, ?_⟩
  rw [hrange]
  exact hspan

/-- Application to the literal finite theta-source cutoff and every shell.
The frame is chosen from that cutoff, and all positivity, mask, determinant and
integrability premises are discharged on these objects. -/
theorem sourceSpan_Gram_shells {J : Type*} [Countable J]
    (mu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (T : Finset (Lp ℂ 2 mu)) (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (p : J → X → ℝ) (hp : ReviewM.PositivePartition p) :
    let E := DSourceKernel.sourceSpan mu e0 eF Theta T
    let M := fun e => KPhysicalMask.realMaskCLM mu (p e) (hp.measurable e)
      (fun x => ⟨hp.nonneg e x, ReviewM.partition_le_one p hp e x⟩)
    ∃ n : ℕ, ∃ r : Fin n → Lp ℂ 2 mu,
      (∀ i, r i ∈ (T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta) ∧
      LinearIndependent ℂ r ∧ Submodule.span ℂ (Set.range r) = E ∧
      IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j))) ∧
      let g := fun e => ∑ i, ∑ j,
        sourceGramInverse r j i *
          inner ℂ (r i) (A (M e (r j)))
      (∀ e, (∫ x, (p e x : ℂ) * DSourceKernel.finiteKernel mu b E A x x ∂mu) = g e) ∧
      HasSum g (Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
      (∑' e, ‖g e‖) ≤ ∫ x, ‖DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  classical
  dsimp only
  obtain ⟨n, r, hrmem, hr, hspan⟩ := sourceSpan_frame mu e0 eF Theta T
  refine ⟨n, r, hrmem, hr, hspan, source_Gram_isUnit r hr, ?_⟩
  dsimp only
  have he (e : J) := finiteKernel_masked_Gram mu b hb r hr A (p e)
    (hp.measurable e) (fun x => ⟨hp.nonneg e x, ReviewM.partition_le_one p hp e x⟩)
  simp only [hspan] at he
  refine ⟨he, ?_, ?_⟩
  · simpa only [he] using
      (BSourceShell.finiteKernel_trace_shells mu b hb
        (DSourceKernel.sourceSpan mu e0 eF Theta T) A p hp).2
  · simpa only [he] using
      (ReviewM.positive_shell_l1 mu p hp
        (fun x => DSourceKernel.finiteKernel mu b
          (DSourceKernel.sourceSpan mu e0 eF Theta T) A x x)
        (DSourceKernel.finiteKernel_diagonal mu b hb _ A).1).2

end
end BSourceGram

/- B actual arithmetic application. Insert after BSourceGramFragment,
   the J/O full source, L required tests and NCanonicalShellPartition. -/
namespace BSourceGram
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry PIntervalConvolution
open scoped InnerProductSpace Matrix BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu] [MeasurableSpace (HeckeAdeles K)]

/-- Exact original-source inverse-Gram shell contraction for each manuscript
test and each source cutoff. The actual independent source frame and actual
arithmetic mask hypotheses are constructed, not assumed. This attaches to
the same finite kernels in P's global strong-limit theorem. -/
theorem both_tests_original_source_Gram_shells
    (addHaar : Measure (HeckeAdeles K))
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (v : ℕ → NumberField.FinitePlace K) (q : Fin 2)
    (T : Finset (Lp ℂ 2 mu)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    let hp := NDivisorialShells.arithmetic_positivePartition K v
    let M := fun e => KPhysicalMask.realMaskCLM mu (p e) (hp.measurable e)
      (fun x => ⟨hp.nonneg e x, ReviewM.partition_le_one p hp e x⟩)
    ∃ n : ℕ, ∃ r : Fin n → Lp ℂ 2 mu,
      (∀ i, r i ∈ (T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta) ∧
      LinearIndependent ℂ r ∧ Submodule.span ℂ (Set.range r) = E ∧
      IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j))) ∧
      let g := fun e => ∑ i, ∑ j,
        sourceGramInverse r j i *
          inner ℂ (r i) (A (M e (r j)))
      (∀ e, (∫ x, (p e x : ℂ) * DSourceKernel.finiteKernel mu b E A x x ∂mu) = g e) ∧
      HasSum g (Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
      (∑' e, ‖g e‖) ≤ ∫ x, ‖DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  dsimp only
  exact sourceSpan_Gram_shells mu
    (fun x => intervalHalfWeight l r s (classLog K x))
    (fun x => by
      change 0 < intervalHalfWeight l r s (classLog K x)
      unfold intervalHalfWeight
      positivity)
    (0 : JThetaAttachment.fullSourceSpan K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (OAllCharacterClosure.fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    T (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    (NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K))
    (NDivisorialShells.arithmetic_positivePartition K v)

end
end BSourceGram

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

section Product
variable (mu : Measure X) (nu : Measure Y) [SFinite mu] [SFinite nu]
variable (orbit : Y → Lp ℂ 2 mu) (raw : Y → X → ℂ)
variable (hraw : StronglyMeasurable (Function.uncurry raw))
variable (horbit : ∀ g, raw g =ᵐ[mu] (orbit g : X → ℂ))
variable (h : Y → ℂ) (hh : StronglyMeasurable h)
variable (B : Y → ℝ) (hB : Integrable (fun g => ‖h g‖ * B g) nu)
variable (hbound : ∀ g, ‖orbit g‖ ≤ B g)

include hraw horbit hh hB hbound in
/-- L2 product estimates and the actual orbit envelope discharge Fubini. -/
theorem tested_product_integrable (V : Lp ℂ 2 mu) :
    Integrable (fun p : Y × X => h p.1 * star (V p.2) * raw p.1 p.2)
      (nu.prod mu) := by
  have hm : AEStronglyMeasurable
      (fun p : Y × X => h p.1 * star (V p.2) * raw p.1 p.2) (nu.prod mu) :=
    (((hh.comp_measurable measurable_fst).mul
      ((Lp.stronglyMeasurable V).star.comp_measurable measurable_snd)).mul
        hraw).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  constructor
  · apply Eventually.of_forall
    intro g
    have hi := ((Lp.memLp V).star.integrable_mul (Lp.memLp (orbit g))).const_mul (h g)
    apply hi.congr
    filter_upwards [horbit g] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [← hx]
    ring
  · apply (hB.mul_const ‖V‖).mono' hm.norm.integral_prod_right'
    apply Eventually.of_forall
    intro g
    have he : (∫ x, ‖h g * star (V x) * raw g x‖ ∂mu) =
        ‖h g‖ * ∫ x, ‖V x‖ * ‖orbit g x‖ ∂mu := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [horbit g] with x hx
      rw [hx, norm_mul, norm_mul, norm_star]
      ring
    rw [he, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (integral_nonneg (fun x => mul_nonneg
        (norm_nonneg _) (norm_nonneg _))))]
    calc
      _ ≤ ‖h g‖ * (‖V‖ * ‖orbit g‖) :=
        mul_le_mul_of_nonneg_left (integral_norm_product_le mu V (orbit g)) (norm_nonneg _)
      _ ≤ ‖h g‖ * (‖V‖ * B g) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound g) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring

end Product

section Realization
variable (mu : Measure X) (nu : Measure Y) [SigmaFinite mu] [SFinite nu]
variable (out : Lp ℂ 2 mu) (orbit : Y → Lp ℂ 2 mu) (raw : Y → X → ℂ)
variable (hraw : StronglyMeasurable (Function.uncurry raw))
variable (horbit : ∀ g, raw g =ᵐ[mu] (orbit g : X → ℂ))
variable (h : Y → ℂ) (hh : StronglyMeasurable h)
variable (B : Y → ℝ) (hB : Integrable (fun g => ‖h g‖ * B g) nu)
variable (hbound : ∀ g, ‖orbit g‖ ≤ B g)
variable (hp : ∀ V : Lp ℂ 2 mu,
  inner ℂ V out = ∫ g, h g * inner ℂ V (orbit g) ∂nu)

include hraw horbit hh hB hbound hp in
theorem integral_representation :
    (out : X → ℂ) =ᵐ[mu] (fun x => ∫ g, h g * raw g x ∂nu) := by
  have hlocal (A : Set X) (hA : MeasurableSet A) (hmu : mu A < ⊤) :
      Integrable (A.indicator (fun x => ∫ g, h g * raw g x ∂nu)) mu ∧
      (∫ x in A, out x ∂mu) = ∫ x in A, (∫ g, h g * raw g x ∂nu) ∂mu := by
    let V : Lp ℂ 2 mu := indicatorConstLp 2 hA hmu.ne 1
    have hi := tested_product_integrable mu nu orbit raw hraw horbit h hh B hB hbound V
    have hv : (V : X → ℂ) =ᵐ[mu] A.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have he : (fun x => ∫ g, h g * star (V x) * raw g x ∂nu) =ᵐ[mu]
        A.indicator (fun x => ∫ g, h g * raw g x ∂nu) := by
      filter_upwards [hv] with x hx
      rw [hx]
      by_cases ha : x ∈ A
      · simp [ha]
      · simp [ha]
    refine ⟨hi.integral_prod_right.congr he, ?_⟩
    rw [← L2.inner_indicatorConstLp_one hA hmu.ne, hp]
    calc
      _ = ∫ g, ∫ x, h g * star (V x) * raw g x ∂mu ∂nu := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro g
        dsimp only
        rw [L2.inner_def, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [horbit g] with x hx
        rw [hx]
        simp only [RCLike.inner_apply]
        change h g * ((orbit g) x * star (V x)) = h g * star (V x) * (orbit g) x
        ring
      _ = ∫ x, ∫ g, h g * star (V x) * raw g x ∂nu ∂mu :=
        integral_integral_swap hi
      _ = _ := by rw [integral_congr_ae he, integral_indicator hA]
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hmu => integrableOn_Lp_of_measure_ne_top out one_le_two hmu.ne)
    (fun A hA hmu => (integrable_indicator_iff hA).mp (hlocal A hA hmu).1)
  exact fun A hA hmu => (hlocal A hA hmu).2

include hraw horbit hh hB hbound in
theorem ae_integrable_orbit :
    ∀ᵐ x ∂mu, Integrable (fun g => h g * raw g x) nu := by
  have hn (n : ℕ) : ∀ᵐ x ∂mu, x ∈ spanningSets mu n →
      Integrable (fun g => h g * raw g x) nu := by
    let A := spanningSets mu n
    have hA := measurableSet_spanningSets mu n
    have hmu := measure_spanningSets_lt_top mu n
    let V : Lp ℂ 2 mu := indicatorConstLp 2 hA hmu.ne 1
    have hi := tested_product_integrable mu nu orbit raw hraw horbit h hh B hB hbound V
    have hv : (V : X → ℂ) =ᵐ[mu] A.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    filter_upwards [hi.prod_left_ae, hv] with x hx hvx
    intro hax
    simpa [hvx, A, hax] using hx
  filter_upwards [ae_all_iff.mpr hn] with x hx
  have hall : x ∈ ⋃ n, spanningSets mu n := by rw [iUnion_spanningSets]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hall
  exact hx n hn

end Realization
end GPointwiseCore


/- Insert after the seed's PIntervalConvolution and GPointwiseCore (without its import).
No R/Mellin or source-projection declarations are needed. -/
namespace GPointwiseConvolution
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.NativeRep Masullo.NativeHalfWeightAddLe
open Masullo.NativeTranslationBound Masullo.NativePettisVectorBound
open PIntervalConvolution
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Actual Pettis convolution is the literal measured convolution a.e. on every
completed input. Its scalar integrability is proved from the translation envelope. -/
theorem nativeConvolutionCLM_measured
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    ((nativeConvolutionCLM K mu alpha s ha hs h hh hc F : HeckeIdeleClasses K → ℂ)
      =ᵐ[mu] (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        ∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu)) ∧
    (∀ᵐ x ∂mu, Integrable (fun g => h g * nativeRep K mu alpha s F (g⁻¹*x)) mu) := by
  let w : HeckeIdeleClasses K → ℂ := fun x =>
    (nativeHalfWeight alpha s (classLog K x) : ℂ)
  let raw := fun g x => w x * (F (g⁻¹*x) / w (g⁻¹*x))
  let orbit := fun g => nativeTranslationCLM K mu alpha s ha hs g F
  have hw : Measurable w := (actual_halfWeight_continuous K alpha s hs).measurable
  have hm : Measurable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => p.1⁻¹*p.2) :=
    measurable_fst.inv.mul measurable_snd
  have hraw : StronglyMeasurable (Function.uncurry raw) :=
    ((hw.comp measurable_snd).mul
      (((Lp.stronglyMeasurable F).measurable.comp hm).div (hw.comp hm))).stronglyMeasurable
  have horbit (g) : raw g =ᵐ[mu] (orbit g : HeckeIdeleClasses K → ℂ) :=
    (nativeTranslationCLM_ae K mu alpha s ha hs g F).symm
  let B := fun g => nativeTranslationBound K alpha s g * ‖F‖
  have hB : Integrable (fun g => ‖h g‖ * B g) mu := by
    simpa only [B, mul_assoc] using
      (native_convolution_envelope_integrable K mu alpha s hs h hh hc).mul_const ‖F‖
  have hb (g) : ‖orbit g‖ ≤ B g := nativeTranslation_norm K mu alpha s ha hs g F
  have hp (V : Lp ℂ 2 mu) :
      inner ℂ V (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∫ g, h g * inner ℂ V (orbit g) ∂mu :=
    nativeConvolutionCLM_pairing K mu alpha s ha hs h hh hc F V
  constructor
  · have he := GPointwiseCore.integral_representation mu mu
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) orbit raw hraw horbit
      h hh.stronglyMeasurable B hB hb hp
    filter_upwards [he] with x hx
    rw [hx, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun g => by dsimp [raw, w, nativeRep]; ring)
  · have hi := GPointwiseCore.ae_integrable_orbit mu mu orbit raw hraw horbit
      h hh.stronglyMeasurable B hB hb
    filter_upwards [hi] with x hx
    have hn : w x ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
    apply (hx.const_mul ((w x)⁻¹)).congr
    apply Eventually.of_forall
    intro g
    change (w x)⁻¹ * (h g * (w x * nativeRep K mu alpha s F (g⁻¹*x))) = _
    field_simp

/-- Literal original-interval inverse-input convolution and its a.e. integrability. -/
theorem intervalConvolutionCLM_measured
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    ((intervalConvolutionCLM K mu l r s hlr hs h hh hc F : HeckeIdeleClasses K → ℂ)
      =ᵐ[mu] (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
        ∫ g, h g * (F (g⁻¹*x) /
          (intervalHalfWeight l r s (classLog K (g⁻¹*x)) : ℂ)) ∂mu)) ∧
    (∀ᵐ x ∂mu, Integrable (fun g => h g * (F (g⁻¹*x) /
      (intervalHalfWeight l r s (classLog K (g⁻¹*x)) : ℂ))) mu) := by
  have hreps (y : HeckeIdeleClasses K) :
      nativeRep K mu ((r-l)/2) s F y = radialTwist K ((l+r)/2) y *
        (F y / (intervalHalfWeight l r s (classLog K y) : ℂ)) := by
    unfold nativeRep
    rw [interval_halfWeight l r s _ hlr]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, radialTwist]
    have hw : (nativeHalfWeight ((r-l)/2) s (classLog K y) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
    have he : Complex.exp ((((l+r)/2 : ℝ) : ℂ) * (classLog K y : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    field_simp
  have ht := nativeConvolutionCLM_measured K mu ((r-l)/2) s (by linarith) hs
    (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2 F
  constructor
  · filter_upwards [ht.1] with x hx
    change nativeConvolutionCLM K mu _ _ _ _ _ _ _ F x = _
    rw [hx]
    simp_rw [hreps]
    rw [← interval_convolution_conjugacy K mu ((l+r)/2) h
      (fun y => F y / (intervalHalfWeight l r s (classLog K y) : ℂ)) x, ← mul_assoc]
    congr 1
    rw [interval_halfWeight l r s _ hlr]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp, radialTwist]
    ring
  · filter_upwards [ht.2] with x hx
    have hn : radialTwist K ((l+r)/2) x ≠ 0 := Complex.exp_ne_zero _
    apply (hx.const_mul ((radialTwist K ((l+r)/2) x)⁻¹)).congr
    apply Eventually.of_forall
    intro g
    dsimp only
    rw [hreps]
    have he : radialTwist K ((l+r)/2) g * radialTwist K ((l+r)/2) (g⁻¹*x) =
        radialTwist K ((l+r)/2) x := by
      rw [← radialTwist_mul, mul_inv_cancel_left]
    calc
      _ = (radialTwist K ((l+r)/2) x)⁻¹ *
          ((radialTwist K ((l+r)/2) g * radialTwist K ((l+r)/2) (g⁻¹*x)) *
            (h g * (F (g⁻¹*x) / (intervalHalfWeight l r s (classLog K (g⁻¹*x)) : ℂ)))) := by ring
      _ = _ := by rw [he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The actual original-Haar free kernel on every completed interval input.
This is the free-action application required by D's residual kernel theorem. -/
theorem intervalConvolutionCLM_kernel [mu.IsInvInvariant]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    ((intervalConvolutionCLM K mu l r s hlr hs h hh hc F : HeckeIdeleClasses K → ℂ)
      =ᵐ[mu] (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
        ∫ y, h (x*y⁻¹) * (F y / (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu)) ∧
    (∀ᵐ x ∂mu, Integrable (fun y => h (x*y⁻¹) *
      (F y / (intervalHalfWeight l r s (classLog K y) : ℂ))) mu) := by
  let f := fun y => F y / (intervalHalfWeight l r s (classLog K y) : ℂ)
  have ht := intervalConvolutionCLM_measured K mu l r s hlr hs h hh hc F
  have he (x : HeckeIdeleClasses K) :
      (∫ g, h g * f (g⁻¹*x) ∂mu) = ∫ y, h (x*y⁻¹) * f y ∂mu := by
    calc
      _ = ∫ y, h (x*y) * f y⁻¹ ∂mu := by
        simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using
          (integral_mul_left_eq_self (μ := mu) (fun g => h g * f (g⁻¹*x)) x).symm
      _ = _ := by
        simpa only [inv_inv] using
          (integral_inv_eq_self (μ := mu) (fun y => h (x*y) * f y⁻¹)).symm
  constructor
  · filter_upwards [ht.1] with x hx
    rw [hx]
    exact congrArg (fun z => (intervalHalfWeight l r s (classLog K x) : ℂ) * z) (he x)
  · filter_upwards [ht.2] with x hx
    have hm := (measurePreserving_mul_left mu x).comp (Measure.measurePreserving_inv mu)
    have hi := (hm.integrable_comp hx.aestronglyMeasurable).mpr hx
    simpa only [Function.comp_def, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
      using hi

end
end GPointwiseConvolution


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

/-- Compact test support and the actual interval weight discharge L2 row
admission, with no kernel-row admission hypothesis. -/
theorem interval_kernel_row_memLp
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (x : HeckeIdeleClasses K) :
    MemLp (fun y => h (x*y⁻¹) /
      (intervalHalfWeight l r s (classLog K y) : ℂ)) 2 mu := by
  have hb := intervalHalfWeight_continuous_pos K l r s hlr hs
  exact compact_kernel_row_memLp mu
    (fun y => (intervalHalfWeight l r s (classLog K y) : ℂ)) hb.1
    (fun y => Complex.ofReal_ne_zero.mpr (ne_of_gt (hb.2 y))) h hh hc x

/-- The actual free-kernel action is absolutely integrable for every output
point on every completed input, strengthening the earlier a.e. conclusion. -/
theorem interval_kernel_integrable_everywhere
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) :
    Integrable (fun y => h (x*y⁻¹) *
      (F y / (intervalHalfWeight l r s (classLog K y) : ℂ))) mu := by
  have hi := (interval_kernel_row_memLp K mu l r s hlr hs h hh hc x).integrable_mul
    (Lp.memLp F)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun y => by dsimp only [Pi.mul_apply]; ring)

/-- The constructed arithmetic convolution has the same original-Haar
kernel action and everywhere-defined scalar integral on all completed inputs. -/
theorem intervalConvolutionCLM_kernel_everywhere
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SigmaFinite mu]
    [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    ((intervalConvolutionCLM K mu l r s hlr hs h hh hc F : HeckeIdeleClasses K → ℂ)
      =ᵐ[mu] (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
        ∫ y, h (x*y⁻¹) * (F y / (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu)) ∧
    (∀ x, Integrable (fun y => h (x*y⁻¹) *
      (F y / (intervalHalfWeight l r s (classLog K y) : ℂ))) mu) :=
  ⟨(intervalConvolutionCLM_kernel K mu l r s hlr hs h hh hc F).1,
    interval_kernel_integrable_everywhere K mu l r s hlr hs h hh hc F⟩

end
end GPointwiseConvolution

/- Insert after BArithmeticSourceGramFragment and GKernelRowsFragment.
   These are scalar entries of the existing Gram contraction, with the
   existing original Haar and actual interval convolution. -/
namespace BSourceGram
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution
open scoped InnerProductSpace Matrix BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- The literal original-Haar convolution entry, retaining both source factors
and the incoming mask at y. This defines a scalar, not another operator. -/
def sourceConvolutionEntry (l r s : ℝ) (h : HeckeIdeleClasses K → ℂ)
    (rho : HeckeIdeleClasses K → ℝ) (U V : Lp ℂ 2 mu) : ℂ :=
  ∫ x, (intervalHalfWeight l r s (classLog K x) : ℂ) * star (U x) *
    (∫ y, h (x*y⁻¹) * ((rho y : ℂ) * V y /
      (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu) ∂mu

/-- Inner and outer integration hypotheses are proved from the actual L2
action and compact convolution rows. No exchange of the two integrals occurs. -/
theorem sourceConvolutionEntry_eq
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (rho : HeckeIdeleClasses K → ℝ) (hm : Measurable rho)
    (hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (U V : Lp ℂ 2 mu) :
    (∀ x, Integrable (fun y => h (x*y⁻¹) * ((rho y : ℂ) * V y /
      (intervalHalfWeight l r s (classLog K y) : ℂ))) mu) ∧
    Integrable (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) * star (U x) *
      (∫ y, h (x*y⁻¹) * ((rho y : ℂ) * V y /
        (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu)) mu ∧
    sourceConvolutionEntry K mu l r s h rho U V =
      inner ℂ U (intervalConvolutionCLM K mu l r s hlr hs h hh hc
        (KPhysicalMask.realMaskCLM mu rho hm hrho V)) := by
  let M := KPhysicalMask.realMaskCLM mu rho hm hrho
  let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
  have hmask : (fun y => M V y) =ᵐ[mu] (fun y => (rho y : ℂ) * V y) :=
    KPhysicalMask.realMask_ae mu rho hm hrho V
  have hk := GPointwiseConvolution.intervalConvolutionCLM_kernel_everywhere
    K mu l r s hlr hs h hh hc (M V)
  have he (x : HeckeIdeleClasses K) :
      (∫ y, h (x*y⁻¹) * (M V y /
        (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu) =
      ∫ y, h (x*y⁻¹) * ((rho y : ℂ) * V y /
        (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu := by
    apply integral_congr_ae
    filter_upwards [hmask] with y hy
    rw [hy]
  have hout : (fun x => (A (M V)) x * star (U x)) =ᵐ[mu]
      (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) * star (U x) *
        (∫ y, h (x*y⁻¹) * ((rho y : ℂ) * V y /
          (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu)) := by
    filter_upwards [hk.1] with x hx
    change (A (M V)) x = _ at hx
    rw [hx, he]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro x
    apply (hk.2 x).congr
    filter_upwards [hmask] with y hy
    rw [hy]
  · exact ((Lp.memLp (A (M V))).integrable_mul (Lp.memLp U).star).congr hout
  · change (∫ x, _ ∂mu) = inner ℂ U (A (M V))
    rw [← integral_congr_ae hout]
    exact HNormalizedKernel.l2_inner_formula mu (A (M V)) U

variable [MeasurableSpace (HeckeAdeles K)]

/-- Concrete original-Haar entries for every finite source cutoff and both
manuscript tests. Frame, Gram invertibility, canonical shells, row admission,
and all diagonal integrability applications use the common arithmetic objects. -/
theorem both_tests_original_source_measured_Gram_shells
    (addHaar : Measure (HeckeAdeles K))
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (v : ℕ → NumberField.FinitePlace K) (q : Fin 2)
    (T : Finset (Lp ℂ 2 mu)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    ∃ n : ℕ, ∃ u : Fin n → Lp ℂ 2 mu,
      (∀ i, u i ∈ (T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta) ∧
      LinearIndependent ℂ u ∧ Submodule.span ℂ (Set.range u) = E ∧
      IsUnit (Matrix.det (fun i j => inner ℂ (u i) (u j))) ∧
      let g := fun e => ∑ i, ∑ j,
        sourceGramInverse u j i * sourceConvolutionEntry K mu l r s h (p e) (u i) (u j)
      (∀ e, (∫ x, (p e x : ℂ) * DSourceKernel.finiteKernel mu b E A x x ∂mu) = g e) ∧
      HasSum g (Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
      (∑' e, ‖g e‖) ≤ ∫ x, ‖DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  dsimp only
  obtain ⟨n, u, hrmem, hr, hspan, hdet, hdiagonal, hsum, hbound⟩ :=
    both_tests_original_source_Gram_shells K mu addHaar a l r s hlr hs
      phi hh hc v q T
  refine ⟨n, u, hrmem, hr, hspan, hdet, ?_⟩
  let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
  have hp := NDivisorialShells.arithmetic_positivePartition K v
  have he (e : Option ℕ) (i j : Fin n) :=
    (sourceConvolutionEntry_eq K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2 (p e) (hp.measurable e)
      (fun x => ⟨hp.nonneg e x, ReviewM.partition_le_one p hp e x⟩) (u i) (u j)).2.2
  dsimp only [p] at he
  simp_rw [he]
  exact ⟨hdiagonal, hsum, hbound⟩

end
end BSourceGram

namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Masullo.GenuineMellinJet Masullo.IdeleTheta Masullo.NativeRep
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open scoped NumberField NNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
theorem classTheta_const_mul (c : ℂ) (f : HeckeAdeles K → ℂ)
    (x : HeckeIdeleClasses K) :
    classTheta K (fun y => c * f y) x = c * classTheta K f x := by
  induction x using Quotient.inductionOn with
  | h y => exact tsum_mul_left

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


end
end JThetaAttachment

/- Supplied constructive dependency: inputs/review_core/Masullo/Spectral/ThetaSummability.lean; import/print commands removed; number-field binders generalized from Type to Type* and redundant local Fintype instances removed to use the common Schwartz norm instances. -/
set_option maxHeartbeats 1200000
set_option linter.unnecessarySeqFocus false
open NumberField IsDedekindDomain Topology Filter Set
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
namespace Masullo.EqAlgebraMapAddNsmul
private theorem exists_valuation_sub_lt_of_injective (F : Type*) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (c : HeightOneSpectrum (𝓞 F) → F) :
    ∃ w : F, (∀ v ∈ T, v.valuation F (w - c v) ≤ 1) ∧ ∀ v ∉ T, v.valuation F w ≤ 1 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 F)⁰ T c
  set d : 𝓞 F := (b : 𝓞 F) with hd_def
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hdK : algebraMap (𝓞 F) F d ≠ 0 := by
    rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 F) F)]
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d * (if v ∈ T then c v else 0) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨r, hr⟩ := RingHom.mem_rangeS.1 (hb v hv)
      refine ⟨r, ?_⟩
      rw [if_pos hv, hr, Algebra.smul_def]
    · exact ⟨0, by simp [hv]⟩
  choose g hg using hex
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by
      simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hd0)
  set S : Finset (HeightOneSpectrum (𝓞 F)) := T ∪ hfin.toFinset with hS
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal (𝓞 F))).factors)
    (fun v _ => v.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun i => g i)
  have key : ∀ v ∈ S, v.valuation F (algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d -
      (if v ∈ T then c v else 0)) ≤ 1 := by
    intro v hv
    have h1 : algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d - (if v ∈ T then c v else 0)
        = algebraMap (𝓞 F) F (r - g v) / algebraMap (𝓞 F) F d := by
      rw [map_sub, hg v, sub_div, mul_div_cancel_left₀ _ hdK]
    rw [h1, map_div₀, div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff (v.valuation F)).2 hdK)),
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_if_neg hd0]
    exact (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
  refine ⟨algebraMap (𝓞 F) F r / algebraMap (𝓞 F) F d, fun v hv => ?_, fun v hv => ?_⟩
  · have h := key v (Finset.mem_union_left _ hv)
    rwa [if_pos hv] at h
  · by_cases hvS : v ∈ S
    · have h := key v hvS
      rwa [if_neg hv, sub_zero] at h
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {d} := fun h =>
        hvS (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
      have hd1 : v.valuation F (algebraMap (𝓞 F) F d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d)
          (not_lt.1 (fun h => hnd ((v.intValuation_lt_one_iff_dvd d).1 h)))
      rw [map_div₀, hd1, div_one, HeightOneSpectrum.valuation_of_algebraMap]
      exact v.intValuation_le_one r

private theorem exists_sub_mem_adicCompletionIntegers' (F : Type*) [Field F] [NumberField F]
    (z : FiniteAdeleRing (𝓞 F) F) :
    ∃ w : F, ∀ v, z v - algebraMap F (FiniteAdeleRing (𝓞 F) F) w v ∈
      v.adicCompletionIntegers F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ z v ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 z.2
  have hc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ c : F,
      z v - (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro v
    have hdense : DenseRange (fun c : WithVal (v.valuation F) =>
        (c : UniformSpace.Completion (WithVal (v.valuation F)))) :=
      UniformSpace.Completion.denseRange_coe
    have hopen : IsOpen {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} :=
      (Valued.isOpen_valuationSubring _).preimage (continuous_const.sub continuous_id)
    have hne : z v ∈ {t : v.adicCompletion F | z v - t ∈ v.adicCompletionIntegers F} := by
      show z v - z v ∈ v.adicCompletionIntegers F
      rw [sub_self]
      exact zero_mem _
    exact hdense.exists_mem_open hopen ⟨z v, hne⟩
  choose c hc using hc
  obtain ⟨w, hw1, hw2⟩ := exists_valuation_sub_lt_of_injective F hfin.toFinset c
  refine ⟨w, fun v => ?_⟩
  change z v - (w : v.adicCompletion F) ∈ v.adicCompletionIntegers F
  by_cases hv : v ∈ hfin.toFinset
  · have h1 : ((c v : F) : v.adicCompletion F) =
        ((c v - w : F) : v.adicCompletion F) + (w : v.adicCompletion F) := by
      have hc : ∀ q : F, (q : v.adicCompletion F) = algebraMap F (v.adicCompletion F) q :=
        fun q => by simp [HeightOneSpectrum.algebraMap_adicCompletion]
      rw [hc, hc, hc, map_sub]
      ring
    have h2 : z v - (w : v.adicCompletion F) =
        (z v - (c v : v.adicCompletion F)) + ((c v - w : F) : v.adicCompletion F) := by
      rw [h1]; ring
    rw [h2]
    refine add_mem (hc v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Valuation.map_sub_swap]
    exact hw1 v hv
  · have hz : z v ∈ v.adicCompletionIntegers F := by
      by_contra h
      exact hv (hfin.mem_toFinset.2 h)
    refine sub_mem hz ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hw2 v hv

theorem exists_eq_algebraMap_add_nsmul (F : Type*) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N)
    (y : FiniteAdeleRing (𝓞 F) F) :
    ∃ (x : F) (a : FiniteAdeleRing (𝓞 F) F), (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
      y = algebraMap F _ x + N • a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨w, hw⟩ := exists_sub_mem_adicCompletionIntegers' F
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y)
  refine ⟨N * w, algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ * y -
    algebraMap F (FiniteAdeleRing (𝓞 F) F) w, fun v => hw v, ?_⟩
  have hA : (N : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ hN', map_one]
  rw [nsmul_eq_mul, map_mul, map_natCast]
  linear_combination (-y) * hA

variable (F : Type*) [Field F] [NumberField F]
def integralSet : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v, x v ∈ v.adicCompletionIntegers F}
def multiplier (d : (𝓞 F)⁰) : FiniteAdeleRing (𝓞 F) F :=
  algebraMap F _ (algebraMap (𝓞 F) F d.val)
theorem integralSet_open : IsOpen (integralSet F) := by
  have h : IsOpen {x : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), True → x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem
      (fun v => Valued.isOpen_valuationSubring (v.adicCompletion F))
  simpa only [integralSet, true_implies] using h
theorem integer_mul_integral (d : (𝓞 F)⁰) {x : FiniteAdeleRing (𝓞 F) F}
    (hx : x ∈ integralSet F) : multiplier F d * x ∈ integralSet F := by
  intro v
  exact mul_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v d.val) (hx v)
theorem exists_integer_mul_integral (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ d : (𝓞 F)⁰, multiplier F d * a ∈ integralSet F := by
  obtain ⟨x,b,hb,hab⟩ := exists_eq_algebraMap_add_nsmul F 1 one_pos a
  obtain ⟨n,d,hd,hx⟩ := IsFractionRing.div_surjective (A := 𝓞 F) x
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr (nonZeroDivisors.ne_zero hd)
  have he : algebraMap (𝓞 F) F d * x = algebraMap (𝓞 F) F n := by
    rw [← hx]
    field_simp
  refine ⟨⟨d,hd⟩,?_⟩
  rw [hab,one_smul,mul_add]
  have hf : multiplier F ⟨d,hd⟩ * algebraMap F (FiniteAdeleRing (𝓞 F) F) x =
      algebraMap F _ (algebraMap (𝓞 F) F n) := by
    dsimp [multiplier]
    rw [← map_mul,he]
  rw [hf]
  intro v
  exact add_mem (HeightOneSpectrum.coe_mem_adicCompletionIntegers v n)
    ((integer_mul_integral F ⟨d,hd⟩ hb) v)

theorem compact_denominator (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C) :
    ∃ d : (𝓞 F)⁰, ∀ x ∈ C, multiplier F d * x ∈ integralSet F := by
  let V : (𝓞 F)⁰ → Set (FiniteAdeleRing (𝓞 F) F) :=
    fun d => {x | multiplier F d * x ∈ integralSet F}
  have hm (d e : (𝓞 F)⁰) : multiplier F (d*e) = multiplier F d * multiplier F e := by
    simp only [multiplier,Submonoid.coe_mul,map_mul]
  have hV : Directed (· ⊆ ·) V := by
    intro d e
    refine ⟨d*e,fun x hx => ?_,fun x hx => ?_⟩
    · have h := integer_mul_integral F e hx
      change multiplier F (d*e) * x ∈ integralSet F
      rw [hm]
      convert h using 1 <;> ring
    · have h := integer_mul_integral F d hx
      change multiplier F (d*e) * x ∈ integralSet F
      rw [hm,mul_assoc]
      exact h
  obtain ⟨d,hd⟩ := hC.elim_directed_cover V
    (fun d => (integralSet_open F).preimage (continuous_const.mul continuous_id))
    (fun x _ => by
      obtain ⟨e,h⟩ := exists_integer_mul_integral F x
      exact Set.mem_iUnion.mpr ⟨e,h⟩) hV
  exact ⟨d,fun x hx => hd hx⟩

theorem compact_transformed_support_denominator
    (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ d : (𝓞 F)⁰, ∀ a ∈ U, ∀ y ∈ C,
      multiplier F d * (a.inv.2 * y) ∈ integralSet F := by
  let T : (AdeleRing (𝓞 F) F)ˣ × FiniteAdeleRing (𝓞 F) F →
      FiniteAdeleRing (𝓞 F) F := fun p => p.1.inv.2 * p.2
  have hT : Continuous T :=
    (continuous_snd.comp (Units.continuous_coe_inv.comp continuous_fst)).mul continuous_snd
  obtain ⟨d,h⟩ := compact_denominator F (T '' (U ×ˢ C)) ((hU.prod hC).image hT)
  exact ⟨d,fun a ha y hy => h _ ⟨(a,y),⟨ha,hy⟩,rfl⟩⟩

theorem compact_support_diagonal_integrality
    (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ d : (𝓞 F)⁰, ∀ a ∈ U, ∀ ξ : F,
      a.val.2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ C →
      ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d.val * ξ := by
  obtain ⟨d,h⟩ := compact_transformed_support_denominator F C hC U hU
  refine ⟨d,?_⟩
  intro a ha ξ hξ
  have hh := h a ha _ hξ
  have he : a.inv.2 * (a.val.2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := by
    rw [← mul_assoc, show a.inv.2 * a.val.2 = 1 from congrArg Prod.snd a.inv_val,one_mul]
  rw [he] at hh
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F
  intro v
  have hv := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hh v)
  change Valued.v ((algebraMap (𝓞 F) F d.val : v.adicCompletion F) *
    (ξ : v.adicCompletion F)) ≤ 1 at hv
  have hc : ∀ q : F, (q : v.adicCompletion F) = algebraMap F (v.adicCompletion F) q :=
    fun q => by simp [HeightOneSpectrum.algebraMap_adicCompletion]
  rw [hc, hc, ← map_mul] at hv
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le hv
end Masullo.EqAlgebraMapAddNsmul

namespace Masullo.SupportedPoints
variable (F : Type*) [Field F] [NumberField F]
/-- Nonzero diagonal points meeting an arbitrary original finite support. -/
def supportedPoints (C : Set (FiniteAdeleRing (𝓞 F) F))
    (a : (AdeleRing (𝓞 F) F)ˣ) :=
  {ξ : F // ξ ≠ 0 ∧ a.val.2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ C}

/-- ONE denominator embeds every supported nonzero diagonal set, uniformly
on a compact family of original ideles, into the genuine nonzero integers. -/
theorem compact_support_integer_embedding
    (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ d : (𝓞 F)⁰, ∀ a ∈ U,
      ∃ e : supportedPoints F C a ↪ {r : 𝓞 F // r ≠ 0},
        ∀ ξ, algebraMap (𝓞 F) F (e ξ).val = algebraMap (𝓞 F) F d.val * ξ.val := by
  classical
  obtain ⟨d,hd⟩ := Masullo.EqAlgebraMapAddNsmul.compact_support_diagonal_integrality F C hC U hU
  have hd0 : algebraMap (𝓞 F) F d.val ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr
      (nonZeroDivisors.ne_zero d.property)
  refine ⟨d,?_⟩
  intro a ha
  have hex (ξ : supportedPoints F C a) : ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = algebraMap (𝓞 F) F d.val * ξ.val :=
    hd a ha ξ.val ξ.property.2
  choose r hr using hex
  have hr0 (ξ : supportedPoints F C a) : r ξ ≠ 0 := by
    intro hz
    have hh := hr ξ
    rw [hz,map_zero] at hh
    exact (mul_ne_zero hd0 ξ.property.1) hh.symm
  let e : supportedPoints F C a ↪ {r : 𝓞 F // r ≠ 0} :=
    { toFun := fun ξ => ⟨r ξ,hr0 ξ⟩
      inj' := by
        intro ξ η he
        apply Subtype.ext
        apply mul_left_cancel₀ hd0
        rw [← hr ξ,← hr η]
        exact congrArg (algebraMap (𝓞 F) F) (congrArg Subtype.val he) }
  exact ⟨e,hr⟩

/-- Absolute series on every translated finite support are subseries of ONE
actual denominator-integer series. No cancellation estimate is substituted. -/
theorem compact_support_absolute_subseries
    (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) :
    ∃ d : (𝓞 F)⁰, ∀ a ∈ U, ∀ G : F → ℂ,
      Summable (fun r : {r : 𝓞 F // r ≠ 0} =>
        ‖G (algebraMap (𝓞 F) F r.val / algebraMap (𝓞 F) F d.val)‖) →
      Summable (fun ξ : supportedPoints F C a => ‖G ξ.val‖) ∧
      (∑' ξ : supportedPoints F C a, ‖G ξ.val‖) ≤
        ∑' r : {r : 𝓞 F // r ≠ 0},
          ‖G (algebraMap (𝓞 F) F r.val / algebraMap (𝓞 F) F d.val)‖ := by
  obtain ⟨d,hd⟩ := compact_support_integer_embedding F C hC U hU
  have hd0 : algebraMap (𝓞 F) F d.val ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr
      (nonZeroDivisors.ne_zero d.property)
  refine ⟨d,?_⟩
  intro a ha G hs
  obtain ⟨e,he⟩ := hd a ha
  have hcoord (ξ : supportedPoints F C a) :
      algebraMap (𝓞 F) F (e ξ).val / algebraMap (𝓞 F) F d.val = ξ.val := by
    apply (div_eq_iff hd0).mpr
    rw [he]
    ring
  have hS : Summable (fun ξ : supportedPoints F C a => ‖G ξ.val‖) := by
    simpa only [Function.comp_def,hcoord] using hs.comp_injective e.injective
  refine ⟨hS,?_⟩
  exact Summable.tsum_le_tsum_of_inj e e.injective
    (fun _ _ => norm_nonneg _) (fun ξ => by rw [hcoord]) hS hs
end Masullo.SupportedPoints

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000
open NumberField NumberField.mixedEmbedding Filter Topology Set
open scoped SchwartzMap nonZeroDivisors NumberField
noncomputable section
namespace Masullo.IdealUnitDilationUniform
variable (K : Type*) [Field K] [NumberField K]

/-- Actual lattice theta decay uniformly before both test and multiplier. -/
theorem actual_ideal_unit_dilation_uniform
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(mixedSpace K, ℂ), ∀ a : (mixedSpace K)ˣ,
      ‖((a⁻¹ : (mixedSpace K)ˣ) : mixedSpace K)‖ ≤ R →
      ∀ t : ℝ, 1 ≤ t →
      Summable (fun x : {x : idealLattice K I // x ≠ 0} =>
        ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖) ∧
      (∑' x : {x : idealLattice K I // x ≠ 0},
        ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖) ≤
        C * SchwartzMap.seminorm ℝ k 0 f * (t ^ N)⁻¹ := by
  let L := idealLattice K I
  let J := {x : L // x ≠ 0}
  let k := Module.finrank ℤ L + N + 1
  let b : J → ℝ := fun x => ‖(x.val : mixedSpace K)‖⁻¹ ^ k
  have hb : Summable b := by
    exact (ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)).subtype
      {x : L | x ≠ 0}
  refine ⟨k, (∑' x : J, b x) * R ^ k,
    mul_nonneg (tsum_nonneg (fun x => by dsimp [b]; positivity)) (pow_nonneg hR k), ?_⟩
  intro f a ha t ht
  let S : ℝ := SchwartzMap.seminorm ℝ k 0 f
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hmajor (x : J) :
      ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖ ≤
        (R ^ k * S * (t ^ N)⁻¹) * b x := by
    have hx : (x.val : mixedSpace K) ≠ 0 := by
      intro h
      exact x.property (Subtype.ext h)
    have hnx : 0 < ‖(x.val : mixedSpace K)‖ := norm_pos_iff.mpr hx
    have hbase : ‖(x.val : mixedSpace K)‖ ≤
        R * ‖(a : mixedSpace K) * (x.val : mixedSpace K)‖ := by
      calc
        _ = ‖((a⁻¹ : (mixedSpace K)ˣ) : mixedSpace K) *
            ((a : mixedSpace K) * (x.val : mixedSpace K))‖ := by
              rw [Units.inv_mul_cancel_left]
        _ ≤ ‖((a⁻¹ : (mixedSpace K)ˣ) : mixedSpace K)‖ *
            ‖(a : mixedSpace K) * (x.val : mixedSpace K)‖ := norm_mul_le _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    have hp := pow_le_pow_left₀ (norm_nonneg (x.val : mixedSpace K)) hbase k
    rw [mul_pow] at hp
    have hs := f.norm_pow_mul_le_seminorm ℝ k
      (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))
    rw [_root_.norm_smul, Real.norm_eq_abs, abs_of_pos ht0, mul_pow] at hs
    have hNk : t ^ N ≤ t ^ k := pow_le_pow_right₀ ht (by dsimp [k]; omega)
    have hs' : ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖ *
        (t ^ N * ‖(x.val : mixedSpace K)‖ ^ k) ≤ R ^ k * S := by
      calc
        _ ≤ ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖ *
          (t ^ k * (R ^ k * ‖(a : mixedSpace K) * (x.val : mixedSpace K)‖ ^ k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hNk hp (pow_nonneg hnx.le k) (pow_nonneg ht0.le k))
              (norm_nonneg _)
        _ = R ^ k * (t ^ k * ‖(a : mixedSpace K) * (x.val : mixedSpace K)‖ ^ k *
          ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hs (pow_nonneg hR k)
    have he : (R ^ k * S * (t ^ N)⁻¹) * b x =
        (R ^ k * S) / (t ^ N * ‖(x.val : mixedSpace K)‖ ^ k) := by
      simp only [b, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    rw [he]
    exact (le_div_iff₀ (mul_pos (pow_pos ht0 N) (pow_pos hnx k))).mpr hs'
  have hb' : Summable (fun x : J => (R ^ k * S * (t ^ N)⁻¹) * b x) := hb.mul_left _
  have hf : Summable (fun x : J =>
      ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖) :=
    hb'.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∑' x : J, (R ^ k * S * (t ^ N)⁻¹) * b x := hf.tsum_le_tsum hmajor hb'
    _ = _ := by rw [hb.tsum_mul_left]; dsimp [S]; ring

/-- Compactness supplies the inverse-norm bound; it is not a hypothesis
about decay or test continuity. The finite support ideal stays fixed. -/
theorem actual_ideal_compact_unit_dilation_uniform
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : ℕ)
    (U : Set (mixedSpace K)ˣ) (hU : IsCompact U) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(mixedSpace K, ℂ), ∀ a ∈ U, ∀ t : ℝ, 1 ≤ t →
      Summable (fun x : {x : idealLattice K I // x ≠ 0} =>
        ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖) ∧
      (∑' x : {x : idealLattice K I // x ≠ 0},
        ‖f (t • ((a : mixedSpace K) * (x.val : mixedSpace K)))‖) ≤
        C * SchwartzMap.seminorm ℝ k 0 f * (t ^ N)⁻¹ := by
  have hc : Continuous (fun a : (mixedSpace K)ˣ =>
      ((a⁻¹ : (mixedSpace K)ˣ) : mixedSpace K)) :=
    Units.continuous_val.comp continuous_inv
  obtain ⟨R, hR⟩ := hU.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨k, C, hC, h⟩ := actual_ideal_unit_dilation_uniform K I N (max R 0)
    (le_max_right _ _)
  exact ⟨k, C, hC, fun f a ha t ht => h f a ((hR a ha).trans (le_max_left _ _)) t ht⟩

end Masullo.IdealUnitDilationUniform

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

namespace Masullo.IdealUnitDilationUniform
open Masullo.HomeomorphMixedSpace
variable (K : Type*) [Field K] [NumberField K]

/-- Uniformity for actual original ideles, using their native topology.
The actual lattice is fixed; varying finite support still requires attachment. -/
theorem actual_ideal_compact_idele_dilation_uniform
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (N : ℕ)
    (U : Set (AdeleRing (𝓞 K) K)ˣ) (hU : IsCompact U) :
    ∃ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ f : 𝓢(mixedSpace K, ℂ), ∀ a ∈ U, ∀ t : ℝ, 1 ≤ t →
      Summable (fun x : {x : idealLattice K I // x ≠ 0} =>
        ‖f (t • (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.1 *
          (x.val : mixedSpace K)))‖) ∧
      (∑' x : {x : idealLattice K I // x ≠ 0},
        ‖f (t • (InfiniteAdeleRing.ringEquiv_mixedSpace K a.val.1 *
          (x.val : mixedSpace K)))‖) ≤
        C * SchwartzMap.seminorm ℝ k 0 f * (t ^ N)⁻¹ := by
  obtain ⟨k, C, hC, h⟩ := actual_ideal_compact_unit_dilation_uniform K I N
    (archPart '' U) (hU.image continuous_archPart)
  exact ⟨k, C, hC, fun f a ha t ht => h f (archPart a) ⟨a, ha, rfl⟩ t ht⟩

end Masullo.IdealUnitDilationUniform

namespace Masullo.CompactSupportedThetaUniform
open NumberField NumberField.mixedEmbedding Filter Topology Set Masullo.IdealUnitDilationUniform Masullo.SupportedPoints
open Masullo.HomeomorphMixedSpace
open scoped SchwartzMap nonZeroDivisors NumberField.AdeleRing
variable (F : Type*) [Field F] [NumberField F]

/-- Arbitrary compact finite supports have uniform absolute theta decay over
compact ORIGINAL idele families. No decay or summability premise is supplied. -/
theorem compact_supported_theta_uniform
    (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) (N : ℕ) :
    ∃ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ f : 𝓢(mixedSpace F, ℂ), ∀ a ∈ U, ∀ t : ℝ, 1 ≤ t →
      Summable (fun ξ : supportedPoints F C a =>
        ‖f (t • ((archPart a).val * mixedEmbedding F ξ.val))‖) ∧
      (∑' ξ : supportedPoints F C a,
        ‖f (t • ((archPart a).val * mixedEmbedding F ξ.val))‖) ≤
        B * SchwartzMap.seminorm ℝ k 0 f * (t ^ N)⁻¹ := by
  classical
  obtain ⟨d,hd⟩ := compact_support_integer_embedding F C hC U hU
  have hd0 : algebraMap (𝓞 F) F d.val ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr
      (nonZeroDivisors.ne_zero d.property)
  let u : (mixedSpace F)ˣ := Units.map (mixedEmbedding F).toMonoidHom
    (Units.mk0 (algebraMap (𝓞 F) F d.val) hd0)
  let V : Set (mixedSpace F)ˣ := (fun a : (AdeleRing (𝓞 F) F)ˣ => archPart a * u⁻¹) '' U
  have hV : IsCompact V := hU.image (continuous_archPart.mul continuous_const)
  obtain ⟨k,B,hB,h⟩ := actual_ideal_compact_unit_dilation_uniform F 1 N V hV
  refine ⟨k,B,hB,?_⟩
  intro f a ha t ht
  obtain ⟨e,he⟩ := hd a ha
  let E : supportedPoints F C a → {x : idealLattice F 1 // x ≠ 0} := fun ξ =>
    ⟨⟨mixedEmbedding F (algebraMap (𝓞 F) F (e ξ).val),
      (mem_idealLattice F 1).mpr ⟨_,
        (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mpr ⟨(e ξ).val,rfl⟩,rfl⟩⟩,
      by
        intro hz
        have hz' : mixedEmbedding F (algebraMap (𝓞 F) F (e ξ).val) = 0 :=
          congrArg (fun x : idealLattice F 1 => (x : mixedSpace F)) hz
        have hr : algebraMap (𝓞 F) F (e ξ).val = 0 :=
          (map_eq_zero_iff _ (mixedEmbedding_injective F)).mp hz'
        exact (e ξ).property ((IsFractionRing.injective (𝓞 F) F)
          (hr.trans (map_zero _).symm))⟩
  have hE : Function.Injective E := by
    intro ξ η hh
    apply e.injective
    apply Subtype.ext
    apply IsFractionRing.injective (𝓞 F) F
    apply mixedEmbedding_injective F
    exact congrArg (fun x : {x : idealLattice F 1 // x ≠ 0} =>
      (x.val : mixedSpace F)) hh
  have hcoord (ξ : supportedPoints F C a) :
      (archPart a * u⁻¹).val * ((E ξ).val : mixedSpace F) =
        (archPart a).val * mixedEmbedding F ξ.val := by
    change (archPart a).val * (u⁻¹).val *
      mixedEmbedding F (algebraMap (𝓞 F) F (e ξ).val) = _
    rw [he ξ, map_mul, mul_assoc]
    have hu : u.val = mixedEmbedding F (algebraMap (𝓞 F) F d.val) := rfl
    rw [← hu, ← mul_assoc (u⁻¹).val, Units.inv_mul, one_mul]
  obtain ⟨hs,hb⟩ := h f (archPart a * u⁻¹) ⟨a,ha,rfl⟩ t ht
  have hs' : Summable (fun ξ : supportedPoints F C a =>
      ‖f (t • ((archPart a).val * mixedEmbedding F ξ.val))‖) := by
    simpa only [Function.comp_def,hcoord] using hs.comp_injective hE
  refine ⟨hs',le_trans ?_ hb⟩
  exact Summable.tsum_le_tsum_of_inj E hE (fun _ _ => norm_nonneg _)
    (fun ξ => by rw [hcoord]) hs' hs

end Masullo.CompactSupportedThetaUniform

namespace Masullo.CompactSupportedThetaUniform
open Masullo.HomeomorphMixedSpace Masullo.SupportedPoints NumberField NumberField.mixedEmbedding
open scoped SchwartzMap nonZeroDivisors NumberField.AdeleRing
variable (F : Type*) [Field F] [NumberField F]
/-- Actual full F× theta series for a bounded finite factor supported in C. -/
theorem full_supported_theta_absolute
    (C : Set (FiniteAdeleRing (𝓞 F) F)) (hC : IsCompact C)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsCompact U) (N : ℕ) :
    ∃ k : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ (f : 𝓢(mixedSpace F, ℂ)) (a : (AdeleRing (𝓞 F) F)ˣ), a ∈ U →
      ∀ t : ℝ, 1 ≤ t → ∀ (ψ : FiniteAdeleRing (𝓞 F) F → ℂ) (M : ℝ),
      0 ≤ M → (∀ y ∉ C, ψ y = 0) → (∀ y ∈ C, ‖ψ y‖ ≤ M) →
      let P := fun ξ : {ξ : F // ξ ≠ 0} =>
        ψ (a.val.2 * algebraMap F _ ξ.val) *
          f (t • ((archPart a).val * mixedEmbedding F ξ.val))
      Summable (fun ξ => ‖P ξ‖) ∧
        (∑' ξ, ‖P ξ‖) ≤ M * (B * SchwartzMap.seminorm ℝ k 0 f * (t^N)⁻¹) := by
  classical
  obtain ⟨k,B,hB,h⟩ := compact_supported_theta_uniform F C hC U hU N
  refine ⟨k,B,hB,?_⟩
  intro f a ha t ht ψ M hM hzero hbound
  dsimp only
  let P := fun ξ : {ξ : F // ξ ≠ 0} =>
    ψ (a.val.2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ.val) *
      f (t • ((archPart a).val * mixedEmbedding F ξ.val))
  let E : supportedPoints F C a → {ξ : F // ξ ≠ 0} :=
    fun ξ => ⟨ξ.val,ξ.property.1⟩
  have hE : Function.Injective E := by
    intro ξ η he
    exact Subtype.ext (congrArg (fun x : {ξ : F // ξ ≠ 0} => x.val) he)
  have hout (ξ : {ξ : F // ξ ≠ 0}) (hx : ξ ∉ Set.range E) : P ξ = 0 := by
    have hc : a.val.2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ.val ∉ C := by
      intro hh
      exact hx ⟨⟨ξ.val,ξ.property,hh⟩,rfl⟩
    dsimp [P]
    rw [hzero _ hc,zero_mul]
  obtain ⟨hs,hb⟩ := h f a ha t ht
  have hmajor (ξ : supportedPoints F C a) : ‖P (E ξ)‖ ≤
      M * ‖f (t • ((archPart a).val * mixedEmbedding F ξ.val))‖ := by
    dsimp [P,E]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound _ ξ.property.2) (norm_nonneg _)
  have hs' : Summable (fun ξ : supportedPoints F C a => ‖P (E ξ)‖) :=
    (hs.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hmajor
  have hall : Summable (fun ξ => ‖P ξ‖) :=
    (hE.summable_iff (fun ξ hx => by rw [hout ξ hx]; exact norm_zero)).mp hs'
  refine ⟨hall,?_⟩
  change (∑' ξ, ‖P ξ‖) ≤ _
  rw [← hE.tsum_eq (fun ξ hx => by
    by_contra hn
    exact hx (by change ‖P ξ‖ = 0; rw [hout ξ hn]; exact norm_zero))]
  exact (hs'.tsum_le_tsum hmajor (hs.mul_left M)).trans
    ((by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hb hM))
end Masullo.CompactSupportedThetaUniform

/- Insert after JThetaDefinitions and JThetaSummabilityCore.
   Applies the supplied compact-support/lattice estimate to the exact
   finite tensor definition of original Schwartz--Bruhat tests. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleTheta
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open Masullo.CompactSupportedThetaUniform Masullo.HomeomorphMixedSpace
open scoped NumberField BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Every original Schwartz--Bruhat test has an absolutely convergent
principal-idele series. This discharges the source summability field from
the actual test-space condition, without a convergence hypothesis. -/
theorem originalBruhat_theta_summable (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) (x : HeckeIdeles K) :
    Summable (fun u : Kˣ => f ((principalIdele K u * x).val)) := by
  rcases hf with ⟨n, p, q, hq, he⟩
  have hi (i : Fin n) : Summable (fun u : Kˣ =>
      p i (InfiniteAdeleRing.ringEquiv_mixedSpace K (principalIdele K u * x).val.1) *
        q i (principalIdele K u * x).val.2) := by
    obtain ⟨M, hM⟩ := (hq i).1.continuous.bounded_above_of_compact_support (hq i).2
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    obtain ⟨k, B, hB, h⟩ := full_supported_theta_absolute K
      (tsupport (q i)) (hq i).2.isCompact {x} isCompact_singleton 0
    have hs := (h (p i) x (by simp) 1 le_rfl (q i) M hM0
      (fun y hy => by
        by_contra hny
        exact hy (subset_tsupport (q i) hny))
      (fun y _ => hM y)).1
    let E : Kˣ → {z : K // z ≠ 0} := fun u => ⟨u.val, u.ne_zero⟩
    have hE : Function.Injective E := by
      intro u v huv
      exact Units.ext (congrArg Subtype.val huv)
    have hu := hs.of_norm.comp_injective hE
    apply hu.congr
    intro u
    dsimp only [Function.comp_def, E]
    simp only [one_smul]
    change q i (x.val.2 * algebraMap K (FiniteAdeleRing (𝓞 K) K) (u : K)) *
        p i (InfiniteAdeleRing.ringEquiv_mixedSpace K x.val.1 * mixedEmbedding K (u : K)) =
      p i (InfiniteAdeleRing.ringEquiv_mixedSpace K
        (algebraMap K (InfiniteAdeleRing K) (u : K) * x.val.1)) *
        q i (algebraMap K (FiniteAdeleRing (𝓞 K) K) (u : K) * x.val.2)
    have harch : InfiniteAdeleRing.ringEquiv_mixedSpace K
        (algebraMap K (InfiniteAdeleRing K) (u : K)) = mixedEmbedding K (u : K) := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace K), harch,
      mul_comm (mixedEmbedding K (u : K))]
    rw [mul_comm (algebraMap K (FiniteAdeleRing (𝓞 K) K) (u : K))]
    exact mul_comm _ _
  have hs := summable_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [he] using hs

end
end JThetaAttachment

/- Insert after JAllCharacterSource and JOriginalThetaSummable.
   Convergence is now derived, while the remaining Hilbert admission is explicit. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- Actual original-source admission from the original two moments and the
specified Hilbert membership. The principal-series convergence is proved
from Schwartz--Bruhat membership, not passed as an application hypothesis. -/
def admitFullSourceOfMemLp (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ)
    (f : HeckeAdeles K → ℂ) (hf : IsOriginalBruhat K f)
    (h0 : f 0 = 0) (hi : Integrable f addHaar)
    (hI : ∫ x, f x ∂addHaar = 0)
    (hmem : MemLp (normalizedTheta K a alpha s f) 2 mu) :
    AdmittedFullSource K addHaar mu a alpha s where
  test := f
  bruhat := hf
  zero_value := h0
  integrable := hi
  zero_integral := hI
  summable := originalBruhat_theta_summable K f hf
  memLp := hmem

/-- Exact characterization of the full admitted test family: summability
is no longer an independent admission obligation. -/
theorem full_source_admission_iff (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ)
    (f : HeckeAdeles K → ℂ) :
    (∃ F : AdmittedFullSource K addHaar mu a alpha s, F.test = f) ↔
      IsOriginalBruhat K f ∧ f 0 = 0 ∧ Integrable f addHaar ∧
      (∫ x, f x ∂addHaar) = 0 ∧ MemLp (normalizedTheta K a alpha s f) 2 mu := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.bruhat, F.zero_value, F.integrable, F.zero_integral, F.memLp⟩
  · rintro ⟨hf, h0, hi, hI, hmem⟩
    exact ⟨admitFullSourceOfMemLp K addHaar mu a alpha s f hf h0 hi hI hmem, rfl⟩

/-- The constructed original test maps to the common full theta closure,
with its actual normalized-theta Lp representative. -/
theorem original_test_mem_fullThetaClosure (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ)
    (f : HeckeAdeles K → ℂ) (hf : IsOriginalBruhat K f)
    (h0 : f 0 = 0) (hi : Integrable f addHaar)
    (hI : ∫ x, f x ∂addHaar = 0)
    (hmem : MemLp (normalizedTheta K a alpha s f) 2 mu) :
    hmem.toLp (normalizedTheta K a alpha s f) ∈
      fullThetaClosure K addHaar mu a alpha s :=
  fullSourceVector_mem_closure K
    (admitFullSourceOfMemLp K addHaar mu a alpha s f hf h0 hi hI hmem)

end
end JThetaAttachment

/- Insert after JThetaDefinitions and JThetaSummabilityCore.
   Original Haar integrability is transported through the actual mixed-space
   homeomorphism; the original additive Haar is never normalized to probability. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH NumberField NumberField.mixedEmbedding IsDedekindDomain
open Masullo.HomeomorphMixedSpace
open scoped NumberField NNReal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def thetaMixedAdele : HeckeAdeles K ≃ₜ+
    (mixedSpace K × FiniteAdeleRing (𝓞 K) K) where
  toFun x := (homeomorphMixedSpace K x.1, x.2)
  invFun x := ((homeomorphMixedSpace K).symm x.1, x.2)
  left_inv x := by
    apply Prod.ext
    · exact (homeomorphMixedSpace K).symm_apply_apply x.1
    · rfl
  right_inv x := by
    apply Prod.ext
    · exact (homeomorphMixedSpace K).apply_symm_apply x.1
    · rfl
  map_add' x y := by
    apply Prod.ext
    · exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace K) x.1 y.1
    · rfl
  continuous_toFun := ((homeomorphMixedSpace K).continuous.comp continuous_fst).prodMk continuous_snd
  continuous_invFun := ((homeomorphMixedSpace K).symm.continuous.comp continuous_fst).prodMk continuous_snd

theorem thetaFiniteEmbedding : Topology.IsClosedEmbedding
    (fun y : FiniteAdeleRing (𝓞 K) K => ((0 : InfiniteAdeleRing K), y) :
      FiniteAdeleRing (𝓞 K) K → HeckeAdeles K) := by
  letI : T2Space (InfiniteAdeleRing K) :=
    inferInstanceAs (T2Space (∀ w : InfinitePlace K, w.Completion))
  have he : Topology.IsEmbedding
      (fun y : FiniteAdeleRing (𝓞 K) K => ((0 : InfiniteAdeleRing K), y)) :=
    Topology.IsEmbedding.of_comp (continuous_const.prodMk continuous_id) continuous_snd
      (Homeomorph.refl (FiniteAdeleRing (𝓞 K) K)).isEmbedding
  refine ⟨he, ?_⟩
  have hr : Set.range (fun y : FiniteAdeleRing (𝓞 K) K => ((0 : InfiniteAdeleRing K), y)) =
      {z : HeckeAdeles K | z.1 = 0} := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rfl
    · intro hz
      exact ⟨z.2, Prod.ext hz.symm rfl⟩
  rw [hr]
  exact isClosed_eq continuous_fst continuous_const

variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]

/-- All finite-tensor original Schwartz--Bruhat tests are integrable for
every original additive Haar measure, with its normalization retained. -/
theorem originalBruhat_integrable (addHaar : Measure (HeckeAdeles K))
    [addHaar.IsAddHaarMeasure] (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) : Integrable f addHaar := by
  letI : LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    inferInstanceAs (LocallyCompactSpace (HeckeAdeles K))
  letI : SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K) :=
    inferInstanceAs (SecondCountableTopology (HeckeAdeles K))
  letI : LocallyCompactSpace (FiniteAdeleRing (𝓞 K) K) :=
    (thetaFiniteEmbedding K).locallyCompactSpace
  letI : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
    (thetaFiniteEmbedding K).isEmbedding.secondCountableTopology
  borelize (FiniteAdeleRing (𝓞 K) K)
  haveI : MeasurableAdd₂ (FiniteAdeleRing (𝓞 K) K) :=
    ⟨(continuous_fst.add continuous_snd).measurable⟩
  haveI : MeasurableAdd₂ (mixedSpace K) :=
    ⟨(continuous_fst.add continuous_snd).measurable⟩
  haveI : SigmaFinite (volume : Measure (mixedSpace K)) := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 K) K)) :=
    sigmaFinite_of_locallyFinite
  haveI : (volume : Measure (mixedSpace K)).IsAddHaarMeasure := inferInstance
  haveI : (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 K) K)).IsAddHaarMeasure := inferInstance
  let nu : Measure (mixedSpace K × FiniteAdeleRing (𝓞 K) K) :=
    (volume : Measure (mixedSpace K)).prod (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 K) K))
  let eta : Measure (HeckeAdeles K) := nu.map (thetaMixedAdele K).symm
  haveI : nu.IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (mixedSpace K))
      (Measure.addHaar : Measure (FiniteAdeleRing (𝓞 K) K))
  haveI : eta.IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map nu (thetaMixedAdele K).symm
  rcases hf with ⟨n, p, q, hq, he⟩
  have ht (i : Fin n) : Integrable
      (fun x : HeckeAdeles K => p i (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q i x.2) eta := by
    apply (thetaMixedAdele K).symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding.integrable_map_iff.mpr
    have hprod : Integrable (fun z : mixedSpace K × FiniteAdeleRing (𝓞 K) K => p i z.1 * q i z.2) nu :=
      (p i).integrable.mul_prod ((hq i).1.continuous.integrable_of_hasCompactSupport (hq i).2)
    convert hprod using 1
    funext z
    change p i (InfiniteAdeleRing.ringEquiv_mixedSpace K ((homeomorphMixedSpace K).symm z.1)) *
      q i z.2 = p i z.1 * q i z.2
    rw [← homeomorphMixedSpace_apply, Homeomorph.apply_symm_apply]
  have hs : Integrable f eta := by
    have hh := integrable_finset_sum Finset.univ (fun i _ => ht i)
    have heq : f = fun x => ∑ i, p i (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q i x.2 :=
      funext he
    rw [heq]
    exact hh
  rw [Measure.isAddLeftInvariant_eq_smul addHaar eta]
  exact hs.smul_measure_nnreal

end
end JThetaAttachment

/- Insert after JOriginalIntegrable and JAdmissionConstructors.
   The arithmetic source map is defined on original tests. O owns projection
   transport from the exact range equality at the end of this fragment. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleTheta Masullo.IdeleClassGeometry
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open Masullo.HomeomorphMixedSpace
open scoped NumberField BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

theorem originalBruhat_zero : IsOriginalBruhat K (0 : HeckeAdeles K → ℂ) := by
  exact ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by intro x; simp⟩

theorem originalBruhat_add (f g : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) (hg : IsOriginalBruhat K g) :
    IsOriginalBruhat K (f + g) := by
  rcases hf with ⟨n, p, q, hq, he⟩
  rcases hg with ⟨m, p', q', hq', he'⟩
  refine ⟨n+m, Fin.addCases p p', Fin.addCases q q', ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.addCases_left] using hq j
    · simpa only [Fin.addCases_right] using hq' j
  · intro x
    simp only [Pi.add_apply, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    rw [he, he']

theorem originalBruhat_smul (c : ℂ) (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) : IsOriginalBruhat K (c • f) :=
  originalBruhat_const_mul K c f hf

/-- Continuity is proved for the literal finite-tensor source definition. -/
theorem originalBruhat_continuous (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) : Continuous f := by
  rcases hf with ⟨n, p, q, hq, he⟩
  rw [funext he]
  apply continuous_finset_sum
  intro i hi
  exact ((p i).continuous.comp
    ((homeomorphMixedSpace K).continuous.comp continuous_fst)).mul
    ((hq i).1.continuous.comp continuous_snd)

/-- The genuine theta sum is additive on original tests, with convergence
discharged by the previously checked lattice theorem. -/
theorem classTheta_add_original (f g : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) (hg : IsOriginalBruhat K g) :
    classTheta K (f+g) = classTheta K f + classTheta K g := by
  funext x
  induction x using Quotient.inductionOn with
  | h y =>
    exact (originalBruhat_theta_summable K f hf y).tsum_add
      (originalBruhat_theta_summable K g hg y)

theorem normalizedTheta_zero (a alpha s : ℝ) :
    normalizedTheta K a alpha s (0 : HeckeAdeles K → ℂ) = 0 := by
  funext x
  induction x using Quotient.inductionOn with
  | h y => simp [normalizedTheta, classTheta, ideleTheta]

theorem normalizedTheta_add_original (a alpha s : ℝ)
    (f g : HeckeAdeles K → ℂ) (hf : IsOriginalBruhat K f)
    (hg : IsOriginalBruhat K g) :
    normalizedTheta K a alpha s (f+g) =
      normalizedTheta K a alpha s f + normalizedTheta K a alpha s g := by
  funext x
  simp only [normalizedTheta, classTheta_add_original K f g hf hg, Pi.add_apply, mul_add]

theorem normalizedTheta_smul (a alpha s : ℝ) (c : ℂ)
    (f : HeckeAdeles K → ℂ) :
    normalizedTheta K a alpha s (c • f) = c • normalizedTheta K a alpha s f := by
  funext x
  change _ * _ * classTheta K (fun y => c * f y) x = c * (_ * _ * classTheta K f x)
  rw [classTheta_const_mul]
  ring

variable [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ)

/-- The original two-moment test domain with exactly the still-explicit
weighted Hilbert admission. Neither integrability nor theta convergence
is an extra field: both are proved for original Bruhat tests. -/
def originalTestDomain : Submodule ℂ (HeckeAdeles K → ℂ) where
  carrier := {f | IsOriginalBruhat K f ∧ f 0 = 0 ∧
    (∫ x, f x ∂addHaar) = 0 ∧ MemLp (normalizedTheta K a alpha s f) 2 mu}
  zero_mem' := by
    refine ⟨originalBruhat_zero K, rfl, ?_, ?_⟩
    · simp
    · rw [normalizedTheta_zero]
      simp
  add_mem' := by
    intro f g hf hg
    refine ⟨originalBruhat_add K f g hf.1 hg.1, ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, hf.2.1, hg.2.1, add_zero]
    · change (∫ x, f x + g x ∂addHaar) = 0
      rw [integral_add (originalBruhat_integrable K addHaar f hf.1)
        (originalBruhat_integrable K addHaar g hg.1), hf.2.2.1, hg.2.2.1, add_zero]
    · rw [normalizedTheta_add_original K a alpha s f g hf.1 hg.1]
      exact hf.2.2.2.add hg.2.2.2
  smul_mem' := by
    intro c f hf
    refine ⟨originalBruhat_smul K c f hf.1, ?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, hf.2.1, smul_zero]
    · change (∫ x, c • f x ∂addHaar) = 0
      rw [integral_smul, hf.2.2.1, smul_zero]
    · rw [normalizedTheta_smul]
      exact hf.2.2.2.const_smul c

def admitOriginalTest
    (f : originalTestDomain K addHaar mu a alpha s) :
    AdmittedFullSource K addHaar mu a alpha s :=
  admitFullSourceOfMemLp K addHaar mu a alpha s f f.property.1 f.property.2.1
    (originalBruhat_integrable K addHaar f f.property.1)
    f.property.2.2.1 f.property.2.2.2

/-- The actual normalized principal-idele theta map, linear on original
tests. Its codomain representative is the already shared sourceVector. -/
def originalThetaLinear : originalTestDomain K addHaar mu a alpha s →ₗ[ℂ] Lp ℂ 2 mu where
  toFun f := fullSourceVector K (admitOriginalTest K addHaar mu a alpha s f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f+g).property.2.2.2.coeFn_toLp,
      f.property.2.2.2.coeFn_toLp, g.property.2.2.2.coeFn_toLp,
      Lp.coeFn_add (fullSourceVector K (admitOriginalTest K addHaar mu a alpha s f))
        (fullSourceVector K (admitOriginalTest K addHaar mu a alpha s g))]
      with x hfg hf hg hsum
    rw [hsum]
    simp only [Pi.add_apply]
    dsimp only [fullSourceVector, originalSourceVector, admitOriginalTest, admitFullSourceOfMemLp]
    rw [hfg, hf, hg]
    exact congrFun (normalizedTheta_add_original K a alpha s f g f.property.1 g.property.1) x
  map_smul' c f := by
    change fullSourceVector K (admitOriginalTest K addHaar mu a alpha s (c • f)) =
      c • fullSourceVector K (admitOriginalTest K addHaar mu a alpha s f)
    apply Lp.ext
    filter_upwards [(c • f).property.2.2.2.coeFn_toLp,
      f.property.2.2.2.coeFn_toLp,
      Lp.coeFn_smul c (fullSourceVector K (admitOriginalTest K addHaar mu a alpha s f))]
      with x hcf hf hsmul
    rw [hsmul]
    simp only [Pi.smul_apply]
    dsimp only [fullSourceVector, originalSourceVector, admitOriginalTest, admitFullSourceOfMemLp]
    rw [hcf, hf]
    exact congrFun (normalizedTheta_smul K a alpha s c f) x

/-- No new source closure is introduced: the map on the literal original
test domain has exactly the previously admitted arithmetic image. -/
theorem originalThetaLinear_range :
    Set.range (originalThetaLinear K addHaar mu a alpha s) =
      Set.range (fullSourceVector K (addHaar := addHaar) (mu := mu)
        (a := a) (alpha := alpha) (s := s)) := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨admitOriginalTest K addHaar mu a alpha s f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨⟨f.test, f.bruhat, f.zero_value, f.zero_integral, f.memLp⟩, rfl⟩

end
end JThetaAttachment

/- Insert after JOriginalLinearTheta and OAllCharacterClosure.
   The original domain already imposes both original moments. Its remaining
   weighted MemLp condition is explicit in J.originalTestDomain. -/
namespace OOriginalThetaProjection
open MeasureTheory MasulloGRH JThetaAttachment OAllCharacterClosure Filter
open Masullo.NativeRep Masullo.IdeleClassGeometry PIntervalConvolution
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ)

/-- The admitted source span is exactly the range of the actual linear
principal-theta map on original tests, not merely the span of a new family. -/
theorem originalThetaLinear_range_eq_fullSourceSpan :
    LinearMap.range (originalThetaLinear K addHaar mu a alpha s) =
      fullSourceSpan K addHaar mu a alpha s := by
  have hspan : Submodule.span ℂ (Set.range (originalThetaLinear K addHaar mu a alpha s)) =
      LinearMap.range (originalThetaLinear K addHaar mu a alpha s) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨f, rfl⟩
      exact ⟨f, rfl⟩
    · rintro y ⟨f, rfl⟩
      exact Submodule.subset_span ⟨f, rfl⟩
  rw [← hspan, originalThetaLinear_range]
  rfl

/-- Exact closure identification on the single shared source definition. -/
theorem originalThetaLinear_closure_eq :
    (LinearMap.range (originalThetaLinear K addHaar mu a alpha s)).topologicalClosure =
      fullThetaClosure K addHaar mu a alpha s := by
  rw [originalThetaLinear_range_eq_fullSourceSpan]
  rfl

/-- Every retained character component lies in the closure of this same
original-test theta map. No decomposition/completeness premise is added. -/
theorem character_closure_le_originalThetaLinear (chi : UnitaryHeckeCharacter K) :
    thetaClosure K addHaar mu chi a alpha s ≤
      (LinearMap.range (originalThetaLinear K addHaar mu a alpha s)).topologicalClosure := by
  rw [originalThetaLinear_closure_eq]
  exact thetaClosure_le_fullThetaClosure K addHaar mu chi a alpha s

/-- Genuine geometric orthogonal projection, with its instance transported
through topological closure rather than supplied as an application premise. -/
theorem originalThetaLinear_projection_eq :
    (LinearMap.range (originalThetaLinear K addHaar mu a alpha s)).topologicalClosure.starProjection =
      (fullThetaClosure K addHaar mu a alpha s).starProjection := by
  exact congrArg
    (fun W : Submodule ℂ (Lp ℂ 2 mu) => W.topologicalClosure.starProjection)
    (originalThetaLinear_range_eq_fullSourceSpan K addHaar mu a alpha s)

/-- The spectral projector is the actual orthogonal complement of the
original-theta range closure. -/
theorem originalThetaLinear_spectralProjection_eq :
    (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (LinearMap.range (originalThetaLinear K addHaar mu a alpha s)).topologicalClosure.starProjection =
      (fullThetaClosure K addHaar mu a alpha s)ᗮ.starProjection := by
  rw [originalThetaLinear_projection_eq]
  apply ContinuousLinearMap.ext
  intro F
  simp only [Submodule.starProjection_orthogonal_val, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]

/-- Every original test in the stated domain is fixed by the actual
geometric projection; weighted membership is retained in that domain. -/
theorem original_test_geometric_projection
    (f : originalTestDomain K addHaar mu a alpha s) :
    (fullThetaClosure K addHaar mu a alpha s).starProjection
      (originalThetaLinear K addHaar mu a alpha s f) =
        originalThetaLinear K addHaar mu a alpha s f :=
  actual_full_theta_projected K addHaar mu a alpha s
    (admitOriginalTest K addHaar mu a alpha s f)

/-- Finite subsets of the images of the actual original-test linear map
exhaust the geometric and spectral projections after any bounded operator. -/
theorem original_test_projection_exhaustion
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (F : Lp ℂ 2 mu) :
    let E := fun T : Finset (Lp ℂ 2 mu) => Submodule.span ℂ
      ((T : Set (Lp ℂ 2 mu)) ∩ Set.range (originalThetaLinear K addHaar mu a alpha s))
    ∃ p : Finset (Lp ℂ 2 mu) → Lp ℂ 2 mu,
      (∀ T, ∃ hp : (E T).HasOrthogonalProjection,
        p T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (E T) hp (A F)) ∧
      Tendsto p atTop (𝓝 ((fullThetaClosure K addHaar mu a alpha s).starProjection (A F))) ∧
      Tendsto (fun T => A F - p T) atTop
        (𝓝 (((fullThetaClosure K addHaar mu a alpha s)ᗮ.starProjection.comp A) F)) := by
  rw [originalThetaLinear_range]
  obtain ⟨p, hp, hgeom, hspec⟩ :=
    actual_full_theta_source_exhaustion K addHaar mu a alpha s (A F)
  refine ⟨p, hp, hgeom, ?_⟩
  simpa only [Submodule.starProjection_orthogonal_val, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hspec

/-- The established source-map presentation and the original-test theta map
have exactly the same output family. This transports every finite kernel
cutoff, not just their limiting closed subspace. -/
theorem fullSourceMap_setRange_eq_originalThetaLinear :
    Set.range (fullSourceMap K addHaar mu a alpha s) =
      Set.range (originalThetaLinear K addHaar mu a alpha s) := by
  change (LinearMap.range (fullSourceMap K addHaar mu a alpha s) : Set (Lp ℂ 2 mu)) =
    (LinearMap.range (originalThetaLinear K addHaar mu a alpha s) : Set (Lp ℂ 2 mu))
  rw [fullSourceMap_range, originalThetaLinear_range_eq_fullSourceSpan]

/-- D's kernel span and Q's cutoff span are both this same expression.
Their finite source spaces are literally spanned by original-test theta
vectors, with no cofinality replacement or density assumption. -/
theorem original_test_finite_span_eq (T : Finset (Lp ℂ 2 mu)) :
    Submodule.span ℂ ((T : Set (Lp ℂ 2 mu)) ∩
      Set.range (fullSourceMap K addHaar mu a alpha s)) =
    Submodule.span ℂ ((T : Set (Lp ℂ 2 mu)) ∩
      Set.range (originalThetaLinear K addHaar mu a alpha s)) := by
  rw [fullSourceMap_setRange_eq_originalThetaLinear]


end
end OOriginalThetaProjection

/- Append after OThetaClosure.lean. Uses the common interval operator, both
sharp tests, and the original arithmetic theta normalization. -/
namespace OArithmeticClosure
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry JThetaAttachment Filter
open PIntervalConvolution Masullo.IdeleTheta Masullo.GenuineMellinJet
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- For a nonsymmetric interval the arithmetic theta exponent is shifted by
the midpoint. The physical parameter a itself is retained explicitly. -/
theorem interval_normalizedTheta (a l r s : ℝ) (hlr : l ≤ r)
    (f : HeckeAdeles K → ℂ) (x : HeckeIdeleClasses K) :
    (intervalHalfWeight l r s (classLog K x) : ℂ) *
      (Real.exp (a * classLog K x) : ℂ) * classTheta K f x =
      normalizedTheta K (a + (l+r)/2) ((r-l)/2) s f x := by
  rw [interval_halfWeight l r s _ hlr]
  unfold normalizedTheta
  have he : Real.exp ((a + (l+r)/2) * classLog K x) =
      Real.exp (((l+r)/2) * classLog K x) * Real.exp (a * classLog K x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  simp only [Complex.ofReal_mul]
  ring


end
end OArithmeticClosure

/- Insert after BOriginalHaarGramFragment, JOriginalLinearTheta and
   OArithmeticClosure.interval_normalizedTheta. This is the original-source
   factor application in B35 (35.6), on the one existing convolution entry. -/
namespace BSourceGram
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.IdeleTheta JThetaAttachment PIntervalConvolution
open scoped InnerProductSpace Matrix BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K))

/-- The original test supplies the physical theta representative, with the
actual interval half-weight and exactly the required midpoint shift. -/
theorem originalThetaLinear_interval_ae (a l r s : ℝ) (hlr : l ≤ r)
    (f : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s) :
    (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f :
      HeckeIdeleClasses K → ℂ) =ᵐ[mu]
      (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
        ((Real.exp (a * classLog K x) : ℂ) * classTheta K f x)) := by
  filter_upwards [f.property.2.2.2.coeFn_toLp] with x hx
  change (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f) x = _ at hx
  rw [hx, ← OArithmeticClosure.interval_normalizedTheta K a l r s hlr f x]
  ring

/-- Dividing by the same half-weight returns the manuscript's actual theta
source, rather than an independently specified L2 representative. -/
theorem originalThetaLinear_physical_ae (a l r s : ℝ) (hlr : l ≤ r)
    (f : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s) :
    (fun x => (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f) x /
      (intervalHalfWeight l r s (classLog K x) : ℂ)) =ᵐ[mu]
      (fun x => (Real.exp (a * classLog K x) : ℂ) * classTheta K f x) := by
  filter_upwards [originalThetaLinear_interval_ae K addHaar mu a l r s hlr f]
    with x hx
  have hb : (intervalHalfWeight l r s (classLog K x) : ℂ) ≠ 0 := by
    have hp : 0 < intervalHalfWeight l r s (classLog K x) := by
      unfold intervalHalfWeight
      positivity
    exact_mod_cast ne_of_gt hp
  rw [hx]
  field_simp

/-- The Gram entries are the original weighted theta integrals. Both source
factors are the actual original tests, and the measure remains mu. -/
theorem originalThetaLinear_Gram (a l r s : ℝ) (hlr : l ≤ r)
    (f g : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s) :
    (∫ x, star ((Real.exp (a * classLog K x) : ℂ) * classTheta K f x) *
      ((Real.exp (a * classLog K x) : ℂ) * classTheta K g x) *
      (intervalHalfWeight l r s (classLog K x) : ℂ)^2 ∂mu) =
      inner ℂ (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f)
        (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s g) := by
  rw [← HNormalizedKernel.l2_inner_formula]
  apply integral_congr_ae
  filter_upwards [originalThetaLinear_interval_ae K addHaar mu a l r s hlr f,
    originalThetaLinear_interval_ae K addHaar mu a l r s hlr g] with x hf hg
  rw [hf, hg]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- The scalar convolution entry is the literal iterated theta integral in
B35 (35.6). Its inner and outer integrability are proved from the actual
convolution action. The arithmetic/physical mask stays on the incoming y. -/
theorem sourceConvolutionEntry_originalTheta
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (rho : HeckeIdeleClasses K → ℝ) (hm : Measurable rho)
    (hrho : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (f g : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s) :
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let theta := fun f : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s =>
      fun x => (Real.exp (a * classLog K x) : ℂ) * classTheta K f x
    (∀ x, Integrable (fun y => h (x*y⁻¹) * ((rho y : ℂ) * theta g y)) mu) ∧
    Integrable (fun x => (b x : ℂ)^2 * star (theta f x) *
      (∫ y, h (x*y⁻¹) * ((rho y : ℂ) * theta g y) ∂mu)) mu ∧
    sourceConvolutionEntry K mu l r s h rho
      (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f)
      (originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s g) =
      ∫ x, (b x : ℂ)^2 * star (theta f x) *
        (∫ y, h (x*y⁻¹) * ((rho y : ℂ) * theta g y) ∂mu) ∂mu := by
  dsimp only
  let U := originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f
  let V := originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s g
  have ha := sourceConvolutionEntry_eq K mu l r s hlr hs h hh hc rho hm hrho U V
  have hrow (x : HeckeIdeleClasses K) :
      (fun y => h (x*y⁻¹) * ((rho y : ℂ) * V y /
        (intervalHalfWeight l r s (classLog K y) : ℂ))) =ᵐ[mu]
      (fun y => h (x*y⁻¹) * ((rho y : ℂ) *
        ((Real.exp (a * classLog K y) : ℂ) * classTheta K g y))) := by
    filter_upwards [originalThetaLinear_physical_ae K addHaar mu a l r s hlr g]
      with y hy
    change V y / _ = _ at hy
    rw [mul_div_assoc, hy]
  have hi (x : HeckeIdeleClasses K) := integral_congr_ae (hrow x)
  have hout :
      (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) * star (U x) *
        (∫ y, h (x*y⁻¹) * ((rho y : ℂ) * V y /
          (intervalHalfWeight l r s (classLog K y) : ℂ)) ∂mu)) =ᵐ[mu]
      (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ)^2 *
        star ((Real.exp (a * classLog K x) : ℂ) * classTheta K f x) *
        (∫ y, h (x*y⁻¹) * ((rho y : ℂ) *
          ((Real.exp (a * classLog K y) : ℂ) * classTheta K g y)) ∂mu)) := by
    filter_upwards [originalThetaLinear_interval_ae K addHaar mu a l r s hlr f]
      with x hx
    change U x = _ at hx
    rw [hx, hi x]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring
  refine ⟨fun x => (ha.1 x).congr (hrow x), ha.2.1.congr hout, ?_⟩
  exact integral_congr_ae hout

end
end BSourceGram
/- Insert after BOriginalThetaEntriesFragment, BArithmeticSourceGramFragment,
   BOriginalHaarGramFragment and OOriginalThetaProjection. This applies the
   existing shell theorem to actual original-test factors, with no new kernel. -/
namespace BSourceGram
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.IdeleTheta JThetaAttachment PIntervalConvolution OAllCharacterClosure
open scoped InnerProductSpace Matrix BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K))
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- Actual original-test theta factors in the full source-Gram shell formula.
Every finite cutoff has such a frame, its original weighted Gram is invertible,
and its literal iterated theta entries give the SAME kernel diagonal and trace.
Weighted admission stays explicit in originalTestDomain. -/
theorem both_tests_original_theta_Gram_shells
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (v : ℕ → NumberField.FinitePlace K) (q : Fin 2)
    (T : Finset (Lp ℂ 2 mu)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    ∃ n : ℕ,
    ∃ f : Fin n → originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s,
      let u := fun i => originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s (f i)
      let theta := fun i x => (Real.exp (a * classLog K x) : ℂ) * classTheta K (f i) x
      (∀ i, u i ∈ T) ∧ LinearIndependent ℂ u ∧
      Submodule.span ℂ (Set.range u) = E ∧
      (∀ i j, (∫ x, star (theta i x) * theta j x * (b x : ℂ)^2 ∂mu) =
        inner ℂ (u i) (u j)) ∧
      IsUnit (Matrix.det (fun i j =>
        ∫ x, star (theta i x) * theta j x * (b x : ℂ)^2 ∂mu)) ∧
      let g := fun e => ∑ i, ∑ j, sourceGramInverse u j i *
        (∫ x, (b x : ℂ)^2 * star (theta i x) *
          (∫ y, h (x*y⁻¹) * ((p e y : ℂ) * theta j y) ∂mu) ∂mu)
      (∀ e, (∫ x, (p e x : ℂ) * DSourceKernel.finiteKernel mu b E A x x ∂mu) = g e) ∧
      HasSum g (Masullo.TraceClass.trace (E.starProjection.comp A)) ∧
      (∑' e, ‖g e‖) ≤ ∫ x, ‖DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  classical
  dsimp only
  obtain ⟨n, u, hmem, hli, hspan, hdet, hdiag, hsum, hbound⟩ :=
    both_tests_original_source_measured_Gram_shells K mu addHaar a l r s hlr hs
      phi hh hc v q T
  have ho (i : Fin n) :
      ∃ f : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s,
        originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f = u i := by
    have hi := (hmem i).2
    rw [OOriginalThetaProjection.fullSourceMap_setRange_eq_originalThetaLinear] at hi
    exact hi
  choose f hf using ho
  have hu : (fun i => originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s
      (f i)) = u := funext hf
  have hgram (i j : Fin n) :
      (∫ x, star ((Real.exp (a * classLog K x) : ℂ) * classTheta K (f i) x) *
        ((Real.exp (a * classLog K x) : ℂ) * classTheta K (f j) x) *
        (intervalHalfWeight l r s (classLog K x) : ℂ)^2 ∂mu) =
        inner ℂ (u i) (u j) := by
    simpa only [hf i, hf j] using
      originalThetaLinear_Gram K addHaar mu a l r s hlr (f i) (f j)
  refine ⟨n, f, ?_⟩
  dsimp only
  simp only [hu, hf]
  refine ⟨fun i => (hmem i).1, hli, hspan, hgram, ?_, ?_⟩
  · simpa only [hgram] using hdet
  · let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    have hp := NDivisorialShells.arithmetic_positivePartition K v
    have he (e : Option ℕ) (i j : Fin n) :=
      (sourceConvolutionEntry_originalTheta K addHaar mu a l r s hlr hs
        (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2
        (p e) (hp.measurable e)
        (fun x => ⟨hp.nonneg e x, ReviewM.partition_le_one p hp e x⟩)
        (f i) (f j)).2.2
    simp only [hf] at he
    dsimp only [p] at he
    simp_rw [he] at hdiag hsum hbound
    exact ⟨hdiag, hsum, hbound⟩

end
end BSourceGram

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


end
end FSmoothCutoff
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
/- Insert after BSourceGramFragment, ICanonicalSignedSourceFragment and
   FSmoothRadial. This is the signed arithmetic application of B's one Gram
   interface, using the canonical residual kernel and the actual cutoff. -/
namespace ReviewI.Integration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure
open scoped Topology InnerProductSpace BigOperators Matrix
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem canonical_smooth_shell_bounds (v : ℕ → NumberField.FinitePlace K)
    (L epsilon : ℝ) (e : Option ℕ) (x : HeckeIdeleClasses K) :
    0 ≤ FSmoothCutoff.realMask K L epsilon x *
      NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K) e x ∧
    FSmoothCutoff.realMask K L epsilon x *
      NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K) e x ≤ 1 := by
  have hp := NDivisorialShells.arithmetic_positivePartition K v
  exact ⟨mul_nonneg (FSmoothCutoff.realMask_bounds K L epsilon x).1 (hp.nonneg e x),
    mul_le_one₀ (FSmoothCutoff.realMask_bounds K L epsilon x).2 (hp.nonneg e x)
      (ReviewM.partition_le_one _ hp e x)⟩

theorem canonical_smooth_shell_measurable (v : ℕ → NumberField.FinitePlace K)
    (L epsilon : ℝ) (e : Option ℕ) :
    Measurable (fun x => FSmoothCutoff.realMask K L epsilon x *
      NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K) e x) :=
  (FSmoothCutoff.realMask_continuous K L epsilon).measurable.mul
    ((NDivisorialShells.arithmetic_positivePartition K v).measurable e)

variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Every signed, physically smoothed shell of the actual residual kernel is
the positive full inverse-Gram contraction of the same finite source frame.
The incoming mask remains inside A; no commutation is used. -/
theorem both_tests_full_signed_smoothed_Gram
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (q : Fin 2) (T : Finset (Lp ℂ 2 mu)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    let alpha := NDivisorialShells.descendedStratumMask K v
      (NDivisorialShells.arithmeticIndentation K)
    let d := fun x => DSourceKernel.residualKernel mu b E A
      (fun x y => h (x*y⁻¹)) x x
    ∃ n : ℕ, ∃ frame : Fin n → Lp ℂ 2 mu,
      (∀ i, frame i ∈ (T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta) ∧
      LinearIndependent ℂ frame ∧ Submodule.span ℂ (Set.range frame) = E ∧
      IsUnit (Matrix.det (fun i j => inner ℂ (frame i) (frame j))) ∧
      ∀ L epsilon : ℝ,
        let Mphys := KPhysicalMask.realMaskCLM mu (FSmoothCutoff.realMask K L epsilon)
          (FSmoothCutoff.realMask_continuous K L epsilon).measurable
          (FSmoothCutoff.realMask_bounds K L epsilon)
        let M := fun e => KPhysicalMask.realMaskCLM mu
          (fun x => FSmoothCutoff.realMask K L epsilon x * p e x)
          (canonical_smooth_shell_measurable K v L epsilon e)
          (canonical_smooth_shell_bounds K v L epsilon e)
        let g := fun e => ∑ i, ∑ j, BSourceGram.sourceGramInverse frame j i *
          inner ℂ (frame i) (A (M e (frame j)))
        (∀ e, (∫ x, (p e x : ℂ) * (FSmoothCutoff.mask K L epsilon x *
          DSourceKernel.finiteKernel mu b E A x x) ∂mu) = g e) ∧
        (∀ k : ℕ, (∫ x, FSmoothCutoff.mask K L epsilon x *
          (((alpha (k+1) x - alpha k x : ℝ) : ℂ) * d x) ∂mu) = g (some k)) ∧
        HasSum g (Masullo.TraceClass.trace (Mphys.comp (E.starProjection.comp A))) ∧
        Summable (fun e => ‖g e‖) ∧
        (∑' e, ‖g e‖) ≤ ∫ x, ‖FSmoothCutoff.mask K L epsilon x *
          DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  classical
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  let ht := LIntegrated.requiredTest_compact K phi hh hc q
  let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
  let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let Theta := fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
  let alpha := NDivisorialShells.descendedStratumMask K v
    (NDivisorialShells.arithmeticIndentation K)
  let d := fun x => DSourceKernel.residualKernel mu b E A
    (fun x y => h (x*y⁻¹)) x x
  have hb : ∀ x, 0 < b x := by
    intro x
    dsimp [b, intervalHalfWeight]
    positivity
  obtain ⟨n, frame, hmem, hli, hspan⟩ :=
    BSourceGram.sourceSpan_frame mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
  refine ⟨n, frame, hmem, hli, hspan, BSourceGram.source_Gram_isUnit frame hli, ?_⟩
  intro L epsilon
  let Mphys := KPhysicalMask.realMaskCLM mu (FSmoothCutoff.realMask K L epsilon)
    (FSmoothCutoff.realMask_continuous K L epsilon).measurable
    (FSmoothCutoff.realMask_bounds K L epsilon)
  let M := fun e => KPhysicalMask.realMaskCLM mu
    (fun x => FSmoothCutoff.realMask K L epsilon x * p e x)
    (canonical_smooth_shell_measurable K v L epsilon e)
    (canonical_smooth_shell_bounds K v L epsilon e)
  let g := fun e => ∑ i, ∑ j, BSourceGram.sourceGramInverse frame j i *
    inner ℂ (frame i) (A (M e (frame j)))
  let f := fun x => FSmoothCutoff.mask K L epsilon x *
    DSourceKernel.finiteKernel mu b E A x x
  have he (e : Option ℕ) : (∫ x, (p e x : ℂ) * f x ∂mu) = g e := by
    have hgram := BSourceGram.finiteKernel_masked_Gram mu b hb frame hli A
      (fun x => FSmoothCutoff.realMask K L epsilon x * p e x)
      (canonical_smooth_shell_measurable K v L epsilon e)
      (canonical_smooth_shell_bounds K v L epsilon e)
    simp only [hspan] at hgram
    calc
      _ = ∫ x, ((FSmoothCutoff.realMask K L epsilon x * p e x : ℝ) : ℂ) *
          DSourceKernel.finiteKernel mu b E A x x ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [f, FSmoothCutoff.mask, Complex.ofReal_mul]
        ring
      _ = g e := hgram
  have hf : Integrable f mu :=
    BSourceShell.masked_integrable mu _ _
      (DSourceKernel.finiteKernel_diagonal mu b hb E A).1
      (FSmoothCutoff.mask_measurable K mu L epsilon)
      (Eventually.of_forall (FSmoothCutoff.mask_norm_le K L epsilon))
  have hp := NDivisorialShells.arithmetic_positivePartition K v
  have hrec := ReviewM.shell_reconstruction mu p hp f hf
  have hnorm := ReviewM.positive_shell_l1 mu p hp f hf
  have htrace : (∫ x, f x ∂mu) =
      Masullo.TraceClass.trace (Mphys.comp (E.starProjection.comp A)) :=
    BSourceGram.finiteKernel_masked_trace mu b hb E A (FSmoothCutoff.realMask K L epsilon)
      (FSmoothCutoff.realMask_continuous K L epsilon).measurable
      (FSmoothCutoff.realMask_bounds K L epsilon)
  rw [htrace] at hrec
  refine ⟨he, ?_, ?_, ?_, ?_⟩
  · intro k
    calc
      _ = ∫ x, (p (some k) x : ℂ) * f x ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [NDivisorialShells.descendedStratumMask_step,
          Complex.ofReal_neg, DSourceKernel.residualKernel, mul_inv_cancel,
          LIntegrated.requiredTest_at_one K phi hphi q, zero_sub, f, p]
        ring
      _ = g (some k) := he _
  · simpa only [he] using hrec
  · simpa only [he] using hnorm.1
  · simpa only [he] using hnorm.2

end
end ReviewI.Integration
/- Insert after BOriginalHaarGramFragment and ISignedSmoothedGramFragment.
   Application only: I owns the signed shell theorem, B the measured entries. -/
namespace BSourceGram
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure
open scoped Topology InnerProductSpace BigOperators Matrix
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- Literal original-Haar integral entries in I's actual signed and smoothed
source-kernel theorem. The frame and all mask applications are proved on the
canonical arithmetic definitions; both manuscript test families are retained. -/
theorem both_tests_signed_smoothed_measured_Gram
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (q : Fin 2) (T : Finset (Lp ℂ 2 mu)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    let alpha := NDivisorialShells.descendedStratumMask K v
      (NDivisorialShells.arithmeticIndentation K)
    let d := fun x => DSourceKernel.residualKernel mu b E A
      (fun x y => h (x*y⁻¹)) x x
    ∃ n : ℕ, ∃ frame : Fin n → Lp ℂ 2 mu,
      (∀ i, frame i ∈ (T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta) ∧
      LinearIndependent ℂ frame ∧ Submodule.span ℂ (Set.range frame) = E ∧
      IsUnit (Matrix.det (fun i j => inner ℂ (frame i) (frame j))) ∧
      ∀ L epsilon : ℝ,
        let Mphys := KPhysicalMask.realMaskCLM mu (FSmoothCutoff.realMask K L epsilon)
          (FSmoothCutoff.realMask_continuous K L epsilon).measurable
          (FSmoothCutoff.realMask_bounds K L epsilon)
        let g := fun e => ∑ i, ∑ j, BSourceGram.sourceGramInverse frame j i *
          sourceConvolutionEntry K mu l r s h
            (fun x => FSmoothCutoff.realMask K L epsilon x * p e x) (frame i) (frame j)
        (∀ e, (∫ x, (p e x : ℂ) * (FSmoothCutoff.mask K L epsilon x *
          DSourceKernel.finiteKernel mu b E A x x) ∂mu) = g e) ∧
        (∀ k : ℕ, (∫ x, FSmoothCutoff.mask K L epsilon x *
          (((alpha (k+1) x - alpha k x : ℝ) : ℂ) * d x) ∂mu) = g (some k)) ∧
        HasSum g (Masullo.TraceClass.trace (Mphys.comp (E.starProjection.comp A))) ∧
        Summable (fun e => ‖g e‖) ∧
        (∑' e, ‖g e‖) ≤ ∫ x, ‖FSmoothCutoff.mask K L epsilon x *
          DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  dsimp only
  obtain ⟨n, frame, hmem, hli, hspan, hdet, hrest⟩ :=
    ReviewI.Integration.both_tests_full_signed_smoothed_Gram K addHaar mu
      a l r s hlr hs phi hh hc hphi v q T
  refine ⟨n, frame, hmem, hli, hspan, hdet, ?_⟩
  intro L epsilon
  have he (e : Option ℕ) (i j : Fin n) :=
    (sourceConvolutionEntry_eq K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2
      (fun x => FSmoothCutoff.realMask K L epsilon x *
        NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K) e x)
      (ReviewI.Integration.canonical_smooth_shell_measurable K v L epsilon e)
      (ReviewI.Integration.canonical_smooth_shell_bounds K v L epsilon e)
      (frame i) (frame j)).2.2
  simp_rw [he]
  exact hrest L epsilon

end
end BSourceGram

/- Insert after BOriginalThetaEntriesFragment, BSignedMeasuredGramFragment
   and OOriginalThetaProjection. I owns the signed-shell calculation; this
   applies it to the literal original-test theta factors in B35 (35.6). -/
namespace BSourceGram
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.IdeleTheta JThetaAttachment PIntervalConvolution OAllCharacterClosure
open scoped Topology InnerProductSpace BigOperators Matrix
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K))
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- Both original tests, signed residual shells and every physical mask use
one original theta frame. The two minus signs give the displayed plus Gram
contraction; the physical and arithmetic masks remain on incoming y. -/
theorem both_tests_signed_smoothed_original_theta_Gram
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (q : Fin 2) (T : Finset (Lp ℂ 2 mu)) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    let alpha := NDivisorialShells.descendedStratumMask K v
      (NDivisorialShells.arithmeticIndentation K)
    let d := fun x => DSourceKernel.residualKernel mu b E A
      (fun x y => h (x*y⁻¹)) x x
    ∃ n : ℕ,
    ∃ f : Fin n → originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s,
      let frame := fun i => originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s (f i)
      let theta := fun i x => (Real.exp (a * classLog K x) : ℂ) * classTheta K (f i) x
      (∀ i, frame i ∈ T) ∧ LinearIndependent ℂ frame ∧
      Submodule.span ℂ (Set.range frame) = E ∧
      IsUnit (Matrix.det (fun i j =>
        ∫ x, star (theta i x) * theta j x * (b x : ℂ)^2 ∂mu)) ∧
      ∀ L epsilon : ℝ,
        let Mphys := KPhysicalMask.realMaskCLM mu (FSmoothCutoff.realMask K L epsilon)
          (FSmoothCutoff.realMask_continuous K L epsilon).measurable
          (FSmoothCutoff.realMask_bounds K L epsilon)
        let g := fun e => ∑ i, ∑ j, sourceGramInverse frame j i *
          (∫ x, (b x : ℂ)^2 * star (theta i x) *
            (∫ y, h (x*y⁻¹) *
              (((FSmoothCutoff.realMask K L epsilon y * p e y : ℝ) : ℂ) *
                theta j y) ∂mu) ∂mu)
        (∀ e, (∫ x, (p e x : ℂ) * (FSmoothCutoff.mask K L epsilon x *
          DSourceKernel.finiteKernel mu b E A x x) ∂mu) = g e) ∧
        (∀ k : ℕ, (∫ x, FSmoothCutoff.mask K L epsilon x *
          (((alpha (k+1) x - alpha k x : ℝ) : ℂ) * d x) ∂mu) = g (some k)) ∧
        HasSum g (Masullo.TraceClass.trace (Mphys.comp (E.starProjection.comp A))) ∧
        Summable (fun e => ‖g e‖) ∧
        (∑' e, ‖g e‖) ≤ ∫ x, ‖FSmoothCutoff.mask K L epsilon x *
          DSourceKernel.finiteKernel mu b E A x x‖ ∂mu := by
  classical
  dsimp only
  obtain ⟨n, frame, hmem, hli, hspan, hdet, hrest⟩ :=
    both_tests_signed_smoothed_measured_Gram K addHaar mu
      a l r s hlr hs phi hh hc hphi v q T
  have ho (i : Fin n) :
      ∃ f : originalTestDomain K addHaar mu (a+(l+r)/2) ((r-l)/2) s,
        originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s f = frame i := by
    have hi := (hmem i).2
    rw [OOriginalThetaProjection.fullSourceMap_setRange_eq_originalThetaLinear] at hi
    exact hi
  choose f hf using ho
  have hu : (fun i => originalThetaLinear K addHaar mu (a+(l+r)/2) ((r-l)/2) s
      (f i)) = frame := funext hf
  have hgram (i j : Fin n) :
      (∫ x, star ((Real.exp (a * classLog K x) : ℂ) * classTheta K (f i) x) *
        ((Real.exp (a * classLog K x) : ℂ) * classTheta K (f j) x) *
        (intervalHalfWeight l r s (classLog K x) : ℂ)^2 ∂mu) =
        inner ℂ (frame i) (frame j) := by
    simpa only [hf i, hf j] using
      originalThetaLinear_Gram K addHaar mu a l r s hlr (f i) (f j)
  refine ⟨n, f, ?_⟩
  dsimp only
  simp only [hu, hf]
  refine ⟨fun i => (hmem i).1, hli, hspan, ?_, ?_⟩
  · simpa only [hgram] using hdet
  · intro L epsilon
    have he (e : Option ℕ) (i j : Fin n) :=
      (sourceConvolutionEntry_originalTheta K addHaar mu a l r s hlr hs
        (LIntegrated.requiredTest K phi q)
        (LIntegrated.requiredTest_compact K phi hh hc q).1
        (LIntegrated.requiredTest_compact K phi hh hc q).2
        (fun x => FSmoothCutoff.realMask K L epsilon x *
          NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K) e x)
        (ReviewI.Integration.canonical_smooth_shell_measurable K v L epsilon e)
        (ReviewI.Integration.canonical_smooth_shell_bounds K v L epsilon e)
        (f i) (f j)).2.2
    simp only [hf] at he
    have hout := hrest L epsilon
    simp_rw [he] at hout
    exact hout

end
end BSourceGram
#check BSourceGram.both_tests_signed_smoothed_original_theta_Gram
#print axioms BSourceGram.both_tests_signed_smoothed_original_theta_Gram

#check BSourceGram.both_tests_original_theta_Gram_shells
#print axioms BSourceGram.both_tests_original_theta_Gram_shells
#check BSourceGram.sourceConvolutionEntry_originalTheta
#print axioms BSourceGram.sourceConvolutionEntry_originalTheta
