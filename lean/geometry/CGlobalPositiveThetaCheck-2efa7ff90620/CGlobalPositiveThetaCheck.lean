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
/- Insert after JOriginalLinearTheta and the already shared JThetaSummabilityCore.
   This applies the existing lattice estimate to the actual principal series
   along genuine radial ideles. No theta decay premise is supplied. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleTheta
open NumberField NumberField.mixedEmbedding IsDedekindDomain
open Masullo.CompactSupportedThetaUniform Masullo.HomeomorphMixedSpace
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

def thetaUnitsNonzero : Kˣ ≃ {x : K // x ≠ 0} where
  toFun u := ⟨u.val, u.ne_zero⟩
  invFun u := Units.mk0 u.val u.property
  left_inv _ := Units.ext rfl
  right_inv _ := Subtype.ext rfl

theorem originalTensor_bruhat (p : SchwartzMap (mixedSpace K) ℂ)
    (q : FiniteAdeleRing (𝓞 K) K → ℂ)
    (hq : IsLocallyConstant q ∧ HasCompactSupport q) :
    IsOriginalBruhat K (fun x => p (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q x.2) := by
  exact ⟨1, fun _ => p, fun _ => q, fun _ => hq, by intro x; simp⟩

/-- Uniform positive radial decay of each original pure tensor, on every
compact family of the actual ideles. -/
theorem originalTensor_theta_radial_bound
    (p : SchwartzMap (mixedSpace K) ℂ) (q : FiniteAdeleRing (𝓞 K) K → ℂ)
    (hq : IsLocallyConstant q ∧ HasCompactSupport q)
    (U : Set (HeckeIdeles K)) (hU : IsCompact U) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ U, ∀ t : ℝ, ∀ ht : 1 ≤ t,
      ‖classTheta K (fun x => p (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q x.2)
        (QuotientGroup.mk (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a))‖ ≤
          B * (t ^ N)⁻¹ := by
  obtain ⟨M, hM⟩ := hq.1.continuous.bounded_above_of_compact_support hq.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨k, B, hB, h⟩ := full_supported_theta_absolute K
    (tsupport q) hq.2.isCompact U hU N
  refine ⟨M * (B * SchwartzMap.seminorm ℝ k 0 p), by positivity, ?_⟩
  intro a ha t ht
  let P : {u : K // u ≠ 0} → ℂ := fun u =>
    q (a.val.2 * algebraMap K (FiniteAdeleRing (𝓞 K) K) u.val) *
      p (t • ((archPart a).val * mixedEmbedding K u.val))
  have hc := h p a ha t ht q M hM0
    (fun y hy => by
      by_contra hny
      exact hy (subset_tsupport q hny)) (fun y _ => hM y)
  have hs : Summable (fun u => ‖P u‖) := hc.1
  have he (u : Kˣ) :
      p (InfiniteAdeleRing.ringEquiv_mixedSpace K
          (principalIdele K u *
            (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a)).val.1) *
        q (principalIdele K u *
          (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a)).val.2 =
      P (thetaUnitsNonzero K u) := by
    change p (InfiniteAdeleRing.ringEquiv_mixedSpace K
      (algebraMap K (InfiniteAdeleRing K) (u : K) *
        ((thetaRadialIdele K t _).val.1 * a.val.1))) *
      q (algebraMap K (FiniteAdeleRing (𝓞 K) K) (u : K) *
        ((thetaRadialIdele K t _).val.2 * a.val.2)) = _
    have harch : InfiniteAdeleRing.ringEquiv_mixedSpace K
        (algebraMap K (InfiniteAdeleRing K) (u : K)) = mixedEmbedding K (u : K) := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    rw [(InfiniteAdeleRing.ringEquiv_mixedSpace K).map_mul,
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).map_mul,
      thetaRadialIdele_arch, thetaRadialIdele_finite, one_mul, harch]
    simp only [P, thetaUnitsNonzero, archPart, Algebra.smul_def,
      mul_assoc, mul_left_comm, mul_comm]
    rfl
  change ‖∑' u : Kˣ, _‖ ≤ _
  rw [tsum_congr he]
  calc
    ‖∑' u : Kˣ, P (thetaUnitsNonzero K u)‖ ≤ ∑' u : Kˣ, ‖P (thetaUnitsNonzero K u)‖ :=
      norm_tsum_le_tsum_norm (hs.comp_injective (thetaUnitsNonzero K).injective)
    _ = ∑' u, ‖P u‖ := (thetaUnitsNonzero K).tsum_eq (fun u => ‖P u‖)
    _ ≤ (M * (B * SchwartzMap.seminorm ℝ k 0 p)) * (t ^ N)⁻¹ := by
      simpa only [mul_assoc] using hc.2

variable [MeasurableSpace (HeckeAdeles K)]

theorem classTheta_finite_sum_original {ι : Type*} [Fintype ι]
    (f : ι → HeckeAdeles K → ℂ) (hf : ∀ i, IsOriginalBruhat K (f i))
    (x : HeckeIdeleClasses K) :
    classTheta K (fun y => ∑ i, f i y) x = ∑ i, classTheta K (f i) x := by
  induction x using Quotient.inductionOn with
  | h a =>
    exact Summable.tsum_finsetSum
      (fun i _ => originalBruhat_theta_summable K (f i) (hf i) a)

/-- The supplied arithmetic lattice estimate now applies to every original
finite-tensor test along the genuine radial ideles. This is the positive
tail; inversion/Poisson and quotient-Haar integration are separate steps. -/
theorem originalBruhat_theta_radial_bound (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) (U : Set (HeckeIdeles K)) (hU : IsCompact U) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ U, ∀ t : ℝ, ∀ ht : 1 ≤ t,
      ‖classTheta K f
        (QuotientGroup.mk (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a))‖ ≤
          B * (t ^ N)⁻¹ := by
  rcases hf with ⟨n, p, q, hq, he⟩
  choose B hB hb using
    (fun i : Fin n => originalTensor_theta_radial_bound K (p i) (q i) (hq i) U hU N)
  refine ⟨∑ i, B i, Finset.sum_nonneg (fun i _ => hB i), ?_⟩
  intro a ha t ht
  have hsum : classTheta K f
      (QuotientGroup.mk (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a)) =
      ∑ i, classTheta K
        (fun x => p i (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q i x.2)
        (QuotientGroup.mk (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a)) := by
    rw [funext he]
    exact classTheta_finite_sum_original K _ (fun i => originalTensor_bruhat K (p i) (q i) (hq i)) _
  rw [hsum]
  calc
    _ ≤ ∑ i, ‖classTheta K
        (fun x => p i (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * q i x.2)
        (QuotientGroup.mk (thetaRadialIdele K t (ne_of_gt (lt_of_lt_of_le zero_lt_one ht)) * a))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, B i * (t ^ N)⁻¹ := Finset.sum_le_sum (fun i _ => hb i a ha t ht)
    _ = (∑ i, B i) * (t ^ N)⁻¹ := (Finset.sum_mul _ _ _).symm

end
end JThetaAttachment
#check JThetaAttachment.originalBruhat_theta_radial_bound
#print axioms JThetaAttachment.originalBruhat_theta_radial_bound

/- Insert after JOriginalLinearTheta. The Fourier-zero comparison is
   independent of the additive character and retains the original Haar. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- At zero the original adelic Fourier integral is the original additive
Haar integral, for every additive character. Thus no self-dual rescaling
or character choice is needed to compare the second source moment. -/
theorem original_fourier_at_zero (addHaar : Measure (HeckeAdeles K))
    (psi : AddChar (HeckeAdeles K) Circle) (f : HeckeAdeles K → ℂ) :
    (∫ x, f x * (psi (x * 0) : ℂ) ∂addHaar) = ∫ x, f x ∂addHaar := by
  simp only [mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, mul_one]

variable [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure]
variable (mu : Measure (HeckeIdeleClasses K)) (a alpha s : ℝ)

/-- The actual source domain has the two manuscript moments f(0)=fhat(0)=0,
with the one remaining Hilbert admission stated separately. -/
theorem originalTestDomain_iff_fourier_zero
    (psi : AddChar (HeckeAdeles K) Circle) (f : HeckeAdeles K → ℂ) :
    f ∈ originalTestDomain K addHaar mu a alpha s ↔
      IsOriginalBruhat K f ∧ f 0 = 0 ∧
      (∫ x, f x * (psi (x * 0) : ℂ) ∂addHaar) = 0 ∧
      MemLp (normalizedTheta K a alpha s f) 2 mu := by
  rw [original_fourier_at_zero]
  rfl

end
end JThetaAttachment
#check JThetaAttachment.originalTestDomain_iff_fourier_zero
#print axioms JThetaAttachment.originalTestDomain_iff_fourier_zero


/- Insert after JOriginalThetaRadial. Normalization uses the actual product
   formula modulus: diagonal coordinate dilation t has modulus t^[K:Q]. -/
namespace JThetaAttachment
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Masullo.IdeleTheta NumberField NumberField.mixedEmbedding IsDedekindDomain
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

variable [MeasurableSpace (HeckeAdeles K)]

/-- The actual theta series has arbitrary positive-logarithmic decay,
uniformly on compact original idele families, with the field-degree
normalization proved above. -/
theorem originalBruhat_theta_log_bound (f : HeckeAdeles K → ℂ)
    (hf : IsOriginalBruhat K f) (U : Set (HeckeIdeles K)) (hU : IsCompact U) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a ∈ U, ∀ u : ℝ, 0 ≤ u →
      ‖classTheta K f (QuotientGroup.mk (thetaLogSection K u * a))‖ ≤
        B * Real.exp (-R * u) := by
  have hd : 0 < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  obtain ⟨N, hN⟩ := exists_nat_gt (R * (Module.finrank ℚ K : ℝ))
  obtain ⟨B, hB, hb⟩ := originalBruhat_theta_radial_bound K f hf U hU N
  refine ⟨B, hB, ?_⟩
  intro a ha u hu
  have ht : 1 ≤ Real.exp (u / (Module.finrank ℚ K : ℝ)) :=
    Real.one_le_exp_iff.mpr (div_nonneg hu hd.le)
  have h := hb a ha (Real.exp (u / (Module.finrank ℚ K : ℝ))) ht
  change ‖classTheta K f (QuotientGroup.mk (thetaLogSection K u * a))‖ ≤ _ at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hB)
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hnd : R ≤ (N : ℝ) / (Module.finrank ℚ K : ℝ) :=
    (le_div_iff₀ hd).mpr hN.le
  calc
    -((N : ℝ) * (u / (Module.finrank ℚ K : ℝ))) =
        -((N : ℝ) / (Module.finrank ℚ K : ℝ) * u) := by ring
    _ ≤ -(R * u) := neg_le_neg (mul_le_mul_of_nonneg_right hnd hu)
    _ = -R * u := by ring

end
end JThetaAttachment
#check JThetaAttachment.thetaLogSection_classLog
#print axioms JThetaAttachment.thetaLogSection_classLog
#print axioms JThetaAttachment.classLog_surjective


/- C -> J/O/P. Insert after JOriginalThetaRadial and JOriginalThetaLogSection.
   This is the actual positive-tail application, with field degree retained. -/
namespace CThetaLogDecay
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.IdeleTheta
open Masullo.GenuineMellinJet Masullo.WeightedIdeleClass JThetaAttachment
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- The same bound on the literal normalized theta source used by the common
Hilbert realization. All weight and twist factors are retained explicitly. -/
theorem originalBruhat_normalizedTheta_log_bound (a alpha s : ℝ)
    (f : HeckeAdeles K → ℂ) (hf : IsOriginalBruhat K f)
    (U : Set (HeckeIdeles K)) (hU : IsCompact U) (R : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ U, ∀ u : ℝ, 0 ≤ u →
      ‖normalizedTheta K a alpha s f (QuotientGroup.mk (thetaLogSection K u * g))‖ ≤
        B * nativeHalfWeight alpha s (u + classLog K (QuotientGroup.mk g)) *
          Real.exp (a * (u + classLog K (QuotientGroup.mk g)) -
            R * u) := by
  obtain ⟨B, hB, hb⟩ := JThetaAttachment.originalBruhat_theta_log_bound K f hf U hU R
  refine ⟨B, hB, ?_⟩
  intro g hg u hu
  have hl : classLog K (QuotientGroup.mk (thetaLogSection K u * g)) =
      u + classLog K (QuotientGroup.mk g) := by
    change classLog K ((QuotientGroup.mk (thetaLogSection K u)) *
      (QuotientGroup.mk g)) = _
    rw [classLog_mul, thetaLogSection_classLog]
  rw [normalizedTheta, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (nativeHalfWeight_pos _ _ _),
    abs_of_pos (Real.exp_pos _), hl]
  calc
    _ ≤ (nativeHalfWeight alpha s (u + classLog K (QuotientGroup.mk g)) *
          Real.exp (a * (u + classLog K (QuotientGroup.mk g)))) *
          (B * Real.exp (-(R * u))) :=
      by
        simpa only [neg_mul] using mul_le_mul_of_nonneg_left (hb g hg u hu)
          (mul_nonneg (nativeHalfWeight_pos alpha s _).le (Real.exp_pos _).le)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

/-- On the positive logarithmic half-line the literal polynomial half-weight
has this explicit exponential envelope. No weight is replaced in the source. -/
theorem nativeHalfWeight_nonneg_log_le (alpha s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    nativeHalfWeight alpha s u ≤ Real.exp ((alpha + s / 2) * u) := by
  have hlin : 1 + u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hsq : (1 + u) ^ 2 ≤ (Real.exp u) ^ 2 := by
    simpa only [pow_two] using
      mul_self_le_mul_self (by linarith : 0 ≤ 1 + u) hlin
  have hbase : 1 + u ^ 2 ≤ Real.exp (2 * u) := by
    calc
      _ ≤ (1 + u) ^ 2 := by nlinarith
      _ ≤ (Real.exp u) ^ 2 := hsq
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + u ^ 2) hbase
    (by linarith : 0 ≤ s / 4)
  rw [Real.rpow_def_of_pos (Real.exp_pos (2 * u)), Real.log_exp] at hp
  calc
    nativeHalfWeight alpha s u = Real.exp (alpha * u) * (1 + u ^ 2) ^ (s / 4) := by
      rw [nativeHalfWeight, abs_of_nonneg hu]
    _ ≤ Real.exp (alpha * u) * Real.exp ((2 * u) * (s / 4)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp ((alpha + s / 2) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Arbitrary positive decay of the actual weighted source on any compact
family of norm-one representatives, ready for O's arithmetic compact lift. -/
theorem originalBruhat_normalizedTheta_normOne_log_decay (a alpha s rate : ℝ)
    (hs : 0 ≤ s) (f : HeckeAdeles K → ℂ) (hf : IsOriginalBruhat K f)
    (U : Set (HeckeIdeles K)) (hU : IsCompact U)
    (hU0 : ∀ g ∈ U, classLog K (QuotientGroup.mk g) = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ g ∈ U, ∀ u : ℝ, 0 ≤ u →
      ‖normalizedTheta K a alpha s f (QuotientGroup.mk (thetaLogSection K u * g))‖ ≤
        B * Real.exp (-rate * u) := by
  obtain ⟨B, hB, hb⟩ := originalBruhat_normalizedTheta_log_bound K a alpha s f hf U hU
    (a + alpha + s / 2 + rate)
  refine ⟨B, hB, ?_⟩
  intro g hg u hu
  calc
    _ ≤ B * nativeHalfWeight alpha s u *
        Real.exp (a * u - (a + alpha + s / 2 + rate) * u) := by
      simpa only [hU0 g hg, add_zero] using hb g hg u hu
    _ ≤ B * Real.exp ((alpha + s / 2) * u) *
        Real.exp (a * u - (a + alpha + s / 2 + rate) * u) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (nativeHalfWeight_nonneg_log_le alpha s u hs hu) hB)
        (Real.exp_pos _).le
    _ = B * Real.exp (-rate * u) := by
      rw [mul_assoc, ← Real.exp_add]
      have he : (alpha + s / 2) * u + (a * u - (a + alpha + s / 2 + rate) * u) =
          -rate * u := by ring
      rw [he]

end
end CThetaLogDecay
#check CThetaLogDecay.originalBruhat_normalizedTheta_log_bound
#print axioms CThetaLogDecay.originalBruhat_normalizedTheta_log_bound
#check CThetaLogDecay.originalBruhat_normalizedTheta_normOne_log_decay
#print axioms CThetaLogDecay.originalBruhat_normalizedTheta_normOne_log_decay


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
#check OSourceHaar.isCompact_classLog_zero
#print axioms OSourceHaar.isCompact_classLog_zero
#print axioms OSourceHaar.exists_compact_normOne_representatives


/- C -> J/O/P. Insert after CThetaLogDecay and OActualNormOne.
   Applies the arithmetic compact representatives; no compactness premise. -/
namespace CThetaLogDecay
open MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open JThetaAttachment OSourceHaar
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- The literal original weighted theta source has arbitrary exponential
decay on the entire positive half of the actual class quotient. Arithmetic
compact norm-one representatives discharge the preceding compact-family
conditions. The negative half still requires Poisson and both moments. -/
theorem originalBruhat_normalizedTheta_global_positive_decay
    (a alpha s rate : ℝ) (hs : 0 ≤ s)
    (f : HeckeAdeles K → ℂ) (hf : IsOriginalBruhat K f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : HeckeIdeleClasses K, 0 ≤ classLog K x →
      ‖normalizedTheta K a alpha s f x‖ ≤ B * Real.exp (-rate * classLog K x) := by
  obtain ⟨D, hD, hDN, hcover⟩ := exists_compact_normOne_representatives K
  have hD0 : ∀ g ∈ D, classLog K (QuotientGroup.mk g) = 0 := by
    intro g hg
    change Real.log (genuineIdeleModulus K g) = 0
    rw [hDN g hg, Real.log_one]
  obtain ⟨B, hB, hb⟩ := originalBruhat_normalizedTheta_normOne_log_decay K
    a alpha s rate hs f hf D hD hD0
  refine ⟨B, hB, ?_⟩
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    intro hx
    let u := classLog K (QuotientGroup.mk g)
    let y : HeckeIdeles K := (thetaLogSection K u)⁻¹ * g
    have he : (QuotientGroup.mk (thetaLogSection K u) : HeckeIdeleClasses K) *
        QuotientGroup.mk y = QuotientGroup.mk g := by
      rw [← QuotientGroup.mk_mul]
      simp only [y, mul_inv_cancel_left]
    have hy0 : classLog K (QuotientGroup.mk y) = 0 := by
      have hh := classLog_mul K (QuotientGroup.mk (thetaLogSection K u))
        (QuotientGroup.mk y)
      rw [he, thetaLogSection_classLog] at hh
      change u = u + classLog K (QuotientGroup.mk y) at hh
      linarith
    have hypos : 0 < genuineIdeleModulus K y := by
      rw [← ideleModule_eq_genuine]
      exact (GroundTheory.Global.IdeleGroup.ideleModule K y).property
    have hynorm : genuineIdeleModulus K y = 1 := by
      have hh := congrArg Real.exp hy0
      change Real.exp (Real.log (genuineIdeleModulus K y)) = Real.exp 0 at hh
      simpa only [Real.exp_log hypos, Real.exp_zero] using hh
    obtain ⟨q, hq⟩ := hcover y hynorm
    have hp : (QuotientGroup.mk (principalIdele K q) : HeckeIdeleClasses K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨q, rfl⟩
    have hre : (QuotientGroup.mk (thetaLogSection K u * (principalIdele K q * y)) :
        HeckeIdeleClasses K) = QuotientGroup.mk g := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hp, one_mul]
      exact he
    simpa only [hre, u] using hb (principalIdele K q * y) hq u hx

end
end CThetaLogDecay
#check CThetaLogDecay.originalBruhat_normalizedTheta_global_positive_decay
#print axioms CThetaLogDecay.originalBruhat_normalizedTheta_global_positive_decay
