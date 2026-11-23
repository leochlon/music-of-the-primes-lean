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


-- Integrated required-test family from L
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


end
end LIntegrated



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

/- Append after DSourceKernel, HSourceTraceFragment, LIntegrated.requiredTest and OThetaClosure.
   Uses the actual interval convolution and the actual admitted theta closure. -/
namespace DArithmeticKernel
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OArithmeticClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Exact arithmetic application: the original interval weight, constructed
Haar convolution, and admitted arithmetic theta closure occur in one theorem.
The finite kernels represent the source projection; subtracting their action
from A recovers the full complementary projection strongly. -/
theorem arithmetic_kernel_connection
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    let S := (JThetaAttachment.thetaClosure K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
      (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
        (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ T, Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  have hb : ∀ x : HeckeIdeleClasses K,
      0 < intervalHalfWeight l r s (classLog K x) := by
    intro x
    unfold intervalHalfWeight
    positivity
  have hmain := DSourceKernel.source_kernel_trace_global_connection mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hb
    (0 : JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    (intervalConvolutionCLM K mu l r s hlr hs h hh hc) F
  simpa only [OSourceClosure.sourceClosure, arithmeticSourceMap_range,
    JThetaAttachment.thetaClosure] using hmain

/-- Both manuscript tests use the same source family, geometric projection,
interval weight and original Haar. No nuclear/trace limit is inferred here. -/
theorem both_tests_arithmetic_kernel_connection
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let tests := LIntegrated.requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    let S := (JThetaAttachment.thetaClosure K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
      (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
        (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ T, Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  exact arithmetic_kernel_connection K addHaar mu chi a l r s hlr hs
    (LIntegrated.requiredTest K phi q) (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2 F

end
end DArithmeticKernel

/- Insert after DResidualKernelFragment, LIntegrated.requiredTest_at_one,
   and OArithmeticClosure. No new arithmetic source or test definition. -/
namespace DArithmeticKernel
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OArithmeticClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- The specified finite residual kernel on the actual admitted arithmetic
source has the signed diagonal required by h(1)=0. Its physical limit equals
minus the finite source trace; no trace of the residual operator is presumed. -/
theorem arithmetic_residual_diagonal
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) :
    let h := LIntegrated.requiredTest K phi q
    let tests := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h tests.1 tests.2
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.sourceSpan K addHaar mu chi
        (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
    let k := fun T => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹))
    ∀ T,
      (∀ x, k T x x = -DSourceKernel.finiteKernel mu b (E T) A x x) ∧
      Integrable (fun x => k T x x) mu ∧
      (∫ x, k T x x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => k T x x) x ∂mu) atTop
        (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  let E := DSourceKernel.sourceSpan mu
    (0 : JThetaAttachment.sourceSpan K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s)
  have hb : ∀ x : HeckeIdeleClasses K,
      0 < intervalHalfWeight l r s (classLog K x) := by
    intro x
    unfold intervalHalfWeight
    positivity
  have hdiag : ∀ x : HeckeIdeleClasses K,
      LIntegrated.requiredTest K phi q (x*x⁻¹) = 0 := by
    intro x
    rw [mul_inv_cancel]
    exact LIntegrated.requiredTest_at_one K phi hphi q
  have hd := DSourceKernel.residualKernel_diagonal mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hb (E T)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) hdiag
  refine ⟨?_, hd.1, hd.2, ?_⟩
  · intro x
    simp only [DSourceKernel.residualKernel, hdiag x, zero_sub]
  · have ht := DReview.originalHaar_physical_limit K mu _ hd.1
    rw [hd.2] at ht
    exact ht

end
end DArithmeticKernel

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

/- Append after DSourceKernel, HSourceTraceFragment, LIntegrated.requiredTest and OAllCharacterClosure; JAllCharacterSource.
   Uses the actual interval convolution and the actual unrestricted admitted original theta closure. -/
namespace DAllSourceKernel
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Exact arithmetic application: the original interval weight, constructed
Haar convolution, and admitted arithmetic theta closure occur in one theorem.
The finite kernels represent the source projection; subtracting their action
from A recovers the full complementary projection strongly. -/
theorem original_kernel_connection
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let S := (JThetaAttachment.fullThetaClosure K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
      (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
        (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ T, Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  have hb : ∀ x : HeckeIdeleClasses K,
      0 < intervalHalfWeight l r s (classLog K x) := by
    intro x
    unfold intervalHalfWeight
    positivity
  have hmain := DSourceKernel.source_kernel_trace_global_connection mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hb
    (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    (intervalConvolutionCLM K mu l r s hlr hs h hh hc) F
  refine ⟨hmain.1, hmain.2.1, ?_⟩
  have hlim := hmain.2.2
  rw [full_sourceProjection_eq] at hlim
  exact hlim

/-- Both manuscript tests use the same source family, geometric projection,
interval weight and original Haar. No nuclear/trace limit is inferred here. -/
theorem both_tests_original_kernel_connection
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let tests := LIntegrated.requiredTest_compact K phi hh hc q
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let A := intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q) tests.1 tests.2
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let S := (JThetaAttachment.fullThetaClosure K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
      (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
        (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ T, Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  exact original_kernel_connection K addHaar mu a l r s hlr hs
    (LIntegrated.requiredTest K phi q) (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2 F

end
end DAllSourceKernel

/- Insert after DResidualKernelFragment, LIntegrated.requiredTest_at_one,
   and OArithmeticClosure. No new arithmetic source or test definition. -/
namespace DAllSourceKernel
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- The specified finite residual kernel on the actual admitted arithmetic
source has the signed diagonal required by h(1)=0. Its physical limit equals
minus the finite source trace; no trace of the residual operator is presumed. -/
theorem original_residual_diagonal
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) :
    let h := LIntegrated.requiredTest K phi q
    let tests := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h tests.1 tests.2
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu
        (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let k := fun T => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹))
    ∀ T,
      (∀ x, k T x x = -DSourceKernel.finiteKernel mu b (E T) A x x) ∧
      Integrable (fun x => k T x x) mu ∧
      (∫ x, k T x x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => k T x x) x ∂mu) atTop
        (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  let E := DSourceKernel.sourceSpan mu
    (0 : JThetaAttachment.fullSourceSpan K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
  have hb : ∀ x : HeckeIdeleClasses K,
      0 < intervalHalfWeight l r s (classLog K x) := by
    intro x
    unfold intervalHalfWeight
    positivity
  have hdiag : ∀ x : HeckeIdeleClasses K,
      LIntegrated.requiredTest K phi q (x*x⁻¹) = 0 := by
    intro x
    rw [mul_inv_cancel]
    exact LIntegrated.requiredTest_at_one K phi hphi q
  have hd := DSourceKernel.residualKernel_diagonal mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hb (E T)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) hdiag
  refine ⟨?_, hd.1, hd.2, ?_⟩
  · intro x
    simp only [DSourceKernel.residualKernel, hdiag x, zero_sub]
  · have ht := DReview.originalHaar_physical_limit K mu _ hd.1
    rw [hd.2] at ht
    exact ht

end
end DAllSourceKernel
set_option pp.proofs false

/- Insert after DResidualKernelFragment. The same explicit integral kernels
   now themselves define the L2 approximants in the proved global limit. -/
namespace DSourceKernel
open MeasureTheory Filter ContinuousLinearMap OSourceClosure
open scoped Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Strong convergence of the actual weighted residual-kernel integrals,
with L2 admission derived from the kernel-action proof on every full input. -/
theorem residualKernel_integral_limit (nu : Measure X)
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
    let kF := fun T x => (b x : ℂ) *
      ∫ y, residualKernel nu b (E T) A freeKernel x y * (F y / (b y : ℂ)) ∂nu
    ∃ hm : ∀ T, MemLp (kF T) 2 nu,
      (∀ T, (hm T).toLp (kF T) = A F - (E T).starProjection (A F)) ∧
      Tendsto (fun T => (hm T).toLp (kF T)) atTop (𝓝 ((P.comp A) F)) := by
  dsimp only
  let E := sourceSpan nu e0 eF Theta
  let kF := fun T x => (b x : ℂ) *
    ∫ y, residualKernel nu b (E T) A freeKernel x y * (F y / (b y : ℂ)) ∂nu
  have hact (T) : (fun x => (A F - (E T).starProjection (A F)) x) =ᵐ[nu] kF T :=
    residualKernel_action nu b hb (E T) A freeKernel F hfree hint
  have hm (T) : MemLp (kF T) 2 nu :=
    (Lp.memLp (A F - (E T).starProjection (A F))).ae_eq (hact T)
  have he (T) : (hm T).toLp (kF T) = A F - (E T).starProjection (A F) := by
    apply Lp.ext
    exact (hm T).coeFn_toLp.trans (hact T).symm
  refine ⟨hm, he, ?_⟩
  change Tendsto (fun T => (hm T).toLp (kF T)) atTop _
  have hfun : (fun T => (hm T).toLp (kF T)) =
      (fun T => A F - (E T).starProjection (A F)) := funext he
  rw [hfun]
  exact (residualKernel_global_connection nu b hb e0 eF Theta A freeKernel F hfree hint).2

end
end DSourceKernel

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


/- Insert after DResidualKernelLimitFragment, DAllSourceResidualDiagonalFragment,
   OAllCharacterClosure and GPointwiseConvolutionFragment. The free-kernel
   action and integrability are proved by G's actual measured convolution. -/
namespace DAllSourceKernel
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SigmaFinite mu] [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- The explicit original-Haar residual kernels act on every completed input,
carry the negative source diagonal and its physical cutoff, and their actual
L2 integral operators converge to the original-source complement AFTER the
constructed arithmetic convolution. Both manuscript tests use this theorem.
No kernel action, scalar integrability or L2 admission is an application premise. -/
theorem both_tests_original_residual_kernel
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let tests := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h tests.1 tests.2
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let P := (JThetaAttachment.fullThetaClosure K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s)ᗮ.starProjection
    let k := fun T => DSourceKernel.residualKernel mu b (E T) A (fun x y => h (x*y⁻¹))
    let kF := fun T x => (b x : ℂ) * ∫ y, k T x y * (F y / (b y : ℂ)) ∂mu
    (∀ T, (fun x => (A F - (E T).starProjection (A F)) x) =ᵐ[mu] kF T) ∧
    (∀ T,
      (∀ x, k T x x = -DSourceKernel.finiteKernel mu b (E T) A x x) ∧
      Integrable (fun x => k T x x) mu ∧
      (∫ x, k T x x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => k T x x) x ∂mu) atTop
        (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A)))) ∧
    (∃ hm : ∀ T, MemLp (kF T) 2 mu,
      (∀ T, (hm T).toLp (kF T) = A F - (E T).starProjection (A F)) ∧
      Tendsto (fun T => (hm T).toLp (kF T)) atTop (𝓝 ((P.comp A) F))) := by
  dsimp only
  have hb : ∀ x : HeckeIdeleClasses K,
      0 < intervalHalfWeight l r s (classLog K x) := by
    intro x
    unfold intervalHalfWeight
    positivity
  have hk := GPointwiseConvolution.intervalConvolutionCLM_kernel K mu l r s hlr hs
    (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2 F
  have hact := DSourceKernel.residualKernel_global_connection mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hb
    (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) F hk.1 hk.2
  have hlim := DSourceKernel.residualKernel_integral_limit mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hb
    (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    (intervalConvolutionCLM K mu l r s hlr hs (LIntegrated.requiredTest K phi q)
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2)
    (fun x y => LIntegrated.requiredTest K phi q (x*y⁻¹)) F hk.1 hk.2
  rw [full_sourceProjection_eq] at hlim
  refine ⟨hact.1, original_residual_diagonal K addHaar mu a l r s hlr hs
    phi hh hc hphi q, ?_⟩
  simpa only [ContinuousLinearMap.comp_apply, Submodule.starProjection_orthogonal_val,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hlim

end
end DAllSourceKernel
set_option pp.proofs false
set_option pp.proofs false

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

/- Insert after DAllSourceMeasuredResidualFragment and CArithmeticMeasure. The free-kernel
   action and integrability are proved by G's actual measured convolution. -/
namespace DAllSourceKernel
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable [SecondCountableTopology (HeckeIdeles K)] [LocallyCompactSpace (HeckeIdeles K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsHaarMeasure]

/-- C's actual quotient-Haar instances discharge sigma-finiteness and inversion
invariance. The explicit original-Haar residual kernels act on every completed input,
carry the negative source diagonal and its physical cutoff, and their actual
L2 integral operators converge to the original-source complement AFTER the
constructed arithmetic convolution. Both manuscript tests use this theorem.
No kernel action, scalar integrability or L2 admission is an application premise. -/
theorem both_tests_original_residual_kernel_haar
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) (F : Lp ℂ 2 mu) :
    letI : SigmaFinite mu := CNormalization.ideleClass_locallyFinite_sigmaFinite K mu
    letI : mu.IsInvInvariant := CNormalization.ideleClass_haar_invInvariant K mu
    let h := LIntegrated.requiredTest K phi q
    let tests := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h tests.1 tests.2
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let E := DSourceKernel.sourceSpan mu
      (0 : JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    let P := (JThetaAttachment.fullThetaClosure K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s)ᗮ.starProjection
    let k := fun T => DSourceKernel.residualKernel mu b (E T) A (fun x y => h (x*y⁻¹))
    let kF := fun T x => (b x : ℂ) * ∫ y, k T x y * (F y / (b y : ℂ)) ∂mu
    (∀ T, (fun x => (A F - (E T).starProjection (A F)) x) =ᵐ[mu] kF T) ∧
    (∀ T,
      (∀ x, k T x x = -DSourceKernel.finiteKernel mu b (E T) A x x) ∧
      Integrable (fun x => k T x x) mu ∧
      (∫ x, k T x x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => k T x x) x ∂mu) atTop
        (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A)))) ∧
    (∃ hm : ∀ T, MemLp (kF T) 2 mu,
      (∀ T, (hm T).toLp (kF T) = A F - (E T).starProjection (A F)) ∧
      Tendsto (fun T => (hm T).toLp (kF T)) atTop (𝓝 ((P.comp A) F))) := by
  letI : SigmaFinite mu := CNormalization.ideleClass_locallyFinite_sigmaFinite K mu
  letI : mu.IsInvInvariant := CNormalization.ideleClass_haar_invInvariant K mu
  exact both_tests_original_residual_kernel K addHaar mu a l r s hlr hs phi hh hc hphi q F

end
end DAllSourceKernel
set_option pp.proofs false
set_option pp.proofs false
#print DAllSourceKernel.both_tests_original_residual_kernel_haar
#print axioms DAllSourceKernel.both_tests_original_residual_kernel_haar
