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


-- Final arithmetic assembly
namespace PIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Assembly on the literal admitted arithmetic theta source. For both required
convolutions: full-input finite source-kernel action, integrable original-Haar
diagonal equal to the genuine finite operator trace, physical cutoff passage,
and strong convergence to the complement of the chosen admitted chi-source,
applied after A. The all-character manuscript application is separate.
No global trace limit or arithmetic local evaluation is asserted here. -/
theorem arithmetic_kernel_trace_source_limit
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let hh' := (LIntegrated.requiredTest_compact K phi hh hc q).1
    let hc' := (LIntegrated.requiredTest_compact K phi hh hc q).2
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh' hc'
    let V := JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
    let Theta := OArithmeticClosure.arithmeticSourceMap K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let S := (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    (∀ T, (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
      (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
        (F y / (b y : ℂ)) ∂mu)) ∧
    (∀ T, Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) x ∂mu)
        atTop (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A)))) ∧
    Tendsto (fun T => A F - (E T).starProjection (A F)) atTop
      (𝓝 (A F - S (A F))) := by
  dsimp only
  let A := intervalConvolutionCLM K mu l r s hlr hs
    (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let V := JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
  have ht := DSourceKernel.source_kernel_trace_global_connection mu
    (fun x => intervalHalfWeight l r s (classLog K x))
    (fun x => by
      change 0 < intervalHalfWeight l r s (classLog K x)
      rw [PIntervalConvolution.interval_halfWeight l r s (classLog K x) hlr]
      exact mul_pos (Real.exp_pos _) (nativeHalfWeight_pos _ _ _))
    (0 : V →ₗ[ℂ] ℂ) 0
    (OArithmeticClosure.arithmeticSourceMap K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s) A F
  refine ⟨ht.1, ?_, ?_⟩
  · intro T
    have hd := ht.2.1 T
    refine ⟨hd.1, hd.2, ?_⟩
    have hl := DReview.originalHaar_physical_limit K mu _ hd.1
    rw [hd.2] at hl
    exact hl
  · have hp := OArithmeticClosure.arithmetic_sourceProjection_eq
      K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
    have hlim := ht.2.2
    rw [hp] at hlim
    exact hlim

end
end PIntegrated



-- Integrated supplier: inputs/exchange/R/RJetFragment.lean
-- Insert after the canonical seed; reuses its genuineMellinJet and nativeHalfWeight.
namespace Masullo.ClassCharacterMul
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

theorem actual_classCharacter_mul (chi : UnitaryHeckeCharacter K)
    (g y : HeckeIdeleClasses K) :
    classCharacter K chi (g*y) = classCharacter K chi g * classCharacter K chi y := by
  refine Quotient.inductionOn₂ g y ?_
  intro a b
  exact map_mul chi.character a b

theorem actual_jet_mul (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (m : ℕ) (g y : HeckeIdeleClasses K) :
    genuineMellinJet K chi z a m (g*y) =
      ∑ k ∈ Finset.range (m+1), genuineMellinJet K chi z a k g *
        genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ) := by
  simp only [genuineMellinJet, actual_classCharacter_mul, classLog_mul,
    Circle.coe_mul, Complex.ofReal_add, Complex.ofReal_pow, mul_add, Complex.exp_add]
  rw [add_pow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The genuine idele-class Mellin jets satisfy the measured transpose action.
This discharges the algebraic and measured-moment part of the native flag premise.
Fubini with the original weighted convolution remains a separate attachment. -/
theorem actual_measured_jet_action (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (m : ℕ)
    (hint : ∀ k ∈ Finset.range (m+1),
      Integrable (fun g => h g * genuineMellinJet K chi z a k g) mu)
    (y : HeckeIdeleClasses K) :
    (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  have hp : (fun g => h g * genuineMellinJet K chi z a m (g*y)) =
      (fun g => ∑ k ∈ Finset.range (m+1),
        (h g * genuineMellinJet K chi z a k g) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ))) := by
    funext g
    rw [actual_jet_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hp, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_mul_const _ _
  · intro k hk
    exact (hint k hk).mul_const _

/-- Every actual jet is continuous on the original quotient. -/
theorem actual_jet_continuous (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) :
    Continuous (genuineMellinJet K chi z a m) := by
  have hc : Continuous (fun x => (classCharacter K chi x : ℂ)) :=
    continuous_subtype_val.comp (classCharacter_continuous K chi)
  have hl := classLog_continuous K
  unfold genuineMellinJet
  fun_prop

/-- Compact original test kernels supply ALL measured jet moments on the same
locally finite quotient measure. Applies equally to the logged test kernel. -/
theorem actual_compact_jet_moment (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (z : ℂ) (a : ℝ) (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hsupp : HasCompactSupport h) (m : ℕ) :
    Integrable (fun g => h g * genuineMellinJet K chi z a m g) mu := by
  apply (hh.mul (actual_jet_continuous K chi z a m)).integrable_of_hasCompactSupport
  have hc : HasCompactSupport (fun g => genuineMellinJet K chi z a m g * h g) :=
    hsupp.mul_left
  simpa only [mul_comm] using hc

/-- Actual same-measure binomial action, with moment premises discharged for
continuous compactly supported kernels. No independent spectrum is specified. -/
theorem actual_compact_measured_jet_action (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (z : ℂ) (a : ℝ) (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hsupp : HasCompactSupport h)
    (m : ℕ) (y : HeckeIdeleClasses K) :
    (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  exact actual_measured_jet_action K chi mu z a h m
    (fun k _ => actual_compact_jet_moment K chi mu z a h hh hsupp k) y

/-- Multiplication by the original class logarithm preserves the compact test
hypotheses used by the measured action. This keeps the logged test in scope. -/
theorem actual_log_kernel_compact (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hsupp : HasCompactSupport h) :
    Continuous (fun g => (classLog K g : ℂ) * h g) ∧
      HasCompactSupport (fun g => (classLog K g : ℂ) * h g) := by
  exact ⟨(Complex.continuous_ofReal.comp (classLog_continuous K)).mul hh,
    hsupp.mul_left⟩

end Masullo.ClassCharacterMul

namespace Masullo.GenuineNormalizedMellinJet
open MasulloGRH Masullo.IdeleClassGeometry
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)

end Masullo.GenuineNormalizedMellinJet
namespace Masullo.GenuineMellinJet
open MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet
theorem genuineMellinJet_normalization
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    genuineNormalizedMellinJet K chi z a s alpha m x *
      (nativeHalfWeight alpha s (classLog K x) : ℂ) =
      genuineMellinJet K chi z a m x := by
  let t := classLog K x
  have hp : (((1+t^2)^(-s/4) : ℝ) : ℂ) *
      (((1+t^2)^(s/4) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
    simp [show -s/4+s/4 = 0 by ring]
  have he : Complex.exp ((z - (a : ℂ)) * (t : ℂ) -
      ((alpha * |t| : ℝ) : ℂ)) * (Real.exp (alpha * |t|) : ℂ) =
      Complex.exp ((z - (a : ℂ)) * (t : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, sub_add_cancel]
  simp only [Complex.ofReal_mul] at he
  simp only [genuineNormalizedMellinJet, nativeHalfWeight, genuineMellinJet,
    Complex.ofReal_mul]
  change ((classCharacter K chi x : ℂ) *
      Complex.exp ((z-(a:ℂ))*(t:ℂ)-((alpha:ℂ)*((|t|:ℝ):ℂ))) *
      (((t^m:ℝ):ℂ) * (((1+t^2)^(-s/4):ℝ):ℂ))) *
      ((Real.exp (alpha*|t|):ℂ) * (((1+t^2)^(s/4):ℝ):ℂ)) = _
  calc
    _ = ((classCharacter K chi x : ℂ) *
      (Complex.exp ((z-(a:ℂ))*(t:ℂ)-((alpha:ℂ)*((|t|:ℝ):ℂ))) *
        (Real.exp (alpha*|t|):ℂ)) * ((t^m:ℝ):ℂ)) *
      ((((1+t^2)^(-s/4):ℝ):ℂ) * (((1+t^2)^(s/4):ℝ):ℂ)) := by ring
    _ = _ := by rw [he, hp, mul_one]

end Masullo.GenuineMellinJet

namespace Masullo.GenuineMellinJet
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet

end Masullo.GenuineMellinJet
namespace Masullo.NativePairingIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
theorem native_pairing_integrable
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun x => genuineMellinJet K chi z a m x * f x) mu := by
  have hi := hg.integrable_mul hF
  change Integrable (fun x => genuineNormalizedMellinJet K chi z a s alpha m x *
    ((nativeHalfWeight alpha s (classLog K x) : ℂ) * f x)) mu at hi
  have he : (fun x => genuineNormalizedMellinJet K chi z a s alpha m x *
      ((nativeHalfWeight alpha s (classLog K x) : ℂ) * f x)) =
      (fun x => genuineMellinJet K chi z a m x * f x) := by
    funext x
    rw [← mul_assoc, genuineMellinJet_normalization]
  rwa [he] at hi

end Masullo.NativePairingIntegrable
namespace Masullo.NativeTranslatedProductIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.NativePairingIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

/-- Absolute integrability of the actual translated jet against a compact kernel
and a native weighted vector. This supplies the previously absent Fubini premise
in the proof of manuscript (10.3.1.8), with the very same quotient measure. -/
theorem native_translated_product_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m (p.1 * p.2) * f p.2) (mu.prod mu) := by
  have he : (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m (p.1 * p.2) * f p.2) =
    (fun p => ∑ k ∈ Finset.range (m+1),
      ((h p.1 * genuineMellinJet K chi z a k p.1) *
        (genuineMellinJet K chi z a (m-k) p.2 * f p.2)) * (m.choose k : ℂ)) := by
    funext p
    rw [actual_jet_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  apply integrable_finset_sum
  intro k hk
  exact ((actual_compact_jet_moment K chi mu z a h hh hs k).mul_prod
    (native_pairing_integrable K chi mu z a s alpha (m-k)
      (hg (m-k) (Nat.sub_le _ _)) f hf)).mul_const _

theorem native_translated_fubini
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ g, ∫ y, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu) =
      ∫ y, ∫ g, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu := by
  exact integral_integral_swap
    (native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf)

end Masullo.NativeTranslatedProductIntegrable

namespace Masullo.NativeConvolutionProductIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.NativePairingIntegrable Masullo.NativeTranslatedProductIntegrable
variable (K : Type*) [Field K] [NumberField K]

/-- The missing original-convolution Fubini premise, derived from the weighted
native pairing, compact test moments and SAME-Haar shear preservation. -/
theorem native_convolution_product_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m p.2 * f (p.1⁻¹*p.2)) (mu.prod mu) := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  have ht := (measurePreserving_prod_inv_mul mu mu).integrable_comp hi.aestronglyMeasurable
  have hc := ht.mpr hi
  simpa only [Function.comp_def, mul_inv_cancel_left] using hc

/-- Actual left convolution paired against an admitted native jet on the
original weighted function space. The product/Fubini premise is proved above. -/
theorem native_weighted_convolution_pairing
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a m x ∂mu) =
      ∫ y, (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) * f y ∂mu := by
  have hi := native_convolution_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  calc
    _ = ∫ x, ∫ g, h g * genuineMellinJet K chi z a m x * f (g⁻¹*x) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_mul_const]
      congr 1
      funext g
      ring
    _ = ∫ g, ∫ x, h g * genuineMellinJet K chi z a m x * f (g⁻¹*x) ∂mu ∂mu :=
      (integral_integral_swap hi).symm
    _ = ∫ g, ∫ y, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with g
      have he := integral_mul_left_eq_self (μ := mu)
        (fun x => h g * genuineMellinJet K chi z a m x * f (g⁻¹*x)) g
      simpa only [inv_mul_cancel_left] using he.symm
    _ = ∫ y, ∫ g, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu :=
      native_translated_fubini K mu chi z a s alpha m h f hh hs hg hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact integral_mul_const _ _

end Masullo.NativeConvolutionProductIntegrable

namespace Masullo.NativeWeightedConvolutionTriangular
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.NativePairingIntegrable Masullo.NativeConvolutionProductIntegrable
variable (K : Type*) [Field K] [NumberField K]

/-- Measured convolution acts triangularly on the weighted Mellin functionals,
by Haar invariance and Fubini. -/
theorem native_weighted_convolution_triangular
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a m x ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        ((∫ g, h g * genuineMellinJet K chi z a k g ∂mu) * (m.choose k : ℂ)) *
          (∫ y, genuineMellinJet K chi z a (m-k) y * f y ∂mu) := by
  rw [native_weighted_convolution_pairing K mu chi z a s alpha m h f hh hs hg hf]
  have he : (fun y => (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) * f y) =
      (fun y => ∑ k ∈ Finset.range (m+1),
        ((∫ g, h g * genuineMellinJet K chi z a k g ∂mu) * (m.choose k : ℂ)) *
          (genuineMellinJet K chi z a (m-k) y * f y)) := by
    funext y
    rw [actual_compact_measured_jet_action K chi mu z a h hh hs m y, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_const_mul _ _
  · intro k hk
    exact (native_pairing_integrable K chi mu z a s alpha (m-k)
      (hg (m-k) (Nat.sub_le _ _)) f hf).const_mul _

/-- The diagonal coefficient is the genuine character Mellin integral at z-a
on the original quotient Haar, acting on arbitrary native weighted f. -/
theorem native_weighted_convolution_mellin
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha 0) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a 0 x ∂mu) =
      (∫ g, h g * genuineMellinJet K chi z a 0 g ∂mu) *
        (∫ y, genuineMellinJet K chi z a 0 y * f y ∂mu) := by
  have hzero : ∀ k ≤ 0, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu := by
    intro k hk
    have he : k = 0 := Nat.eq_zero_of_le_zero hk
    simpa only [he] using hg
  simpa using native_weighted_convolution_triangular K mu chi z a s alpha 0 h f hh hs hzero hf

end Masullo.NativeWeightedConvolutionTriangular


namespace RReview.MeasuredShell
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeWeightedConvolutionTriangular
noncomputable section
/-- R35 (35.9): actual weighted representatives, original Haar and top-jet shell.
This is the measured-convolution identity, not a postulated scalar action. -/
theorem actual_shell_eigenfunctional
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (hvan : ∀ j < m, (∫ x, genuineMellinJet K chi z a j x * f x ∂mu) = 0) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a m x ∂mu) =
      (∫ g, h g * genuineMellinJet K chi z a 0 g ∂mu) *
        (∫ x, genuineMellinJet K chi z a m x * f x ∂mu) := by
  rw [native_weighted_convolution_triangular K mu chi z a s alpha m h f hh hc hg hf]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkm := Finset.mem_range.mp hk
    rw [hvan (m-k) (by omega)]
    exact mul_zero _
  · intro h0
    exact False.elim (h0 (Finset.mem_range.mpr (Nat.zero_lt_succ m)))
end
end RReview.MeasuredShell


-- Integrated supplier: inputs/exchange/I/IArithmeticKernelCore.lean
-- Insert after RJetFragment; all names are the checked common arithmetic definitions.
namespace Masullo.TransposeDiagonalIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeTranslatedProductIntegrable Masullo.NativeConvolutionProductIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

/-- The specific transposed Mellin coefficient paired with a native vector
is integrable. This is a diagonal estimate, not a product-a.e. restriction. -/
theorem actual_transpose_diagonal_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h u : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hu : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * u x) 2 mu) :
    Integrable (fun y => (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) * u y) mu := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h u hh hs hg hu
  have hj : Integrable (fun y => ∫ g,
      h g * genuineMellinJet K chi z a m (g*y) * u y ∂mu) mu := by
    first | exact hi.integral_prod_left | exact hi.integral_prod_right
  simpa only [integral_mul_const] using hj

/-- This is the actual finite tensor with its functional slot precomposed
with convolution. No projection or convergence identity is assumed. -/
noncomputable def finitePAKernel {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K))
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ :=
  ∑ i ∈ F, u i x * (∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu)

/-- Correct-order finite-kernel action on every admitted native weighted
input. It is P_F A, not A P_F. The passage P_F A → PA remains separate. -/
theorem actual_finite_PA_kernel_action {ι : Type*} (F : Finset ι)
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ i ∈ F, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (hf : MemLp (fun y => (nativeHalfWeight alpha s (classLog K y) : ℂ) * f y) 2 mu)
    (x : HeckeIdeleClasses K) :
    (∑ i ∈ F, u i x * (∫ y, (∫ g, h g * f (g⁻¹*y) ∂mu) *
      genuineMellinJet K (chi i) (z i) a (m i) y ∂mu)) =
      ∫ y, finitePAKernel K F mu chi z a m h u x y * f y ∂mu := by
  unfold finitePAKernel
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [native_weighted_convolution_pairing K mu (chi i) (z i) a s alpha (m i)
      h f hh hs (hg i hi) hf]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by ring)
  · intro i hi
    have hd := (actual_transpose_diagonal_integrable K mu (chi i) (z i)
      a s alpha (m i) h f hh hs (hg i hi) hf).const_mul (u i x)
    simpa only [mul_assoc] using hd

/-- Actual Haar diagonal integrability for the finite arithmetic tensor;
the native weight and admitted jets supply the estimate. -/
theorem actual_finite_PA_diagonal_integrable {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ i ∈ F, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (hu : ∀ i ∈ F, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * u i x) 2 mu) :
    Integrable (fun x => finitePAKernel K F mu chi z a m h u x x) mu := by
  unfold finitePAKernel
  apply integrable_finset_sum
  intro i hi
  simpa only [mul_comm] using actual_transpose_diagonal_integrable K mu
    (chi i) (z i) a s alpha (m i) h (u i) hh hs (hg i hi) (hu i hi)

end Masullo.TransposeDiagonalIntegrable

namespace Masullo.TransposeRowContinuous
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.TransposeDiagonalIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

theorem actual_transpose_row_continuous
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    Continuous (fun y => ∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) := by
  have he : (fun y => ∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      (fun y => ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ))) := by
    funext y
    exact actual_compact_measured_jet_action K chi mu z a h hh hs m y
  rw [he]
  exact continuous_finset_sum _ (fun k hk => continuous_const.mul
    ((actual_jet_continuous K chi z a (m-k)).mul continuous_const))

/-- The product representative is genuinely continuous, so its diagonal is
specified pointwise; no restriction of a product-a.e. equivalence is used. -/
theorem actual_finite_PA_kernel_continuous {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hs : HasCompactSupport h)
    (hu : ∀ i ∈ F, Continuous (u i)) :
    Continuous (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      finitePAKernel K F mu chi z a m h u p.1 p.2) := by
  unfold finitePAKernel
  exact continuous_finset_sum _ (fun i hi =>
    ((hu i hi).comp continuous_fst).mul
      ((actual_transpose_row_continuous K mu (chi i) (z i) a (m i) h hh hs).comp
        continuous_snd))

noncomputable def actualWeight (alpha s : ℝ) (x : HeckeIdeleClasses K) : ℝ :=
  Real.exp (2 * alpha * |classLog K x|) * (1 + (classLog K x)^2) ^ (s/2)

theorem actualWeight_pos (alpha s : ℝ) (x : HeckeIdeleClasses K) :
    0 < actualWeight K alpha s x := by
  unfold actualWeight
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

theorem actualWeight_continuous (alpha s : ℝ) (hs0 : 0 ≤ s) : Continuous (actualWeight K alpha s) := by
  unfold actualWeight
  have hc := Masullo.WeightedIdeleClass.classLog_continuous K
  fun_prop (disch := positivity)

/-- The original weighted Riesz vector, not a freely chosen continuous column. -/
noncomputable def actualRieszColumn (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a alpha s : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  star (genuineMellinJet K chi z a m x) / (actualWeight K alpha s x : ℂ)

theorem actualRieszColumn_continuous (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a alpha s : ℝ) (m : ℕ) (hs0 : 0 ≤ s) :
    Continuous (actualRieszColumn K chi z a alpha s m) := by
  unfold actualRieszColumn
  exact (actual_jet_continuous K chi z a m).star.div
    (Complex.continuous_ofReal.comp (actualWeight_continuous K alpha s hs0))
    (fun x => Complex.ofReal_ne_zero.mpr (ne_of_gt (actualWeight_pos K alpha s x)))

/-- Finite Gram-inverse combinations of actual Riesz vectors have a continuous
PA kernel. Choosing the coefficients to be the inverse Gram matrix is a
separate finite-dimensional identification, not an assumption hidden here. -/
theorem actual_Gram_PA_kernel_continuous {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a alpha s : ℝ) (m : ι → ℕ)
    (c : ι → ι → ℂ) (h : HeckeIdeleClasses K → ℂ) (hs0 : 0 ≤ s)
    (hh : Continuous h) (hs : HasCompactSupport h) :
    Continuous (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      finitePAKernel K F mu chi z a m h
        (fun i x => ∑ j ∈ F, c i j * actualRieszColumn K (chi j) (z j) a alpha s (m j) x)
        p.1 p.2) := by
  apply actual_finite_PA_kernel_continuous K F mu chi z a m h _ hh hs
  intro i hi
  exact continuous_finset_sum _ (fun j hj => continuous_const.mul
    (actualRieszColumn_continuous K (chi j) (z j) a alpha s (m j) hs0))

end Masullo.TransposeRowContinuous

namespace Masullo.ActualRiesz
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine weighted Riesz vector, written using the half-weight already
attached pointwise to the original Mellin jet. -/
noncomputable def actualRiesz (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  star (genuineNormalizedMellinJet K chi z a s alpha m x) /
    (nativeHalfWeight alpha s (classLog K x) : ℂ)

theorem halfWeight_pos (alpha s t : ℝ) : 0 < nativeHalfWeight alpha s t := by
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

/-- Identifies the square of the half-weight with the manuscript weight. -/
theorem halfWeight_sq (alpha s t : ℝ) :
    nativeHalfWeight alpha s t * nativeHalfWeight alpha s t =
      Real.exp (2 * alpha * |t|) * (1+t^2)^(s/2) := by
  unfold nativeHalfWeight
  calc
    _ = (Real.exp (alpha*|t|) * Real.exp (alpha*|t|)) *
      ((1+t^2)^(s/4) * (1+t^2)^(s/4)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
      congr 2 <;> ring

/-- The weighted column is the conjugate normalized genuine jet pointwise. -/
theorem actualRiesz_weighted (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      actualRiesz K chi z a s alpha m x =
        star (genuineNormalizedMellinJet K chi z a s alpha m x) := by
  have hw : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (halfWeight_pos alpha s _))
  unfold actualRiesz
  field_simp

/-- The original-Haar functional density is the genuine jet, not an
independently postulated coefficient. This equality holds on the diagonal. -/
theorem actualRiesz_density (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ((Real.exp (2*alpha*|classLog K x|) *
      (1+(classLog K x)^2)^(s/2) : ℝ) : ℂ) *
      star (actualRiesz K chi z a s alpha m x) =
        genuineMellinJet K chi z a m x := by
  rw [← halfWeight_sq, Complex.ofReal_mul]
  have he : (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      star (actualRiesz K chi z a s alpha m x) =
      genuineNormalizedMellinJet K chi z a s alpha m x := by
    simpa [mul_comm] using congrArg star (actualRiesz_weighted K chi z a s alpha m x)
  calc
    _ = (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      ((nativeHalfWeight alpha s (classLog K x) : ℂ) *
        star (actualRiesz K chi z a s alpha m x)) := by ring
    _ = (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      genuineNormalizedMellinJet K chi z a s alpha m x := by rw [he]
    _ = _ := by rw [mul_comm, genuineMellinJet_normalization]

/-- Removes the separate native-vector admission premise for actual Riesz
columns. Only the genuine normalized jet admission remains. -/
theorem actualRiesz_memLp (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      actualRiesz K chi z a s alpha m x) 2 mu := by
  simp_rw [actualRiesz_weighted]
  exact hg.star

end Masullo.ActualRiesz

namespace Masullo.ActualGram
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet Masullo.ActualRiesz
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def actualGram
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
    actualRiesz K (chi j) (z j) a s alpha (m j) x ∂mu

noncomputable def actualGramDual
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (i : ι) (x : HeckeIdeleClasses K) : ℂ :=
  ∑ j, (actualGram K mu chi z a s alpha m)⁻¹ j i *
    actualRiesz K (chi j) (z j) a s alpha (m j) x

theorem actual_Gram_density (chi psi : UnitaryHeckeCharacter K) (z v : ℂ)
    (a s alpha : ℝ) (m n : ℕ) (x : HeckeIdeleClasses K) :
    genuineMellinJet K chi z a m x * actualRiesz K psi v a s alpha n x =
      genuineNormalizedMellinJet K chi z a s alpha m x *
        star (genuineNormalizedMellinJet K psi v a s alpha n x) := by
  rw [← genuineMellinJet_normalization K chi z a s alpha m x]
  unfold actualRiesz
  have hw : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (halfWeight_pos alpha s _))
  field_simp

theorem actual_Gram_integrable
    (mu : Measure (HeckeIdeleClasses K)) (chi psi : UnitaryHeckeCharacter K)
    (z v : ℂ) (a s alpha : ℝ) (m n : ℕ)
    (hi : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (hj : MemLp (genuineNormalizedMellinJet K psi v a s alpha n) 2 mu) :
    Integrable (fun x => genuineMellinJet K chi z a m x *
      actualRiesz K psi v a s alpha n x) mu := by
  simp_rw [actual_Gram_density]
  exact hi.integrable_mul hj.star

/-- Concrete original-Haar biorthogonality. The inverse must be indexed j,i;
using i,j here would generally not give the actual orthogonal section. -/
theorem actual_GramDual_pairing
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det) (i k : ι) :
    (∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
      actualGramDual K mu chi z a s alpha m k x ∂mu) = if i = k then 1 else 0 := by
  have hi (j : ι) := actual_Gram_integrable K mu (chi i) (chi j)
    (z i) (z j) a s alpha (m i) (m j) (hg i) (hg j)
  unfold actualGramDual
  simp_rw [Finset.mul_sum, mul_left_comm (genuineMellinJet K (chi i) (z i) a (m i) _)]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    have hm := congrArg (fun M : Matrix ι ι ℂ => M i k)
      (Matrix.mul_nonsing_inv (actualGram K mu chi z a s alpha m) hdet)
    simpa only [Matrix.mul_apply, actualGram, Matrix.one_apply, mul_comm] using hm
  · intro j hj
    exact (hi j).const_mul _

end Masullo.ActualGram

namespace Masullo.GramDualPairingIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.ActualGram Masullo.ClassCharacterMul
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_GramDual_pairing_integrable
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (i k : ι) :
    Integrable (fun x => genuineMellinJet K (chi i) (z i) a (m i) x *
      actualGramDual K mu chi z a s alpha m k x) mu := by
  unfold actualGramDual
  simp_rw [Finset.mul_sum, mul_left_comm (genuineMellinJet K (chi i) (z i) a (m i) _)]
  apply integrable_finset_sum
  intro j hj
  exact (actual_Gram_integrable K mu (chi i) (chi j) (z i) (z j)
    a s alpha (m i) (m j) (hg i) (hg j)).const_mul _

/-- Every genuine lower jet is represented in the finite label family.
This is the concrete finite flag condition, not a spectral action premise. -/
def JetClosed (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ) : Prop :=
  ∀ i k, k ≤ m i → ∃ j, chi j = chi i ∧ z j = z i ∧ m j = k

/-- On the actual inverse-Gram column the diagonal coefficient is the genuine
zero-th Mellin moment, even for a higher jet. All off-diagonal jet terms
vanish by the proved original-Haar duality, not by a trace assertion. -/
theorem actual_GramDual_PA_coefficient
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (i : ι) :
    (∫ y, (∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu) *
      actualGramDual K mu chi z a s alpha m i y ∂mu) =
      ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu := by
  have hi (k : ℕ) : Integrable (fun y =>
      genuineMellinJet K (chi i) (z i) a (m i-k) y *
        actualGramDual K mu chi z a s alpha m i y) mu := by
    obtain ⟨j, hc, hz, hm⟩ := hclosed i (m i-k) (Nat.sub_le _ _)
    simpa only [hc, hz, hm] using
      actual_GramDual_pairing_integrable K mu chi z a s alpha m hg j i
  have hp (k : ℕ) (hk : k ≤ m i) :
      (∫ y, genuineMellinJet K (chi i) (z i) a (m i-k) y *
        actualGramDual K mu chi z a s alpha m i y ∂mu) =
      if k = 0 then 1 else 0 := by
    by_cases hk0 : k = 0
    · subst k
      simpa using actual_GramDual_pairing K mu chi z a s alpha m hg hdet i i
    · obtain ⟨j, hc, hz, hm⟩ := hclosed i (m i-k) (Nat.sub_le _ _)
      have hji : j ≠ i := by
        intro he
        subst j
        omega
      simpa only [hc, hz, hm, if_neg hji, if_neg hk0] using
        actual_GramDual_pairing K mu chi z a s alpha m hg hdet j i
  have he : (fun y => (∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu) *
      actualGramDual K mu chi z a s alpha m i y) =
      (fun y => ∑ k ∈ Finset.range (m i+1),
        ((∫ g, h g * genuineMellinJet K (chi i) (z i) a k g ∂mu) * ((m i).choose k : ℂ)) *
          (genuineMellinJet K (chi i) (z i) a (m i-k) y *
            actualGramDual K mu chi z a s alpha m i y)) := by
    funext y
    rw [actual_compact_measured_jet_action K (chi i) mu (z i) a h hh hs (m i) y,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, integral_finset_sum]
  · simp_rw [integral_const_mul]
    calc
      _ = ∑ k ∈ Finset.range (m i+1),
          ((∫ g, h g * genuineMellinJet K (chi i) (z i) a k g ∂mu) * ((m i).choose k : ℂ)) *
            (if k = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hp k (by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))]
      _ = _ := by simp
  · intro k hk
    exact (hi k).const_mul _

end Masullo.GramDualPairingIntegrable

namespace Masullo.GramDualNativeMemLp
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.TransposeDiagonalIntegrable Masullo.ActualGram Masullo.GramDualPairingIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_GramDual_native_memLp
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (i : ι) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      actualGramDual K mu chi z a s alpha m i x) 2 mu := by
  unfold actualGramDual
  simp_rw [Finset.mul_sum, mul_left_comm (nativeHalfWeight alpha s (classLog K _) : ℂ)]
  exact memLp_finset_sum _ (fun j hj =>
    (actualRiesz_memLp K mu (chi j) (z j) a s alpha (m j) (hg j)).const_mul _)

omit [Fintype ι] [DecidableEq ι] in
theorem closed_family_native_admission
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m) (i : ι) (k : ℕ) (hk : k ≤ m i) :
    MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu := by
  obtain ⟨j, hc, hz, hm⟩ := hclosed i k hk
  simpa only [hc, hz, hm] using hg j

/-- The actual inverse-Gram PA diagonal is integrable with ORIGINAL Haar.
No integrable-diagonal premise and no independent output-column premise. -/
theorem actual_Gram_PA_diagonal_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    Integrable (fun x => finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x) mu := by
  exact actual_finite_PA_diagonal_integrable K Finset.univ mu chi z a s alpha m h
    (actualGramDual K mu chi z a s alpha m) hh hs
    (fun i hi k hk => closed_family_native_admission K mu chi z a s alpha m hg hclosed i k hk)
    (fun i hi => actual_GramDual_native_memLp K mu chi z a s alpha m hg i)

/-- The explicitly chosen genuine PA diagonal integrates to the complete
finite jet-multiplicity sum. This is a direct arithmetic diagonal identity,
not a restriction of a product-a.e. kernel equality. -/
theorem actual_Gram_PA_diagonal_integral
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    (∫ x, finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x ∂mu) =
      ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu := by
  unfold finitePAKernel
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    simpa only [mul_comm] using actual_GramDual_PA_coefficient K mu chi z a s alpha m
      hg hdet hclosed h hh hs i
  · intro i hi
    simpa only [mul_comm] using actual_transpose_diagonal_integrable K mu (chi i) (z i)
      a s alpha (m i) h (actualGramDual K mu chi z a s alpha m i) hh hs
      (closed_family_native_admission K mu chi z a s alpha m hg hclosed i)
      (actual_GramDual_native_memLp K mu chi z a s alpha m hg i)

end Masullo.GramDualNativeMemLp


-- Integrated supplier: inputs/exchange/G/GConvolutionFragment.lean
/- Insert after RJetFragment. Exact repository convolution bridge, followed by assembly adapters. -/
namespace Masullo.WeightedConvolutionIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeTranslatedProductIntegrable
variable (K : Type*) [Field K] [NumberField K]

/-- Attach the proven weighted-vector integrability to the ORIGINAL convolution
integrand by the actual quotient-Haar shear (g,x) ↦ (g,g⁻¹*x). -/
theorem actual_weighted_convolution_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m p.2 * f (p.1⁻¹*p.2)) (mu.prod mu) := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  have hp : MeasurePreserving
      (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => (p.1,p.1⁻¹*p.2))
      (mu.prod mu) (mu.prod mu) := by
    exact measurePreserving_prod_inv_mul mu mu
  have hr := (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  simpa only [Function.comp_def, mul_inv_cancel_left] using hr

/-- The actual SAME-Haar convolution paired with an admitted weighted vector.
The product-integrability/Fubini premise is proved, not assumed. -/
theorem actual_weighted_convolution_pairing
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, genuineMellinJet K chi z a m x * (∫ g, h g * f (g⁻¹*x) ∂mu) ∂mu) =
      ∫ g, h g * (∫ y, genuineMellinJet K chi z a m (g*y) * f y ∂mu) ∂mu := by
  have hi := actual_weighted_convolution_integrable K mu chi z a s alpha m h f hh hs hg hf
  have he : (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m p.2 * f (p.1⁻¹*p.2)) =
    (fun p => genuineMellinJet K chi z a m p.2 * (h p.1 * f (p.1⁻¹*p.2))) := by
    funext p; ring
  rw [he] at hi
  simp only [← integral_const_mul]
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  have hv := integral_mul_left_eq_self (μ := mu)
    (fun x => genuineMellinJet K chi z a m x * (h g * f (g⁻¹*x))) g
  dsimp only
  rw [← hv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by simp only [inv_mul_cancel_left]; ring)

end Masullo.WeightedConvolutionIntegrable

namespace Masullo.NativePairingInner
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeRep Masullo.NativePettisVectorBound
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

 omit [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
   [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu] in
 theorem native_pairing_inner (j : HeckeIdeleClasses K → ℂ) (hj : MemLp j 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, j x * F x ∂mu) = inner ℂ (hj.star.toLp (star j)) F := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hj.star.coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, Pi.star_apply, starRingEnd_apply, star_star]
  ring

 omit [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
   [SFinite mu] [IsLocallyFiniteMeasure mu] in
 theorem native_translation_mellin (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a : ℝ) (m : ℕ) (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z a s alpha m x *
      nativeTranslationCLM K mu alpha s ha hs g F x ∂mu) =
      ∫ y, genuineMellinJet K chi z a m (g*y) * nativeRep K mu alpha s F y ∂mu := by
  calc
    _ = ∫ x, genuineMellinJet K chi z a m x * nativeRep K mu alpha s F (g⁻¹*x) ∂mu := by
      apply integral_congr_ae
      filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs g F] with x hx
      rw [hx, ← mul_assoc, genuineMellinJet_normalization]
      rfl
    _ = _ := by
      have ht := integral_mul_left_eq_self (μ := mu)
        (fun x => genuineMellinJet K chi z a m x * nativeRep K mu alpha s F (g⁻¹*x)) g
      simpa only [inv_mul_cancel_left] using ht.symm

/-- Attach the constructed bounded Pettis convolution to the ACTUAL same-Haar
measured convolution, on every original normalized native Mellin functional.
Neither an operator action nor a scalar pairing identity is assumed. -/
theorem actual_bounded_convolution_mellin
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z a s alpha m x *
      nativeConvolutionCLM K mu alpha s ha hs h hh hc F x ∂mu) =
      ∫ x, genuineMellinJet K chi z a m x *
        (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu) ∂mu := by
  rw [native_pairing_inner K mu _ (hg m le_rfl), nativeConvolutionCLM_pairing]
  calc
    _ = ∫ g, h g * (∫ y, genuineMellinJet K chi z a m (g*y) *
        nativeRep K mu alpha s F y ∂mu) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [← native_pairing_inner K mu _ (hg m le_rfl),
        native_translation_mellin K mu alpha s ha hs chi z a m g F]
    _ = _ := (Masullo.WeightedConvolutionIntegrable.actual_weighted_convolution_pairing
      K mu chi z a s alpha m h (nativeRep K mu alpha s F) hh hc hg
      (nativeRep_memLp K mu alpha s F)).symm

end Masullo.NativePairingInner

namespace GIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.NativeRep Masullo.NativePairingInner
open Masullo.NativePettisVectorBound Masullo.NativeTranslatedProductIntegrable
open Masullo.NativeConvolutionProductIntegrable Masullo.NativeWeightedConvolutionTriangular

variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)

/-- The unweighted jet functional on the actual weighted representative is
exactly its normalized L2 pairing, with the same Haar measure. -/
theorem native_jet_pairing_normalized (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (F : Lp ℂ 2 mu) :
    (∫ x, genuineMellinJet K chi z a m x * nativeRep K mu alpha s F x ∂mu) =
      ∫ x, genuineNormalizedMellinJet K chi z a s alpha m x * F x ∂mu := by
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← genuineMellinJet_normalization K chi z a s alpha m x]
  rw [mul_assoc, nativeRep_normalization]

/-- Exact triangular chain action of the ACTUAL bounded convolution in the
canonical assembly. No abstract action or eigenvalue identity is assumed. -/
theorem nativeConvolutionCLM_triangular (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z a s alpha m x *
      nativeConvolutionCLM K mu alpha s ha hs h hh hc F x ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        ((∫ g, h g * genuineMellinJet K chi z a k g ∂mu) * (m.choose k : ℂ)) *
          (∫ y, genuineNormalizedMellinJet K chi z a s alpha (m-k) y * F y ∂mu) := by
  rw [actual_bounded_convolution_mellin K mu alpha s ha hs chi z a m h hh hc hg F]
  simp_rw [mul_comm (genuineMellinJet K chi z a m _)]
  rw [native_weighted_convolution_triangular K mu chi z a s alpha m h
    (nativeRep K mu alpha s F) hh hc hg (nativeRep_memLp K mu alpha s F)]
  simp_rw [native_jet_pairing_normalized K mu alpha s]


end GIntegrated

namespace GIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open PIntervalConvolution

/-- The interval midpoint shifts the dual parameter by the same amount as
it twists the convolution test. Thus the original Mellin coefficient is retained. -/
theorem midpoint_jet_cancellation
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a b : ℝ) (m : ℕ)
    (x : HeckeIdeleClasses K) :
    radialTwist K b x * genuineMellinJet K chi z (a+b) m x =
      genuineMellinJet K chi z a m x := by
  unfold radialTwist genuineMellinJet
  have he : (b : ℂ) * (classLog K x : ℂ) +
      (z - ((a+b : ℝ) : ℂ)) * (classLog K x : ℂ) =
      (z - (a : ℂ)) * (classLog K x : ℂ) := by push_cast; ring
  calc
    _ = (classCharacter K chi x : ℂ) *
        (Complex.exp ((b : ℂ) * (classLog K x : ℂ)) *
        Complex.exp ((z - ((a+b : ℝ) : ℂ)) * (classLog K x : ℂ))) *
        ((classLog K x ^ m : ℝ) : ℂ) := by ring
    _ = _ := by rw [← Complex.exp_add, he]

/-- The nonsymmetric interval operator from the common contract has the
original untwisted Mellin coefficients. The centered dual parameter is a+b. -/
theorem intervalConvolutionCLM_triangular
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z
      (a+(l+r)/2) s ((r-l)/2) k) 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m x *
      intervalConvolutionCLM K mu l r s hlr hs h hh hc F x ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        ((∫ g, h g * genuineMellinJet K chi z a k g ∂mu) * (m.choose k : ℂ)) *
          (∫ y, genuineNormalizedMellinJet K chi z (a+(l+r)/2)
            s ((r-l)/2) (m-k) y * F y ∂mu) := by
  unfold intervalConvolutionCLM
  rw [nativeConvolutionCLM_triangular K mu ((r-l)/2) s (by linarith) hs
    (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2
    chi z (a+(l+r)/2) m hg F]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (fun g => (radialTwist K ((l+r)/2) g * h g) *
      genuineMellinJet K chi z (a+(l+r)/2) k g) =
      (fun g => h g * genuineMellinJet K chi z a k g) := by
    funext g
    rw [mul_comm (radialTwist K ((l+r)/2) g) (h g), mul_assoc,
      midpoint_jet_cancellation]
  rw [he]

end GIntegrated



-- Integrated supplier: inputs/exchange/B/BProjection.lean
/- B fragment: insert after G supplies Masullo.NativePairingInner.
   Existing names retained; D owns the subsequent GramCompletedKernelAction block. -/
namespace Masullo.InverseGramProjection
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeRep Masullo.NativePettisVectorBound Masullo.NativePairingInner
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

/-- Actual finite PA on every vector of the completed native realization.
The bounded convolution is constructed from the original Haar translations;
its Mellin coefficients are the original convolution integrals. No separate
MemLp hypothesis for the output of that integral is assumed. -/
theorem actual_completed_orthogonal_PA_action
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hg : ∀ i, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hG : IsUnit (Matrix.det (fun i j => inner ℂ
      ((hg i (m i) le_rfl).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i))))
      ((hg j (m j) le_rfl).star.toLp
        (star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j)))))))
    (F : Lp ℂ 2 mu) :
    let r : ι → Lp ℂ 2 mu := fun i => (hg i (m i) le_rfl).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    (Submodule.span ℂ (Set.range r)).starProjection
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∑ j, (((fun i j => inner ℂ (r i) (r j)) : Matrix ι ι ℂ)⁻¹ *ᵥ
        (fun i => ∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
          (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu) ∂mu)) j • r j := by
  dsimp only
  rw [inverseGram_projection _ hG]
  have hi (i : ι) : inner ℂ
      ((hg i (m i) le_rfl).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i))))
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
        (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu) ∂mu := by
    rw [← native_pairing_inner K mu _ (hg i (m i) le_rfl)]
    exact actual_bounded_convolution_mellin K mu alpha s ha hs
      (chi i) (z i) a (m i) h hh hc (hg i) F
  simp_rw [hi]

end Masullo.InverseGramProjection


-- Integrated supplier: inputs/exchange/D/DProjectedKernelFragment.lean
namespace Masullo.GramCompletedKernelAction
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.TransposeDiagonalIntegrable Masullo.ActualGram Masullo.GramDualNativeMemLp Masullo.InverseGramProjection
open Masullo.NativeRep Masullo.NativePettisVectorBound
open scoped Matrix BigOperators InnerProductSpace
variable (K : Type*) [Field K] [NumberField K]

/-- The explicit original-Haar kernel acts as genuine finite orthogonal
projection AFTER completed native convolution, on every native input.
No output-admission or kernel-representation hypothesis is assumed. -/
theorem actual_Gram_completed_kernel_action
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hg : ∀ i, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hG : IsUnit (actualGram K mu chi z a s alpha m).det)
    (F : Lp ℂ 2 mu) :
    let r : ι → Lp ℂ 2 mu := fun i => (hg i (m i) le_rfl).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    (fun x => ((Submodule.span ℂ (Set.range r)).starProjection
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F)) x) =ᵐ[mu]
    (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      ∫ y, finitePAKernel K Finset.univ mu chi z a m h
        (actualGramDual K mu chi z a s alpha m) x y * nativeRep K mu alpha s F y ∂mu) := by
  classical
  let r : ι → Lp ℂ 2 mu := fun i => (hg i (m i) le_rfl).star.toLp
    (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
  let v : ι → ℂ := fun i => ∫ y, (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*y) ∂mu) *
    genuineMellinJet K (chi i) (z i) a (m i) y ∂mu
  let c := (actualGram K mu chi z a s alpha m)⁻¹ *ᵥ v
  have hmat : (fun i j => inner ℂ (r i) (r j)) = actualGram K mu chi z a s alpha m := by
    funext i j
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hg i (m i) le_rfl).star.coeFn_toLp,
      (hg j (m j) le_rfl).star.coeFn_toLp] with x hx hy
    change r i x = _ at hx
    change r j x = _ at hy
    rw [hx, hy]
    rw [actual_Gram_density]
    simp [RCLike.inner_apply, mul_comm]
  have hp : (Submodule.span ℂ (Set.range r)).starProjection
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) = ∑ j, c j • r j := by
    have hg' : IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j))) := by rwa [hmat]
    have hp := actual_completed_orthogonal_PA_action K mu chi z m a s alpha ha hs
      hg h hh hc hg' F
    change _ = ∑ j, _ • r j at hp
    rw [hmat] at hp
    simpa only [c, v, mul_comm] using hp
  have he (T : Finset ι) :
      (fun x => (∑ j ∈ T, c j • r j) x) =ᵐ[mu]
      (fun x => ∑ j ∈ T, c j * star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j) x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • r i) (∑ j ∈ T, c j • r j),
        Lp.coeFn_smul (c i) (r i), (hg i (m i) le_rfl).star.coeFn_toLp, ih] with x hx hs hj ht
      change r i x = _ at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  change (fun x => ((Submodule.span ℂ (Set.range r)).starProjection
    (nativeConvolutionCLM K mu alpha s ha hs h hh hc F)) x) =ᵐ[mu] _
  rw [hp]
  filter_upwards [he Finset.univ] with x hx
  rw [hx, ← actual_finite_PA_kernel_action K Finset.univ mu chi z a s alpha m h
    (nativeRep K mu alpha s F) (actualGramDual K mu chi z a s alpha m) hh hc
    (fun i _ => hg i) (nativeRep_memLp K mu alpha s F) x]
  change (∑ j, c j * star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j) x)) =
    (nativeHalfWeight alpha s (classLog K x) : ℂ) * ∑ i, actualGramDual K mu chi z a s alpha m i x * v i
  simp only [c, Matrix.mulVec, dotProduct, actualGramDual, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← actualRiesz_weighted K (chi j) (z j) a s alpha (m j) x]
  ring

end Masullo.GramCompletedKernelAction


-- Integrated supplier: inputs/exchange/H/HDiagonalSeriesFragment.lean
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

end Masullo.WeightedDiagonalFactorization


-- Integrated supplier: inputs/exchange/M/MPartitionFragment.lean
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


-- Integrated supplier: inputs/exchange/F/FIntervalPhysical.lean
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



-- Integrated supplier: inputs/exchange/K/KMaskCore.lean

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace KPhysicalMask

/-- An error estimate on the original measure. The plateau, rather than an
assumed limit, localizes the entire error to the complement. -/
theorem real_mask_error_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (d : X → ℂ) (hd : Integrable d mu)
    (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ S, rho x = 1) :
    ‖(∫ x, (rho x : ℂ) * d x ∂mu) - ∫ x, d x ∂mu‖ ≤
      ∫ x, Sᶜ.indicator (fun y => ‖d y‖) x ∂mu := by
  have hr : Integrable (fun x => (rho x : ℂ) * d x) mu := by
    apply hd.norm.mono' (hm.complex_ofReal.aestronglyMeasurable.mul hd.aestronglyMeasurable)
    filter_upwards [] with x
    change ‖(rho x : ℂ) * d x‖ ≤ ‖d x‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb x).2
  have he : Integrable (fun x => (rho x : ℂ) * d x - d x) mu := hr.sub hd
  have ht : Integrable (Sᶜ.indicator (fun y => ‖d y‖)) mu := hd.norm.indicator hS.compl
  rw [← integral_sub hr hd]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono he.norm ht
  intro x
  by_cases hx : x ∈ S
  · simp [hp x hx, hx]
  · have hsub : |rho x - 1| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hb x).2)]
      linarith [(hb x).1]
    have heq : (rho x : ℂ) * d x - d x = ((rho x - 1 : ℝ) : ℂ) * d x := by
      push_cast
      ring
    change ‖(rho x : ℂ) * d x - d x‖ ≤ _
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simpa [hx] using mul_le_of_le_one_left (norm_nonneg (d x)) hsub

/-- Finite original-Haar densities need only the actual L1 application. -/
theorem real_mask_finite_error_bound {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) (S : Set X) (hS : MeasurableSet S)
    (F : Finset ι) (d : ι → X → ℂ)
    (hd : ∀ i ∈ F, Integrable (d i) mu)
    (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ S, rho x = 1) :
    ‖(∫ x, (rho x : ℂ) * (∑ i ∈ F, d i x) ∂mu) -
      ∫ x, (∑ i ∈ F, d i x) ∂mu‖ ≤
      ∫ x, Sᶜ.indicator (fun y => ‖∑ i ∈ F, d i y‖) x ∂mu := by
  exact real_mask_error_bound mu S hS _ (integrable_finset_sum F hd) rho hm hb hp

/-- Explicit contraction for a nonnegative real physical mask on any of the
original weighted L2 representatives; the weight is not discarded. -/
theorem weighted_real_mask_eLpNorm {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (w : X → ℝ) (rho : X → ℝ)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : X → ℂ) :
    eLpNorm (fun x => (w x : ℂ) * ((rho x : ℂ) * f x)) 2 mu ≤
      eLpNorm (fun x => (w x : ℂ) * f x) 2 mu := by
  apply eLpNorm_mono_ae
  filter_upwards [] with x
  have hx : ‖(rho x : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2
  calc
    ‖(w x : ℂ) * ((rho x : ℂ) * f x)‖ =
        ‖(rho x : ℂ)‖ * ‖(w x : ℂ) * f x‖ := by simp only [norm_mul]; ring
    _ ≤ ‖(w x : ℂ) * f x‖ := mul_le_of_le_one_left (norm_nonneg _) hx

end KPhysicalMask



-- Integrated supplier: inputs/exchange/E/SourceTailFragment.lean
/-! Append after the canonical seed. E's source-tail fragment.
The original Haar measure remains mu; Lp representatives already contain the
native interval half-weight. All families below are fixed finite families. -/
namespace EIntegratedTail
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass PIntervalConvolution OSourceClosure
open scoped Topology BigOperators
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Dominated convergence for each ORIGINAL weighted Gram entry. The caller
sets d = w_beta * conjugate(r_i) * r_j, with r_j = S_beta kappa_j. -/
theorem tail_entry_tendsto (mu : Measure X) (d : X → ℂ)
    (hd : Integrable d mu) (psi : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (psi n))
    (hbound : ∀ n x, 0 ≤ psi n x ∧ psi n x ≤ 1)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => psi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (((1 - psi n x)^2 : ℝ) : ℂ) * d x ∂mu)
      atTop (𝓝 0) := by
  have hb (n : ℕ) (x : X) : |(1 - psi n x)^2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hp := hbound n x
    nlinarith [sq_nonneg (psi n x)]
  have ht : Tendsto (fun n => ∫ x, (((1 - psi n x)^2 : ℝ) : ℂ) * d x ∂mu)
      atTop (𝓝 (∫ _ : X, (0 : ℂ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
    · intro n
      exact (((measurable_const.sub (hm n)).pow_const 2).complex_ofReal.aestronglyMeasurable).mul hd.aestronglyMeasurable
    · exact hd.norm
    · intro n
      filter_upwards [] with x
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb n x)
    · filter_upwards [hlim] with x hx
      have hh := ((tendsto_const_nhds (x := (1 : ℝ))).sub hx).pow 2
      have hhC := Complex.continuous_ofReal.continuousAt.tendsto.comp hh
      simpa using hhC.mul_const (d x)
  simpa using ht

/-- Full finite inverse-Gram contraction; off-diagonal entries are retained. -/
theorem tail_gram_contraction_tendsto {κ : Type*} [Fintype κ]
    (mu : Measure X) (Ginv : Matrix κ κ ℂ) (d : κ → κ → X → ℂ)
    (hd : ∀ i j, Integrable (d i j) mu) (psi : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (psi n))
    (hb : ∀ n x, 0 ≤ psi n x ∧ psi n x ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => psi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∑ i, ∑ j, Ginv i j *
      ∫ x, (((1 - psi n x)^2 : ℝ) : ℂ) * d j i x ∂mu)
      atTop (𝓝 0) := by
  have hi (i j : κ) := (tail_entry_tendsto mu (d j i) (hd j i) psi hm hb hl).const_mul (Ginv i j)
  have hj (i : κ) := tendsto_finset_sum Finset.univ (fun j _ => hi i j)
  simpa using tendsto_finset_sum Finset.univ (fun i _ => hj i)

variable (K : Type*) [Field K] [NumberField K]

def physicalMask (n : ℕ) (x : HeckeIdeleClasses K) : ℝ :=
  if x ∈ DReview.physicalBand K n then 1 else 0

theorem physicalMask_measurable (n : ℕ) : Measurable (physicalMask K n) := by
  exact Measurable.ite (DReview.physicalBand_measurable K n)
    measurable_const measurable_const

theorem physicalMask_bounds (n : ℕ) (x : HeckeIdeleClasses K) :
    0 ≤ physicalMask K n x ∧ physicalMask K n x ≤ 1 := by
  unfold physicalMask
  split_ifs <;> norm_num

theorem physicalMask_tendsto (x : HeckeIdeleClasses K) :
    Tendsto (fun n => physicalMask K n x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hx : x ∈ DReview.physicalBand K n := hN.trans (by exact_mod_cast hn)
  simp [physicalMask, hx]

/-- Finite Gram contraction of the physical tail, retaining all cross entries. -/
def physicalTailGram {ι : Type*} [Fintype ι]
    (mu : Measure (HeckeIdeleClasses K)) (Ginv : Matrix ι ι ℂ)
    (r : ι → Lp ℂ 2 mu) (n : ℕ) : ℂ :=
  ∑ i, ∑ j, Ginv i j * ∫ x,
    (((1 - physicalMask K n x)^2 : ℝ) : ℂ) * (star (r j x) * r i x) ∂mu

/-- L2 membership discharges every entry's integrability hypothesis. -/
theorem lp_physical_tail_gram {ι : Type*} [Fintype ι]
    (mu : Measure (HeckeIdeleClasses K)) (Ginv : Matrix ι ι ℂ)
    (r : ι → Lp ℂ 2 mu) :
    Tendsto (physicalTailGram K mu Ginv r) atTop (𝓝 0) := by
  unfold physicalTailGram
  apply tail_gram_contraction_tendsto
  · intro i j
    exact (Lp.memLp (r i)).star.integrable_mul (Lp.memLp (r j))
  · exact physicalMask_measurable K
  · exact physicalMask_bounds K
  · exact Filter.Eventually.of_forall (physicalMask_tendsto K)

/-- Concrete application to the canonical original two-moment source closure.
No alternate source admission type, normalization, or independent projection. -/
theorem actual_source_physical_tail_gram {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V]
    (mu : Measure (HeckeIdeleClasses K)) (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (Ginv : Matrix ι ι ℂ) (kappa : ι → Lp ℂ 2 mu) :
    Tendsto (physicalTailGram K mu Ginv
      (fun i => (sourceClosure e0 eF Theta).starProjection (kappa i)))
      atTop (𝓝 0) :=
  lp_physical_tail_gram K mu Ginv _

variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Actual convolution FIRST, then the genuine complementary source projection.
This proves the finite output-tail assertion for PA on every input packet. -/
theorem actual_PA_physical_tail_gram {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (Ginv : Matrix ι ι ℂ) (kappa : ι → Lp ℂ 2 mu) :
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (sourceClosure e0 eF Theta).starProjection
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A) (kappa i)))
      atTop (𝓝 0) := by
  exact lp_physical_tail_gram K mu Ginv _

/-- Both manuscript test partners are instantiated, with their actual compact
support proofs. The logged sharp sign is supplied by DReview.sharp_log. -/
theorem both_tests_PA_physical_tail_gram {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℂ V]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (Ginv : Matrix ι ι ℂ) (kappa : ι → Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (sourceClosure e0 eF Theta).starProjection
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A0) (kappa i))) atTop (𝓝 0) ∧
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A1) (kappa i))) atTop (𝓝 0) := by
  constructor <;> exact lp_physical_tail_gram K mu Ginv _

end
end EIntegratedTail


-- Integrated supplier: inputs/exchange/Q/QSourceCutoffFragment.lean
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


-- Integrated supplier: inputs/exchange/C/CNormalization.lean
/-! C insertion fragment. Requires the canonical seed plus HKernelFragment.lean.
    The seed already uses original Haar mu; specialize H's scale V to one. -/
namespace CNormalization
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.NativeRep
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ)

/-- H's original-Haar kernel in the exact same-Haar realization of the seed. -/
def nativeHaarKernel (U R : Lp ℂ 2 mu) :
    HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ :=
  HNormalizedKernel.haarKernel
    (fun x => nativeHalfWeight alpha s (classLog K x)) 1 U R

/-- Full-input action on the seed's original weighted representatives. -/
theorem native_kernel_action (U R F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) :
    (∫ y, nativeHaarKernel K mu alpha s U R x y * nativeRep K mu alpha s F y ∂mu) =
      inner ℂ R F * nativeRep K mu alpha s U x := by
  have hb : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  have h := HNormalizedKernel.kernel_action mu
    (fun y => nativeHalfWeight alpha s (classLog K y))
    (fun y => nativeHalfWeight_pos _ _ _) 1 zero_lt_one U R F x
  have he : (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      (∫ y, nativeHaarKernel K mu alpha s U R x y * nativeRep K mu alpha s F y ∂mu) =
      inner ℂ R F * U x := by
    simpa only [nativeHaarKernel, nativeRep, ENNReal.ofReal_one, one_smul] using h
  apply mul_left_cancel₀ hb
  rw [he]
  unfold nativeRep
  field_simp

/-- The diagonal keeps original Haar and contains no extra covolume factor. -/
theorem native_kernel_diagonal (U R : Lp ℂ 2 mu) :
    Integrable (fun x => nativeHaarKernel K mu alpha s U R x x) mu ∧
    (∫ x, nativeHaarKernel K mu alpha s U R x x ∂mu) = inner ℂ R U := by
  constructor
  · simpa only [nativeHaarKernel, ENNReal.ofReal_one, one_smul] using
      HNormalizedKernel.diagonal_integrable mu
        (fun x => nativeHalfWeight alpha s (classLog K x))
        (fun x => nativeHalfWeight_pos _ _ _) 1 U R
  · simpa only [nativeHaarKernel, ENNReal.ofReal_one, one_smul] using
      HNormalizedKernel.diagonal_integral mu
        (fun x => nativeHalfWeight alpha s (classLog K x))
        (fun x => nativeHalfWeight_pos _ _ _) 1 zero_lt_one U R

/-- Application of the seed's physical exhaustion to that specified diagonal. -/
theorem native_kernel_physical_limit (U R : Lp ℂ 2 mu) :
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
      (fun x => nativeHaarKernel K mu alpha s U R x x) x ∂mu)
      atTop (𝓝 (inner ℂ R U)) := by
  have h := native_kernel_diagonal K mu alpha s U R
  rw [← h.2]
  exact DReview.originalHaar_physical_limit K mu _ h.1

end
end CNormalization


-- Integrated supplier: inputs/exchange/I/IFiniteKernelFragment.lean
/- Insert after IArithmeticKernelCore and the seed DReview block.
   This is a finite-kernel statement. The global theta-complement identification
   is supplied separately by the common assembly. -/
namespace ReviewI.Integration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The arithmetic finite kernel acts after measured convolution. Both its
original-Haar diagonal and the literal complementary kernel have physical
cutoff limits. The latter has a negative diagonal because h(1)=0. -/
theorem finite_kernel_diagonal_cutoff
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (h1 : h 1 = 0) :
    let u := actualGramDual K mu chi z a s alpha m
    let ker := finitePAKernel K Finset.univ mu chi z a m h u
    let spectral := ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu
    (∀ f : HeckeIdeleClasses K → ℂ,
      MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu →
      ∀ x, (∑ i, u i x * (∫ y, (∫ g, h g * f (g⁻¹*y) ∂mu) *
        genuineMellinJet K (chi i) (z i) a (m i) y ∂mu)) =
        ∫ y, ker x y * f y ∂mu) ∧
    Integrable (fun x => ker x x) mu ∧
    (∫ x, ker x x ∂mu) = spectral ∧
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
      (fun y => ker y y) x ∂mu) atTop (𝓝 spectral) ∧
    (∀ x, h (x*x⁻¹) - ker x x = -ker x x) ∧
    Integrable (fun x => h (x*x⁻¹) - ker x x) mu ∧
    (∫ x, h (x*x⁻¹) - ker x x ∂mu) = -spectral ∧
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
      (fun y => h (y*y⁻¹) - ker y y) x ∂mu) atTop (𝓝 (-spectral)) := by
  dsimp only
  let ker := finitePAKernel K Finset.univ mu chi z a m h
    (actualGramDual K mu chi z a s alpha m)
  have hd := actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m
    hg hclosed h hh hc
  have he := actual_Gram_PA_diagonal_integral K mu chi z a s alpha m
    hg hdet hclosed h hh hc
  have hneg : (fun x => h (x*x⁻¹) - ker x x) = (fun x => -ker x x) := by
    funext x
    simp only [mul_inv_cancel, h1, zero_sub]
  have hgd : Integrable (fun x => h (x*x⁻¹) - ker x x) mu := by
    rw [hneg]
    exact hd.neg
  have hge : (∫ x, h (x*x⁻¹) - ker x x ∂mu) =
      -(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu) := by
    rw [hneg, integral_neg]
    exact congrArg Neg.neg he
  refine ⟨?_, hd, he, ?_, ?_, hgd, hge, ?_⟩
  · intro f hf x
    exact actual_finite_PA_kernel_action K Finset.univ mu chi z a s alpha m h f
      (actualGramDual K mu chi z a s alpha m) hh hc
      (fun i _ => closed_family_native_admission K mu chi z a s alpha m hg hclosed i) hf x
  · have ht := DReview.originalHaar_physical_limit K mu (fun x => ker x x) hd
    rw [he] at ht
    exact ht
  · intro x
    exact congrFun hneg x
  · have ht := DReview.originalHaar_physical_limit K mu _ hgd
    rw [hge] at ht
    exact ht

/-- Both requested sharp tests satisfy the finite kernel/diagonal cutoff
statement with the same arithmetic parameters. This uses the common sharp
definition and proves the test hypotheses from phi on the actual quotient. -/
theorem both_sharp_finite_kernel_diagonal
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) :
    ∀ h ∈ ({DReview.sharp K phi,
      DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)} :
        Set (HeckeIdeleClasses K → ℂ)),
    let u := actualGramDual K mu chi z a s alpha m
    let ker := finitePAKernel K Finset.univ mu chi z a m h u
    let spectral := ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu
    (∀ f : HeckeIdeleClasses K → ℂ,
      MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu →
      ∀ x, (∑ i, u i x * (∫ y, (∫ g, h g * f (g⁻¹*y) ∂mu) *
        genuineMellinJet K (chi i) (z i) a (m i) y ∂mu)) =
        ∫ y, ker x y * f y ∂mu) ∧
    Integrable (fun x => ker x x) mu ∧
    (∫ x, ker x x ∂mu) = spectral ∧
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
      (fun y => ker y y) x ∂mu) atTop (𝓝 spectral) ∧
    (∀ x, h (x*x⁻¹) - ker x x = -ker x x) ∧
    Integrable (fun x => h (x*x⁻¹) - ker x x) mu ∧
    (∫ x, h (x*x⁻¹) - ker x x ∂mu) = -spectral ∧
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
      (fun y => h (y*y⁻¹) - ker y y) x ∂mu) atTop (𝓝 (-spectral)) := by
  have hz : classLog K (1 : HeckeIdeleClasses K) = 0 := by
    have ht := Masullo.WeightedIdeleClass.classLog_mul K (1 : HeckeIdeleClasses K) 1
    simp only [one_mul] at ht
    linarith
  have ht := DReview.both_sharp_tests_compact K phi hh hc
  intro h hm
  rcases Set.mem_insert_iff.mp hm with he | hm
  · subst h
    exact finite_kernel_diagonal_cutoff K mu chi z m a s alpha hg hdet hclosed _
      ht.1.1 ht.1.2 (DReview.sharp_vanishes_normOne K phi hphi 1 hz)
  · have he := Set.mem_singleton_iff.mp hm
    subst h
    exact finite_kernel_diagonal_cutoff K mu chi z m a s alpha hg hdet hclosed _
      ht.2.1 ht.2.2 (DReview.sharp_vanishes_normOne K _
        (fun x hx => by simp [hx]) 1 hz)

end
end ReviewI.Integration


-- Integrated supplier: inputs/exchange/N/NShellFragment.lean
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


-- Integrated supplier: inputs/exchange/J/JThetaEquivariance.lean
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


-- Integrated supplier: inputs/exchange/J/JOriginalSourceAction.lean
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


-- Integrated supplier: inputs/exchange/O/OArithmeticOperators.lean
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

variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Application to both constructed arithmetic convolutions and the genuine
projection onto the chosen admitted theta closure. Convolution is performed
first. No invariance premise or assumed density is needed for these limits. -/
theorem both_tests_arithmetic_source_exhaustion
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ)
    (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (x : Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun y => (classLog K y : ℂ) * phi y)) tests.2.1 tests.2.2
    let S := (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
    let F := fun T : Finset (Lp ℂ 2 mu) => Submodule.span ℂ
      ((T : Set (Lp ℂ 2 mu)) ∩ Set.range
        (sourceVector K (addHaar := addHaar) (nu := mu) (chi := chi)
          (a := a+(l+r)/2) (alpha := (r-l)/2) (s := s)))
    ∃ p0 p1 : Finset (Lp ℂ 2 mu) → Lp ℂ 2 mu,
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p0 T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (F T) hp (A0 x)) ∧
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p1 T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (F T) hp (A1 x)) ∧
      Tendsto (fun T => A0 x-p0 T) atTop (𝓝 (A0 x-S (A0 x))) ∧
      Tendsto (fun T => A1 x-p1 T) atTop (𝓝 (A1 x-S (A1 x))) := by
  dsimp only
  have tests := DReview.both_sharp_tests_compact K phi hh hc
  obtain ⟨p0, hp0, _, ht0⟩ := actual_theta_source_exhaustion K addHaar mu chi
    (a+(l+r)/2) ((r-l)/2) s
    (intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2 x)
  obtain ⟨p1, hp1, _, ht1⟩ := actual_theta_source_exhaustion K addHaar mu chi
    (a+(l+r)/2) ((r-l)/2) s
    (intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun y => (classLog K y : ℂ) * phi y)) tests.2.1 tests.2.2 x)
  exact ⟨p0, p1, hp0, hp1, ht0, ht1⟩

end
end OArithmeticClosure


-- Integrated supplier: inputs/exchange/C/CThetaAdmission.lean
/- Insert after OArithmeticOperators.lean. O owns the pointwise transport;
   C supplies its precise Hilbert-admission interface. -/
namespace CNormalization
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem interval_theta_memLp_iff (mu : Measure (HeckeIdeleClasses K))
    (l r s a : ℝ) (hlr : l ≤ r) (f : HeckeAdeles K → ℂ) :
    MemLp (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
      (Real.exp (a * classLog K x) : ℂ) * Masullo.IdeleTheta.classTheta K f x) 2 mu ↔
      MemLp (normalizedTheta K (a + (l+r)/2) ((r-l)/2) s f) 2 mu := by
  have he : (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
      (Real.exp (a * classLog K x) : ℂ) * Masullo.IdeleTheta.classTheta K f x) =
      normalizedTheta K (a + (l+r)/2) ((r-l)/2) s f :=
    funext (OArithmeticClosure.interval_normalizedTheta K a l r s hlr f)
  rw [he]

end
end CNormalization


-- Integrated supplier: inputs/exchange/A/AOrderFragment.lean
/- Insert after PCombinedReview. This fragment uses the existing measured
convolution and source annihilation result; it does not assume commutation. -/
namespace AReview.Order
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The exact correction when an AP kernel is compared with the required PA.
Source invariance is supplied as PAQ=0, not as a reducing-space assumption. -/
theorem order_remainder_of_source_zero
    (A Q : H →L[ℂ] H)
    (hzero : ((((1 : H →L[ℂ] H) - Q).comp A).comp Q) = 0) :
    A.comp ((1 : H →L[ℂ] H) - Q) - ((1 : H →L[ℂ] H) - Q).comp A =
      Q.comp (A.comp ((1 : H →L[ℂ] H) - Q)) := by
  apply ContinuousLinearMap.ext
  intro x
  have hz := congrArg (fun T : H →L[ℂ] H => T x) hzero
  change A (Q x) - Q (A (Q x)) = 0 at hz
  have hq : Q (A (Q x)) = A (Q x) := (sub_eq_zero.mp hz).symm
  change A (x-Q x) - (A x-Q (A x)) = Q (A (x-Q x))
  simp only [map_sub, hq]
  abel

/-- The physical mask acts last, and the same correction survives before
any trace or cutoff passage. -/
theorem masked_order_remainder
    (A Q M : H →L[ℂ] H)
    (hzero : ((((1 : H →L[ℂ] H) - Q).comp A).comp Q) = 0) (x : H) :
    M (A (x-Q x)) - M (A x-Q (A x)) = M (Q (A (x-Q x))) := by
  have h := congrArg (fun T : H →L[ℂ] H => T x)
    (order_remainder_of_source_zero A Q hzero)
  change A (x-Q x) - (A x-Q (A x)) = Q (A (x-Q x)) at h
  simpa only [map_sub] using congrArg M h

end
end AReview.Order

namespace AReview.ArithmeticOrder
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OSourceClosure
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The seed's actual interval convolution, both sharp tests, and the genuine
source projection have this exact order correction under the displayed theta
equivariance hypotheses. No arithmetic theta admission is inferred here. -/
theorem both_tests_masked_order_remainder
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
    (M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (x : Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun y => (classLog K y : ℂ) * phi y)) tests.2.1 tests.2.2
    let S := (sourceClosure e0 eF Theta).starProjection
    (M (A0 (x-S x)) - M (A0 x-S (A0 x)) = M (S (A0 (x-S x)))) ∧
    (M (A1 (x-S x)) - M (A1 x-S (A1 x)) = M (S (A1 (x-S x)))) := by
  have hz := PCombinedReview.both_tests_original_source K mu l r s hlr hs
    e0 eF Theta B c0 cF h0 hF hint phi hh hc
  exact ⟨AReview.Order.masked_order_remainder _ _ M hz.1 x,
    AReview.Order.masked_order_remainder _ _ M hz.2 x⟩

end AReview.ArithmeticOrder


-- Integrated supplier: inputs/exchange/M/MSeriesFragment.lean
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


-- Integrated supplier: inputs/exchange/K/KPhysicalApplication.lean
/-! Append after KMaskCore (without its import), HKernelFragment, and
FIntervalPhysical. No arithmetic or kernel definitions are redeclared. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- Manuscript Remark 9.3.3.2 on the canonical, possibly nonsymmetric interval.
This contracts the original weighted representative, not its unweighted norm. -/
theorem interval_mask_contraction
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (rho : HeckeIdeleClasses K → ℝ)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : HeckeIdeleClasses K → ℂ) :
    eLpNorm (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) *
      ((rho x : ℂ) * f x)) 2 mu ≤
      eLpNorm (fun x => (intervalHalfWeight l r s (classLog K x) : ℂ) * f x) 2 mu :=
  weighted_real_mask_eLpNorm mu _ rho hb f

/-- Quantitative physical error for the canonical original-Haar kernel.
Its L1 hypothesis is proved from completed L2 columns; no diagonal
integrability or trace equality is supplied as an application premise. -/
theorem interval_kernel_mask_error
    (nu : Measure (HeckeIdeleClasses K)) (l r s V : ℝ) (hV : 0 < V)
    (U R : Lp ℂ 2 nu) (n : ℕ) (rho : HeckeIdeleClasses K → ℝ)
    (hm : Measurable rho) (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ DReview.physicalBand K n, rho x = 1) :
    ‖(∫ x, (rho x : ℂ) * HNormalizedKernel.haarKernel
      (fun y => intervalHalfWeight l r s (classLog K y)) V U R x x
        ∂(ENNReal.ofReal V • nu)) - inner ℂ R U‖ ≤
      ∫ x, (DReview.physicalBand K n)ᶜ.indicator
        (fun y => ‖HNormalizedKernel.haarKernel
          (fun z => intervalHalfWeight l r s (classLog K z)) V U R y y‖) x
        ∂(ENNReal.ofReal V • nu) := by
  rw [← HNormalizedKernel.diagonal_integral nu
    (fun y => intervalHalfWeight l r s (classLog K y))
    (fun y => FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K y)) V hV U R]
  exact real_mask_error_bound (ENNReal.ofReal V • nu) (DReview.physicalBand K n)
    (DReview.physicalBand_measurable K n) _
    (HNormalizedKernel.diagonal_integrable nu _
      (fun y => FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K y)) V U R)
    rho hm hb hp

/-- The mask estimate is applied to the actual completed convolution followed
by the orthogonal complement projection. The result controls a matrix
coefficient density; a global trace-series identification remains separate. -/
theorem actual_PA_coefficient_mask_error
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [E.HasOrthogonalProjection]
    (F R : Lp ℂ 2 mu) (n : ℕ) (rho : HeckeIdeleClasses K → ℝ)
    (hm : Measurable rho) (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ DReview.physicalBand K n, rho x = 1) :
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
    let U := (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - E.starProjection).comp A) F
    ‖(∫ x, (rho x : ℂ) * HNormalizedKernel.haarKernel
      (fun y => intervalHalfWeight l r s (classLog K y)) 1 U R x x ∂mu) -
        inner ℂ R U‖ ≤
      ∫ x, (DReview.physicalBand K n)ᶜ.indicator
        (fun y => ‖HNormalizedKernel.haarKernel
          (fun z => intervalHalfWeight l r s (classLog K z)) 1 U R y y‖) x ∂mu := by
  dsimp only
  simpa using interval_kernel_mask_error K mu l r s 1 (by norm_num)
    ((((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - E.starProjection).comp
      (intervalConvolutionCLM K mu l r s hlr hs h hh hc)) F) R n rho hm hb hp

end KPhysicalMask
end



-- Integrated supplier: inputs/exchange/N/NArithmeticShellFragment.lean
/- Append after NShellFragment, MPartitionFragment, the I arithmetic core,
   and the seed DReview block. No alternative kernel or sharp is defined. -/
namespace NArithmeticIntegration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Physical exhaustion of an actual original-Haar diagonal in L1. -/
theorem physical_diagonal_L1 (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun n => ∫ x, ‖(DReview.physicalBand K n).indicator d x - d x‖ ∂mu)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫ x, ‖(DReview.physicalBand K n).indicator d x-d x‖ ∂mu)
      atTop (𝓝 (∫ _ : HeckeIdeleClasses K, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
    · intro n
      exact ((hd.aestronglyMeasurable.indicator (DReview.physicalBand_measurable K n)).sub
        hd.aestronglyMeasurable).norm
    · exact hd.norm
    · intro n
      filter_upwards [] with x
      by_cases hx : x ∈ DReview.physicalBand K n <;> simp [hx]
    · filter_upwards [] with x
      obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ DReview.physicalBand K n := hN.trans (by exact_mod_cast hn)
      simp [hx]
  simpa only [integral_zero] using ht

/-- Actual arithmetic shell partition. The displayed measurable-descent and
indentation normalization obligations remain visible to the caller. -/
theorem descended_positivePartition (v : ℕ → NumberField.FinitePlace K)
    (b : HeckeIdeles K → ℝ) (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (hm : ∀ e, Measurable (NDivisorialShells.descendedMask K v b e)) :
    ReviewM.PositivePartition (NDivisorialShells.descendedMask K v b) := by
  refine ⟨hm, ?_, ?_⟩
  · intro e x
    exact (NDivisorialShells.descended_partition_mass K v b hb hbs x).1 e
  · intro x
    exact (NDivisorialShells.descended_partition_mass K v b hb hbs x).2

/-- Finite complementary-kernel shells, with the negative spectral sign.
This is not an identification of the finite jet span with the full theta source. -/
theorem finite_complement_shells
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Countable J]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (h1 : h 1 = 0)
    (p : J → HeckeIdeleClasses K → ℝ) (hp : ReviewM.PositivePartition p) :
    let ker := finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m)
    let d := fun x => h (x*x⁻¹) - ker x x
    HasSum (fun j => ∫ x, (p j x : ℂ) * d x ∂mu)
      (-(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu)) ∧
    Summable (fun j => ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ∧
    (∑' j, ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' j, ‖(∫ x, (p j x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p j x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let ker := finitePAKernel K Finset.univ mu chi z a m h
    (actualGramDual K mu chi z a s alpha m)
  let d := fun x => h (x*x⁻¹) - ker x x
  have hd0 := actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m
    hg hclosed h hh hc
  have he := actual_Gram_PA_diagonal_integral K mu chi z a s alpha m
    hg hdet hclosed h hh hc
  have hneg : d = (fun x => -ker x x) := by
    funext x
    simp only [d, mul_inv_cancel, h1, zero_sub]
  have hd : Integrable d mu := by rw [hneg]; exact hd0.neg
  have hge : (∫ x, d x ∂mu) =
      -(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu) := by
    rw [hneg, integral_neg]
    exact congrArg Neg.neg he
  have hsum := ReviewM.shell_reconstruction mu p hp d hd
  rw [hge] at hsum
  have hbound := ReviewM.positive_shell_l1 mu p hp d hd
  refine ⟨hsum, hbound.1, hbound.2, ?_⟩
  exact ReviewM.shell_l1_limit mu p hp (fun n => (DReview.physicalBand K n).indicator d) d
    (fun n => hd.indicator (DReview.physicalBand_measurable K n)) hd
    (physical_diagonal_L1 K mu d hd)

/-- Both literal manuscript tests on the concrete descended divisorial masks. -/
theorem both_sharp_arithmetic_shells
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q*x)) 1)
    (hm : ∀ e, Measurable (NDivisorialShells.descendedMask K v b e)) :
    ∀ h ∈ ({DReview.sharp K phi,
      DReview.sharp K (fun x => (classLog K x : ℂ)*phi x)} :
        Set (HeckeIdeleClasses K → ℂ)),
    let p := NDivisorialShells.descendedMask K v b
    let ker := finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m)
    let d := fun x => h (x*x⁻¹) - ker x x
    HasSum (fun j => ∫ x, (p j x : ℂ) * d x ∂mu)
      (-(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu)) ∧
    Summable (fun j => ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ∧
    (∑' j, ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' j, ‖(∫ x, (p j x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p j x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  have hz : classLog K (1 : HeckeIdeleClasses K) = 0 := by
    have ht := Masullo.WeightedIdeleClass.classLog_mul K (1 : HeckeIdeleClasses K) 1
    simp only [one_mul] at ht
    linarith
  have hp := descended_positivePartition K v b hb hbs hm
  have ht := DReview.both_sharp_tests_compact K phi hh hc
  intro h hmemb
  rcases Set.mem_insert_iff.mp hmemb with he | hmemb
  · subst h
    exact finite_complement_shells K mu chi z m a s alpha hg hdet hclosed _
      ht.1.1 ht.1.2 (DReview.sharp_vanishes_normOne K phi hphi 1 hz) _ hp
  · have he := Set.mem_singleton_iff.mp hmemb
    subst h
    exact finite_complement_shells K mu chi z m a s alpha hg hdet hclosed _
      ht.2.1 ht.2.2 (DReview.sharp_vanishes_normOne K _
        (fun x hx => by simp [hx]) 1 hz) _ hp
end
end NArithmeticIntegration


-- Integrated supplier: inputs/exchange/B/BSourceShellFragment.lean
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


-- Integrated supplier: inputs/exchange/F/FSourcePhysical.lean
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


-- Integrated supplier: inputs/exchange/K/KFiniteSourceError.lean
/-! Append after KMaskFragment and HSourceTraceFragment.
K owns the quantitative estimate; H owns finiteKernel_trace; F owns cutoff convergence. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory

/-- Quantitative physical-mask error for the specified finite source kernel,
with its actual operator trace and unchanged original Haar measure. -/
theorem source_kernel_mask_error {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (band : Set X) (hband : MeasurableSet band)
    (rho : X → ℝ) (hm : Measurable rho)
    (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ band, rho x = 1) :
    ‖(∫ x, (rho x : ℂ) * DSourceKernel.finiteKernel nu b E A x x ∂nu) -
      Masullo.TraceClass.trace (E.starProjection.comp A)‖ ≤
      ∫ x, bandᶜ.indicator (fun y => ‖DSourceKernel.finiteKernel nu b E A y y‖) x ∂nu := by
  rw [← DSourceKernel.finiteKernel_trace nu b hb E A]
  exact real_mask_error_bound nu band hband _
    (DSourceKernel.finiteKernel_diagonal nu b hb E A).1 rho hm hbound hp

end KPhysicalMask
end


-- Integrated supplier: inputs/exchange/E/SourceTailArithmeticFragment.lean
/- Append after SourceTailFragment.lean and JThetaDefinitions.lean.
This is the arithmetic specialization, retaining all theta parameters. -/
namespace EIntegratedTail
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- Explicit synthesis through the named actual closure; no projection axiom. -/
local instance source_tail_thetaProjection
    (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (a alpha s : ℝ) :
    (thetaClosure K addHaar mu chi a alpha s).HasOrthogonalProjection := by
  unfold thetaClosure
  infer_instance

/-- Tail entries for the genuine projection of the admitted original theta
source. Admission retains Bruhat, both moments, convergence, character and L2. -/
theorem admitted_source_physical_tail_gram {ι : Type*} [Fintype ι]
    (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (a alpha s : ℝ)
    (Ginv : Matrix ι ι ℂ) (kappa : ι → Lp ℂ 2 mu) :
    Tendsto (physicalTailGram K mu Ginv
      (fun i => (thetaClosure K addHaar mu chi a alpha s).starProjection (kappa i)))
      atTop (𝓝 0) :=
  lp_physical_tail_gram K mu Ginv _

variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- For interval [l,r], normalization shifts theta's original parameter a to
`a+(l+r)/2` and uses half-width `(r-l)/2`. This specializes both actual
convolutions to J's arithmetic closure and discharges every tail-integrability
and cutoff hypothesis. It does not assert that all manuscript tests satisfy
J's source-admission obligations, or infer trace-class from this finite tail. -/
theorem both_tests_arithmetic_PA_physical_tail_gram {ι : Type*} [Fintype ι]
    (addHaar : Measure (HeckeAdeles K))
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (Ginv : Matrix ι ι ℂ) (kappa : ι → Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A0) (kappa i))) atTop (𝓝 0) ∧
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A1) (kappa i))) atTop (𝓝 0) := by
  constructor <;> exact lp_physical_tail_gram K mu Ginv _

end
end EIntegratedTail


-- Integrated supplier: inputs/exchange/E/SourceResidualFragment.lean
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


-- Integrated supplier: inputs/exchange/E/SourceResidualApplication.lean
/- Append after E SourceResidualFragment and QSourceCutoffFragment.
   This applies E's unit bound to Q's exact canonical finite source sets. -/
namespace ESourceResidual
open OSourceClosure Q.IntegratedSourceCutoff
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- No inclusion/density assumption is imposed here: Q's concrete finite
source construction proves the needed inclusion in the same source closure. -/
theorem common_source_factor_cost_bound (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H) (T : Finset H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    (∑' j, ‖u j‖ *
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
       (sourceClosure e0 eF Theta).starProjection (v j)‖) ≤
    ∑' j, ‖u j‖ * ‖v j‖ := by
  exact source_factor_cost_le (sourceClosure e0 eF Theta)
    (finiteSourceSpan e0 eF Theta T) (finiteSourceSpan_le e0 eF Theta T) u v hc

end
end ESourceResidual


-- Integrated supplier: inputs/exchange/Q/QRightCutoffFragment.lean
/- Append after QSourceCutoffFragment.lean. This records the different RIGHT
   source cutoff used in manuscript 11.2.1.2 without dropping its remainder. -/
namespace Q.IntegratedSourceCutoff
open Filter OSourceClosure
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem source_projection_self_pairing (S : Submodule ℂ H)
    [S.HasOrthogonalProjection] (x y : H) :
    ⟪S.starProjection x, y⟫_ℂ = ⟪x, S.starProjection y⟫_ℂ := by
  have h1 := Submodule.inner_right_of_mem_orthogonal
    (S.starProjection_apply_mem x) (S.sub_starProjection_mem_orthogonal y)
  rw [inner_sub_right, sub_eq_zero] at h1
  have h2 := (Submodule.mem_orthogonal' S _).1
    (S.sub_starProjection_mem_orthogonal x)
    (S.starProjection y) (S.starProjection_apply_mem y)
  rw [inner_sub_left, sub_eq_zero] at h2
  exact h1.trans h2.symm

/-- RIGHT source condensation tends to T S. Its difference from T is kept. -/
theorem right_source_condensation_with_remainder (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (x : H) :
    let S := (sourceClosure e0 eF Theta).starProjection
    Tendsto (fun T : Finset H => M (S (A ((finiteSourceSpan e0 eF Theta T).starProjection x))))
      atTop (𝓝 (M (S (A x)) - M (S (A (x - S x))))) := by
  classical
  dsimp only
  have hp := Masullo.NestedProjection.global_projection_tendsto
    (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
    (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
    (finiteSourceSpan_dense e0 eF Theta) x
  have ht := M.continuous.tendsto _ |>.comp
    ((sourceClosure e0 eF Theta).starProjection.continuous.tendsto _ |>.comp
      (A.continuous.tendsto _ |>.comp hp))
  convert ht using 1
  simp only [map_sub]
  abel

/-- The dual rows, not output columns, carry a right source cutoff. -/
theorem right_source_nuclear_cost_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j,
      ‖(finiteSourceSpan e0 eF Theta T).starProjection (u j) -
        (sourceClosure e0 eF Theta).starProjection (u j)‖ * ‖v j‖) atTop (𝓝 0) := by
  have hc' : Summable (fun j => ‖v j‖ * ‖u j‖) := by simpa only [mul_comm] using hc
  simpa only [mul_comm] using actual_theta_nuclear_cost_limit e0 eF Theta v u hc'

theorem right_source_factor_residual (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A : H →L[ℂ] H) (u v : ℕ → H)
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A x))
    (T : Finset H) (x : H) :
    HasSum (fun j =>
      ⟪(finiteSourceSpan e0 eF Theta T).starProjection (u j) -
        (sourceClosure e0 eF Theta).starProjection (u j), x⟫_ℂ • v j)
      (A ((finiteSourceSpan e0 eF Theta T).starProjection x) -
       A ((sourceClosure e0 eF Theta).starProjection x)) := by
  have he := hfactor ((finiteSourceSpan e0 eF Theta T).starProjection x)
  have hs := hfactor ((sourceClosure e0 eF Theta).starProjection x)
  simpa only [inner_sub_left, source_projection_self_pairing, sub_smul] using he.sub hs

/-- Source condensation plus its retained complementary row gives the full
coefficient sum in the limit; no unsupported disappearance of a block occurs. -/
theorem right_source_compensated_series_limit (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset H => ∑' j,
      (⟪(finiteSourceSpan e0 eF Theta T).starProjection (u j), v j⟫_ℂ +
       ⟪u j - (sourceClosure e0 eF Theta).starProjection (u j), v j⟫_ℂ))
      atTop (𝓝 (∑' j, ⟪u j, v j⟫_ℂ)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence (hc.mul_left 3)
  · intro j
    have hp := Masullo.NestedProjection.global_projection_tendsto
      (sourceClosure e0 eF Theta) (finiteSourceSpan e0 eF Theta)
      (finiteSourceSpan_monotone e0 eF Theta) (finiteSourceSpan_le e0 eF Theta)
      (finiteSourceSpan_dense e0 eF Theta) (u j)
    simpa only [inner_sub_left, add_sub_cancel] using
      (hp.inner (tendsto_const_nhds (x := v j))).add
        (tendsto_const_nhds (x := ⟪u j - (sourceClosure e0 eF Theta).starProjection (u j), v j⟫_ℂ))
  · apply Eventually.of_forall
    intro T j
    have hp := (finiteSourceSpan e0 eF Theta T).norm_starProjection_apply_le (u j)
    have hq : ‖u j - (sourceClosure e0 eF Theta).starProjection (u j)‖ ≤ 2 * ‖u j‖ :=
      (norm_sub_le _ _).trans (by linarith [(sourceClosure e0 eF Theta).norm_starProjection_apply_le (u j)])
    calc
      _ ≤ ‖⟪(finiteSourceSpan e0 eF Theta T).starProjection (u j), v j⟫_ℂ‖ +
          ‖⟪u j - (sourceClosure e0 eF Theta).starProjection (u j), v j⟫_ℂ‖ := norm_add_le _ _
      _ ≤ ‖(finiteSourceSpan e0 eF Theta T).starProjection (u j)‖ * ‖v j‖ +
          ‖u j - (sourceClosure e0 eF Theta).starProjection (u j)‖ * ‖v j‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖u j‖ * ‖v j‖ + (2 * ‖u j‖) * ‖v j‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
      _ = _ := by ring

end
end Q.IntegratedSourceCutoff


-- Integrated supplier: inputs/exchange/Q/QArithmeticCutoffFragment.lean
/- Append after QSourceCutoffFragment and OThetaClosure. -/
namespace Q.ArithmeticSourceCutoff
open MeasureTheory MasulloGRH JThetaAttachment OSourceClosure OArithmeticClosure
open Q.IntegratedSourceCutoff Filter
open scoped Topology InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
variable (chi : UnitaryHeckeCharacter K) (a alpha s : ℝ)

abbrev arithmeticFiniteSpan (T : Finset (Lp ℂ 2 mu)) : Submodule ℂ (Lp ℂ 2 mu) :=
  finiteSourceSpan (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0
    (arithmeticSourceMap K addHaar mu chi a alpha s) T

/-- Concrete principal-theta source, character and weight parameters retained.
The summable factors are explicit; the actual operator factorization must be
proved before using this cost as its nuclear error bound. -/
theorem arithmetic_source_nuclear_cost_limit
    (u v : ℕ → Lp ℂ 2 mu) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => ∑' j, ‖u j‖ *
      ‖(arithmeticFiniteSpan K addHaar mu chi a alpha s T).starProjection (v j) -
        (thetaClosure K addHaar mu chi a alpha s).starProjection (v j)‖) atTop (𝓝 0) := by
  simpa only [arithmetic_sourceClosure_eq] using
    actual_theta_nuclear_cost_limit
      (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi a alpha s) u v hc

theorem arithmetic_source_trace_series_limit
    (u v : ℕ → Lp ℂ 2 mu) (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) :
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => ∑' j,
      ⟪u j, v j - (arithmeticFiniteSpan K addHaar mu chi a alpha s T).starProjection (v j)⟫_ℂ)
      atTop (𝓝 (∑' j, ⟪u j, v j - (thetaClosure K addHaar mu chi a alpha s).starProjection (v j)⟫_ℂ)) := by
  simpa only [arithmetic_sourceClosure_eq] using
    actual_theta_trace_series_limit
      (0 : sourceSpan K addHaar mu chi a alpha s →ₗ[ℂ] ℂ) 0
      (arithmeticSourceMap K addHaar mu chi a alpha s) u v hc

end
end Q.ArithmeticSourceCutoff


-- Integrated supplier: inputs/exchange/Q/QKernelFactorFragment.lean
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


-- Integrated supplier: inputs/exchange/R/RBoundaryFragment.lean
-- Insert after RJetFragment.lean; reuses genuineNormalizedMellinJet.
namespace Masullo.BoundaryJetOrders

/-- The finite set of boundary jets satisfying the STRICT numerical condition
in Proposition 9.1.2.5. This is an index set, not a spectrum or an L-function.
The unresolved analytic bridge is that these are exactly the continuous jets
of the actual weighted idele-class quotient. -/
noncomputable def boundaryJetOrders (N : ℕ) (s : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (2 : ℝ) * j + 1 < s)

/-- Discharges the finite counting premise for boundary multiplicities:
at odd integral weight 2*k+1, the strict cutoff retains min(N,k) jets. -/
theorem boundaryJetOrders_odd (N k : ℕ) :
    boundaryJetOrders N (2 * (k : ℝ) + 1) = Finset.range (min N k) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  constructor
  · intro h
    have hj : (j : ℝ) < (k : ℝ) := by linarith [h.2]
    exact ⟨h.1, by exact_mod_cast hj⟩
  · rintro ⟨hN, hk⟩
    have hj : (j : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ⟨hN, by linarith⟩

/-- Conditional finite-block trace reduction for the binomial jet action
printed at (10.3.1.17). Discharges only its finite trace calculation; the
hypothesis must be proved for the genuine quotient operator before use. -/
theorem trace_of_binomial_jet_action (n : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    Matrix.trace M = (n : ℂ) * a 0 := by
  have hd (i : Fin n) : M i i = a 0 := by simp [hM]
  simp [Matrix.trace, Matrix.diag, hd, nsmul_eq_mul]

/-- Combined exact finite-count and conditional finite-trace step toward the
correct spectral multiplicity. No assertion of analytic jet admissibility,
zero identification, completeness, nuclearity, or infinite summability. -/
theorem boundary_jet_trace_at_odd_weight (N k : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card)
      (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k ∧
      Matrix.trace M = ((min N k : ℕ) : ℂ) * a 0 := by
  have hc : (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k := by
    rw [boundaryJetOrders_odd, Finset.card_range]
  refine ⟨hc, ?_⟩
  simpa only [hc] using trace_of_binomial_jet_action _ a M hM

/-- Numerical boundary multiplicity for every real Sobolev parameter.
This discharges counting only; continuous native jet attachment is unresolved. -/
theorem boundaryJetOrders_all_real (N : ℕ) (s : ℝ) :
    boundaryJetOrders N s = Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range,
    Nat.lt_min, Nat.lt_ceil]
  constructor
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩

end Masullo.BoundaryJetOrders

namespace Masullo.RadialJetDensity
open MeasureTheory Set
/-- The actual polynomial part of the radial squared dual norm in
Proposition 9.1.2.5; no spectrum or L-function is defined here. -/
noncomputable def radialJetDensity (m : ℕ) (s : ℝ) (x : ℝ) : ℝ :=
  x ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2)

/-- Power comparison needed for the native boundary-jet continuity premise. -/
theorem radialJetDensity_tail_comparison (m : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (x : ℝ) (hx : 1 < x) :
    radialJetDensity m s x ≤ x ^ ((2 : ℝ) * m - s) ∧
    (2 : ℝ) ^ (-s / 2) * x ^ ((2 : ℝ) * m - s) ≤ radialJetDensity m s x := by
  have hp : 0 < x := by linarith
  have hsq : 0 < x ^ 2 := sq_pos_of_pos hp
  have he : x ^ (2 * m) * (x ^ 2) ^ (-s / 2) =
      x ^ ((2 : ℝ) * m - s) := by
    rw [← Real.rpow_natCast x (2 * m), ← Real.rpow_natCast x 2,
      ← Real.rpow_mul (le_of_lt hp), ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  have hnon : 0 ≤ x ^ (2 * m) := pow_nonneg (le_of_lt hp) _
  have hq : -s / 2 ≤ 0 := by linarith
  constructor
  · unfold radialJetDensity
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hsq (by linarith) hq) hnon
  · have hbase : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have hb := Real.rpow_le_rpow_of_nonpos
      (show 0 < 1 + x ^ 2 by positivity) hbase hq
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hsq)] at hb
    have hh := mul_le_mul_of_nonneg_left hb hnon
    rw [← he]
    unfold radialJetDensity
    nlinarith

/-- Exact positive-tail criterion for the radial native Mellin-jet norm.
Discharges the boundary power-tail integrability premise, not the genuine
idele Haar decomposition or the weighted dual representation. -/
theorem radialJetDensity_integrable_tail_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (radialJetDensity m s) (Ioi 1) ↔ (2 : ℝ) * m + 1 < s := by
  have hm : AEStronglyMeasurable (radialJetDensity m s) (volume.restrict (Ioi 1)) := by
    apply Continuous.aestronglyMeasurable
    unfold radialJetDensity
    exact (continuous_id.pow _).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (by positivity)))
  have hn (x : ℝ) : 0 ≤ radialJetDensity m s x := by
    unfold radialJetDensity
    exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
      (Real.rpow_nonneg (by positivity) _)
  have hpow : IntegrableOn (fun x : ℝ => x ^ ((2 : ℝ) * m - s)) (Ioi 1) ↔
      (2 : ℝ) * m + 1 < s := by
    rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    apply hpow.mp
    apply (h.const_mul ((2 : ℝ) ^ (s / 2))).mono'
      ((measurable_id.pow_const _).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp : 0 < x := by exact lt_trans zero_lt_one hx
    simp only [id_eq]
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
    have hb := mul_le_mul_of_nonneg_left
      (radialJetDensity_tail_comparison m s hs x hx).2
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (s / 2))
    have hc : (2 : ℝ) ^ (s / 2) * 2 ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
    simpa only [← mul_assoc, hc, one_mul] using hb
  · intro h
    apply (hpow.mpr h).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
    exact (radialJetDensity_tail_comparison m s hs x hx).1

end Masullo.RadialJetDensity

namespace Masullo.RadialJetDensity
open MeasureTheory Set
/-- Includes the compact part of the actual radial density, so the only
obstruction on the positive half-line is the strict boundary jet cutoff. -/
theorem radialJetDensity_integrable_halfLine_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (radialJetDensity m s) (Ici 0) ↔ (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    apply (radialJetDensity_integrable_tail_iff m s hs).mp
    exact h.mono_set (by intro x hx; change 1 < x at hx; change 0 ≤ x; linarith)
  · intro h
    have hc : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
      ext x
      simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro hx
        by_cases h1 : x ≤ 1
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
    have hi := (hc.integrableOn_Icc (a := 0) (b := 1)).union
      ((radialJetDensity_integrable_tail_iff m s hs).mpr h)
    rwa [hu] at hi
end Masullo.RadialJetDensity

namespace Masullo.RadialJetDensity
open MeasureTheory Set
/-- At the right boundary b=alpha the exponential weight cancels on x>=0.
This discharges that precise tail of the actual weighted jet dual-norm test. -/
theorem boundaryRadialJet_integrable_halfLine_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x)
      (Ici 0) ↔ (2 : ℝ) * m + 1 < s := by
  have he : EqOn (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x)
      (radialJetDensity m s) (Ici 0) := by
    intro x hx
    change 0 ≤ x at hx
    dsimp only
    rw [abs_of_nonneg hx, sub_self, Real.exp_zero, one_mul]
  constructor
  · intro h
    exact (radialJetDensity_integrable_halfLine_iff m s hs).mp
      (h.congr_fun he measurableSet_Ici)
  · intro h
    exact ((radialJetDensity_integrable_halfLine_iff m s hs).mpr h).congr_fun
      (fun x hx => (he hx).symm) measurableSet_Ici
end Masullo.RadialJetDensity

namespace Masullo.RadialJetDensityEven
open MeasureTheory Set Masullo.RadialJetDensity
/-- Discharges reflection symmetry of the squared radial jet norm, needed
for the negative-tail part of the native boundary multiplicity criterion. -/
theorem radialJetDensity_even (m : ℕ) (s x : ℝ) :
    radialJetDensity m s (-x) = radialJetDensity m s x := by
  simp [radialJetDensity, pow_mul]

theorem radialJetDensity_integrable_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (radialJetDensity m s) ↔ (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    exact (radialJetDensity_integrable_halfLine_iff m s hs).mp h.integrableOn
  · intro h
    have hp := (radialJetDensity_integrable_halfLine_iff m s hs).mpr h
    have hn : IntegrableOn (radialJetDensity m s) (Iic 0) := by
      simpa [radialJetDensity_even] using hp.comp_neg
    have hu : Ici (0 : ℝ) ∪ Iic 0 = univ := by
      ext x
      simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
      exact le_total 0 x
    simpa only [hu, integrableOn_univ] using hp.union hn

/-- Full right-boundary squared radial norm, including the decaying tail.
This discharges the analytic boundary cutoff premise for spectral jet
multiplicities; the genuine Haar and weighted-dual bridges remain separate. -/
theorem rightBoundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    exact (boundaryRadialJet_integrable_halfLine_iff m s alpha hs).mp h.integrableOn
  · intro h
    have hc : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    have hw : Continuous (fun x : ℝ =>
        Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x) :=
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
        (continuous_const.mul continuous_abs))).mul hc
    apply ((radialJetDensity_integrable_iff m s hs).mpr h).mono'
      hw.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ radialJetDensity m s x := by
      unfold radialJetDensity
      exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
        (Real.rpow_nonneg (by positivity) _)
    have he : Real.exp (2 * alpha * x - 2 * alpha * |x|) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [le_abs_self x]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hn)]
    exact (mul_le_mul_of_nonneg_right he hn).trans_eq (one_mul _)

/-- Reflection proves the same sharp cutoff at the other strip boundary. -/
theorem leftBoundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * (-alpha) * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    apply (rightBoundaryRadialJet_integrable_iff m s alpha hs ha).mp
    simpa only [mul_neg, neg_mul, neg_neg, abs_neg, radialJetDensity_even] using h.comp_neg
  · intro h
    have hr := (rightBoundaryRadialJet_integrable_iff m s alpha hs ha).mpr h
    simpa only [mul_neg, neg_mul, neg_neg, abs_neg, radialJetDensity_even] using hr.comp_neg

/-- Uniform statement for either genuine strip edge (including alpha=0).
It does not assume a prescribed zero set or any spectral summability. -/
theorem boundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  rcases le_total 0 beta with h | h
  · have he : beta = alpha := by simpa only [abs_of_nonneg h] using hb
    subst beta
    exact rightBoundaryRadialJet_integrable_iff m s alpha hs ha
  · have he : beta = -alpha := by rw [abs_of_nonpos h] at hb; linarith
    subst beta
    exact leftBoundaryRadialJet_integrable_iff m s alpha hs ha

end Masullo.RadialJetDensityEven

namespace Masullo.RadialJetDensityEven
open MeasureTheory Set Masullo.RadialJetDensity Masullo.BoundaryJetOrders
attribute [local instance] Classical.propDecidable
/-- Converts the proven full-line integrability condition into the exact
number of surviving orders below N. This discharges only analytic counting;
N still has to be identified with a genuine Hecke zero's order. -/
theorem boundary_integrable_orders
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => Integrable (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x)) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  rw [← boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, boundaryJetOrders,
    boundaryRadialJet_integrable_iff m s alpha beta hs ha hb]
end Masullo.RadialJetDensityEven

namespace Masullo.BoundaryDensityIntegrablePullbackIff
open MeasureTheory Masullo.RadialJetDensity Masullo.RadialJetDensityEven

/-- Conditional measure bridge for the actual log-norm map: a nonzero finite
Haar scaling preserves the sharp radial boundary criterion. Discharges the
measure-transport premise, not the genuine idele-class pushforward identity. -/
theorem boundary_density_integrable_pullback_iff
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (hell : AEMeasurable ell mu) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    Integrable (fun x => Real.exp (2 * beta * ell x - 2 * alpha * |ell x|) *
      radialJetDensity m s (ell x)) mu ↔ (2 : ℝ) * m + 1 < s := by
  let d : ℝ → ℝ := fun x =>
    Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x
  have hc : Continuous (radialJetDensity m s) := by
    unfold radialJetDensity
    exact (continuous_id.pow _).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (by positivity)))
  have hd : Continuous d :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hc
  have ht := integrable_map_measure
    (μ := mu) (f := ell) (g := d) hd.aestronglyMeasurable hell
  rw [hmap, integrable_smul_measure hc0 hct] at ht
  exact ht.symm.trans (boundaryRadialJet_integrable_iff m s alpha beta hs ha hb)

/-- The scalar weight-normalized Mellin jet. The phase is any Circle-valued
function, including an actual unitary character times its imaginary norm twist.
This defines no operator, spectrum, or L-function. -/
noncomputable def weightedMellinJet {X : Type*} (ell : X → ℝ)
    (phase : X → Circle) (m : ℕ) (s alpha beta : ℝ) (x : X) : ℂ :=
  (phase x : ℂ) * ((Real.exp (beta * ell x - alpha * |ell x|) *
    (ell x)^m * (1 + (ell x)^2)^(-s / 4) : ℝ) : ℂ)

/-- Discharges the pointwise squared-norm identity for the explicit weighted
jet; no integrability assumption or zero enumeration enters the identity. -/
theorem weightedMellinJet_sq_norm {X : Type*} (ell : X → ℝ)
    (phase : X → Circle) (m : ℕ) (s alpha beta : ℝ) (x : X) :
    ‖weightedMellinJet ell phase m s alpha beta x‖^2 =
      Real.exp (2 * beta * ell x - 2 * alpha * |ell x|) *
        radialJetDensity m s (ell x) := by
  unfold weightedMellinJet radialJetDensity
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, mul_pow, ← Real.exp_nat_mul, ← pow_mul,
    ← Real.rpow_natCast ((1 + (ell x)^2)^(-s / 4)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ 1 + (ell x)^2)]
  ring_nf

/-- Conditional native-membership bridge: for an explicit weighted jet and
an actual log-norm pushforward, square integrability has the sharp boundary
cutoff. Native Haar splitting and weighted-dual representation remain open. -/
theorem boundary_weightedMellinJet_memLp_iff
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : AEMeasurable ell mu)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha)
    (hf : AEStronglyMeasurable (weightedMellinJet ell phase m s alpha beta) mu) :
    MemLp (weightedMellinJet ell phase m s alpha beta) 2 mu ↔
      (2 : ℝ) * m + 1 < s := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  simp only [weightedMellinJet_sq_norm]
  exact boundary_density_integrable_pullback_iff mu ell hell c hc0 hct hmap
    m s alpha beta hs ha hb

end Masullo.BoundaryDensityIntegrablePullbackIff

namespace Masullo.BoundaryDensityIntegrablePullbackIff
open MeasureTheory Masullo.BoundaryJetOrders
attribute [local instance] Classical.propDecidable
/-- Measurability follows from the log norm and unitary phase; discharges
this hypothesis of boundary weighted-jet membership without assuming it. -/
theorem weightedMellinJet_measurable
    {X : Type*} [MeasurableSpace X] (ell : X → ℝ) (phase : X → Circle)
    (hell : Measurable ell) (hphase : Measurable (fun x => (phase x : ℂ)))
    (m : ℕ) (s alpha beta : ℝ) :
    Measurable (weightedMellinJet ell phase m s alpha beta) := by
  unfold weightedMellinJet
  fun_prop

/-- Conditional exact multiplicity truncation for the explicit weighted jets.
The only geometric input is the actual log-norm Haar pushforward; N must
still be identified with the genuine Hecke analytic zero order. -/
theorem boundary_weightedMellinJet_orders
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : Measurable ell) (hphase : Measurable (fun x => (phase x : ℂ)))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (weightedMellinJet ell phase m s alpha beta) 2 mu) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  rw [← boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, boundaryJetOrders,
    boundary_weightedMellinJet_memLp_iff mu ell phase hell.aemeasurable
      c hc0 hct hmap m s alpha beta hs ha hb
      (weightedMellinJet_measurable ell phase hell hphase m s alpha beta).aestronglyMeasurable]

end Masullo.BoundaryDensityIntegrablePullbackIff

namespace Masullo.InteriorDensityLeExpPolynomial
open MeasureTheory Set Masullo.RadialJetDensity Masullo.RadialJetDensityEven Masullo.BoundaryDensityIntegrablePullbackIff

/-- The interior membership premise of (10.2.2.6): the actual squared
radial jet density is dominated by an exponentially damped polynomial.
This is a pointwise analytic bound, not a zero or spectrum definition. -/
theorem interior_density_le_exp_polynomial
    (m : ℕ) (s alpha beta x : ℝ) (hs : 0 ≤ s) :
    Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x ≤
      Real.exp (-(2 * (alpha - |beta|)) * |x|) * x ^ (2 * m) := by
  have hp : 0 ≤ x ^ (2 * m) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) m
  have hw : (1 + x ^ 2) ^ (-s / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)
  have hb : beta * x ≤ |beta| * |x| := by
    simpa only [abs_mul] using (le_abs_self (beta * x))
  have he : Real.exp (2 * beta * x - 2 * alpha * |x|) ≤
      Real.exp (-(2 * (alpha - |beta|)) * |x|) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (2 * beta * x - 2 * alpha * |x|) * x ^ (2 * m) := by
      unfold radialJetDensity
      exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left hw hp)
        (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right he hp

end Masullo.InteriorDensityLeExpPolynomial

namespace Masullo.InteriorDensityLeExpPolynomial
open MeasureTheory Set Masullo.RadialJetDensity Masullo.RadialJetDensityEven Masullo.BoundaryDensityIntegrablePullbackIff
/-- The integrable majorant required by the interior jet bound. -/
theorem exp_abs_even_polynomial_integrable (m : ℕ) (d : ℝ) (hd : 0 < d) :
    Integrable (fun x : ℝ => Real.exp (-d * |x|) * x ^ (2 * m)) := by
  let g : ℝ → ℝ := fun x => Real.exp (-d * |x|) * x ^ (2 * m)
  have hc : Continuous g := by dsimp [g]; fun_prop
  have ht : IntegrableOn (fun x : ℝ => x ^ (2 * m) * Real.exp (-d * x)) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 * m : ℕ)) (p := 1)
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num) hd)
  have hg : IntegrableOn g (Ioi 0) := ht.congr_fun (by
    intro x hx
    dsimp [g]
    rw [abs_of_pos hx, mul_comm]) measurableSet_Ioi
  have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hp : IntegrableOn g (Ici 0) := by
    rw [← hu]
    exact (hc.integrableOn_Icc).union (hg.mono_set (by intro x hx; change (0 : ℝ) < x; change (1 : ℝ) < x at hx; linarith))
  have hn : IntegrableOn g (Iic 0) := by
    simpa [g, pow_mul] using hp.comp_neg
  have hall : Ici (0 : ℝ) ∪ Iic 0 = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 x
  simpa only [hall, integrableOn_univ] using hp.union hn

/-- All finite radial jet orders are integrable strictly inside the strip;
this discharges the analytic all-orders premise of (10.2.2.6). -/
theorem interiorRadialJet_integrable (m : ℕ) (s alpha beta : ℝ)
    (hs : 0 ≤ s) (hb : |beta| < alpha) :
    Integrable (fun x : ℝ => Real.exp (2 * beta * x - 2 * alpha * |x|) *
      radialJetDensity m s x) := by
  have hc : Continuous (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x) := by
    have hr : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hr
  apply (exp_abs_even_polynomial_integrable m (2 * (alpha - |beta|))
    (by linarith)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hn : 0 ≤ radialJetDensity m s x := by
    unfold radialJetDensity
    exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
      (Real.rpow_nonneg (by positivity) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hn)]
  exact interior_density_le_exp_polynomial m s alpha beta x hs

/-- Conditional native measure transport of the full interior membership
criterion. The actual Haar pushforward and native dual realization remain
application obligations; no zero set or spectral operator is prescribed. -/
theorem interior_weightedMellinJet_memLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : Measurable ell)
    (hphase : Measurable (fun x => (phase x : ℂ)))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (hb : |beta| < alpha) :
    MemLp (weightedMellinJet ell phase m s alpha beta) 2 mu := by
  rw [memLp_two_iff_integrable_sq_norm
    (weightedMellinJet_measurable ell phase hell hphase m s alpha beta).aestronglyMeasurable]
  simp only [weightedMellinJet_sq_norm]
  let d : ℝ → ℝ := fun x => Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x
  have hd : Continuous d := by
    dsimp [d]
    have hr : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hr
  have ht := integrable_map_measure (μ := mu) (f := ell) (g := d)
    hd.aestronglyMeasurable hell.aemeasurable
  rw [hmap, integrable_smul_measure hc0 hct] at ht
  exact ht.mp (interiorRadialJet_integrable m s alpha beta hs hb)

end Masullo.InteriorDensityLeExpPolynomial

namespace Masullo.GenuineNormalizedMellinJet
open MasulloGRH Masullo.IdeleClassGeometry Masullo.BoundaryDensityIntegrablePullbackIff MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
/-- Discharges the actual character/complex-parameter attachment premise of
native jet integrability. The imaginary parameter is retained in the function. -/
theorem genuineNormalizedMellinJet_norm (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineNormalizedMellinJet K χ z a s alpha m x‖ =
      ‖weightedMellinJet (classLog K) (classCharacter K χ) m s alpha (z.re-a) x‖ := by
  simp only [genuineNormalizedMellinJet, weightedMellinJet, norm_mul,
    Circle.norm_coe, one_mul, Complex.norm_exp, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- Conditional sharp native boundary criterion for the genuine character and
complex Mellin parameter. Only the actual Haar pushforward is supplied; the
zero order and weighted-dual/common-kernel realization remain separate gaps. -/
theorem genuine_boundary_mellin_memLp_iff (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) :
    MemLp (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu ↔
      (2 : ℝ) * m + 1 < s := by
  have hchi : Measurable (fun x => (classCharacter K χ x : ℂ)) :=
    (continuous_subtype_val.comp (classCharacter_continuous K χ)).measurable
  have hell := (Masullo.WeightedIdeleClass.classLog_continuous K).measurable
  have hg : Measurable (genuineNormalizedMellinJet K χ z a s alpha m) := by
    unfold genuineNormalizedMellinJet
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simp only [genuineNormalizedMellinJet_norm, weightedMellinJet_sq_norm]
  exact boundary_density_integrable_pullback_iff mu (classLog K) hell.aemeasurable
    c hc0 hct hmap m s alpha (z.re-a) hs ha hb

end Masullo.GenuineNormalizedMellinJet

namespace Masullo.GenuineNormalizedMellinJet
open MasulloGRH Masullo.IdeleClassGeometry Masullo.BoundaryDensityIntegrablePullbackIff Masullo.InteriorDensityLeExpPolynomial MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Interior counterpart for the genuine complex Mellin jet; discharges the
all-finite-orders membership premise of (10.2.2.6), conditionally on Haar transport. -/
theorem genuine_interior_mellin_memLp (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (hb : |z.re-a| < alpha) :
    MemLp (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu := by
  have hchi : Measurable (fun x => (classCharacter K χ x : ℂ)) :=
    (continuous_subtype_val.comp (classCharacter_continuous K χ)).measurable
  have hell := (Masullo.WeightedIdeleClass.classLog_continuous K).measurable
  have hg : Measurable (genuineNormalizedMellinJet K χ z a s alpha m) := by
    unfold genuineNormalizedMellinJet
    fun_prop
  have hi := interior_weightedMellinJet_memLp mu (classLog K) (classCharacter K χ)
    hell hchi c hc0 hct hmap m s alpha (z.re-a) hs hb
  rw [memLp_two_iff_integrable_sq_norm
    (weightedMellinJet_measurable (classLog K) (classCharacter K χ) hell hchi
      m s alpha (z.re-a)).aestronglyMeasurable] at hi
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simpa only [genuineNormalizedMellinJet_norm] using hi

/-- Exact boundary truncation after actual-character attachment. N is still
an external finite order; identifying it with analytic Hecke multiplicity is OPEN. -/
theorem genuine_boundary_mellin_orders (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (N : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu) =
      Finset.range (min N (Nat.ceil ((s-1)/2))) := by
  classical
  rw [← Masullo.BoundaryJetOrders.boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, Masullo.BoundaryJetOrders.boundaryJetOrders,
    genuine_boundary_mellin_memLp_iff K χ mu c hc0 hct hmap z a s alpha m hs ha hb]

end Masullo.GenuineNormalizedMellinJet

namespace MasulloGRH.NativeTateConverse
open MeasureTheory Set Topology Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet

/-- Strict admission gives membership on the SAME Haar measure, including the
zero-width case only through its single boundary condition. -/
theorem native_admitted_memLp
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadm : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s)) :
    MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu := by
  rcases hadm with hi | ⟨hb, hm⟩
  · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap z a s alpha m hs hi
  · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap z a s alpha m hs ha hb).mpr hm

end MasulloGRH.NativeTateConverse



-- Integrated supplier: inputs/exchange/R/RApplicationFragment.lean
-- Insert after RBoundaryFragment.lean and the seed DReview namespace.
namespace RIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Actual same-Haar Mellin coefficients, retaining the character and shift. -/
def mellinCoefficient (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (m : ℕ) : ℂ :=
  ∫ g, h g * genuineMellinJet K chi z a m g ∂mu

/-- The logarithmic sharp test shifts the coefficient with its actual minus sign. -/
theorem mellinCoefficient_log_sharp (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (phi : HeckeIdeleClasses K → ℂ) (m : ℕ) :
    mellinCoefficient K mu chi z a
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) m =
      -mellinCoefficient K mu chi z a (DReview.sharp K phi) (m + 1) := by
  unfold mellinCoefficient
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g => by
    dsimp only
    rw [DReview.sharp_log]
    simp only [genuineMellinJet, pow_succ, Complex.ofReal_mul]
    ring)

/-- Strict numerical admission is downward closed along the actual chain. -/
theorem admission_downward (z : ℂ) (a s alpha : ℝ) (m k : ℕ) (hkm : k ≤ m)
    (hadm : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s)) :
    |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*k+1 < s) := by
  rcases hadm with hi | ⟨hb, hm⟩
  · exact Or.inl hi
  · refine Or.inr ⟨hb, ?_⟩
    have hk : (k : ℝ) ≤ m := by exact_mod_cast hkm
    linarith

/-- All lower jets needed by the measured convolution theorem are supplied
from one numerical admission, using the stated original-Haar transport. -/
theorem native_admitted_chain_memLp (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadm : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s)) :
    ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu := by
  intro k hk
  exact MasulloGRH.NativeTateConverse.native_admitted_memLp K chi mu c hc0 hct hmap
    z a s alpha k hs ha (admission_downward z a s alpha m k hk hadm)

/-- The original measured chain action with the analytic jet hypotheses
proved from the numerical parameters; Haar transport remains explicit. -/
theorem native_admitted_convolution_triangular
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadm : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s))
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a m x ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (mellinCoefficient K mu chi z a h k * (m.choose k : ℂ)) *
          (∫ y, genuineMellinJet K chi z a (m-k) y * f y ∂mu) := by
  exact Masullo.NativeWeightedConvolutionTriangular.native_weighted_convolution_triangular
    K mu chi z a s alpha m h f hh hc
    (native_admitted_chain_memLp K chi mu c hc0 hct hmap z a s alpha m hs ha hadm) hf

end
end RIntegrated


-- Integrated supplier: inputs/exchange/R/RTwoTestFragment.lean
-- Insert after RApplicationFragment, GConvolutionFragment and LTestBoundary.fragment.
namespace RIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open PIntervalConvolution LIntegrated
noncomputable section

/-- The actual required logged family has the negative successor coefficient. -/
theorem requiredTest_coefficient_one
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (phi : HeckeIdeleClasses K → ℂ) (m : ℕ) :
    mellinCoefficient K mu chi z a (requiredTest K phi 1) m =
      -mellinCoefficient K mu chi z a (requiredTest K phi 0) (m+1) := by
  simpa only [requiredTest_zero, requiredTest_one] using
    mellinCoefficient_log_sharp K mu chi z a phi m

/-- Both test families act by the measured Mellin chain on the contract's
constructed interval convolution, with all lower-jet membership proved from
numerical admission and the explicit original-Haar logarithm transport. -/
theorem both_tests_interval_chain
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (hadm : |z.re-(a+(l+r)/2)| < (r-l)/2 ∨
      (|z.re-(a+(l+r)/2)| = (r-l)/2 ∧ (2 : ℝ)*m+1 < s))
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let ht := requiredTest_compact K phi hh hc q
    (∫ x, genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m x *
      intervalConvolutionCLM K mu l r s hlr hs (requiredTest K phi q) ht.1 ht.2 F x ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (mellinCoefficient K mu chi z a (requiredTest K phi q) k * (m.choose k : ℂ)) *
          (∫ y, genuineNormalizedMellinJet K chi z (a+(l+r)/2)
            s ((r-l)/2) (m-k) y * F y ∂mu) := by
  dsimp only
  exact GIntegrated.intervalConvolutionCLM_triangular K mu l r s hlr hs
    (requiredTest K phi q) (requiredTest_compact K phi hh hc q).1
    (requiredTest_compact K phi hh hc q).2 chi z a m
    (native_admitted_chain_memLp K chi mu c hc0 hct hmap z (a+(l+r)/2) s ((r-l)/2)
      m hs (by linarith) hadm) F

end
end RIntegrated


-- Integrated supplier: inputs/exchange/L/LBoundaryBalance.fragment.lean
/-! Insert after LTestBoundary, RBoundaryFragment and RApplicationFragment.
This is finite boundary bookkeeping on the actual two Mellin coefficients;
it does not assert that an infinite spectral trace has already been identified. -/
namespace LIntegrated
open MeasureTheory MasulloGRH Masullo.BoundaryJetOrders
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Exact real-parameter boundary count, retaining the strict inequality. -/
theorem boundary_card (N : ℕ) (s : ℝ) :
    (boundaryJetOrders N s).card = min N (Nat.ceil ((s-1)/2)) := by
  rw [boundaryJetOrders_all_real, Finset.card_range]

/-- Both required actual coefficients retain the omitted boundary multiplicity.
No boundary contribution is removed by changing the compact test. -/
theorem both_boundary_retained_omitted
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s : ℝ) (N : ℕ) (phi : HeckeIdeleClasses K → ℂ) (q : Fin 2) :
    let n := (boundaryJetOrders N s).card
    let c := RIntegrated.mellinCoefficient K mu chi z a (requiredTest K phi q) 0
    (n : ℂ)*c + ((N-n : ℕ) : ℂ)*c = (N : ℂ)*c := by
  dsimp only
  have hn : (boundaryJetOrders N s).card ≤ N := by
    rw [boundary_card]
    exact Nat.min_le_left _ _
  have hnat := Nat.add_sub_of_le hn
  have hcount : ((boundaryJetOrders N s).card : ℂ) +
      ((N-(boundaryJetOrders N s).card : ℕ) : ℂ) = (N : ℂ) := by
    exact_mod_cast hnat
  rw [← add_mul, hcount]

/-- Once the finite matrix is proved to be the actual admitted chain action,
its trace plus its omitted part gives the full multiplicity. hM records that
application explicitly; this lemma itself only proves finite trace algebra. -/
theorem both_boundary_matrix_balance
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s : ℝ) (N : ℕ) (phi : HeckeIdeleClasses K → ℂ)
    (M : Fin 2 → Matrix (Fin (boundaryJetOrders N s).card)
      (Fin (boundaryJetOrders N s).card) ℂ)
    (hM : ∀ q i j, M q i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * RIntegrated.mellinCoefficient K mu chi z a
        (requiredTest K phi q) (i.val-j.val) else 0) (q : Fin 2) :
    Matrix.trace (M q) + ((N-(boundaryJetOrders N s).card : ℕ) : ℂ) *
      RIntegrated.mellinCoefficient K mu chi z a (requiredTest K phi q) 0 =
      (N : ℂ) * RIntegrated.mellinCoefficient K mu chi z a (requiredTest K phi q) 0 := by
  rw [trace_of_binomial_jet_action _
    (RIntegrated.mellinCoefficient K mu chi z a (requiredTest K phi q)) (M q) (hM q)]
  exact both_boundary_retained_omitted K mu chi z a s N phi q
end
end LIntegrated


-- Integrated supplier: integration/PSourceMilestone.fragment
namespace PIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OSourceClosure
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Actual convolution followed by finite projections of the supplied theta
source converges strongly for both required tests on every native input.
This theorem does not claim trace convergence or arithmetic source admission. -/
theorem both_tests_global_source_exhaustion
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 mu)
    (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi)
    (x : Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun y => (classLog K y : ℂ)*phi y)) tests.2.1 tests.2.2
    let S := (sourceClosure e0 eF Theta).starProjection
    let F := fun T : Finset (Lp ℂ 2 mu) =>
      Submodule.span ℂ ((T : Set (Lp ℂ 2 mu)) ∩ Set.range Theta)
    ∃ p0 p1 : Finset (Lp ℂ 2 mu) → Lp ℂ 2 mu,
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p0 T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (F T) hp (A0 x)) ∧
      (∀ T, ∃ hp : (F T).HasOrthogonalProjection,
        p1 T = @Submodule.starProjection ℂ (Lp ℂ 2 mu) _ _ _ (F T) hp (A1 x)) ∧
      Tendsto (fun T => A0 x-p0 T) atTop (𝓝 (A0 x-S (A0 x))) ∧
      Tendsto (fun T => A1 x-p1 T) atTop (𝓝 (A1 x-S (A1 x))) := by
  dsimp only
  obtain ⟨p0, hp0, ht0⟩ := actual_source_family_exhaustion e0 eF Theta
    (intervalConvolutionCLM K mu l r s hlr hs (DReview.sharp K phi)
      (DReview.both_sharp_tests_compact K phi hh hc).1.1
      (DReview.both_sharp_tests_compact K phi hh hc).1.2) x
  obtain ⟨p1, hp1, ht1⟩ := actual_source_family_exhaustion e0 eF Theta
    (intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun y => (classLog K y : ℂ)*phi y))
      (DReview.both_sharp_tests_compact K phi hh hc).2.1
      (DReview.both_sharp_tests_compact K phi hh hc).2.2) x
  exact ⟨p0, p1, hp0, hp1, ht0, ht1⟩
end PIntegrated





-- Integrated supplier: inputs/exchange/G/GIntervalMeasuredFragment.lean
/- Insert after GConvolutionFragment. No new shared definition. -/
namespace GIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.NativeRep Masullo.NativePairingInner PIntervalConvolution

theorem interval_nativeRep
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ) (hlr : l ≤ r)
    (F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) :
    nativeRep K mu ((r-l)/2) s F x = radialTwist K ((l+r)/2) x *
      (F x / (intervalHalfWeight l r s (classLog K x) : ℂ)) := by
  unfold nativeRep
  rw [interval_halfWeight l r s _ hlr]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, radialTwist]
  have hb : (nativeHalfWeight ((r-l)/2) s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  have he : Complex.exp ((((l+r)/2 : ℝ) : ℂ) * (classLog K x : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp

/-- The common interval operator acts by literal inverse-input measured
convolution on the original interval-weighted representative, tested against
the original arithmetic jet. Both parameter shifts are discharged. -/
theorem intervalConvolutionCLM_measured_jet
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z
      (a+(l+r)/2) s ((r-l)/2) k) 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m x *
      intervalConvolutionCLM K mu l r s hlr hs h hh hc F x ∂mu) =
      ∫ x, genuineMellinJet K chi z a m x *
        (∫ g, h g * (F (g⁻¹*x) /
          (intervalHalfWeight l r s (classLog K (g⁻¹*x)) : ℂ)) ∂mu) ∂mu := by
  unfold intervalConvolutionCLM
  rw [actual_bounded_convolution_mellin K mu ((r-l)/2) s (by linarith) hs
    chi z (a+(l+r)/2) m (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2 hg F]
  simp_rw [interval_nativeRep K mu l r s hlr F]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← interval_convolution_conjugacy K mu ((l+r)/2) h
    (fun y => F y / (intervalHalfWeight l r s (classLog K y) : ℂ)) x]
  rw [← mul_assoc, mul_comm (genuineMellinJet K chi z (a+(l+r)/2) m x),
    midpoint_jet_cancellation]

end GIntegrated



-- Integrated supplier: inputs/exchange/J/JAllCharacterSource.lean
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


-- Integrated supplier: inputs/exchange/O/OSourceAction.lean
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


-- Integrated supplier: inputs/exchange/O/OCharacterAmbient.lean
/- Insert after JThetaDefinitions and OThetaClosure in the common native interval
   context. No original-source action supplier is needed for this component proof. -/
namespace OCharacterAmbient
open MeasureTheory MasulloGRH JThetaAttachment Masullo.NativeRep
open Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
open PIntervalConvolution Masullo.ClosedSubspaceConvolution
open scoped Topology InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- The actual weighted translations compose in the quotient group. -/
theorem nativeTranslationCLM_mul (g h : HeckeIdeleClasses K) :
    (nativeTranslationCLM K mu alpha s ha hs g).comp
      (nativeTranslationCLM K mu alpha s ha hs h) =
      nativeTranslationCLM K mu alpha s ha hs (g*h) := by
  apply ContinuousLinearMap.ext
  intro F
  apply Lp.ext
  have hshift := (measurePreserving_mul_left mu g⁻¹).quasiMeasurePreserving.ae
    (nativeTranslationCLM_ae K mu alpha s ha hs h F)
  filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs g
      (nativeTranslationCLM K mu alpha s ha hs h F), hshift,
    nativeTranslationCLM_ae K mu alpha s ha hs (g*h) F] with x h1 h2 h3
  change (nativeTranslationCLM K mu alpha s ha hs g
      (nativeTranslationCLM K mu alpha s ha hs h F)) x =
    (nativeTranslationCLM K mu alpha s ha hs (g*h) F) x
  rw [h1, h2, h3]
  have he : (g*h)⁻¹*x = h⁻¹*(g⁻¹*x) := by simp only [mul_inv_rev, mul_assoc]
  rw [he]
  have hw : (nativeHalfWeight alpha s (classLog K (g⁻¹*x)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  field_simp

theorem nativeTranslationCLM_commute_apply (g h : HeckeIdeleClasses K)
    (F : Lp ℂ 2 mu) :
    nativeTranslationCLM K mu alpha s ha hs g
      (nativeTranslationCLM K mu alpha s ha hs h F) =
    nativeTranslationCLM K mu alpha s ha hs h
      (nativeTranslationCLM K mu alpha s ha hs g F) := by
  have h1 := congrArg (fun A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu => A F)
    (nativeTranslationCLM_mul K mu alpha s ha hs g h)
  have h2 := congrArg (fun A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu => A F)
    (nativeTranslationCLM_mul K mu alpha s ha hs h g)
  exact h1.trans ((by rw [mul_comm] :
    nativeTranslationCLM K mu alpha s ha hs (g*h) F =
      nativeTranslationCLM K mu alpha s ha hs (h*g) F).trans h2.symm)

/-- The compact-character component in the actual completed Hilbert space.
The inverse is forced by left translation, since admitted theta functions obey
the pointwise law Theta(b*x)=chi(b)Theta(x). -/
def compactCharacterSpace (chi : UnitaryHeckeCharacter K) : Submodule ℂ (Lp ℂ 2 mu) where
  carrier := {F | ∀ b : HeckeIdeleClasses K, classLog K b = 0 →
    nativeTranslationCLM K mu alpha s ha hs b F =
      (classCharacter K chi b⁻¹ : ℂ) • F}
  zero_mem' := by intro b hb; simp
  add_mem' := by
    intro F G hF hG b hb
    rw [map_add, hF b hb, hG b hb, smul_add]
  smul_mem' := by
    intro c F hF b hb
    rw [map_smul, hF b hb]
    exact smul_comm c (classCharacter K chi b⁻¹ : ℂ) F

theorem compactCharacterSpace_isClosed (chi : UnitaryHeckeCharacter K) :
    IsClosed (compactCharacterSpace K mu alpha s ha hs chi : Set (Lp ℂ 2 mu)) := by
  have he : (compactCharacterSpace K mu alpha s ha hs chi : Set (Lp ℂ 2 mu)) =
      ⋂ b : HeckeIdeleClasses K, ⋂ (_ : classLog K b = 0),
        {F | nativeTranslationCLM K mu alpha s ha hs b F =
          (classCharacter K chi b⁻¹ : ℂ) • F} := by
    ext F
    simp only [Set.mem_iInter]
    rfl
  rw [he]
  exact isClosed_iInter fun b => isClosed_iInter fun _ =>
    isClosed_eq (nativeTranslationCLM K mu alpha s ha hs b).continuous
      (continuous_const.smul continuous_id)

instance compactCharacterSpace_complete (chi : UnitaryHeckeCharacter K) :
    CompleteSpace (compactCharacterSpace K mu alpha s ha hs chi) :=
  (compactCharacterSpace_isClosed K mu alpha s ha hs chi).completeSpace_coe

instance compactCharacterSpace_hasOrthogonalProjection (chi : UnitaryHeckeCharacter K) :
    (compactCharacterSpace K mu alpha s ha hs chi).HasOrthogonalProjection := by
  infer_instance

theorem compactCharacterSpace_translation_invariant (chi : UnitaryHeckeCharacter K)
    (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu)
    (hF : F ∈ compactCharacterSpace K mu alpha s ha hs chi) :
    nativeTranslationCLM K mu alpha s ha hs g F ∈
      compactCharacterSpace K mu alpha s ha hs chi := by
  intro b hb
  rw [nativeTranslationCLM_commute_apply, hF b hb, map_smul]

variable [MeasurableSpace (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) (chi : UnitaryHeckeCharacter K) (a : ℝ)

/-- Admission's pointwise character law is applied to the actual Lp theta vector. -/
theorem sourceVector_mem_compactCharacterSpace
    (f : AdmittedSource K addHaar mu chi a alpha s) :
    sourceVector K f ∈ compactCharacterSpace K mu alpha s ha hs chi := by
  intro b hb
  have hbi : classLog K b⁻¹ = 0 := by rw [DReview.classLog_inv, hb, neg_zero]
  have hf : (sourceVector K f : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
      normalizedTheta K a alpha s f.test := f.memLp.coeFn_toLp
  have hshift := (measurePreserving_mul_left mu b⁻¹).quasiMeasurePreserving.ae hf
  apply Lp.ext
  filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs b (sourceVector K f),
    hshift, hf, Lp.coeFn_smul (classCharacter K chi b⁻¹ : ℂ) (sourceVector K f)]
    with x h1 h2 h3 h4
  simp only [Pi.smul_apply, smul_eq_mul] at h4
  rw [h1, h4, h2, h3]
  have hlog : classLog K (b⁻¹*x) = classLog K x := by
    rw [classLog_mul, hbi, zero_add]
  unfold normalizedTheta
  rw [hlog, f.character b⁻¹ x hbi]
  have hw : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  field_simp

/-- The actual closed theta source lies in its named character component. -/
theorem thetaClosure_le_compactCharacterSpace :
    thetaClosure K addHaar mu chi a alpha s ≤
      compactCharacterSpace K mu alpha s ha hs chi := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro _ ⟨f, rfl⟩
    exact sourceVector_mem_compactCharacterSpace K mu alpha s ha hs addHaar chi a f
  · exact compactCharacterSpace_isClosed K mu alpha s ha hs chi

/-- The relative spectral space for this character, with no all-character
completeness assertion. -/
def componentSpectralSpace : Submodule ℂ (Lp ℂ 2 mu) :=
  compactCharacterSpace K mu alpha s ha hs chi ⊓
    (thetaClosure K addHaar mu chi a alpha s)ᗮ

instance componentSpectralSpace_complete :
    CompleteSpace (componentSpectralSpace K mu alpha s ha hs addHaar chi a) :=
  ((compactCharacterSpace_isClosed K mu alpha s ha hs chi).inter
    (Submodule.isClosed_orthogonal (thetaClosure K addHaar mu chi a alpha s))).completeSpace_coe

instance componentSpectralSpace_hasOrthogonalProjection :
    (componentSpectralSpace K mu alpha s ha hs addHaar chi a).HasOrthogonalProjection := by
  infer_instance

/-- On the actual character component, identity minus the geometric projection
is precisely the genuine orthogonal projection onto the relative spectral space. -/
theorem componentSpectralProjection_apply (F : Lp ℂ 2 mu)
    (hF : F ∈ compactCharacterSpace K mu alpha s ha hs chi) :
    (componentSpectralSpace K mu alpha s ha hs addHaar chi a).starProjection F =
      F - (thetaClosure K addHaar mu chi a alpha s).starProjection F := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨(compactCharacterSpace K mu alpha s ha hs chi).sub_mem hF
        (thetaClosure_le_compactCharacterSpace K mu alpha s ha hs addHaar chi a
          ((thetaClosure K addHaar mu chi a alpha s).starProjection_apply_mem F)),
      Submodule.sub_starProjection_mem_orthogonal F⟩
  · intro w hw
    have he : F - (F - (thetaClosure K addHaar mu chi a alpha s).starProjection F) =
        (thetaClosure K addHaar mu chi a alpha s).starProjection F := by abel
    rw [he]
    exact hw.2 _ ((thetaClosure K addHaar mu chi a alpha s).starProjection_apply_mem F)

variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Actual measured convolution preserves the completed character component. -/
theorem intervalConvolution_mem_compactCharacterSpace
    (l r : ℝ) (hlr : l ≤ r)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu)
    (hF : F ∈ compactCharacterSpace K mu ((r-l)/2) s (by linarith) hs chi) :
    intervalConvolutionCLM K mu l r s hlr hs h hh hc F ∈
      compactCharacterSpace K mu ((r-l)/2) s (by linarith) hs chi := by
  exact actual_closed_subspace_convolution K mu ((r-l)/2) s (by linarith) hs
    (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2
    (compactCharacterSpace K mu ((r-l)/2) s (by linarith) hs chi)
    (compactCharacterSpace_translation_invariant K mu ((r-l)/2) s (by linarith) hs chi) F hF

/-- This is the precise character-specific Pspec A application, convolution first. -/
theorem interval_residual_is_component_projection
    (l r : ℝ) (hlr : l ≤ r)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu)
    (hF : F ∈ compactCharacterSpace K mu ((r-l)/2) s (by linarith) hs chi) :
    (componentSpectralSpace K mu ((r-l)/2) s (by linarith) hs addHaar chi
      (a+(l+r)/2)).starProjection (intervalConvolutionCLM K mu l r s hlr hs h hh hc F) =
      intervalConvolutionCLM K mu l r s hlr hs h hh hc F -
        (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
          (intervalConvolutionCLM K mu l r s hlr hs h hh hc F) :=
  componentSpectralProjection_apply K mu ((r-l)/2) s (by linarith) hs addHaar chi
    (a+(l+r)/2) _
    (intervalConvolution_mem_compactCharacterSpace K mu s hs chi l r hlr h hh hc F hF)

end
end OCharacterAmbient


-- Integrated supplier: inputs/exchange/O/OAllCharacterClosure.lean
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


-- Integrated supplier: inputs/exchange/A/AArithmeticOrderFragment.lean
/- A -> P/L/O: insert after OSourceAction and AReview.Order (the first
namespace of the unchanged checked AOrderFragment). No shared definitions. -/
namespace AReview.ArithmeticOrder
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both exact masked order corrections on the chosen admitted arithmetic
source. J/O discharge source invariance by the original Bruhat action; no
free theta-equivariance or projection-commutation hypothesis is introduced.
The correction is retained, with the physical mask applied last. -/
theorem both_tests_admitted_masked_order_remainder
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (F : Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let S := (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
    (M (A0 (F-S F)) - M (A0 F-S (A0 F)) = M (S (A0 (F-S F)))) ∧
    (M (A1 (F-S F)) - M (A1 F-S (A1 F)) = M (S (A1 (F-S F)))) := by
  have hz := OArithmeticClosure.both_tests_arithmetic_PA_source_zero
    K addHaar mu chi a l r s hlr hs phi hh hc
  exact ⟨AReview.Order.masked_order_remainder _ _ M hz.1 F,
    AReview.Order.masked_order_remainder _ _ M hz.2 F⟩

end
end AReview.ArithmeticOrder


-- Integrated supplier: inputs/exchange/C/CKernelGauge.lean
/-! C interface fragment: insert after DSourceKernel.
The same Hilbert operator has different off-diagonal kernels when its
physical representative is divided by a different positive half-weight. -/
namespace CNormalization
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Exact change of physical half-weight for the chosen rank-one kernel. -/
theorem haarKernel_change_halfWeight (b c : X → ℝ)
    (V : ℝ) (U R : X → ℂ) (x y : X) :
    HNormalizedKernel.haarKernel (fun z => c z * b z) V U R x y =
      ((c y : ℂ) / (c x : ℂ)) * HNormalizedKernel.haarKernel b V U R x y := by
  simp only [HNormalizedKernel.haarKernel, Complex.ofReal_mul,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The same change for the actual orthogonal source-projection kernel E A. -/
theorem finiteKernel_change_halfWeight (nu : Measure X) (b c : X → ℝ)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (x y : X) :
    DSourceKernel.finiteKernel nu (fun z => c z * b z) E A x y =
      ((c y : ℂ) / (c x : ℂ)) * DSourceKernel.finiteKernel nu b E A x y := by
  unfold DSourceKernel.finiteKernel
  simp_rw [haarKernel_change_halfWeight b c]
  rw [Finset.mul_sum]

/-- The diagonal of the specified kernel is unchanged by positive half-weights.
This is pointwise and therefore does not restrict a product-a.e. equality. -/
theorem finiteKernel_diagonal_halfWeight_independent (nu : Measure X)
    (b c : X → ℝ) (hb : ∀ x, 0 < b x) (hc : ∀ x, 0 < c x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (x : X) :
    DSourceKernel.finiteKernel nu b E A x x =
      DSourceKernel.finiteKernel nu c E A x x := by
  unfold DSourceKernel.finiteKernel
  simp_rw [HNormalizedKernel.diagonal_formula b hb,
    HNormalizedKernel.diagonal_formula c hc]

/-- Kernel action written on physical representatives, with the output weight
removed exactly once. The integral still uses the same original measure. -/
theorem finiteKernel_physical_action (nu : Measure X) (b : X → ℝ)
    (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    (fun x => (E.starProjection (A F)) x / (b x : ℂ)) =ᵐ[nu]
      (fun x => ∫ y, DSourceKernel.finiteKernel nu b E A x y *
        (F y / (b y : ℂ)) ∂nu) := by
  filter_upwards [DSourceKernel.finiteKernel_action nu b hb E A F] with x hx
  rw [hx]
  have hb0 : (b x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hb x))
  field_simp

end
end CNormalization


-- Integrated supplier: inputs/exchange/C/CIntervalKernelGauge.lean
/-! C arithmetic specialization. Insert after CKernelGauge and the seed.
Requires no copied interval or kernel definition. -/
namespace CNormalization
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet PIntervalConvolution
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The original nonsymmetric interval kernel differs from the centered one
by the precise output/input midpoint ratio, with original Haar unchanged. -/
theorem finiteKernel_interval_transport
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ) (hlr : l ≤ r)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (x y : HeckeIdeleClasses K) :
    DSourceKernel.finiteKernel mu
      (fun z => intervalHalfWeight l r s (classLog K z)) E A x y =
      ((Real.exp (((l+r)/2) * classLog K y) : ℂ) /
        (Real.exp (((l+r)/2) * classLog K x) : ℂ)) *
      DSourceKernel.finiteKernel mu
        (fun z => nativeHalfWeight ((r-l)/2) s (classLog K z)) E A x y := by
  simp_rw [interval_halfWeight l r s _ hlr]
  exact finiteKernel_change_halfWeight mu
    (fun z => nativeHalfWeight ((r-l)/2) s (classLog K z))
    (fun z => Real.exp (((l+r)/2) * classLog K z)) E A x y

/-- The pointwise diagonal and hence any specified physical diagonal cutoff
are preserved by the original interval-to-centered change of representative. -/
theorem finiteKernel_interval_diagonal
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (x : HeckeIdeleClasses K) :
    DSourceKernel.finiteKernel mu
      (fun z => intervalHalfWeight l r s (classLog K z)) E A x x =
      DSourceKernel.finiteKernel mu
        (fun z => nativeHalfWeight ((r-l)/2) s (classLog K z)) E A x x := by
  apply finiteKernel_diagonal_halfWeight_independent
  · intro z
    unfold intervalHalfWeight
    positivity
  · intro z
    exact nativeHalfWeight_pos _ _ _

end
end CNormalization


-- Integrated supplier: inputs/exchange/D/DResidualKernelFragment.lean
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


-- Integrated supplier: inputs/exchange/D/DArithmeticResidualDiagonalFragment.lean
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


-- Integrated supplier: inputs/exchange/M/MDoubleSeriesFragment.lean
/- Insert after MSeriesFragment and ReviewM.shell_reconstruction. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {X ι E : Type*} [MeasurableSpace X] [Countable ι] [Countable E]

/-- Shell and row summations interchange using one total L2 cost.
This connects the original-Haar diagonal series to its entire arithmetic shell vector. -/
theorem all_shell_diagonal_series (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => diagonalL2Cost nu (U i) (R i)))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) :
    (∑' e, ∑' i, ∫ x, (p e x : ℂ) * haarKernel b V (U i) (R i) x x
      ∂(ENNReal.ofReal V • nu)) =
      ∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu) := by
  let mu := ENNReal.ofReal V • nu
  let q := fun i x => haarKernel b V (U i) (R i) x x
  have hi (i : ι) : Integrable (q i) mu := diagonal_integrable nu b hb V (U i) (R i)
  have hs (i : ι) := ReviewM.positive_shell_l1 mu p hp (q i) (hi i)
  have hout : Summable (fun i => ∑' e, ‖∫ x, (p e x : ℂ) * q i x ∂mu‖) :=
    Summable.of_nonneg_of_le (fun i => tsum_nonneg (fun e => norm_nonneg _))
      (fun i => (hs i).2.trans (diagonal_integral_norm_le nu b hb V hV (U i) (R i))) hcost
  have hnorm : Summable (fun ie : ι × E => ‖∫ x, (p ie.2 x : ℂ) * q ie.1 x ∂mu‖) :=
    (summable_prod_of_nonneg (fun ie => norm_nonneg _)).2 ⟨fun i => (hs i).1, hout⟩
  have hall : Summable (fun ie : ι × E => ∫ x, (p ie.2 x : ℂ) * q ie.1 x ∂mu) :=
    hnorm.of_norm
  calc
    _ = ∑' i, ∑' e, ∫ x, (p e x : ℂ) * q i x ∂mu := hall.tsum_comm
    _ = ∑' i, inner ℂ (R i) (U i) := by
      apply tsum_congr
      intro i
      rw [(ReviewM.shell_reconstruction mu p hp (q i) (hi i)).tsum_eq]
      exact diagonal_integral nu b hb V hV (U i) (R i)
    _ = _ := (diagonal_series nu b hb V hV U R hcost).tsum_eq

end
end HNormalizedKernel


-- Integrated supplier: inputs/exchange/M/MNormCostFragment.lean
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


-- Integrated supplier: inputs/exchange/M/MNuclearDiagonalFragment.lean
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


-- Integrated supplier: inputs/exchange/N/NUpstairsContinuityFragment.lean
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


-- Integrated supplier: inputs/exchange/N/NNormalizedDescentFragment.lean
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


-- Integrated supplier: inputs/exchange/B/BSourceCutoffShellFragment.lean
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


-- Integrated supplier: inputs/exchange/B/BIndependence.lean
/- B arithmetic independence fragment; insert after common normalized jets. -/
namespace Masullo.RadialExpHom
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet
open scoped BigOperators

noncomputable def radialExpHom (z : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (z * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' t u := by
    change Complex.exp (z * ((Multiplicative.toAdd t + Multiplicative.toAdd u : ℝ) : ℂ)) = _
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem radialExpHom_injective : Function.Injective radialExpHom := by
  intro z w h
  have hall : (fun t : ℝ => Complex.exp (z*(t:ℂ))) =
      (fun t : ℝ => Complex.exp (w*(t:ℂ))) := by
    funext t
    exact congrArg (fun f : Multiplicative ℝ →* ℂ => f (Multiplicative.ofAdd t)) h
  have hz : HasDerivAt (fun t : ℝ => Complex.exp (z*(t:ℂ))) z 0 := by
    convert (((Complex.hasDerivAt_exp (z*(0:ℂ))).comp 0
      ((hasDerivAt_id (0:ℂ)).const_mul z))).comp_ofReal using 1
    simp
  have hw : HasDerivAt (fun t : ℝ => Complex.exp (w*(t:ℂ))) w 0 := by
    convert (((Complex.hasDerivAt_exp (w*(0:ℂ))).comp 0
      ((hasDerivAt_id (0:ℂ)).const_mul w))).comp_ofReal using 1
    simp
  rw [hall] at hz
  exact hz.unique hw

/-- Actual original-weight zeroth kernels at distinct roots in one Hecke
component are finitely independent modulo the SAME quotient Haar null sets.
No independence or separation conclusion is an input. -/
theorem native_zero_finite_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (b : ι → ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0) :
    ∀ i ∈ S, b i = 0 := by
  classical
  let W : HeckeIdeleClasses K → ℂ := fun x =>
    (classCharacter K chi x : ℂ) * Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) *
      (((1 + (classLog K x)^2)^(-s/4) : ℝ):ℂ)
  have hW (x) : W x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
  have hfactor (i) (x) : genuineNormalizedMellinJet K chi (z i) a s alpha 0 x =
      W x * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) := by
    have he : Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ) -
        ((alpha * |classLog K x| : ℝ):ℂ)) =
        Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) *
        Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) := by
      rw [sub_eq_add_neg, Complex.exp_add]
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul, he]
    dsimp [W]
    ring
  have hrad : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) = 0 := by
    filter_upwards [h] with x hx
    have hh : W x * (∑ i ∈ S, b i * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ))) = 0 := by
      rw [Finset.mul_sum]
      convert hx using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfactor]
      ring
    exact (mul_eq_zero.mp hh).resolve_left (hW x)
  have hcont : Continuous (fun t : ℝ => ∑ i ∈ S,
      b i * Complex.exp ((z i-(a:ℂ))*(t:ℂ))) := by fun_prop
  have hm := (ae_map_iff (Masullo.WeightedIdeleClass.classLog_continuous K).measurable.aemeasurable
    (isClosed_eq hcont continuous_const).measurableSet).mpr hrad
  rw [hmap] at hm
  have hm0 : ∀ᵐ t : ℝ ∂volume, ∑ i ∈ S, b i * Complex.exp ((z i-(a:ℂ))*(t:ℂ)) = 0 := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hm0
  have hinj : Function.Injective (fun i => radialExpHom (z i-(a:ℂ))) := by
    intro i j hij
    apply hz
    have he := radialExpHom_injective hij
    linear_combination he
  have hli := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (fun i => radialExpHom (z i-(a:ℂ))) hinj
  apply (linearIndependent_iff'.mp hli) S b
  funext t
  simpa [radialExpHom, Function.comp_def] using congrFun hall (Multiplicative.toAdd t)

end Masullo.RadialExpHom

namespace Masullo.RadialExpHom
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet
open scoped BigOperators
/-- Independence of the actual conjugated L2 vectors used by native Gram–Schmidt,
for all distinct zeroth roots in one fixed character component. -/
theorem native_zero_L2_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu) :
    LinearIndependent ℂ (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))) := by
  classical
  let J := fun i => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))
  apply linearIndependent_iff'.mpr
  intro S b hsum
  have he (T : Finset ι) :
      (fun x => (∑ i ∈ T, b i • J i) x) =ᵐ[mu]
        (fun x => ∑ i ∈ T, b i * star (genuineNormalizedMellinJet K chi (z i) a s alpha 0 x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (b i • J i) (∑ j ∈ T, b j • J j),
        Lp.coeFn_smul (b i) (J i), (hg i).star.coeFn_toLp, ih] with x hx hs hj ht
      change J i x = star (genuineNormalizedMellinJet K chi (z i) a s alpha 0 x) at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  have hzsum : ∀ᵐ x ∂mu, ∑ i ∈ S,
      star (b i) * genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0 := by
    have hz0 := Lp.coeFn_zero ℂ 2 mu
    have hh := he S
    change (∑ i ∈ S, b i • J i) = 0 at hsum
    rw [hsum] at hh
    filter_upwards [hh, hz0] with x hx hx0
    have hh' := congrArg star (hx.symm.trans hx0)
    simpa only [star_sum, star_mul, star_star, Pi.zero_apply, star_zero, mul_comm] using hh'
  have hb := native_zero_finite_independent K chi mu c hc hmap z hz a s alpha S
    (fun i => star (b i)) hzsum
  intro i hi
  exact star_eq_zero.mp (hb i hi)

end Masullo.RadialExpHom



-- Integrated supplier: inputs/exchange/B/BGramApplications.lean
/- B integration fragment: insert after BGramKernel and BIndependence.
   The finite label closure is unconditional. The nonsingularity theorem uses
   proved arithmetic zeroth-jet independence and states its Haar hypotheses. -/
namespace BGramApplications
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.ActualGram
open Masullo.GramDualPairingIntegrable
open scoped InnerProductSpace ComplexOrder
variable (K : Type*) [Field K] [NumberField K]

/-- Complete finite multiplicity flags are downward closed, including when
N is the actual boundary-truncated multiplicity. -/
theorem fullJetFamily_closed {J : Type*}
    (chi : J → UnitaryHeckeCharacter K) (z : J → ℂ) (N : J → ℕ) :
    JetClosed K (fun i : Sigma (fun j => Fin (N j)) => chi i.1)
      (fun i => z i.1) (fun i => i.2.val) := by
  intro i k hk
  exact ⟨⟨i.1, ⟨k, lt_of_le_of_lt hk i.2.isLt⟩⟩, rfl, rfl, rfl⟩

/-- The actual original-Haar Gram matrix equals the Hilbert Gram matrix of
the actual normalized Riesz representatives, with no transposition. -/
theorem actualGram_eq_L2_Gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K))
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ)
    (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp
      (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu) :
    (fun i j => inner ℂ
      ((hg i).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i))))
      ((hg j).star.toLp
        (star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j))))) =
      actualGram K mu chi z a s alpha m := by
  funext i j
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hg i).star.coeFn_toLp, (hg j).star.coeFn_toLp] with x hx hy
  rw [hx, hy]
  rw [actual_Gram_density]
  simp [RCLike.inner_apply, mul_comm]

/-- Concrete nonsingularity and flag closure for distinct zeroth Mellin
parameters in one genuine Hecke component. Higher jet independence is not
asserted by this declaration. -/
theorem actual_zeroth_Gram_application
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (hg : ∀ i, MemLp
      (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu) :
    IsUnit (actualGram K mu (fun _ => chi) z a s alpha (fun _ => 0)).det ∧
      JetClosed K (fun _ : ι => chi) z (fun _ => 0) := by
  constructor
  · rw [← actualGram_eq_L2_Gram K mu (fun _ => chi) z a s alpha (fun _ => 0) hg]
    exact isUnit_iff_ne_zero.mpr
      (ne_of_gt (Matrix.posDef_gram_of_linearIndependent
        (Masullo.RadialExpHom.native_zero_L2_independent
          K chi mu c hc hmap z hz a s alpha hg)).det_pos)
  · intro i k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    exact ⟨i, rfl, rfl, hk0.symm⟩

end BGramApplications


-- Integrated supplier: inputs/exchange/I/ICompletedShellFragment.lean
/- Insert after B/D's completed projection, L's required tests, and
   NArithmeticShellFragment. The same finite operator and kernel are used. -/
namespace ReviewI.Integration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open Masullo.NativeRep Masullo.NativePettisVectorBound
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- One finite operator-to-shell statement on the actual arithmetic kernel.
The orthogonal projection acts after the constructed completed convolution.
Both test families and the original-Haar negative complement diagonal use
this very kernel. Global theta-source exhaustion/local unfolding remain separate. -/
theorem both_tests_completed_kernel_shells
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (hmeas : ∀ e, Measurable (NDivisorialShells.descendedMask K v b e))
    (q : Fin 2) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let r : ι → Lp ℂ 2 mu := fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    let ker := finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m)
    let d := fun x => h (x*x⁻¹) - ker x x
    let p := NDivisorialShells.descendedMask K v b
    let spectral := ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu
    (∀ F : Lp ℂ 2 mu,
      (fun x => ((Submodule.span ℂ (Set.range r)).starProjection
        (nativeConvolutionCLM K mu alpha s ha hs h ht.1 ht.2 F)) x) =ᵐ[mu]
      (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        ∫ y, ker x y * nativeRep K mu alpha s F y ∂mu)) ∧
    Integrable (fun x => ker x x) mu ∧
    (∫ x, ker x x ∂mu) = spectral ∧
    HasSum (fun e => ∫ x, (p e x : ℂ) * d x ∂mu) (-spectral) ∧
    Summable (fun e => ‖∫ x, (p e x : ℂ) * d x ∂mu‖) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p e x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  have ht := LIntegrated.requiredTest_compact K phi hh hc q
  have hlow : ∀ i k, k ≤ m i →
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu :=
    fun i k hk => closed_family_native_admission K mu chi z a s alpha m hg hclosed i k hk
  have hp := NArithmeticIntegration.descended_positivePartition K v b hb hbs hmeas
  have hn := NArithmeticIntegration.finite_complement_shells K mu chi z m a s alpha
    hg hdet hclosed h ht.1 ht.2 (LIntegrated.requiredTest_at_one K phi hphi q) _ hp
  refine ⟨?_, actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m
    hg hclosed h ht.1 ht.2, actual_Gram_PA_diagonal_integral K mu chi z a s alpha m
      hg hdet hclosed h ht.1 ht.2, hn⟩
  intro F
  exact Masullo.GramCompletedKernelAction.actual_Gram_completed_kernel_action K mu chi z m
    a s alpha ha hs hlow h ht.1 ht.2 hdet F

end
end ReviewI.Integration


-- Integrated supplier: inputs/exchange/I/ISourceShellFragment.lean
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


-- Integrated supplier: inputs/exchange/L/LCharacter.fragment.lean
/-! Append after LTestBoundary.fragment.lean. -/
namespace LIntegrated
open MasulloGRH Masullo.IdeleClassGeometry
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Unitarity reverses the inverse when applying sharp. -/
theorem classCharacter_star_inv (chi : UnitaryHeckeCharacter K)
    (c : HeckeIdeleClasses K) :
    star ((classCharacter K chi c⁻¹ : Circle) : ℂ) =
      ((classCharacter K chi c : Circle) : ℂ) := by
  refine Quotient.inductionOn c ?_
  intro b
  change star ((chi.character b⁻¹ : Circle) : ℂ) = ((chi.character b : Circle) : ℂ)
  rw [map_inv]
  simp [Complex.inv_def, Complex.normSq_eq_norm_sq]

/-- Reverse conjugation preserves the fixed unitary compact character component. -/
theorem sharp_component (chi : UnitaryHeckeCharacter K)
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ c x, classLog K c = 0 →
      phi (c*x) = (classCharacter K chi c : ℂ) * phi x)
    (c x : HeckeIdeleClasses K) (hc : classLog K c = 0) :
    DReview.sharp K phi (c*x) = (classCharacter K chi c : ℂ) * DReview.sharp K phi x := by
  have hci : classLog K c⁻¹ = 0 := by rw [DReview.classLog_inv, hc, neg_zero]
  change star (phi (c*x)⁻¹) = (classCharacter K chi c : ℂ) * star (phi x⁻¹)
  rw [mul_inv_rev, mul_comm x⁻¹ c⁻¹, hphi c⁻¹ x⁻¹ hci, star_mul,
    classCharacter_star_inv]
  exact mul_comm _ _

/-- Both required tests retain the same compact character component. -/
theorem requiredTest_component (chi : UnitaryHeckeCharacter K)
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ c x, classLog K c = 0 →
      phi (c*x) = (classCharacter K chi c : ℂ) * phi x)
    (q : Fin 2) (c x : HeckeIdeleClasses K) (hc : classLog K c = 0) :
    requiredTest K phi q (c*x) =
      (classCharacter K chi c : ℂ) * requiredTest K phi q x := by
  fin_cases q
  · exact sharp_component K chi phi hphi c x hc
  · change requiredTest K phi 1 (c*x) =
      (classCharacter K chi c : ℂ) * requiredTest K phi 1 x
    rw [requiredTest_log_sign, requiredTest_log_sign,
      Masullo.WeightedIdeleClass.classLog_mul, hc, zero_add,
      requiredTest_zero, sharp_component K chi phi hphi c x hc]
    ring
end
end LIntegrated


-- Integrated supplier: inputs/exchange/R/RIntervalParametersFragment.lean
/- Insert after RApplicationFragment. No new arithmetic definition. -/
namespace RIntegrated

/-- The centered numerical admission is exactly the original interval strip,
with its strict endpoint order and no change of Mellin parameter. -/
theorem interval_admission_iff (z : ℂ) (a l r s : ℝ) (m : ℕ) (hlr : l ≤ r) :
    (|z.re - (a + (l+r)/2)| < (r-l)/2 ∨
      (|z.re - (a + (l+r)/2)| = (r-l)/2 ∧ (2 : ℝ)*m+1 < s)) ↔
    ((a+l < z.re ∧ z.re < a+r) ∨
      ((z.re = a+l ∨ z.re = a+r) ∧ (2 : ℝ)*m+1 < s)) := by
  have hi : |z.re - (a + (l+r)/2)| < (r-l)/2 ↔
      a+l < z.re ∧ z.re < a+r := by
    rw [abs_lt]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  have hb : |z.re - (a + (l+r)/2)| = (r-l)/2 ↔
      z.re = a+l ∨ z.re = a+r := by
    by_cases h : 0 ≤ z.re - (a + (l+r)/2)
    · rw [abs_of_nonneg h]
      constructor
      · intro he
        exact Or.inr (by linarith)
      · rintro (he | he) <;> linarith
    · rw [abs_of_neg (lt_of_not_ge h)]
      constructor
      · intro he
        exact Or.inl (by linarith)
      · rintro (he | he) <;> linarith
  rw [hi, hb]

/-- At odd weight the original interval boundary retains precisely min(N,k)
jet orders; the logarithmic test does not enlarge the admissible space. -/
theorem interval_boundary_orders_odd
    (K : Type*) [Field K] [NumberField K]
    (chi : MasulloGRH.UnitaryHeckeCharacter K)
    (mu : MeasureTheory.Measure (MasulloGRH.HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : MeasureTheory.Measure.map (Masullo.IdeleClassGeometry.classLog K) mu =
      c • MeasureTheory.volume)
    (z : ℂ) (a l r : ℝ) (N k : ℕ) (hlr : l ≤ r)
    (hb : z.re = a+l ∨ z.re = a+r) :
    (Finset.range N).filter (fun m => MeasureTheory.MemLp
      (Masullo.GenuineNormalizedMellinJet.genuineNormalizedMellinJet K chi z
        (a+(l+r)/2) (2*(k : ℝ)+1) ((r-l)/2) m) 2 mu) =
      Finset.range (min N k) := by
  classical
  have habs : |z.re - (a+(l+r)/2)| = (r-l)/2 := by
    rcases hb with hb | hb
    · rw [hb, show a+l-(a+(l+r)/2) = -((r-l)/2) by ring, abs_neg,
        abs_of_nonneg (by linarith : 0 ≤ (r-l)/2)]
    · rw [hb, show a+r-(a+(l+r)/2) = (r-l)/2 by ring,
        abs_of_nonneg (by linarith : 0 ≤ (r-l)/2)]
  have hh := Masullo.GenuineNormalizedMellinJet.genuine_boundary_mellin_orders
    K chi mu c hc0 hct hmap z (a+(l+r)/2) (2*(k : ℝ)+1) ((r-l)/2) N
    (by positivity) (by linarith) habs
  rw [← Masullo.BoundaryJetOrders.boundaryJetOrders_all_real,
    Masullo.BoundaryJetOrders.boundaryJetOrders_odd] at hh
  exact hh

end RIntegrated


-- Integrated supplier: inputs/exchange/R/RProjectedChainFragment.lean
/- Insert after RTwoTestFragment, JThetaAttachment, and OThetaClosure.
   This uses the actual admitted theta closure and keeps its correction. -/
namespace RIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.NativePairingInner PIntervalConvolution LIntegrated
open JThetaAttachment OArithmeticClosure
noncomputable section

/-- The normalized Mellin pairing respects subtraction in the completed L2
space, using its actual integrable representative. -/
theorem normalized_pairing_sub
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K))
    (j : HeckeIdeleClasses K → ℂ) (hj : MemLp j 2 mu)
    (U V : Lp ℂ 2 mu) :
    (∫ x, j x * (U-V) x ∂mu) =
      (∫ x, j x * U x ∂mu) - (∫ x, j x * V x ∂mu) := by
  simp only [native_pairing_inner K mu j hj, inner_sub_right]

/-- The actual global complementary operator has the proved Mellin chain
minus the coefficient of its genuine source projection. No annihilation of
the admitted theta sources, spectral completeness, or commutation is assumed. -/
theorem both_tests_arithmetic_projected_chain
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (hadm : |z.re-(a+(l+r)/2)| < (r-l)/2 ∨
      (|z.re-(a+(l+r)/2)| = (r-l)/2 ∧ (2 : ℝ)*m+1 < s))
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let S := (thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s).starProjection
    let j := genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m
    (∫ x, j x * (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S).comp A F) x ∂mu) =
      (∑ k ∈ Finset.range (m+1),
        (mellinCoefficient K mu chi z a (requiredTest K phi q) k * (m.choose k : ℂ)) *
          (∫ y, genuineNormalizedMellinJet K chi z (a+(l+r)/2)
            s ((r-l)/2) (m-k) y * F y ∂mu)) -
      (∫ x, j x * (S (A F)) x ∂mu) := by
  dsimp only
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply]
  have hj := native_admitted_chain_memLp K chi mu c hc0 hct hmap z
    (a+(l+r)/2) s ((r-l)/2) m hs (by linarith) hadm m le_rfl
  rw [normalized_pairing_sub K mu _ hj]
  rw [both_tests_interval_chain K mu l r s hlr hs c hc0 hct hmap chi z a m
    hadm phi hh hc q F]

end
end RIntegrated


-- Integrated supplier: inputs/exchange/H/HNuclearSupportFragment.lean
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


-- Integrated supplier: inputs/exchange/H/HNuclearTraceFragment.lean
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


-- Integrated supplier: inputs/exchange/H/HProjectedBasisFragment.lean
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


-- Integrated supplier: inputs/exchange/Q/QSourceDiagonalLimitFragment.lean
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


-- Integrated supplier: inputs/exchange/Q/QSourceTraceLimitFragment.lean
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
      (fun j : ℕ => norm_nonneg (inner ℂ (u j) (v j)))
      (fun j : ℕ => norm_inner_le_norm (u j) (v j)) hc
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


-- Integrated supplier: inputs/exchange/E/SourceOperatorTailFragment.lean
/- Append after E SourceResidualFragment and QSourceCutoffFragment.
   Quantitative form of the fixed-mask source cutoff in G32 §3/E34 (34.10).
   The explicit factorization is retained; no arithmetic nuclearity is assumed
   implicitly or concluded from strong projection convergence alone. -/
namespace ESourceResidual
open Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The source cost directly bounds the error of the actual ordered operators
on every completed input, with unit constant. -/
theorem common_source_operator_error (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) (x : H) :
    ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A) (M x) -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A) (M x)‖ ≤
      (∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖) * ‖x‖ := by
  have hs := actual_theta_factor_residual e0 eF Theta A M u v hfactor T x
  have hcost := source_factor_cost_summable (sourceClosure e0 eF Theta)
    (finiteSourceSpan e0 eF Theta T) (finiteSourceSpan_le e0 eF Theta T) u v hc
  apply hs.norm_le_of_bounded (hcost.hasSum.mul_right ‖x‖)
  intro j
  rw [norm_smul]
  calc
    ‖⟪u j, x⟫_ℂ‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ ≤
      (‖u j‖ * ‖x‖) * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ :=
      mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

/-- The same estimate is uniform over the unit ball, hence an operator norm
bound, not only the strong limit already provided by the seed. -/
theorem common_source_operator_norm_error (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x)))
    (T : Finset H) :
    ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M‖ ≤
      ∑' j, ‖u j‖ * ‖(finiteSourceSpan e0 eF Theta T).starProjection (v j) -
        (sourceClosure e0 eF Theta).starProjection (v j)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  intro x
  exact common_source_operator_error e0 eF Theta A M u v hc hfactor T x

/-- Explicit finite head plus original nuclear tail, with all cross-source
geometry remaining in the genuine projected columns. -/
theorem source_factor_head_tail_bound (S E : Submodule ℂ H)
    [S.HasOrthogonalProjection] [E.HasOrthogonalProjection]
    (hES : E ≤ S) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖)) (N : ℕ) :
    (∑' j, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) ≤
      (∑ j ∈ Finset.range N, ‖u j‖ * ‖E.starProjection (v j) - S.starProjection (v j)‖) +
      ∑' j, ‖u (j+N)‖ * ‖v (j+N)‖ := by
  have hs := source_factor_cost_summable S E hES u v hc
  rw [← hs.sum_add_tsum_nat_add N]
  apply add_le_add_right
  apply Summable.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left
      (nested_source_residual_contraction S E hES (v (j+N))) (norm_nonneg _))
  · exact (summable_nat_add_iff N).2 hs
  · exact (summable_nat_add_iff N).2 hc

/-- Q's proved directed density now pays the operator norm error, provided
that the actual fixed-mask factorization has separately been constructed. -/
theorem common_source_operator_norm_tendsto (e0 eF : V →ₗ[ℂ] ℂ)
    (Theta : twoMomentSource e0 eF →ₗ[ℂ] H)
    (A M : H →L[ℂ] H) (u v : ℕ → H)
    (hc : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ x, HasSum (fun j => ⟪u j, x⟫_ℂ • v j) (A (M x))) :
    Tendsto (fun T : Finset H =>
      ‖((ContinuousLinearMap.id ℂ H - (sourceClosure e0 eF Theta).starProjection).comp A).comp M -
       ((ContinuousLinearMap.id ℂ H - (finiteSourceSpan e0 eF Theta T).starProjection).comp A).comp M‖)
      atTop (𝓝 0) := by
  classical
  exact squeeze_zero (fun _ => norm_nonneg _)
    (common_source_operator_norm_error e0 eF Theta A M u v hc hfactor)
    (actual_theta_nuclear_cost_limit e0 eF Theta u v hc)

end
end ESourceResidual


-- Integrated supplier: integration/PFullAssembly.fragment.lean
/- P integration: the unrestricted admitted original source, both actual tests,
   the same finite kernels, arithmetic masks, and the actual global operator. -/
namespace PIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Common all-source assembly. The finite source kernels have genuine operator
traces and arithmetic shell decompositions, and their complementary operators
converge strongly to P A on every completed input. The source action and order
remainder are proved for the actual admitted original tests. The indentation
conditions remain explicit until its arithmetic existence is proved. No global
nuclearity, trace-limit, or local-orbital equality is asserted by this theorem. -/
theorem full_arithmetic_kernel_trace_source_shells
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (indent : HeckeIdeles K → ℝ)
    (hindcont : Continuous indent) (hind : ∀ x, 0 ≤ indent x)
    (hmass : ∀ x, HasSum (fun t : Kˣ => indent (principalIdele K t * x)) 1)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let W := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let S := W.starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - S
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v indent
    let d := fun T x => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹)) x x
    (∀ chi : UnitaryHeckeCharacter K,
      thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s ≤ W) ∧
    (P.comp A).comp S = 0 ∧
    A.comp P - P.comp A = S.comp (A.comp P) ∧
    (∀ T,
      (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
        (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
          (F y / (b y : ℂ)) ∂mu) ∧
      Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) x ∂mu)
        atTop (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        (Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Integrable (d T) mu ∧
      (∫ x, d T x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) * d T x ∂mu)
        (-Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Summable (fun e => ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ∧
      (∑' e, ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ≤ ∫ x, ‖d T x‖ ∂mu ∧
      Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
        (DReview.physicalBand K n).indicator (d T) x ∂mu) -
        (∫ x, (p e x : ℂ) * d T x ∂mu)‖) atTop (𝓝 0)) ∧
    Tendsto (fun T => (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (E T).starProjection).comp A) F) atTop (𝓝 ((P.comp A) F)) := by
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  let A := intervalConvolutionCLM K mu l r s hlr hs h
    (LIntegrated.requiredTest_compact K phi hh hc q).1
    (LIntegrated.requiredTest_compact K phi hh hc q).2
  let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
    (a+(l+r)/2) ((r-l)/2) s
  let W := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let S := W.starProjection
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  have hb : ∀ x, 0 < b x := fun x =>
    FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)
  have hmain := DSourceKernel.source_kernel_trace_global_connection mu b hb
    (0 : V →ₗ[ℂ] ℂ) 0 Theta A F
  have hE : ∀ g x, x ∈ W →
      Masullo.NativeRep.nativeTranslationCLM K mu ((r-l)/2) s (by linarith) hs g x ∈ W := by
    intro g
    exact OAllCharacterClosure.fullTheta_translation_invariant K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s (by linarith) hs g
  have hz : (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S).comp A).comp S = 0 :=
    interval_PA_source_zero K mu l r s hlr hs h
      (LIntegrated.requiredTest_compact K phi hh hc q).1
      (LIntegrated.requiredTest_compact K phi hh hc q).2 W hE
  refine ⟨fun chi => thetaClosure_le_fullThetaClosure K addHaar mu chi
    (a+(l+r)/2) ((r-l)/2) s, hz,
    AReview.Order.order_remainder_of_source_zero A S hz, ?_, ?_⟩
  · intro T
    obtain ⟨hi, htrace, hsource, hri, hrt, hrsource, hrsum, hrbound, hrlim⟩ :=
      ReviewI.Integration.finite_interval_source_shells K mu l r s hlr hs
        (DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta T)
        phi hh hc hphi v indent hindcont hind hmass q
    have hphysical := DReview.originalHaar_physical_limit K mu _ hi
    rw [htrace] at hphysical
    exact ⟨hmain.1 T, hi, htrace, hphysical, hsource, hri, hrt,
      hrsource, hrsum, hrbound, hrlim⟩
  · have hp := OAllCharacterClosure.full_sourceProjection_eq K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    have hlim := hmain.2.2
    rw [hp] at hlim
    exact hlim

end
end PIntegrated

#check PIntegrated.full_arithmetic_kernel_trace_source_shells
#print axioms PIntegrated.full_arithmetic_kernel_trace_source_shells
#print axioms OAllCharacterClosure.both_tests_full_PA_source_zero
#print axioms RIntegrated.both_tests_arithmetic_projected_chain


-- Integrated supplier: inputs/exchange/J/JThetaSummabilityCore.lean
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


-- Integrated supplier: inputs/exchange/J/JOriginalThetaSummable.lean
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


-- Integrated supplier: inputs/exchange/G/GPointwiseCore.lean
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



-- Integrated supplier: inputs/exchange/G/GPointwiseConvolutionFragment.lean
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



-- Integrated supplier: inputs/exchange/D/DResidualKernelLimitFragment.lean
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


-- Integrated supplier: inputs/exchange/D/DAllSourceKernelFragment.lean
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


-- Integrated supplier: inputs/exchange/D/DAllSourceResidualDiagonalFragment.lean
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


-- Integrated supplier: inputs/exchange/D/DAllSourceMeasuredResidualFragment.lean
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


-- Integrated supplier: inputs/exchange/H/HNuclearKernelFragment.lean
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


-- Integrated supplier: inputs/exchange/H/HNuclearTraceAssemblyFragment.lean
/- Append after HNuclearKernelFragment and MNuclearDiagonalFragment. -/
namespace HOperatorTrace
open MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section
variable {κ X : Type*} [Countable κ] [MeasurableSpace X]

/-- Original-Haar row diagonal, its actual operator trace, and all shells
are attached to the same completed operator equation. -/
theorem nuclear_kernel_trace_shells {J : Type*} [Countable J]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : κ → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hT : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i) (T F))
    (p : J → X → ℝ) (hp : ReviewM.PositivePartition p) :
    Integrable (fun x => ∑' i, HNormalizedKernel.haarKernel b V (v i) (u i) x x)
      (ENNReal.ofReal V • nu) ∧
    (∫ x, ∑' i, HNormalizedKernel.haarKernel b V (v i) (u i) x x
      ∂(ENNReal.ofReal V • nu)) = Masullo.TraceClass.trace T ∧
    HasSum (fun j => ∫ x, (p j x : ℂ) *
      (∑' i, HNormalizedKernel.haarKernel b V (v i) (u i) x x)
        ∂(ENNReal.ofReal V • nu)) (Masullo.TraceClass.trace T) := by
  have hc' : Summable (fun i => ‖v i‖ * ‖u i‖) := by simpa only [mul_comm] using hc
  refine ⟨(HNormalizedKernel.nuclear_diagonal_integrable nu b hb V hV v u hc').1,
    nuclear_kernel_trace nu b hb V hV T u v hc hT, ?_⟩
  rw [nuclear_trace T u v hc hT]
  exact (HNormalizedKernel.nuclear_diagonal_shells nu b hb V hV v u hc' p hp).1

/-- Contractive physical cutoffs converge to the actual operator trace;
the required L1 diagonal is derived from the very same nuclear factors. -/
theorem nuclear_kernel_cutoff_trace_limit
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : κ → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hT : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i) (T F))
    (omega : ℕ → X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) (ENNReal.ofReal V • nu))
    (hbound : ∀ n, ∀ᵐ x ∂(ENNReal.ofReal V • nu), ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂(ENNReal.ofReal V • nu), Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, omega n x *
      (∑' i, HNormalizedKernel.haarKernel b V (v i) (u i) x x)
        ∂(ENNReal.ofReal V • nu)) atTop (𝓝 (Masullo.TraceClass.trace T)) := by
  rw [← nuclear_kernel_trace nu b hb V hV T u v hc hT]
  have hi := (HNormalizedKernel.nuclear_diagonal_integrable nu b hb V hV v u
    (by simpa only [mul_comm] using hc)).1
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖∑' i, HNormalizedKernel.haarKernel b V (v i) (u i) x x‖)
  · intro n
    exact (hm n).mul hi.aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa only [one_mul] using hx.mul
      (tendsto_const_nhds (x := ∑' i, HNormalizedKernel.haarKernel b V (v i) (u i) x x))

end
end HOperatorTrace


-- Integrated supplier: inputs/exchange/H/HArithmeticBasisFragment.lean
/- Append after JAllCharacterSource, OAllCharacterClosure, LIntegrated and HProjectedBasis. -/
namespace HArithmeticTrace
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped InnerProductSpace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Full-input factorization on the literal full admitted arithmetic source
complement, for both actual interval convolutions. No factor equation or norm
summability is assumed: the former is proved by geometric Hilbert expansion.
The analytic nuclear cost is a further, distinct application. -/
theorem full_arithmetic_basis_factor
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) :
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (LIntegrated.requiredTest K phi q) ht.1 ht.2
    let S := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let e := Masullo.TraceClass.stdHilbertBasis ℂ Sᗮ
    ∀ F : Lp ℂ 2 mu,
      HasSum (fun i => inner ℂ (A.adjoint (e i : Lp ℂ 2 mu)) F • (e i : Lp ℂ 2 mu))
        ((((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S.starProjection).comp A) F) := by
  dsimp only
  intro F
  exact HOperatorTrace.source_complement_basis_factor _ _ _ F

end
end HArithmeticTrace


-- Integrated supplier: inputs/exchange/F/FPhysicalFilter.lean
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


-- Integrated supplier: inputs/exchange/F/FOriginalPhysicalNet.lean
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


/- P integration: the unrestricted admitted original source, both actual tests,
   the same finite kernels, arithmetic masks, and the actual global operator. -/
namespace PIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- The actual full-input residual kernels converge in L2 to the genuine
orthogonal complement projector AFTER arithmetic convolution. The same finite
source and residual diagonals have the original-Haar traces, arithmetic shells,
and independent two-parameter physical limits. Global nuclear cost and local
orbital evaluation are not assumed or concluded here. -/
theorem geometric_trace_operator_assembly
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (indent : HeckeIdeles K → ℝ)
    (hindcont : Continuous indent) (hind : ∀ x, 0 ≤ indent x)
    (hmass : ∀ x, HasSum (fun t : Kˣ => indent (principalIdele K t * x)) 1)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let W := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let S := W.starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - S
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v indent
    let d := fun T x => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹)) x x
    let k := fun T => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹))
    let kF := fun T x => (b x : ℂ) * ∫ y, k T x y * (F y / (b y : ℂ)) ∂mu
    (∀ T, (fun x => (A F - (E T).starProjection (A F)) x) =ᵐ[mu] kF T) ∧
    (∃ hm : ∀ T, MemLp (kF T) 2 mu,
      (∀ T, (hm T).toLp (kF T) = A F - (E T).starProjection (A F)) ∧
      Tendsto (fun T => (hm T).toLp (kF T)) atTop
        (𝓝 ((Wᗮ.starProjection.comp A) F))) ∧
    (∀ (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ),
      (∀ L e, FPhysicalFilter.ValidCutoff L e → AEStronglyMeasurable (omega L e) mu) →
      (∀ L e, FPhysicalFilter.ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1) →
      (∀ L e, FPhysicalFilter.ValidCutoff L e → ∀ x,
        L⁻¹ + e ≤ Real.exp (classLog K x) → Real.exp (classLog K x) ≤ L-e →
          omega L e x = 1) →
      ∀ T,
        Tendsto (fun z : ℝ × ℝ => ∫ x, omega z.1 (z.2/z.1) x *
          DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
          FPhysicalFilter.cutoffRegime
          (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
        Tendsto (fun z : ℝ × ℝ => ∫ x, omega z.1 (z.2/z.1) x * d T x ∂mu)
          FPhysicalFilter.cutoffRegime
          (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A)))) ∧
    (∀ chi : UnitaryHeckeCharacter K,
      thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s ≤ W) ∧
    (P.comp A).comp S = 0 ∧
    A.comp P - P.comp A = S.comp (A.comp P) ∧
    (∀ T,
      (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
        (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
          (F y / (b y : ℂ)) ∂mu) ∧
      Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) x ∂mu)
        atTop (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        (Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Integrable (d T) mu ∧
      (∫ x, d T x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) * d T x ∂mu)
        (-Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Summable (fun e => ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ∧
      (∑' e, ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ≤ ∫ x, ‖d T x‖ ∂mu ∧
      Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
        (DReview.physicalBand K n).indicator (d T) x ∂mu) -
        (∫ x, (p e x : ℂ) * d T x ∂mu)‖) atTop (𝓝 0)) ∧
    Tendsto (fun T => (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (E T).starProjection).comp A) F) atTop (𝓝 ((P.comp A) F)) := by
  dsimp only
  have hd := DAllSourceKernel.both_tests_original_residual_kernel K addHaar mu
    a l r s hlr hs phi hh hc hphi q F
  refine ⟨hd.1, hd.2.2, ?_, ?_⟩
  · intro omega hm hb hp
    exact FArithmeticPhysical.both_tests_original_physical_net K addHaar mu
      a l r s hlr hs phi hh hc hphi q omega hm hb hp
  · exact full_arithmetic_kernel_trace_source_shells K addHaar mu
      a l r s hlr hs phi hh hc hphi v indent hindcont hind hmass q F

end
end PIntegrated
#check PIntegrated.geometric_trace_operator_assembly
#print axioms PIntegrated.geometric_trace_operator_assembly
#print axioms JThetaAttachment.originalBruhat_theta_summable
#print axioms HArithmeticTrace.full_arithmetic_basis_factor


-- Integrated supplier: inputs/exchange/A/AFullSourceOrderFragment.lean
/- A -> P/L/O: insert after OAllCharacterClosure and AReview.Order (the first
namespace of the unchanged checked AOrderFragment). No shared definitions. -/
namespace AReview.ArithmeticOrder
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- Both exact masked order corrections on the full admitted arithmetic
source. J/O discharge source invariance by the original Bruhat action; no
free theta-equivariance or projection-commutation hypothesis is introduced.
The correction is retained, with the physical mask applied last. -/
theorem both_tests_full_masked_order_remainder
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (F : Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    (M (A0 (F-S F)) - M (A0 F-S (A0 F)) = M (S (A0 (F-S F)))) ∧
    (M (A1 (F-S F)) - M (A1 F-S (A1 F)) = M (S (A1 (F-S F)))) := by
  have hz := OAllCharacterClosure.both_tests_full_PA_source_zero
    K addHaar mu a l r s hlr hs phi hh hc
  exact ⟨AReview.Order.masked_order_remainder _ _ M hz.1 F,
    AReview.Order.masked_order_remainder _ _ M hz.2 F⟩

end
end AReview.ArithmeticOrder


-- Integrated supplier: inputs/exchange/C/CArithmeticMeasure.lean
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


-- Integrated supplier: inputs/exchange/J/JAdmissionConstructors.lean
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


-- Integrated supplier: inputs/exchange/R/RComponentChainFragment.lean
/- Insert after RProjectedChainFragment and OCharacterAmbient.
   R owns inverseCharacter; L reviews its source/dual convention. -/
namespace RIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.NativePairingInner PIntervalConvolution LIntegrated
open JThetaAttachment OArithmeticClosure OCharacterAmbient
noncomputable section

/-- The pointwise inverse of an actual unitary Hecke character, still trivial
on principal ideles. This supplies the primal component for a bilinear jet. -/
def inverseCharacter (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) : UnitaryHeckeCharacter K where
  character := chi.character⁻¹
  trivial_on_principal u := by
    change (chi.character (principalIdele K u))⁻¹ = 1
    rw [chi.trivial_on_principal, inv_one]

theorem classCharacter_inverseCharacter
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (x : HeckeIdeleClasses K) :
    classCharacter K (inverseCharacter K chi) x = (classCharacter K chi x)⁻¹ := by
  induction x using Quotient.inductionOn with
  | h x => rfl

/-- The left-translation character on the inverse pointwise component is
exactly the character appearing in the Mellin jet. -/
theorem inverseCharacter_left_eigenvalue
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (x : HeckeIdeleClasses K) :
    classCharacter K (inverseCharacter K chi) x⁻¹ = classCharacter K chi x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change (chi.character x⁻¹)⁻¹ = chi.character x
    rw [map_inv, inv_inv]

/-- Strong source convergence passes through every actually admitted jet
functional; the scalar integral is continuous on the completed Hilbert space. -/
theorem normalized_pairing_continuous
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K))
    (j : HeckeIdeleClasses K → ℂ) (hj : MemLp j 2 mu) :
    Continuous (fun F : Lp ℂ 2 mu => ∫ x, j x * F x ∂mu) := by
  have hh : Continuous (fun F : Lp ℂ 2 mu => inner ℂ (hj.star.toLp (star j)) F) :=
    continuous_const.inner continuous_id
  simpa only [native_pairing_inner K mu j hj] using hh

/-- Genuine relative orthogonal projection after convolution, on its proved
compact-character ambient component. Source and dual labels are separated;
the actual theta-source coefficient is retained as a remainder. -/
theorem both_tests_component_projected_chain
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (sourceChi chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (hadm : |z.re-(a+(l+r)/2)| < (r-l)/2 ∨
      (|z.re-(a+(l+r)/2)| = (r-l)/2 ∧ (2 : ℝ)*m+1 < s))
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu)
    (hF : F ∈ compactCharacterSpace K mu ((r-l)/2) s (by linarith) hs sourceChi) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let P := (componentSpectralSpace K mu ((r-l)/2) s (by linarith) hs addHaar
      sourceChi (a+(l+r)/2)).starProjection
    let S := (thetaClosure K addHaar mu sourceChi (a+(l+r)/2) ((r-l)/2) s).starProjection
    let j := genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m
    (∫ x, j x * (P.comp A F) x ∂mu) =
      (∑ k ∈ Finset.range (m+1),
        (mellinCoefficient K mu chi z a (requiredTest K phi q) k * (m.choose k : ℂ)) *
          (∫ y, genuineNormalizedMellinJet K chi z (a+(l+r)/2)
            s ((r-l)/2) (m-k) y * F y ∂mu)) -
      (∫ x, j x * (S (A F)) x ∂mu) := by
  dsimp only
  rw [ContinuousLinearMap.comp_apply,
    interval_residual_is_component_projection K mu s hs addHaar sourceChi a
      l r hlr (requiredTest K phi q) (requiredTest_compact K phi hh hc q).1
      (requiredTest_compact K phi hh hc q).2 F hF]
  have hj := native_admitted_chain_memLp K chi mu c hc0 hct hmap z
    (a+(l+r)/2) s ((r-l)/2) m hs (by linarith) hadm m le_rfl
  rw [normalized_pairing_sub K mu _ hj,
    both_tests_interval_chain K mu l r s hlr hs c hc0 hct hmap chi z a m
      hadm phi hh hc q F]

/-- Application with the actual dual-character convention: source functions
have pointwise inverse-chi law and left-translation character chi. -/
theorem both_tests_dual_component_chain
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (addHaar : Measure (HeckeAdeles K))
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (hadm : (a+l < z.re ∧ z.re < a+r) ∨
      ((z.re = a+l ∨ z.re = a+r) ∧ (2 : ℝ)*m+1 < s))
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (F : Lp ℂ 2 mu)
    (hF : F ∈ compactCharacterSpace K mu ((r-l)/2) s (by linarith) hs
      (inverseCharacter K chi)) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let P := (componentSpectralSpace K mu ((r-l)/2) s (by linarith) hs addHaar
      (inverseCharacter K chi) (a+(l+r)/2)).starProjection
    let S := (thetaClosure K addHaar mu (inverseCharacter K chi)
      (a+(l+r)/2) ((r-l)/2) s).starProjection
    let j := genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m
    (∫ x, j x * (P.comp A F) x ∂mu) =
      (∑ k ∈ Finset.range (m+1),
        (mellinCoefficient K mu chi z a (requiredTest K phi q) k * (m.choose k : ℂ)) *
          (∫ y, genuineNormalizedMellinJet K chi z (a+(l+r)/2)
            s ((r-l)/2) (m-k) y * F y ∂mu)) -
      (∫ x, j x * (S (A F)) x ∂mu) :=
  both_tests_component_projected_chain K addHaar mu l r s hlr hs c hc0 hct hmap
    (inverseCharacter K chi) chi z a m
    ((interval_admission_iff z a l r s m hlr).mpr hadm) phi hh hc q F hF

end
end RIntegrated


-- Integrated supplier: inputs/exchange/L/LRemainderCutoff.fragment.lean
/-! Insert after DSourceKernel.residualKernel_cutoff_limit, LIntegrated.requiredTest,
and FIntervalPhysical.manuscript_mask_tendsto. This keeps the finite source
trace distinct from a trace of the infinite-rank source complement. -/
namespace LIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet PIntervalConvolution
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The explicit logarithmic cutoff term in 12.4.1.1 vanishes for each of
the required tests. This removes no unspecified asymptotic error. -/
theorem requiredTest_cutoff_log_term
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (Lambda Lambda' : ℝ) :
    requiredTest K phi q 1 * (Real.log (Lambda * Lambda') : ℂ) = 0 := by
  rw [requiredTest_at_one K phi hphi q, zero_mul]

/-- Adding the explicit identity term does not alter the actual remainder
sequence. In particular no zero-limit claim is made for an unproved error. -/
theorem requiredTest_cutoff_remainder
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (Lambda Lambda' : ℕ → ℝ) (remainder : ℕ → ℂ) :
    (fun n => requiredTest K phi q 1 *
      (Real.log (Lambda n * Lambda' n) : ℂ) + remainder n) = remainder := by
  funext n
  rw [requiredTest_cutoff_log_term K phi hphi q, zero_add]

/-- The manuscript physical masks preserve that sign for both tests on
every genuine finite source projection after the completed convolution. -/
theorem both_interval_source_residual_cutoff
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2)
    (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hbound : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    Tendsto (fun n => ∫ x, omega n x *
      DSourceKernel.residualKernel mu b E A (fun x y => requiredTest K phi q (x*y⁻¹)) x x ∂mu)
      atTop (𝓝 (-Masullo.TraceClass.trace (E.starProjection.comp A))) := by
  dsimp only
  let A := intervalConvolutionCLM K mu l r s hlr hs
    (requiredTest K phi q) (requiredTest_compact K phi hh hc q).1
      (requiredTest_compact K phi hh hc q).2
  let b := fun x => intervalHalfWeight l r s (classLog K x)
  apply DSourceKernel.residualKernel_cutoff_limit mu b
    (fun x => FIntervalPhysical.intervalHalfWeight_pos _ _ _ _) E A
    (fun x y => requiredTest K phi q (x*y⁻¹))
  · intro x
    rw [mul_inv_cancel, requiredTest_at_one K phi hphi q]
  · exact hm
  · exact fun n => Filter.Eventually.of_forall (hbound n)
  · exact Filter.Eventually.of_forall
      (FIntervalPhysical.manuscript_mask_tendsto K Lambda epsilon hLambda hprod omega hplateau)


end
end LIntegrated



-- Integrated supplier: inputs/exchange/L/LArithmeticResidual.fragment.lean
/-! Insert after LRemainderCutoff.fragment and OArithmeticClosure's arithmetic
source presentation. This supplies the concrete source-span application. -/
namespace LIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Both tests, the exact admitted arithmetic source span, the original
interval weight, and the manuscript physical cutoffs in one application.
The displayed trace is the finite SOURCE trace; the left side is the
diagonal of the specified convolution-minus-source kernel. -/
theorem both_tests_arithmetic_source_residual_cutoff
    (chi : UnitaryHeckeCharacter K) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2)
    (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hbound : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let V := JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
    let Theta := OArithmeticClosure.arithmeticSourceMap K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    ∀ T, Tendsto (fun n => ∫ x, omega n x *
      DSourceKernel.residualKernel mu b (E T) A
        (fun x y => requiredTest K phi q (x*y⁻¹)) x x ∂mu)
      atTop (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  let V := JThetaAttachment.sourceSpan K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s
  let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0
    (OArithmeticClosure.arithmeticSourceMap K addHaar mu chi
      (a+(l+r)/2) ((r-l)/2) s) T
  exact both_interval_source_residual_cutoff K mu l r s hlr hs E
    phi hh hc hphi q Lambda epsilon hLambda hprod omega hm hbound hplateau


end
end LIntegrated



-- Integrated supplier: inputs/exchange/L/LActualBoundary.fragment.lean
/-! Insert after RBoundaryFragment, RApplicationFragment,
and LBoundaryBalance.fragment. No replacement jet or coefficient definition. -/
namespace LIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.BoundaryJetOrders
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The retained/omitted balance on ACTUAL L2-admitted boundary jets, for
both original-Haar Mellin coefficients and the original nonsymmetric interval.
The Haar transport remains explicit; per-jet membership and the exact retained
count are proved by R's same-measure boundary theorem. N is a supplied finite
chain order, not an asserted identification with an L-function multiplicity. -/
theorem both_actual_boundary_retained_omitted
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s) (N : ℕ)
    (hb : z.re = a+l ∨ z.re = a+r)
    (phi : HeckeIdeleClasses K → ℂ) (q : Fin 2) :
    let orders := (Finset.range N).filter (fun m => MemLp
      (genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m) 2 mu)
    let coeff := RIntegrated.mellinCoefficient K mu chi z a (requiredTest K phi q) 0
    orders.card = min N (Nat.ceil ((s-1)/2)) ∧
      (orders.card : ℂ)*coeff + ((N-orders.card : ℕ) : ℂ)*coeff = (N : ℂ)*coeff := by
  classical
  dsimp only
  have habs : |z.re-(a+(l+r)/2)| = (r-l)/2 := by
    rcases hb with hb | hb
    · rw [hb, show a+l-(a+(l+r)/2) = -((r-l)/2) by ring, abs_neg,
        abs_of_nonneg (by linarith : 0 ≤ (r-l)/2)]
    · rw [hb, show a+r-(a+(l+r)/2) = (r-l)/2 by ring,
        abs_of_nonneg (by linarith : 0 ≤ (r-l)/2)]
  have ho := genuine_boundary_mellin_orders K chi mu c hc0 hct hmap z
    (a+(l+r)/2) s ((r-l)/2) N hs (by linarith) habs
  have he : (Finset.range N).filter (fun m => MemLp
      (genuineNormalizedMellinJet K chi z (a+(l+r)/2) s ((r-l)/2) m) 2 mu) =
      boundaryJetOrders N s := by
    rw [ho, boundaryJetOrders_all_real]
  rw [he]
  exact ⟨boundary_card N s,
    both_boundary_retained_omitted K mu chi z a s N phi q⟩

end
end LIntegrated


-- Integrated supplier: inputs/exchange/L/LOriginalOrder.fragment.lean
/-! Insert after OAllCharacterClosure and LIntegrated.requiredTest.
The source is the actual full admitted original theta closure. -/
namespace LIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution OAllCharacterClosure JThetaAttachment
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [SFinite mu] [IsLocallyFiniteMeasure mu]

/-- The actual arithmetic source action discharges the generic equivariance
premise. For BOTH tests and EVERY input, convolution-first compression keeps
its exact source-return remainder. No commutation or zero-remainder claim. -/
theorem both_tests_original_order_remainder
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (q : Fin 2) (x : Lp ℂ 2 mu) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S
    P (A x) = P (A (P x)) ∧ A (P x)-P (A x) = S (A (P x)) := by
  let A := intervalConvolutionCLM K mu l r s hlr hs
    (requiredTest K phi q) (requiredTest_compact K phi hh hc q).1
      (requiredTest_compact K phi hh hc q).2
  let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
  have hboth := OAllCharacterClosure.both_tests_full_PA_source_zero
    K addHaar mu a l r s hlr hs phi hh hc
  have hz : (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)-S).comp A).comp S = 0 := by
    fin_cases q
    · simpa only [A, S, requiredTest_zero] using hboth.1
    · simpa only [A, S, requiredTest_one] using hboth.2
  have he : A (S x)-S (A (S x)) = 0 := by
    exact DFunLike.congr_fun hz x
  have hfix : S (A (S x)) = A (S x) := (sub_eq_zero.mp he).symm
  change (A x-S (A x) = A (x-S x)-S (A (x-S x))) ∧
    (A (x-S x)-(A x-S (A x)) = S (A (x-S x)))
  simp only [map_sub, hfix]
  constructor <;> abel

end
end LIntegrated


-- Integrated supplier: inputs/exchange/L/LFullSourceCutoff.fragment.lean
/-! Insert after LRemainderCutoff.fragment and OAllCharacterClosure's full-source
source presentation. This supplies the concrete source-span application. -/
namespace LIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (addHaar : Measure (HeckeAdeles K))
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- Both tests, the exact admitted full arithmetic source span, the original
interval weight, and the manuscript physical cutoffs in one application.
The displayed trace is the finite SOURCE trace; the left side is the
diagonal of the specified convolution-minus-source kernel. -/
theorem both_tests_full_source_residual_cutoff
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2)
    (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) atTop (𝓝 0))
    (omega : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) mu)
    (hbound : ∀ n x, ‖omega n x‖ ≤ 1)
    (hplateau : ∀ n x,
      (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    let ht := requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs
      (requiredTest K phi q) ht.1 ht.2
    let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    ∀ T, Tendsto (fun n => ∫ x, omega n x *
      DSourceKernel.residualKernel mu b (E T) A
        (fun x y => requiredTest K phi q (x*y⁻¹)) x x ∂mu)
      atTop (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A))) := by
  dsimp only
  intro T
  let V := JThetaAttachment.fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0
    (OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s) T
  exact both_interval_source_residual_cutoff K mu l r s hlr hs E
    phi hh hc hphi q Lambda epsilon hLambda hprod omega hm hbound hplateau


end
end LIntegrated



-- Integrated supplier: inputs/exchange/L/LSupport.fragment.lean
/-! Insert after LIntegrated.requiredTest. Pointwise support transport for
the exact one-sided premise in manuscript Theorem 11.3.2.1. -/
namespace LIntegrated
open MasulloGRH Masullo.IdeleClassGeometry
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Both test values vanish whenever the original value at the inverse does. -/
theorem requiredTest_zero_of_inverse
    (phi : HeckeIdeleClasses K → ℂ) (q : Fin 2) (x : HeckeIdeleClasses K)
    (hx : phi x⁻¹ = 0) : requiredTest K phi q x = 0 := by
  fin_cases q
  · simp [requiredTest, DReview.sharp, hx]
  · simp [requiredTest, DReview.sharp, hx]

/-- Sharp reverses the one-sided support required by the orbital theorem;
the logged partner satisfies the same support implication. -/
theorem requiredTest_positive_support_reverses
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x ≤ 0 → phi x = 0)
    (q : Fin 2) (x : HeckeIdeleClasses K) (hx : 0 ≤ classLog K x) :
    requiredTest K phi q x = 0 := by
  apply requiredTest_zero_of_inverse K phi q x
  apply hphi
  rw [DReview.classLog_inv]
  exact neg_nonpos.mpr hx

/-- To put each sharp test on the positive norm side, its original test must
have the reflected negative-side support (or a separate extension argument). -/
theorem requiredTest_negative_support_reverses
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, 0 ≤ classLog K x → phi x = 0)
    (q : Fin 2) (x : HeckeIdeleClasses K) (hx : classLog K x ≤ 0) :
    requiredTest K phi q x = 0 := by
  apply requiredTest_zero_of_inverse K phi q x
  apply hphi
  rw [DReview.classLog_inv]
  exact neg_nonneg.mpr hx

/-- A physical mask does not change the logarithmic partner's minus sign. -/
theorem requiredTest_mask_log_sign
    (phi omega : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    omega x * requiredTest K phi 1 x =
      -(classLog K x : ℂ) * (omega x * requiredTest K phi 0 x) := by
  rw [requiredTest_log_sign]
  ring

end
end LIntegrated


-- Integrated supplier: inputs/exchange/I/ILocalFinitenessFragment.lean
/- Insert after DReview and LIntegrated.requiredTest. This is the compact
support step of 12.5.1.1 on the actual quotient, not an orbital trace premise. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Filter
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem classLog_one : classLog K (1 : HeckeIdeleClasses K) = 0 := by
  have h := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h
  linarith

theorem classLog_pow (g : HeckeIdeleClasses K) (n : ℕ) :
    classLog K (g^n) = (n : ℝ) * classLog K g := by
  induction n with
  | zero => simp [classLog_one]
  | succ n ih =>
    rw [pow_succ, classLog_mul, ih]
    push_cast
    ring

theorem classLog_zpow (g : HeckeIdeleClasses K) (n : ℤ) :
    classLog K (g^n) = (n : ℝ) * classLog K g := by
  cases n with
  | ofNat n => simpa using classLog_pow K g n
  | negSucc n =>
    simp only [zpow_negSucc, DReview.classLog_inv, classLog_pow, Int.cast_negSucc]
    push_cast
    ring

/-- Compact support supplies the actual logarithmic bound used outside S. -/
theorem compact_log_support_bound (h : HeckeIdeleClasses K → ℂ)
    (hc : HasCompactSupport h) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, h x ≠ 0 → |classLog K x| ≤ R := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport h) from hc).exists_bound_of_continuousOn
    (classLog_continuous K).continuousOn
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro x hx
  have hm : x ∈ tsupport h := subset_tsupport h hx
  have hb : |classLog K x| ≤ R := by
    simpa only [Real.norm_eq_abs] using hR x hm
  exact hb.trans (le_max_left _ _)

/-- Every nonzero integer power lies outside support when the logarithmic
step is larger than the support radius; the identity term uses h(1)=0. -/
theorem large_log_step_vanishes
    (h : HeckeIdeleClasses K → ℂ) (R : ℝ)
    (hR : ∀ x, h x ≠ 0 → |classLog K x| ≤ R) (h1 : h 1 = 0)
    (g : HeckeIdeleClasses K) (hg : R < |classLog K g|) (n : ℤ) :
    h (g^n) = 0 := by
  by_cases hn : n = 0
  · simp [hn, h1]
  · by_contra hne
    have hx := hR (g^n) hne
    rw [classLog_zpow, abs_mul] at hx
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · have hi : n ≤ -1 := by omega
        have hr : (n : ℝ) ≤ -1 := by exact_mod_cast hi
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hi : (1 : ℤ) ≤ n := by omega
        have hr : (1 : ℝ) ≤ n := by exact_mod_cast hi
        exact hr.trans (le_abs_self _)
    have hstep : |classLog K g| ≤ |(n : ℝ)| * |classLog K g| := by
      nlinarith [abs_nonneg (classLog K g)]
    linarith

/-- The proof of large-place vanishing applies to BOTH literal sharp tests
with one support radius. It allows the actual local character/norm factors
as arbitrary coefficients, since every lattice evaluation already vanishes. -/
theorem both_tests_large_log_step
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q : Fin 2, ∀ g : HeckeIdeleClasses K,
      R < |classLog K g| →
      (∀ n : ℤ, LIntegrated.requiredTest K phi q (g^n) = 0) ∧
      (∀ c : ℤ → ℂ, HasSum
        (fun n : ℤ => c n * LIntegrated.requiredTest K phi q (g^n)) 0) := by
  obtain ⟨R0, hR0, hb0⟩ := compact_log_support_bound K _
    (LIntegrated.requiredTest_compact K phi hh hc 0).2
  obtain ⟨R1, _, hb1⟩ := compact_log_support_bound K _
    (LIntegrated.requiredTest_compact K phi hh hc 1).2
  refine ⟨max R0 R1, hR0.trans (le_max_left _ _), ?_⟩
  intro q g hg
  have hzero : ∀ n : ℤ, LIntegrated.requiredTest K phi q (g^n) = 0 := by
    intro n
    fin_cases q
    · exact large_log_step_vanishes K _ R0 hb0
        (LIntegrated.requiredTest_at_one K phi hphi 0) g
        ((le_max_left R0 R1).trans_lt hg) n
    · exact large_log_step_vanishes K _ R1 hb1
        (LIntegrated.requiredTest_at_one K phi hphi 1) g
        ((le_max_right R0 R1).trans_lt hg) n
  refine ⟨hzero, ?_⟩
  intro c
  simpa only [hzero, mul_zero] using
    (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0)

/-- Sharp inverts the norm direction. Thus the one-sided orbital theorem
requires an actual inversion/splitting application, even for both valid tests. -/
theorem both_tests_support_direction
    (phi : HeckeIdeleClasses K → ℂ)
    (hpos : ∀ x, classLog K x ≤ 0 → phi x = 0)
    (q : Fin 2) (x : HeckeIdeleClasses K) (hx : 0 ≤ classLog K x) :
    LIntegrated.requiredTest K phi q x = 0 := by
  have hi : classLog K x⁻¹ ≤ 0 := by rw [DReview.classLog_inv]; linarith
  have h0 : LIntegrated.requiredTest K phi 0 x = 0 := by
    simp only [LIntegrated.requiredTest_zero, DReview.sharp, hpos x⁻¹ hi, star_zero]
  fin_cases q
  · exact h0
  · change LIntegrated.requiredTest K phi 1 x = 0
    rw [LIntegrated.requiredTest_log_sign, h0, mul_zero]

end
end ReviewI.LocalArithmetic


-- Integrated supplier: inputs/exchange/M/MSourceDiagonalFragment.lean
/- Insert after MNuclearDiagonalFragment. The final source-filter application
   additionally needs QSourceCutoffFragment and the canonical OSourceClosure. -/
namespace ReviewM
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Absolute integral control also constructs pointwise summability a.e. -/
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

namespace HNormalizedKernel
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Pointwise summability is proved for the same actual Haar rows. -/
theorem nuclear_diagonal_ae_summable (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    ∀ᵐ x ∂(ENNReal.ofReal V • nu),
      Summable (fun i => haarKernel b V (U i) (R i) x x) := by
  apply ReviewM.complex_series_ae_summable _ _
    (fun i => diagonal_integrable nu b hb V (U i) (R i))
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg fun x => norm_nonneg _) _ hc
  intro i
  simpa only [diagonalL2Cost_eq_norm_mul] using
    diagonal_integral_norm_le nu b hb V hV (U i) (R i)

/-- Subtraction of the L2 columns represents the difference of the full
original-Haar diagonals a.e.; no product-null-set restriction is used. -/
theorem nuclear_diagonal_sub_ae (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U W R : ι → Lp ℂ 2 nu)
    (hU : Summable (fun i => ‖U i‖ * ‖R i‖))
    (hW : Summable (fun i => ‖W i‖ * ‖R i‖)) :
    (fun x => (∑' i, haarKernel b V (U i) (R i) x x) -
      (∑' i, haarKernel b V (W i) (R i) x x)) =ᵐ[ENNReal.ofReal V • nu]
    (fun x => ∑' i, haarKernel b V (U i - W i : Lp ℂ 2 nu) (R i) x x) := by
  have hd (i : ι) : ∀ᵐ x ∂(ENNReal.ofReal V • nu),
      haarKernel b V (U i - W i : Lp ℂ 2 nu) (R i) x x =
        haarKernel b V (U i) (R i) x x - haarKernel b V (W i) (R i) x x := by
    filter_upwards [Measure.ae_smul_measure (Lp.coeFn_sub (U i) (W i))
      (ENNReal.ofReal V)] with x hx
    simp only [haarKernel, hx, Pi.sub_apply, sub_div, sub_mul]
  filter_upwards [nuclear_diagonal_ae_summable nu b hb V hV U R hU,
    nuclear_diagonal_ae_summable nu b hb V hV W R hW, ae_all_iff.mpr hd] with x hxU hxW hxd
  rw [← hxU.tsum_sub hxW]
  exact tsum_congr fun i => (hxd i).symm

/-- The full diagonal L1 error is controlled by the exact changing-column
nuclear cost. All series existence hypotheses are derived. -/
theorem nuclear_diagonal_difference_bound (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U W R : ι → Lp ℂ 2 nu)
    (hU : Summable (fun i => ‖U i‖ * ‖R i‖))
    (hW : Summable (fun i => ‖W i‖ * ‖R i‖)) :
    (∫ x, ‖(∑' i, haarKernel b V (U i) (R i) x x) -
      (∑' i, haarKernel b V (W i) (R i) x x)‖ ∂(ENNReal.ofReal V • nu)) ≤
    ∑' i, ‖U i-W i‖ * ‖R i‖ := by
  have hdiff : Summable (fun i => ‖U i-W i‖ * ‖R i‖) := by
    apply Summable.of_nonneg_of_le (fun i => by positivity) _ (hU.add hW)
    intro i
    exact (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)).trans_eq
      (add_mul _ _ _)
  have he := nuclear_diagonal_sub_ae nu b hb V hV U W R hU hW
  have hn := he.mono fun x hx => congrArg norm hx
  rw [integral_congr_ae hn]
  exact (nuclear_diagonal_integrable nu b hb V hV (fun i => U i-W i) R hdiff).2

/-- All shells of the actual row diagonal have the same nuclear error bound. -/
theorem nuclear_shell_difference_bound {E : Type*} (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U W R : ι → Lp ℂ 2 nu)
    (hU : Summable (fun i => ‖U i‖ * ‖R i‖))
    (hW : Summable (fun i => ‖W i‖ * ‖R i‖))
    (p : E → X → ℝ) (hp : ReviewM.PositivePartition p) :
    (∑' e, ‖(∫ x, (p e x : ℂ) * (∑' i, haarKernel b V (U i) (R i) x x)
      ∂(ENNReal.ofReal V • nu)) -
      (∫ x, (p e x : ℂ) * (∑' i, haarKernel b V (W i) (R i) x x)
      ∂(ENNReal.ofReal V • nu))‖) ≤ ∑' i, ‖U i-W i‖ * ‖R i‖ :=
  (ReviewM.shell_difference_bound (ENNReal.ofReal V • nu) p hp _ _
    (nuclear_diagonal_integrable nu b hb V hV U R hU).1
    (nuclear_diagonal_integrable nu b hb V hV W R hW).1).trans
      (nuclear_diagonal_difference_bound nu b hb V hV U W R hU hW)

/-- Orthogonal projection proves the summability required above; it is not
an additional premise on the finite source spans. -/
theorem projected_column_cost (nu : Measure X)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [E.HasOrthogonalProjection]
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun i => ‖E.starProjection (v i)‖ * ‖u i‖) := by
  apply Summable.of_nonneg_of_le (fun i => by positivity) _ hc
  intro i
  exact (mul_le_mul_of_nonneg_right (E.norm_starProjection_apply_le (v i))
    (norm_nonneg _)).trans_eq (mul_comm _ _)

end
end HNormalizedKernel

namespace ReviewM
open MeasureTheory Filter OSourceClosure Q.IntegratedSourceCutoff
open scoped Topology
noncomputable section
variable {X V E : Type*} [MeasurableSpace X] [AddCommGroup V] [Module ℂ V]

/-- Q's concrete finite theta spans now exhaust the actual row-diagonal
shell vector in l1. The original Haar and every shell are retained. -/
theorem actual_source_diagonal_shell_limit (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (vol : ℝ) (hvol : 0 < vol)
    (e0 eF : V →ₗ[ℂ] ℂ) (Theta : twoMomentSource e0 eF →ₗ[ℂ] Lp ℂ 2 nu)
    (u v : ℕ → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (p : E → X → ℝ) (hp : PositivePartition p) :
    Tendsto (fun T : Finset (Lp ℂ 2 nu) => ∑' e,
      ‖(∫ x, (p e x : ℂ) * (∑' i, HNormalizedKernel.haarKernel b vol
        ((finiteSourceSpan e0 eF Theta T).starProjection (v i)) (u i) x x)
        ∂(ENNReal.ofReal vol • nu)) -
        (∫ x, (p e x : ℂ) * (∑' i, HNormalizedKernel.haarKernel b vol
        ((sourceClosure e0 eF Theta).starProjection (v i)) (u i) x x)
        ∂(ENNReal.ofReal vol • nu))‖) atTop (𝓝 0) := by
  classical
  apply squeeze_zero (fun T => tsum_nonneg fun e => norm_nonneg _) _
    (actual_theta_nuclear_cost_limit e0 eF Theta u v hc)
  intro T
  simpa only [mul_comm] using HNormalizedKernel.nuclear_shell_difference_bound nu b hb vol hvol
    (fun i => (finiteSourceSpan e0 eF Theta T).starProjection (v i))
    (fun i => (sourceClosure e0 eF Theta).starProjection (v i)) u
    (HNormalizedKernel.projected_column_cost nu (finiteSourceSpan e0 eF Theta T) u v hc)
    (HNormalizedKernel.projected_column_cost nu (sourceClosure e0 eF Theta) u v hc) p hp

end
end ReviewM


-- Integrated supplier: inputs/exchange/M/MBoundaryIntegralFragment.lean
/- Insert after MPartitionFragment; the final arithmetic row application also
   needs NNormalizedDescentFragment and MNormCostFragment. -/
namespace ReviewM
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem partition_pullback (p : ι → X → ℝ) (hp : PositivePartition p)
    (f : Y → X) (hf : Measurable f) : PositivePartition (fun i y => p i (f y)) :=
  ⟨fun i => (hp.measurable i).comp hf, fun i y => hp.nonneg i (f y),
    fun y => hp.mass (f y)⟩

/-- The corrections between two full positive partitions cancel only after
summing all shells; each remains an integrable term with a paid L1 bound. -/
theorem partition_boundary_integrals [Countable ι] (mu : Measure X)
    (p q : ι → X → ℝ) (hp : PositivePartition p) (hq : PositivePartition q)
    (d : X → ℂ) (hd : Integrable d mu) :
    HasSum (fun i => ∫ x, ((p i x : ℂ) - (q i x : ℂ)) * d x ∂mu) 0 ∧
    Summable (fun i => ‖∫ x, ((p i x : ℂ) - (q i x : ℂ)) * d x ∂mu‖) ∧
    (∑' i, ‖∫ x, ((p i x : ℂ) - (q i x : ℂ)) * d x ∂mu‖) ≤
      2 * ∫ x, ‖d x‖ ∂mu := by
  have hcoef (i : ι) : (∫ x, ((p i x : ℂ) - (q i x : ℂ)) * d x ∂mu) =
      (∫ x, (p i x : ℂ) * d x ∂mu) - (∫ x, (q i x : ℂ) * d x ∂mu) := by
    simp only [sub_mul]
    exact integral_sub (shell_integrable mu p hp d hd i) (shell_integrable mu q hq d hd i)
  have hP := positive_shell_l1 mu p hp d hd
  have hQ := positive_shell_l1 mu q hq d hd
  have hbound (i : ι) : ‖∫ x, ((p i x : ℂ) - (q i x : ℂ)) * d x ∂mu‖ ≤
      ‖∫ x, (p i x : ℂ) * d x ∂mu‖ + ‖∫ x, (q i x : ℂ) * d x ∂mu‖ := by
    rw [hcoef]
    exact norm_sub_le _ _
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbound (hP.1.add hQ.1)
  refine ⟨?_, hs, ?_⟩
  · simpa only [hcoef, sub_self] using
      (shell_reconstruction mu p hp d hd).sub (shell_reconstruction mu q hq d hd)
  · calc
      _ ≤ ∑' i, (‖∫ x, (p i x : ℂ) * d x ∂mu‖ +
          ‖∫ x, (q i x : ℂ) * d x ∂mu‖) := hs.tsum_le_tsum hbound (hP.1.add hQ.1)
      _ = (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂mu‖) +
          (∑' i, ‖∫ x, (q i x : ℂ) * d x ∂mu‖) := hP.1.tsum_add hQ.1
      _ ≤ 2 * ∫ x, ‖d x‖ ∂mu := by linarith [hP.2, hQ.2]

end
end ReviewM

namespace NDivisorialShells
open MasulloGRH NumberField MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The actual incoming-point correction has absolutely summable original-Haar
integrals and total zero across shells. Individual corrections are retained.
The density is H's literal L2 kernel row, with integrability proved from U/R. -/
theorem actual_incoming_row_boundary (v : ℕ → FinitePlace K)
    (indent : HeckeIdeles K → ℝ) (hb : Continuous indent) (hb0 : ∀ x, 0 ≤ indent x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => indent (principalIdele K q * x)) 1)
    (nu : Measure (HeckeIdeleClasses K)) (w : HeckeIdeleClasses K → ℝ)
    (hw : ∀ x, 0 < w x) (vol : ℝ) (hvol : 0 < vol)
    (U R : Lp ℂ 2 nu) (t : HeckeIdeleClasses K) :
    HasSum (fun e => ∫ x,
      ((descendedMask K v indent e x : ℂ) - (descendedMask K v indent e (x*t⁻¹) : ℂ)) *
        HNormalizedKernel.haarKernel w vol U R x x ∂(ENNReal.ofReal vol • nu)) 0 ∧
    Summable (fun e => ‖∫ x,
      ((descendedMask K v indent e x : ℂ) - (descendedMask K v indent e (x*t⁻¹) : ℂ)) *
        HNormalizedKernel.haarKernel w vol U R x x ∂(ENNReal.ofReal vol • nu)‖) ∧
    (∑' e, ‖∫ x,
      ((descendedMask K v indent e x : ℂ) - (descendedMask K v indent e (x*t⁻¹) : ℂ)) *
        HNormalizedKernel.haarKernel w vol U R x x ∂(ENNReal.ofReal vol • nu)‖) ≤
      2 * (‖U‖ * ‖R‖) := by
  have hp := descended_positivePartition_of_indentation K v indent hb hb0 hbs
  have hq := ReviewM.partition_pullback (descendedMask K v indent) hp
    (fun x : HeckeIdeleClasses K => x*t⁻¹) (continuous_id.mul continuous_const).measurable
  have hi := HNormalizedKernel.diagonal_integrable nu w hw vol U R
  have h := ReviewM.partition_boundary_integrals (ENNReal.ofReal vol • nu)
    (descendedMask K v indent) (fun e x => descendedMask K v indent e (x*t⁻¹)) hp hq _ hi
  refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [HNormalizedKernel.diagonalL2Cost_eq_norm_mul] using
    HNormalizedKernel.diagonal_integral_norm_le nu w hw vol hvol U R

end
end NDivisorialShells


-- Integrated supplier: inputs/exchange/M/MArithmeticSourceShellFragment.lean
/- Insert after MSourceDiagonalFragment, OAllCharacterClosure, and
   NNormalizedDescentFragment. This is an application to the shared full source. -/
namespace ReviewM
open MeasureTheory Filter MasulloGRH JThetaAttachment OSourceClosure
open Masullo.IdeleClassGeometry PIntervalConvolution Q.IntegratedSourceCutoff
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]

/-- The common original theta source and the actual descended arithmetic masks
satisfy the directed all-shell diagonal limit. No fixed-character source is
substituted for the full source. The independent nuclear factor cost remains
explicit; all source-density, mask and projection applications are proved. -/
theorem full_source_arithmetic_shell_limit
    (addHaar : Measure (HeckeAdeles K)) (mu : Measure (HeckeIdeleClasses K))
    (a l r s : ℝ) (places : ℕ → NumberField.FinitePlace K)
    (indent : HeckeIdeles K → ℝ) (hb : Continuous indent) (hb0 : ∀ x, 0 ≤ indent x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => indent (principalIdele K q * x)) 1)
    (u v : ℕ → Lp ℂ 2 mu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    let W := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := finiteSourceSpan (0 : W →ₗ[ℂ] ℂ) 0 Theta
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let w := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K places indent
    Tendsto (fun T : Finset (Lp ℂ 2 mu) => ∑' e,
      ‖(∫ x, (p e x : ℂ) * (∑' i, HNormalizedKernel.haarKernel w 1
        ((E T).starProjection (v i)) (u i) x x) ∂mu) -
       (∫ x, (p e x : ℂ) * (∑' i, HNormalizedKernel.haarKernel w 1
        (S (v i)) (u i) x x) ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let W := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  have hw : ∀ x : HeckeIdeleClasses K, 0 < intervalHalfWeight l r s (classLog K x) := by
    intro x
    unfold intervalHalfWeight
    positivity
  have hp := NDivisorialShells.descended_positivePartition_of_indentation
    K places indent hb hb0 hbs
  have h := actual_source_diagonal_shell_limit mu
    (fun x => intervalHalfWeight l r s (classLog K x)) hw 1 (by norm_num)
    (0 : W →ₗ[ℂ] ℂ) 0
    (OAllCharacterClosure.fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
    u v hc (NDivisorialShells.descendedMask K places indent) hp
  rw [OAllCharacterClosure.full_sourceProjection_eq] at h
  simpa only [ENNReal.ofReal_one, one_smul] using h

end
end ReviewM


-- Integrated supplier: inputs/exchange/E/ArithmeticFourierBoundsFragment.lean
/- Insert after the canonical seed. The Masullo.Coefficient block is reused
from review_core/Geometry/CompactFourierDecay.lean without redefinition.
The new arithmetic adapter below discharges its integrability hypotheses. -/

namespace Masullo.Coefficient
open MeasureTheory
noncomputable section
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

def coefficient (mu : Measure G) (chi : G →* ℂ) (f : G → ℂ) : ℂ :=
  ∫ x, f x * star (chi x) ∂mu

def difference (u : G) (f : G → ℂ) (x : G) : ℂ := f (u*x)-f x

def differences (u : G) (f : G → ℂ) : ℕ → G → ℂ
  | 0 => f
  | n+1 => difference u (differences u f n)

/-- Translation of a coefficient with the original, unnormalized Haar. -/
theorem translated_coefficient (mu : Measure G) [mu.IsMulLeftInvariant]
    (chi : G →* ℂ) (f : G → ℂ) (u : G) :
    coefficient mu chi (fun x => f (u*x)) =
      star (chi (u⁻¹)) * coefficient mu chi f := by
  have h := integral_mul_left_eq_self (μ := mu)
    (fun x => f (u*x) * star (chi x)) (u⁻¹)
  simp only [mul_inv_cancel_left, map_mul, star_mul] at h
  unfold coefficient
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

/-- One difference is multiplication by the actual character eigenvalue. -/
theorem difference_coefficient (mu : Measure G) [mu.IsMulLeftInvariant]
    (chi : G →* ℂ) (f : G → ℂ) (u : G)
    (hi : Integrable (fun x => f x * star (chi x)) mu)
    (ht : Integrable (fun x => f (u*x) * star (chi x)) mu) :
    coefficient mu chi (difference u f) =
      (star (chi (u⁻¹))-1) * coefficient mu chi f := by
  unfold difference coefficient
  simp_rw [sub_mul]
  rw [integral_sub ht hi]
  have h := translated_coefficient mu chi f u
  unfold coefficient at h
  rw [h]
  ring

/-- Arbitrarily high cancellation, derived by induction rather than assumed. -/
theorem iterated_difference_coefficient (mu : Measure G) [mu.IsMulLeftInvariant]
    (chi : G →* ℂ) (f : G → ℂ) (u : G)
    (hi : ∀ n, Integrable (fun x => differences u f n x * star (chi x)) mu)
    (ht : ∀ n, Integrable (fun x => differences u f n (u*x) * star (chi x)) mu)
    (n : ℕ) :
    coefficient mu chi (differences u f n) =
      (star (chi (u⁻¹))-1)^n * coefficient mu chi f := by
  induction n with
  | zero => simp [differences]
  | succ n ih =>
    change coefficient mu chi (difference u (differences u f n)) = _
    rw [difference_coefficient mu chi _ u (hi n) (ht n), ih, pow_succ]
    ring

/-- The finite-difference L1 norm controls each original-Haar coefficient. -/
theorem character_difference_bound (mu : Measure G) [mu.IsMulLeftInvariant]
    (chi : G →* ℂ) (f : G → ℂ) (u : G)
    (hunit : ∀ x, ‖chi x‖ = 1)
    (hi : ∀ n, Integrable (fun x => differences u f n x * star (chi x)) mu)
    (ht : ∀ n, Integrable (fun x => differences u f n (u*x) * star (chi x)) mu)
    (n : ℕ) :
    ‖star (chi (u⁻¹))-1‖^n * ‖coefficient mu chi f‖ ≤
      ∫ x, ‖differences u f n x‖ ∂mu := by
  have h := norm_integral_le_integral_norm
    (fun x => differences u f n x * star (chi x)) (μ := mu)
  change ‖coefficient mu chi (differences u f n)‖ ≤ _ at h
  rw [iterated_difference_coefficient mu chi f u hi ht n, norm_mul, norm_pow] at h
  simpa only [norm_mul, norm_star, hunit, mul_one] using h

/-- At a character half-period the divisor is exactly 2^n. -/
theorem half_period_coefficient_bound (mu : Measure G) [mu.IsMulLeftInvariant]
    (chi : G →* ℂ) (f : G → ℂ) (u : G)
    (hunit : ∀ x, ‖chi x‖ = 1) (hhalf : chi (u⁻¹) = -1)
    (hi : ∀ n, Integrable (fun x => differences u f n x * star (chi x)) mu)
    (ht : ∀ n, Integrable (fun x => differences u f n (u*x) * star (chi x)) mu)
    (n : ℕ) :
    (2 : ℝ)^n * ‖coefficient mu chi f‖ ≤ ∫ x, ‖differences u f n x‖ ∂mu := by
  have h := character_difference_bound mu chi f u hunit hi ht n
  norm_num [hhalf] at h ⊢
  exact h

end
end Masullo.Coefficient

namespace EArithmeticFourier
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Masullo.Coefficient PIntervalConvolution
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Package the common descended arithmetic character, without changing it. -/
def classCharacterMonoidHom (chi : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K →* ℂ where
  toFun x := (classCharacter K chi x : ℂ)
  map_one' := by
    change ((chi.character 1 : Circle) : ℂ) = 1
    simp
  map_mul' x y := by
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change ((chi.character (a*b) : Circle) : ℂ) =
      ((chi.character a : Circle) : ℂ) * ((chi.character b : Circle) : ℂ)
    simp

theorem actual_character_norm (chi : UnitaryHeckeCharacter K)
    (x : HeckeIdeleClasses K) : ‖classCharacterMonoidHom K chi x‖ = 1 := by
  exact Circle.norm_coe _

theorem actual_character_continuous (chi : UnitaryHeckeCharacter K) :
    Continuous (classCharacterMonoidHom K chi) :=
  continuous_subtype_val.comp (classCharacter_continuous K chi)

/-- All finite differences of the actual compact test remain continuous and
compactly supported; the source estimate does not impose these as premises. -/
theorem actual_differences_compact (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : HasCompactSupport h) (u : HeckeIdeleClasses K)
    (n : ℕ) : Continuous (differences u h n) ∧ HasCompactSupport (differences u h n) := by
  induction n with
  | zero => exact ⟨hh, hc⟩
  | succ n ih =>
    refine ⟨(ih.1.comp (continuous_const.mul continuous_id)).sub ih.1, ?_⟩
    exact (ih.2.comp_homeomorph (Homeomorph.mulLeft u)).sub ih.2

variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable [IsLocallyFiniteMeasure mu]

/-- Original-Haar character bound, applied to the literal quotient test.
Every integrability premise of the reusable source estimate is proved here. -/
theorem actual_difference_coefficient_bound (chi : UnitaryHeckeCharacter K)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (u : HeckeIdeleClasses K) (n : ℕ) :
    ‖star (classCharacterMonoidHom K chi u⁻¹)-1‖^n *
      ‖coefficient mu (classCharacterMonoidHom K chi) h‖ ≤
      ∫ x, ‖differences u h n x‖ ∂mu := by
  apply character_difference_bound mu (classCharacterMonoidHom K chi) h u
    (actual_character_norm K chi)
  · intro m
    have hm := actual_differences_compact K h hh hc u m
    exact (hm.1.mul (actual_character_continuous K chi).star).integrable_of_hasCompactSupport
      hm.2.mul_right
  · intro m
    have hm := actual_differences_compact K h hh hc u m
    exact ((hm.1.comp (continuous_const.mul continuous_id)).mul
      (actual_character_continuous K chi).star).integrable_of_hasCompactSupport
      (hm.2.comp_homeomorph (Homeomorph.mulLeft u)).mul_right

/-- Both required sharp partners, after the exact interval midpoint twist.
The logged sharp remains the literal sharp(log*phi), with its existing minus
sign theorem, and each family retains its own finite-difference integral. -/
theorem both_tests_interval_difference_bound (chi : UnitaryHeckeCharacter K)
    (l r : ℝ) (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi)
    (u : HeckeIdeleClasses K) (n : ℕ) :
    ∀ h : HeckeIdeleClasses K → ℂ,
      (h = DReview.sharp K phi ∨
       h = DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) →
      ‖star (classCharacterMonoidHom K chi u⁻¹)-1‖^n *
        ‖coefficient mu (classCharacterMonoidHom K chi)
          (fun x => radialTwist K ((l+r)/2) x * h x)‖ ≤
        ∫ x, ‖differences u (fun y => radialTwist K ((l+r)/2) y * h y) n x‖ ∂mu := by
  intro h htest
  have ht : Continuous h ∧ HasCompactSupport h := by
    rcases htest with rfl | rfl
    · exact (DReview.both_sharp_tests_compact K phi hh hc).1
    · exact (DReview.both_sharp_tests_compact K phi hh hc).2
  have htw := twisted_test_compact K ((l+r)/2) h ht.1 ht.2
  exact actual_difference_coefficient_bound K mu chi _ htw.1 htw.2 u n

end
end EArithmeticFourier


-- Integrated supplier: inputs/exchange/E/FullSourceTailFragment.lean
/- Append after OAllCharacterClosure, E SourceTailFragment, E SourceResidual,
   QSourceCutoffFragment and E SourceOperatorTailFragment. No shared definitions
   are replaced. The unrestricted source is O's literal fullThetaClosure. -/
namespace EFullSourceTail
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment OSourceClosure OAllCharacterClosure
open Q.IntegratedSourceCutoff ESourceResidual EIntegratedTail
open Masullo.NativeTranslationBound
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]

/-- The constructed arithmetic convolution supplies its own weighted L1
envelope. This is the original Haar, not a probability renormalization. -/
theorem interval_convolution_norm_bound
    (l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F : Lp ℂ 2 mu) :
    ‖intervalConvolutionCLM K mu l r s hlr hs h hh hc F‖ ≤
      (∫ g, ‖radialTwist K ((l+r)/2) g * h g‖ *
        nativeTranslationBound K ((r-l)/2) s g ∂mu) * ‖F‖ := by
  exact Masullo.NativePettisVectorBound.nativePettisVector_bound K mu ((r-l)/2) s
    (by linarith) hs (fun g => radialTwist K ((l+r)/2) g * h g)
    (twisted_test_compact K _ h hh hc).1 (twisted_test_compact K _ h hh hc).2 F

/-- Every finite approximation uses Q's same source span. Its inclusion into
the full admitted original theta closure is proved from O's arithmetic map. -/
theorem original_finiteSourceSpan_le
    (addHaar : Measure (HeckeAdeles K)) (a alpha s : ℝ)
    (T : Finset (Lp ℂ 2 mu)) :
    finiteSourceSpan (0 : fullSourceSpan K addHaar mu a alpha s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu a alpha s) T ≤
      fullThetaClosure K addHaar mu a alpha s := by
  rw [← full_sourceClosure_eq K addHaar mu a alpha s]
  exact finiteSourceSpan_le _ _ _ T

/-- Quantitative source residual for the actual convolution-first operator.
No factorization, smoothness, nuclearity or source-invariance premise is used. -/
theorem original_PA_source_error_bound
    (addHaar : Measure (HeckeAdeles K)) (a l r s : ℝ)
    (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (T : Finset (Lp ℂ 2 mu)) (F : Lp ℂ 2 mu) :
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let E := (finiteSourceSpan
      (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) T).starProjection
    ‖((1-S).comp A) F - ((1-E).comp A) F‖ ≤
      (∫ g, ‖radialTwist K ((l+r)/2) g * h g‖ *
        nativeTranslationBound K ((r-l)/2) s g ∂mu) * ‖F‖ := by
  dsimp only
  let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
  let S := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
  let E := finiteSourceSpan
    (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
    (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) T
  have he : E ≤ S := original_finiteSourceSpan_le K mu addHaar _ _ _ T
  have hb := nested_source_residual_contraction S E he (A F)
  have halg : ((1-S.starProjection).comp A) F - ((1-E.starProjection).comp A) F =
      E.starProjection (A F)-S.starProjection (A F) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply]
    abel
  change ‖((1-S.starProjection).comp A) F - ((1-E.starProjection).comp A) F‖ ≤ _
  rw [halg]
  exact hb.trans (interval_convolution_norm_bound K mu l r s hlr hs h hh hc F)

/-- Both manuscript partners instantiate the previous estimate with their
compactness proved. The logged partner remains the literal sharp(log*phi). -/
theorem both_tests_original_source_error
    (addHaar : Measure (HeckeAdeles K)) (a l r s : ℝ)
    (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (h : HeckeIdeleClasses K → ℂ)
    (htest : h = DReview.sharp K phi ∨
      h = DReview.sharp K (fun x => (classLog K x : ℂ) * phi x))
    (T : Finset (Lp ℂ 2 mu)) (F : Lp ℂ 2 mu) :
    ∃ hh' : Continuous h, ∃ hc' : HasCompactSupport h,
      let A := intervalConvolutionCLM K mu l r s hlr hs h hh' hc'
      let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
      let E := (finiteSourceSpan
        (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
        (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) T).starProjection
      ‖((1-S).comp A) F - ((1-E).comp A) F‖ ≤
        (∫ g, ‖radialTwist K ((l+r)/2) g * h g‖ *
          nativeTranslationBound K ((r-l)/2) s g ∂mu) * ‖F‖ := by
  have ht : Continuous h ∧ HasCompactSupport h := by
    rcases htest with rfl | rfl
    · exact (DReview.both_sharp_tests_compact K phi hh hc).1
    · exact (DReview.both_sharp_tests_compact K phi hh hc).2
  exact ⟨ht.1, ht.2, original_PA_source_error_bound K mu addHaar a l r s hlr hs
    h ht.1 ht.2 T F⟩

/-- The full admitted source and the actual PA columns satisfy every finite
physical-tail hypothesis. There is no extra weight in the original-Haar Gram. -/
theorem both_tests_original_PA_physical_tail_gram {ι : Type*} [Fintype ι]
    (addHaar : Measure (HeckeAdeles K)) (a l r s : ℝ)
    (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (Ginv : Matrix ι ι ℂ) (kappa : ι → Lp ℂ 2 mu) :
    let tests := DReview.both_sharp_tests_compact K phi hh hc
    let A0 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K phi) tests.1.1 tests.1.2
    let A1 := intervalConvolutionCLM K mu l r s hlr hs
      (DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)) tests.2.1 tests.2.2
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A0) (kappa i))) atTop (𝓝 0) ∧
    Tendsto (physicalTailGram K mu Ginv (fun i => (P.comp A1) (kappa i))) atTop (𝓝 0) := by
  constructor <;> exact lp_physical_tail_gram K mu Ginv _

/-- Q's cost limit and E's operator bound on the literal unrestricted source.
The actual fixed-mask factor construction remains explicit, as required. -/
theorem original_source_operator_norm_tendsto
    (addHaar : Measure (HeckeAdeles K)) (a l r s : ℝ)
    (hlr : l ≤ r) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ℕ → Lp ℂ 2 mu)
    (hcost : Summable (fun j => ‖u j‖ * ‖v j‖))
    (hfactor : ∀ F, HasSum (fun j => inner ℂ (u j) F • v j)
      (intervalConvolutionCLM K mu l r s hlr hs h hh hc (M F))) :
    let A := intervalConvolutionCLM K mu l r s hlr hs h hh hc
    let S := (fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s).starProjection
    let E := fun T => (finiteSourceSpan
      (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s) T).starProjection
    Tendsto (fun T : Finset (Lp ℂ 2 mu) =>
      ‖((ContinuousLinearMap.id ℂ (Lp ℂ 2 mu)-S).comp A).comp M -
        ((ContinuousLinearMap.id ℂ (Lp ℂ 2 mu)-E T).comp A).comp M‖)
      atTop (𝓝 0) := by
  dsimp only
  simpa only [full_sourceProjection_eq K addHaar mu (a+(l+r)/2) ((r-l)/2) s] using
    common_source_operator_norm_tendsto
      (0 : fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s →ₗ[ℂ] ℂ) 0
      (fullSourceMap K addHaar mu (a+(l+r)/2) ((r-l)/2) s)
      (intervalConvolutionCLM K mu l r s hlr hs h hh hc) M u v hcost hfactor

end
end EFullSourceTail


-- Integrated supplier: inputs/exchange/Q/QRightTraceLimitFragment.lean
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


-- Integrated supplier: inputs/exchange/Q/QFullSourceTraceFragment.lean
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


-- Integrated supplier: inputs/exchange/K/KStrongPhysicalMask.lean
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


-- Integrated supplier: inputs/exchange/K/KManuscriptMask.lean
/-! Append after FIntervalPhysical and KPhysicalApplication. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- The manuscript plateau eventually covers each entire physical band.
This proves the plateau hypothesis of the quantitative mask estimate. -/
theorem manuscript_mask_band_eventually (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun k => epsilon k * Lambda k) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℝ)
    (hp : ∀ k x, (Lambda k)⁻¹ + epsilon k ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda k - epsilon k → rho k x = 1)
    (n : ℕ) :
    ∀ᶠ k in atTop, ∀ x ∈ DReview.physicalBand K n, rho k x = 1 := by
  filter_upwards [FIntervalPhysical.plateau_eventually Lambda epsilon hLambda hprod
      (Real.exp (-(n : ℝ))) (Real.exp_pos _),
    FIntervalPhysical.plateau_eventually Lambda epsilon hLambda hprod
      (Real.exp (n : ℝ)) (Real.exp_pos _)] with k hlo hhi
  intro x hx
  have hx' : -(n : ℝ) ≤ classLog K x ∧ classLog K x ≤ (n : ℝ) :=
    abs_le.mp hx
  exact hp k x (hlo.1.trans (Real.exp_le_exp.mpr hx'.1))
    ((Real.exp_le_exp.mpr hx'.2).trans hhi.2)

/-- Uniform-on-each-band error control on the canonical interval kernel.
All plateau and L1 hypotheses of the mask bound are discharged. -/
theorem manuscript_interval_kernel_error
    (nu : Measure (HeckeIdeleClasses K)) (l r s V : ℝ) (hV : 0 < V)
    (U R : Lp ℂ 2 nu) (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun k => epsilon k * Lambda k) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℝ)
    (hm : ∀ k, Measurable (rho k))
    (hb : ∀ k x, 0 ≤ rho k x ∧ rho k x ≤ 1)
    (hp : ∀ k x, (Lambda k)⁻¹ + epsilon k ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda k - epsilon k → rho k x = 1)
    (n : ℕ) :
    ∀ᶠ k in atTop,
      ‖(∫ x, (rho k x : ℂ) * HNormalizedKernel.haarKernel
        (fun y => PIntervalConvolution.intervalHalfWeight l r s (classLog K y)) V U R x x
          ∂(ENNReal.ofReal V • nu)) - inner ℂ R U‖ ≤
      ∫ x, (DReview.physicalBand K n)ᶜ.indicator
        (fun y => ‖HNormalizedKernel.haarKernel
          (fun z => PIntervalConvolution.intervalHalfWeight l r s (classLog K z))
            V U R y y‖) x ∂(ENNReal.ofReal V • nu) := by
  filter_upwards [manuscript_mask_band_eventually K Lambda epsilon hLambda hprod rho hp n]
    with k hk
  exact interval_kernel_mask_error K nu l r s V hV U R n (rho k) (hm k) (hb k) hk

end KPhysicalMask
end


-- Integrated supplier: inputs/exchange/K/KManuscriptSourceError.lean
/-! Insert after KFiniteSourceError, FIntervalPhysical, and the checked
KPhysicalMask.manuscript_mask_band_eventually declaration. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- The error majorant really vanishes, on the original Haar measure. -/
theorem originalHaar_diagonal_tail_tendsto
    (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n)ᶜ.indicator
      (fun y => ‖d y‖) x ∂mu) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => ∫ x, (DReview.physicalBand K n)ᶜ.indicator
      (fun y => ‖d y‖) x ∂mu) atTop (𝓝 (∫ _ : HeckeIdeleClasses K, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
    · intro n
      exact hd.norm.aestronglyMeasurable.indicator
        (DReview.physicalBand_measurable K n).compl
    · exact hd.norm
    · intro n
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ DReview.physicalBand K n <;> simp [hx])
    · apply Filter.Eventually.of_forall
      intro x
      obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ DReview.physicalBand K n := hN.trans (by exact_mod_cast hn)
      simp [hx]
  simpa using hlim

/-- A quantitative application to the actual finite source kernel. The
original interval weight, original measure, actual operator trace, and
manuscript plateau are all retained. The finite source stays fixed. -/
theorem manuscript_source_kernel_error
    (mu : Measure (HeckeIdeleClasses K)) (l r s : ℝ)
    (E : Submodule ℂ (Lp ℂ 2 mu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (Lambda epsilon : ℕ → ℝ)
    (hLambda : Tendsto Lambda atTop atTop)
    (hprod : Tendsto (fun k => epsilon k * Lambda k) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℝ)
    (hm : ∀ k, Measurable (rho k))
    (hb : ∀ k x, 0 ≤ rho k x ∧ rho k x ≤ 1)
    (hp : ∀ k x, (Lambda k)⁻¹ + epsilon k ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda k - epsilon k → rho k x = 1) :
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let d := fun x => DSourceKernel.finiteKernel mu b E A x x
    (∀ n, ∀ᶠ k in atTop,
      ‖(∫ x, (rho k x : ℂ) * d x ∂mu) -
        Masullo.TraceClass.trace (E.starProjection.comp A)‖ ≤
      ∫ x, (DReview.physicalBand K n)ᶜ.indicator (fun y => ‖d y‖) x ∂mu) ∧
    Tendsto (fun n => ∫ x, (DReview.physicalBand K n)ᶜ.indicator
      (fun y => ‖d y‖) x ∂mu) atTop (𝓝 0) := by
  dsimp only
  constructor
  · intro n
    filter_upwards [manuscript_mask_band_eventually K Lambda epsilon hLambda hprod rho hp n]
      with k hk
    exact source_kernel_mask_error mu
      (fun x => intervalHalfWeight l r s (classLog K x))
      (fun x => FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x))
      E A (DReview.physicalBand K n) (DReview.physicalBand_measurable K n)
      (rho k) (hm k) (hb k) hk
  · exact originalHaar_diagonal_tail_tendsto K mu _
      (DSourceKernel.finiteKernel_diagonal mu _
        (fun x => FIntervalPhysical.intervalHalfWeight_pos l r s (classLog K x)) E A).1

end KPhysicalMask
end


-- Integrated supplier: inputs/exchange/K/KResidualMaskError.lean
/-! Insert after KFiniteSourceError and DResidualKernelFragment. D owns
the residual kernel and diagonal sign; K applies the physical error bound. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory

/-- The same sharp mask bound for the actual residual kernel. The displayed
target is minus the finite source trace; it is not a trace-class assertion
about the residual operator. -/
theorem residual_kernel_mask_error {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (freeKernel : X → X → ℂ) (hdiag : ∀ x, freeKernel x x = 0)
    (band : Set X) (hband : MeasurableSet band)
    (rho : X → ℝ) (hm : Measurable rho)
    (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ band, rho x = 1) :
    ‖(∫ x, (rho x : ℂ) * DSourceKernel.residualKernel nu b E A freeKernel x x ∂nu) +
      Masullo.TraceClass.trace (E.starProjection.comp A)‖ ≤
      ∫ x, bandᶜ.indicator
        (fun y => ‖DSourceKernel.finiteKernel nu b E A y y‖) x ∂nu := by
  have hd := DSourceKernel.residualKernel_diagonal nu b hb E A freeKernel hdiag
  have h := real_mask_error_bound nu band hband _ hd.1 rho hm hbound hp
  rw [hd.2, sub_neg_eq_add] at h
  simpa only [DSourceKernel.residualKernel, hdiag, zero_sub, norm_neg] using h

end KPhysicalMask
end


-- Integrated supplier: inputs/exchange/F/FGlobalPhysical.lean
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


-- Integrated supplier: inputs/exchange/N/NIdelicTopologyFragment.lean
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


-- Integrated supplier: inputs/exchange/N/NBruhatExistenceFragment.lean
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


-- Integrated supplier: inputs/exchange/N/NIndentationApplicationFragment.lean
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


-- Integrated supplier: inputs/exchange/N/NCanonicalShellPartitionFragment.lean
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


/- P integration: the unrestricted admitted original source, both actual tests,
   the same finite kernels, arithmetic masks, and the actual global operator. -/
namespace PIntegrated
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open PIntervalConvolution JThetaAttachment
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
variable [LocallyCompactSpace (HeckeAdeles K)] [SecondCountableTopology (HeckeAdeles K)]
variable (addHaar : Measure (HeckeAdeles K)) [addHaar.IsAddHaarMeasure] [addHaar.Regular]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SigmaFinite mu]
variable [IsLocallyFiniteMeasure mu] [mu.IsInvInvariant]

/-- The actual kernel/operator, original-Haar diagonal, physical cutoff and
arithmetic-shell assembly with the indentation constructed on the actual ideles.
The remaining global trace/nuclear and local-orbital applications are not premises
or conclusions of this finite-diagonal/strong-operator theorem. -/
theorem geometric_trace_canonical_shell_assembly
    (a l r s : ℝ) (hlr : l ≤ r) (hs : 0 ≤ s)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K)
    (q : Fin 2) (F : Lp ℂ 2 mu) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let A := intervalConvolutionCLM K mu l r s hlr hs h ht.1 ht.2
    let V := fullSourceSpan K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let Theta := OAllCharacterClosure.fullSourceMap K addHaar mu
      (a+(l+r)/2) ((r-l)/2) s
    let E := DSourceKernel.sourceSpan mu (0 : V →ₗ[ℂ] ℂ) 0 Theta
    let W := fullThetaClosure K addHaar mu (a+(l+r)/2) ((r-l)/2) s
    let S := W.starProjection
    let P := (1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) - S
    let b := fun x => intervalHalfWeight l r s (classLog K x)
    let p := NDivisorialShells.descendedMask K v (NDivisorialShells.arithmeticIndentation K)
    let d := fun T x => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹)) x x
    let k := fun T => DSourceKernel.residualKernel mu b (E T) A
      (fun x y => h (x*y⁻¹))
    let kF := fun T x => (b x : ℂ) * ∫ y, k T x y * (F y / (b y : ℂ)) ∂mu
    (∀ T, (fun x => (A F - (E T).starProjection (A F)) x) =ᵐ[mu] kF T) ∧
    (∃ hm : ∀ T, MemLp (kF T) 2 mu,
      (∀ T, (hm T).toLp (kF T) = A F - (E T).starProjection (A F)) ∧
      Tendsto (fun T => (hm T).toLp (kF T)) atTop
        (𝓝 ((Wᗮ.starProjection.comp A) F))) ∧
    (∀ (omega : ℝ → ℝ → HeckeIdeleClasses K → ℂ),
      (∀ L e, FPhysicalFilter.ValidCutoff L e → AEStronglyMeasurable (omega L e) mu) →
      (∀ L e, FPhysicalFilter.ValidCutoff L e → ∀ x, ‖omega L e x‖ ≤ 1) →
      (∀ L e, FPhysicalFilter.ValidCutoff L e → ∀ x,
        L⁻¹ + e ≤ Real.exp (classLog K x) → Real.exp (classLog K x) ≤ L-e →
          omega L e x = 1) →
      ∀ T,
        Tendsto (fun z : ℝ × ℝ => ∫ x, omega z.1 (z.2/z.1) x *
          DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
          FPhysicalFilter.cutoffRegime
          (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
        Tendsto (fun z : ℝ × ℝ => ∫ x, omega z.1 (z.2/z.1) x * d T x ∂mu)
          FPhysicalFilter.cutoffRegime
          (𝓝 (-Masullo.TraceClass.trace ((E T).starProjection.comp A)))) ∧
    (∀ chi : UnitaryHeckeCharacter K,
      thetaClosure K addHaar mu chi (a+(l+r)/2) ((r-l)/2) s ≤ W) ∧
    (P.comp A).comp S = 0 ∧
    A.comp P - P.comp A = S.comp (A.comp P) ∧
    (∀ T,
      (fun x => ((E T).starProjection (A F)) x) =ᵐ[mu]
        (fun x => (b x : ℂ) * ∫ y, DSourceKernel.finiteKernel mu b (E T) A x y *
          (F y / (b y : ℂ)) ∂mu) ∧
      Integrable (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) mu ∧
      (∫ x, DSourceKernel.finiteKernel mu b (E T) A x x ∂mu) =
        Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      Tendsto (fun n => ∫ x, (DReview.physicalBand K n).indicator
        (fun x => DSourceKernel.finiteKernel mu b (E T) A x x) x ∂mu)
        atTop (𝓝 (Masullo.TraceClass.trace ((E T).starProjection.comp A))) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) *
        DSourceKernel.finiteKernel mu b (E T) A x x ∂mu)
        (Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Integrable (d T) mu ∧
      (∫ x, d T x ∂mu) = -Masullo.TraceClass.trace ((E T).starProjection.comp A) ∧
      HasSum (fun e => ∫ x, (p e x : ℂ) * d T x ∂mu)
        (-Masullo.TraceClass.trace ((E T).starProjection.comp A)) ∧
      Summable (fun e => ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ∧
      (∑' e, ‖∫ x, (p e x : ℂ) * d T x ∂mu‖) ≤ ∫ x, ‖d T x‖ ∂mu ∧
      Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
        (DReview.physicalBand K n).indicator (d T) x ∂mu) -
        (∫ x, (p e x : ℂ) * d T x ∂mu)‖) atTop (𝓝 0)) ∧
    Tendsto (fun T => (((1 : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) -
      (E T).starProjection).comp A) F) atTop (𝓝 ((P.comp A) F)) := by
  exact geometric_trace_operator_assembly K addHaar mu a l r s hlr hs
    phi hh hc hphi v (NDivisorialShells.arithmeticIndentation K)
    (NDivisorialShells.arithmeticIndentation_continuous K)
    (NDivisorialShells.arithmeticIndentation_nonneg K)
    (NDivisorialShells.arithmeticIndentation_hasSum K) q F

end
end PIntegrated
#check PIntegrated.geometric_trace_canonical_shell_assembly
#print axioms PIntegrated.geometric_trace_canonical_shell_assembly
#print axioms JThetaAttachment.originalBruhat_theta_summable
#print axioms JThetaAttachment.full_source_admission_iff
#print axioms HArithmeticTrace.full_arithmetic_basis_factor
#print axioms NDivisorialShells.arithmetic_positivePartition
