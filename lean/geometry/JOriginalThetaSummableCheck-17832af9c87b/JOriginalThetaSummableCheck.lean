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

#check JThetaAttachment.translatedSource_equivariance
#print axioms JThetaAttachment.translatedSource_equivariance

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
#check JThetaAttachment.translateOriginalSource_equivariance
#print axioms JThetaAttachment.translateOriginalSource_equivariance

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
#check JThetaAttachment.originalBruhat_theta_summable
#print axioms JThetaAttachment.originalBruhat_theta_summable
