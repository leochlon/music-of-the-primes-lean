import Mathlib
attribute [local instance] Classical.propDecidable

/- Exact reused arithmetic quotient/log definitions and continuity from nuclear B177.
No new credit is claimed for this retained component. -/
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

namespace Round166F
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

end Round166F
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

namespace Round175B
open MasulloGRH Round166F MeasureTheory
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


end Round175B
end

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- Exact character structure from the checked finite-idelic foundation. -/
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


namespace SpectralRound11B
open MasulloGRH Round166F
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

end SpectralRound11B



namespace SpectralRound11B
noncomputable def nativeHalfWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (alpha * |t|) * (1 + t^2) ^ (s/4)

theorem nativeHalfWeight_pos (alpha s t : ℝ) :
    0 < nativeHalfWeight alpha s t := by
  unfold nativeHalfWeight
  positivity


end SpectralRound11B

namespace SpectralCycle7G
open MeasureTheory MasulloGRH Round166F Round175B SpectralRound11B

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
end SpectralCycle7G


noncomputable section
namespace SpectralA904
open MeasureTheory MasulloGRH Round166F Round175B SpectralRound11B SpectralCycle7G
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
end SpectralA904
end
