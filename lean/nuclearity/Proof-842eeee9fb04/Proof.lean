import Mathlib

/-!
Round 66 B, reusing rounds 54–65 B: a necessary character-action calculation for the actual convolution
operator in the spectral trace calculation, Theorem 10.4.2.8 / 12.5.1.1.
The quotient below is the genuine idele-class group, copied at definition level
from the compatible round-53 F checked source. No zero set or trace is defined.
-/
open scoped NumberField
open MeasureTheory

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

structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K →* Circle :=
  QuotientGroup.lift (principalIdeles K) χ.character.toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact χ.trivial_on_principal a)

/-- The descended character is the original genuine idelic character. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (a : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk a) = χ.character a := rfl

noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)

instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

instance classMeasurableInv : MeasurableInv (HeckeIdeleClasses K) := by
  infer_instance
instance classMeasurableMul : MeasurableMul (HeckeIdeleClasses K) := by
  infer_instance

/-- Actual left convolution on functions on the genuine idele-class group.
The measure is explicit; its normalized Haar construction is not asserted here. -/
noncomputable def ideleClassConvolution (μ : Measure (HeckeIdeleClasses K))
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ


/-- Nonunitary idelic characters are needed for the spectral strip.
No membership in any Hecke zero set is postulated by this definition. -/
structure HeckeQuasicharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) ℂˣ
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

noncomputable def quasiClassCharacter (χ : HeckeQuasicharacter K) :
    HeckeIdeleClasses K →* ℂˣ :=
  QuotientGroup.lift (principalIdeles K) χ.character.toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact χ.trivial_on_principal a)

/-- The descended character is the original genuine idelic character. -/
theorem quasiClassCharacter_mk (χ : HeckeQuasicharacter K) (a : HeckeIdeles K) :
    quasiClassCharacter K χ (QuotientGroup.mk a) = χ.character a := rfl


theorem quasiClassCharacter_continuous (χ : HeckeQuasicharacter K) :
    Continuous (quasiClassCharacter K χ) := by
  exact (map_continuous χ.character).quotient_lift _


noncomputable def ideleClassKernelConvolution (μ : Measure (HeckeIdeleClasses K))
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ y, φ (x * y⁻¹) * f y ∂μ

/-- Haar substitution on genuine idele classes, used by the spectral/geometric
kernel comparison. No spectral projector or trace equality is assumed. -/
theorem genuine_kernel_eq_convolution
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    ideleClassKernelConvolution K μ φ f x = ideleClassConvolution K μ φ f x := by
  have h := integral_div_left_eq_self (fun g => φ g * f (g⁻¹ * x)) μ x
  have hc (y : HeckeIdeleClasses K) : (x / y)⁻¹ * x = y := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  simp_rw [hc] at h
  simpa only [ideleClassKernelConvolution, ideleClassConvolution, div_eq_mul_inv] using h

#check genuine_kernel_eq_convolution
#print axioms genuine_kernel_eq_convolution

noncomputable def jetMoment (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ) (χ : HeckeQuasicharacter K)
    (ℓ : HeckeIdeleClasses K → ℂ) (j : ℕ) : ℂ :=
  ∫ g, (φ g * (quasiClassCharacter K χ g : ℂ)) * ℓ g ^ j ∂μ

/-- Every jet moment is absolutely integrable for compact tests. -/
theorem genuine_jetMoment_integrable
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (ℓ : HeckeIdeleClasses K → ℂ) (hℓ : Continuous ℓ) (j : ℕ) :
    Integrable (fun g => (φ g * (quasiClassCharacter K χ g : ℂ)) * ℓ g ^ j) μ := by
  apply ((hφ.mul (Units.continuous_val.comp
    (quasiClassCharacter_continuous K χ))).mul (hℓ.pow j)).integrable_of_hasCompactSupport
  exact hcφ.mul_right.mul_right


noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : NumberField.InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : NumberField.FinitePlace K, ‖a.val.2 v.maximalIdeal‖
noncomputable def genuineIdeleLog (a : HeckeIdeles K) : ℂ :=
  (Real.log (genuineIdeleModulus K a) : ℂ)
/-- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
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
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
#check genuineIdeleModulus_principal
#print axioms genuineIdeleModulus_principal
#check genuineIdeleLog_principal
#print axioms genuineIdeleLog_principal
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
#check genuineIdele_finite_norm_support
#print axioms genuineIdele_finite_norm_support
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

theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]
#check genuineIdeleModulus_mul
#print axioms genuineIdeleModulus_mul
#check genuineIdeleModulus_ne_zero
#print axioms genuineIdeleModulus_ne_zero
#check genuineIdeleLog_add
#print axioms genuineIdeleLog_add

/-- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
local-norm logarithm. This is not supplied by an abstract replacement norm. -/
noncomputable def genuineLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeles K →* Multiplicative ℂ where
  toFun a := Multiplicative.ofAdd (genuineIdeleLog K a)
  map_one' := by
    change genuineIdeleLog K 1 = 0
    simpa only [map_one] using genuineIdeleLog_principal K 1
  map_mul' a b := hadd a b

noncomputable def genuineClassLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeleClasses K →* Multiplicative ℂ :=
  QuotientGroup.lift (principalIdeles K) (genuineLogHom K hadd) (by
    rintro x ⟨a, rfl⟩
    exact genuineIdeleLog_principal K a)

noncomputable def genuineClassLog
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (x : HeckeIdeleClasses K) : ℂ :=
  Multiplicative.toAdd (genuineClassLogHom K hadd x)

theorem genuineClassLog_mk
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (a : HeckeIdeles K) :
    genuineClassLog K hadd (QuotientGroup.mk a) = genuineIdeleLog K a := rfl

theorem genuineClassLog_translate
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (g x : HeckeIdeleClasses K) :
    genuineClassLog K hadd (g⁻¹ * x) =
      genuineClassLog K hadd x - genuineClassLog K hadd g := by
  unfold genuineClassLog
  rw [map_mul, map_inv]
  change -Multiplicative.toAdd (genuineClassLogHom K hadd g) +
    Multiplicative.toAdd (genuineClassLogHom K hadd x) = _
  abel


theorem genuineArithmeticClassLog_continuous
    (hcont : Continuous (genuineIdeleLog K)) :
    Continuous (genuineClassLog K (genuineIdeleLog_add K)) := by
  exact hcont.quotient_lift _


open Topology Filter
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

theorem genuineIdeleLog_continuous : Continuous (genuineIdeleLog K) := by
  exact Complex.continuous_ofReal.comp ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K))
#check integralFiniteSet_open
#print axioms integralFiniteSet_open
#check finiteNorm_mul
#print axioms finiteNorm_mul
#check finiteNorm_one_of_integral
#print axioms finiteNorm_one_of_integral
#check finiteNorm_continuous
#print axioms finiteNorm_continuous
#check genuineIdeleModulus_continuous
#print axioms genuineIdeleModulus_continuous
#check genuineIdeleLog_continuous
#print axioms genuineIdeleLog_continuous


noncomputable def genuineNormTwist (χ : UnitaryHeckeCharacter K) (s : ℂ) :
    HeckeQuasicharacter K where
  character := {
    toFun := fun a => Units.mk0
      ((χ.character a : ℂ) * Complex.exp (s * genuineIdeleLog K a))
      (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
    map_one' := by
      apply Units.ext
      have h : genuineIdeleLog K 1 = 0 := by
        simpa only [map_one] using genuineIdeleLog_principal K 1
      simp [h]
    map_mul' := by
      intro a b
      apply Units.ext
      change (χ.character (a*b) : ℂ) * Complex.exp (s * genuineIdeleLog K (a*b)) =
        ((χ.character a : ℂ) * Complex.exp (s * genuineIdeleLog K a)) *
        ((χ.character b : ℂ) * Complex.exp (s * genuineIdeleLog K b))
      rw [map_mul, Circle.coe_mul, genuineIdeleLog_add, mul_add, Complex.exp_add]
      ring
    continuous_toFun := by
      have hv : Continuous (fun a : HeckeIdeles K =>
          (χ.character a : ℂ) * Complex.exp (s * genuineIdeleLog K a)) :=
        (continuous_subtype_val.comp χ.character.continuous).mul
          (Complex.continuous_exp.comp (continuous_const.mul (genuineIdeleLog_continuous K)))
      apply Units.continuous_iff.mpr
      constructor
      · exact hv
      · change Continuous (fun a : HeckeIdeles K =>
          ((χ.character a : ℂ) * Complex.exp (s * genuineIdeleLog K a))⁻¹)
        exact hv.inv₀ (fun a => mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _)) }
  trivial_on_principal := by
    intro a
    apply Units.ext
    change (χ.character (principalIdele K a) : ℂ) *
      Complex.exp (s * genuineIdeleLog K (principalIdele K a)) = 1
    rw [χ.trivial_on_principal, genuineIdeleLog_principal]
    simp

theorem genuineNormTwist_class_value (χ : UnitaryHeckeCharacter K) (s : ℂ)
    (x : HeckeIdeleClasses K) :
    (quasiClassCharacter K (genuineNormTwist K χ s) x : ℂ) =
      (classCharacter K χ x : ℂ) *
        Complex.exp (s * genuineClassLog K (genuineIdeleLog_add K) x) := by
  refine Quotient.inductionOn' x ?_
  intro a
  rfl


noncomputable def genuineSpectralJet (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  ((classCharacter K χ x : ℂ) *
    Complex.exp (z * genuineClassLog K (genuineIdeleLog_add K) x)) *
      genuineClassLog K (genuineIdeleLog_add K) x ^ m


theorem genuineSpectralJet_coefficient_action
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (m : ℕ) (x : HeckeIdeleClasses K) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun g => φ g * genuineSpectralJet K χ z m (g*x)) μ ∧
    (∫ g, φ g * genuineSpectralJet K χ z m (g*x) ∂μ) =
      ∑ j ∈ Finset.range (m+1), jetMoment K μ φ ψ ℓ j *
        (genuineSpectralJet K χ z (m-j) x * (m.choose j : ℂ)) := by
  let ℓ := genuineClassLog K (genuineIdeleLog_add K)
  let ψ := genuineNormTwist K χ z
  let b := fun j : ℕ => (quasiClassCharacter K ψ x : ℂ) *
    ℓ x ^ (m-j) * (m.choose j : ℂ)
  have hadd (g : HeckeIdeleClasses K) : ℓ (g*x) = ℓ g + ℓ x := by
    change Multiplicative.toAdd (genuineClassLogHom K (genuineIdeleLog_add K) (g*x)) = _
    rw [map_mul]
    rfl
  have factor (g : HeckeIdeleClasses K) :
      φ g * ((quasiClassCharacter K ψ (g*x) : ℂ) * ℓ (g*x)^m) =
      ∑ j ∈ Finset.range (m+1),
        ((φ g * (quasiClassCharacter K ψ g : ℂ)) * ℓ g ^ j) * b j := by
    rw [map_mul, Units.val_mul, hadd, add_pow]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [b]
    ring
  have hi (j : ℕ) := (genuine_jetMoment_integrable K μ φ hφ hcφ ψ ℓ
    (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K)) j).mul_const (b j)
  have hint : Integrable (fun g => φ g *
      ((quasiClassCharacter K ψ (g*x) : ℂ) * ℓ (g*x)^m)) μ := by
    simp_rw [factor]
    exact integrable_finset_sum _ (fun j _ => hi j)
  have heq : (∫ g, φ g * ((quasiClassCharacter K ψ (g*x) : ℂ) * ℓ (g*x)^m) ∂μ) =
      ∑ j ∈ Finset.range (m+1), jetMoment K μ φ ψ ℓ j * b j := by
    simp_rw [factor]
    rw [integral_finset_sum _ (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_mul_const _ _
  simpa only [ψ, b, ℓ, genuineNormTwist_class_value, genuineSpectralJet] using And.intro hint heq
#check genuineSpectralJet_coefficient_action
#print axioms genuineSpectralJet_coefficient_action
/-- The actual convolution pairing with the manuscript's coefficient functions.
The displayed joint-integrability hypothesis is the remaining Fubini obligation
on the intended Hardy-Sobolev domain; it is not a spectral-completeness premise.
This theorem uses the checked positive coefficient action inside the pairing.
-/
theorem genuineSpectralJet_transpose_pairing
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (m : ℕ)
    (hjoint : Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      (φ (p.1 * p.2⁻¹) * f p.2) * genuineSpectralJet K χ z m p.1) (μ.prod μ)) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∫ y, f y * (∑ j ∈ Finset.range (m+1), jetMoment K μ φ ψ ℓ j *
        (genuineSpectralJet K χ z (m-j) y * (m.choose j : ℂ))) ∂μ := by
  let η := genuineSpectralJet K χ z m
  have hrow (x : HeckeIdeleClasses K) :
      ideleClassConvolution K μ φ f x * η x =
        ∫ y, (φ (x * y⁻¹) * f y) * η x ∂μ := by
    rw [← genuine_kernel_eq_convolution K μ φ f x]
    exact (integral_mul_const _ _).symm
  have hcol (y : HeckeIdeleClasses K) :
      (∫ x, (φ (x * y⁻¹) * f y) * η x ∂μ) =
        f y * (∫ g, φ g * η (g*y) ∂μ) := by
    calc
      _ = ∫ g, (φ ((g*y) * y⁻¹) * f y) * η (g*y) ∂μ :=
        (integral_mul_right_eq_self (μ := μ)
          (fun x => (φ (x * y⁻¹) * f y) * η x) y).symm
      _ = ∫ g, f y * (φ g * η (g*y)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        simp only [mul_assoc, mul_inv_cancel, mul_one]
        ring
      _ = _ := integral_const_mul _ _
  constructor
  · apply hjoint.integral_prod_left.congr
    filter_upwards [] with x
    exact (hrow x).symm
  · calc
      _ = ∫ x, ∫ y, (φ (x * y⁻¹) * f y) * η x ∂μ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hrow x
      _ = ∫ y, ∫ x, (φ (x * y⁻¹) * f y) * η x ∂μ ∂μ :=
        integral_integral_swap hjoint
      _ = ∫ y, f y * (∫ g, φ g * η (g*y) ∂μ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact hcol y
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact congrArg (fun a : ℂ => f y * a)
          (genuineSpectralJet_coefficient_action K μ φ hφ hcφ χ z m y).2
#check genuineSpectralJet_transpose_pairing
#print axioms genuineSpectralJet_transpose_pairing

/-- The Fubini premise for actual idelic coefficients, with finite weighted
moments instead of compact support of the input. This remains conditional on
those moments, which must be proved for the intended Hardy-Sobolev domain. -/
theorem genuineSpectralJet_weighted_joint_integrable
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (hm : ∀ j ≤ m, Integrable (fun y => f y * genuineSpectralJet K χ z j y) μ) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      (φ (p.1 * p.2⁻¹) * f p.2) * genuineSpectralJet K χ z m p.1) (μ.prod μ) := by
  let ℓ := genuineClassLog K (genuineIdeleLog_add K)
  let ψ := genuineNormTwist K χ z
  have hη (n : ℕ) : Continuous (genuineSpectralJet K χ z n) := by
    have hψ := Units.continuous_val.comp (quasiClassCharacter_continuous K ψ)
    have hℓ := genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K)
    simpa only [ψ, Function.comp_def, genuineNormTwist_class_value, genuineSpectralJet]
      using hψ.mul (hℓ.pow n)
  have hηval (n : ℕ) (x : HeckeIdeleClasses K) :
      genuineSpectralJet K χ z n x = (quasiClassCharacter K ψ x : ℂ) * ℓ x ^ n := by
    simp only [ψ, genuineNormTwist_class_value, ℓ, genuineSpectralJet]
  have hadd (g y : HeckeIdeleClasses K) : ℓ (g*y) = ℓ g + ℓ y := by
    change Multiplicative.toAdd (genuineClassLogHom K (genuineIdeleLog_add K) (g*y)) = _
    rw [map_mul]
    rfl
  have factor (g y : HeckeIdeleClasses K) :
      (φ g * f y) * genuineSpectralJet K χ z m (g*y) =
        ∑ j ∈ Finset.range (m+1),
          ((φ g * genuineSpectralJet K χ z j g) *
            (f y * genuineSpectralJet K χ z (m-j) y)) * (m.choose j : ℂ) := by
    simp_rw [hηval]
    rw [map_mul, Units.val_mul, hadd, add_pow]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi (j : ℕ) : Integrable (fun g => φ g * genuineSpectralJet K χ z j g) μ :=
    (hφ.mul (hη j)).integrable_of_hasCompactSupport hcφ.mul_right
  have hs : Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      (φ p.1 * f p.2) * genuineSpectralJet K χ z m (p.1*p.2)) (μ.prod μ) := by
    simp_rw [factor]
    apply integrable_finset_sum
    intro j hj
    exact ((hi j).mul_prod (hm (m-j) (Nat.sub_le m j))).mul_const (m.choose j : ℂ)
  have hmeas : AEStronglyMeasurable
      (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
        (φ (p.1 * p.2⁻¹) * f p.2) * genuineSpectralJet K χ z m p.1) (μ.prod μ) :=
    (((hφ.comp (continuous_fst.mul continuous_snd.inv)).measurable.mul
      (hf.comp measurable_snd)).mul
        ((hη m).comp continuous_fst).measurable).aestronglyMeasurable
  apply ((measurePreserving_mul_prod μ μ).integrable_comp hmeas).mp
  simpa only [Function.comp_def, mul_assoc, mul_inv_cancel, mul_one] using hs
#check genuineSpectralJet_weighted_joint_integrable
#print axioms genuineSpectralJet_weighted_joint_integrable

/-- Immediate use of the weighted Fubini result in the actual pairing.
No global quotient, Hecke divisor, pole correction or nuclear trace is asserted. -/
theorem genuineSpectralJet_weighted_transpose_pairing
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (hm : ∀ j ≤ m, Integrable (fun y => f y * genuineSpectralJet K χ z j y) μ) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∫ y, f y * (∑ j ∈ Finset.range (m+1), jetMoment K μ φ ψ ℓ j *
        (genuineSpectralJet K χ z (m-j) y * (m.choose j : ℂ))) ∂μ := by
  exact genuineSpectralJet_transpose_pairing K μ φ f hφ hcφ χ z m
    (genuineSpectralJet_weighted_joint_integrable K μ φ f hφ hcφ hf χ z m hm)
#check genuineSpectralJet_weighted_transpose_pairing
#print axioms genuineSpectralJet_weighted_transpose_pairing

/-- The scalar coefficient identity used for the transpose's Mellin diagonal
entries in (10.3.1.12). Both Fubini and the finite sum/integral exchange are
justified by the stated weighted moments on the genuine idele-class group.
The Hecke spectral identification and global nuclear trace remain open. -/
theorem genuineSpectralJet_weighted_moment_action
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (hm : ∀ j ≤ m, Integrable (fun y => f y * genuineSpectralJet K χ z j y) μ) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  let ℓ := genuineClassLog K (genuineIdeleLog_add K)
  let ψ := genuineNormTwist K χ z
  have h := genuineSpectralJet_weighted_transpose_pairing K μ φ f hφ hcφ hf χ z m hm
  refine ⟨h.1, h.2.trans ?_⟩
  have hi (j : ℕ) : Integrable (fun y =>
      (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
        (f y * genuineSpectralJet K χ z (m-j) y)) μ :=
    (hm (m-j) (Nat.sub_le m j)).const_mul _
  calc
    _ = ∫ y, ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (f y * genuineSpectralJet K χ z (m-j) y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ j ∈ Finset.range (m+1), ∫ y,
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (f y * genuineSpectralJet K χ z (m-j) y) ∂μ :=
      integral_finset_sum _ (fun j _ => hi j)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_const_mul _ _
#check genuineSpectralJet_weighted_moment_action
#print axioms genuineSpectralJet_weighted_moment_action

end MasulloGRH

/-! Round 67 C: concrete B/G compatibility check for the authorized review.
The complete B/r66 measurable source is retained below this insertion.
The compatibility theorem is appended at the end, after the actual norm is defined.
-/


/-! Round 67 C. Reuse B/r66 receipt 926cb591c7e441b1889bf726ad58b711
 and adapt G/r66 receipt f70f30aad205425885467fd4991b0b70.
 This resolves G's free logarithm/character hypotheses using B's actual idelic
 norm and norm twist, with explicit coercion from complex units to scalars.
 It does not identify any mode with a Hecke zero or construct a trace.
-/
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine norm twist and genuine logarithm in the all-orders left action.
The finite-mode integrals are proved integrable, not merely totalized. -/
theorem ideleClassConvolution_generalizedModes_actualLog
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (n : ℕ) (x : HeckeIdeleClasses K) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun g => φ g *
      ((quasiClassCharacter K ψ ((g⁻¹ * x)⁻¹) : ℂ) * ℓ (g⁻¹ * x) ^ n)) μ ∧
    ideleClassConvolution K μ φ
      (fun y => (quasiClassCharacter K ψ (y⁻¹) : ℂ) * ℓ y ^ n) x =
      ∑ j ∈ Finset.range (n + 1),
        (∫ g, φ g * (quasiClassCharacter K ψ g : ℂ) * (-ℓ g) ^ j ∂μ) *
          ((quasiClassCharacter K ψ (x⁻¹) : ℂ) * ℓ x ^ (n-j)) * (n.choose j : ℂ) := by
  let ℓ := genuineClassLog K (genuineIdeleLog_add K)
  let ψ := genuineNormTwist K χ z
  have hℓ : Continuous ℓ :=
    genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K)
  have hq : Continuous (fun g => (quasiClassCharacter K ψ g : ℂ)) :=
    Units.continuous_val.comp (quasiClassCharacter_continuous K ψ)
  have hm (j : ℕ) : Integrable
      (fun g => φ g * (quasiClassCharacter K ψ g : ℂ) * (-ℓ g) ^ j) μ :=
    ((hφ.mul hq).mul (hℓ.neg.pow j)).integrable_of_hasCompactSupport
      (hc.mul_right.mul_right)
  have hshift (g y : HeckeIdeleClasses K) : ℓ (g⁻¹ * y) = ℓ y - ℓ g :=
    genuineClassLog_translate K (genuineIdeleLog_add K) g y
  have factor (g : HeckeIdeleClasses K) :
      φ g * ((quasiClassCharacter K ψ ((g⁻¹ * x)⁻¹) : ℂ) * ℓ (g⁻¹ * x) ^ n) =
      ∑ j ∈ Finset.range (n+1),
        (φ g * (quasiClassCharacter K ψ g : ℂ) * (-ℓ g)^j) *
          ((quasiClassCharacter K ψ (x⁻¹) : ℂ) * ℓ x^(n-j)) * (n.choose j : ℂ) := by
    have hi : (g⁻¹ * x)⁻¹ = x⁻¹ * g :=
      (mul_inv_rev (g⁻¹) x).trans
        (congrArg (fun t => x⁻¹ * t) (inv_inv g))
    rw [hi, map_mul, Units.val_mul, hshift, sub_eq_add_neg,
      add_comm (ℓ x) (-ℓ g), add_pow]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  constructor
  · change Integrable (fun g => φ g *
      ((quasiClassCharacter K ψ ((g⁻¹ * x)⁻¹) : ℂ) * ℓ (g⁻¹ * x)^n)) μ
    simp_rw [factor]
    exact integrable_finset_sum _ (fun j _ => ((hm j).mul_const _).mul_const _)
  · change (∫ g, φ g *
      ((quasiClassCharacter K ψ ((g⁻¹ * x)⁻¹) : ℂ) * ℓ (g⁻¹ * x)^n) ∂μ) = _
    simp_rw [factor]
    rw [integral_finset_sum _ (fun j _ => ((hm j).mul_const _).mul_const _)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_mul_const, integral_mul_const]

#check ideleClassConvolution_generalizedModes_actualLog
#print axioms ideleClassConvolution_generalizedModes_actualLog
end MasulloGRH

/-! Round 68 C: exact radial reduction of genuine coefficient moments.
The normalized global Haar decomposition remains open. -/
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

noncomputable def genuineRealClassLog (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re

theorem genuineClassLog_eq_real (x : HeckeIdeleClasses K) :
    genuineClassLog K (genuineIdeleLog_add K) x =
      (genuineRealClassLog K x : ℂ) := by
  refine Quotient.inductionOn' x ?_
  intro a
  simp [genuineRealClassLog, genuineClassLog_mk, genuineIdeleLog]

theorem genuineSpectralJet_norm_radial (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (j : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineSpectralJet K χ z j x‖ =
      Real.exp (z.re * genuineRealClassLog K x) * |genuineRealClassLog K x| ^ j := by
  rw [genuineSpectralJet, genuineClassLog_eq_real K x]
  simp [norm_pow, Complex.norm_exp, Complex.mul_re,
    Complex.norm_real, Real.norm_eq_abs]

/-- Exact scalar integrability premise; this equivalence does not assert it holds. -/
theorem genuineSpectralJet_moment_integrable_iff_radial
    (μ : Measure (HeckeIdeleClasses K)) (f : HeckeIdeleClasses K → ℂ)
    (hf : Measurable f) (χ : UnitaryHeckeCharacter K) (z : ℂ) (j : ℕ) :
    Integrable (fun x => f x * genuineSpectralJet K χ z j x) μ ↔
      Integrable (fun x => ‖f x‖ *
        (Real.exp (z.re * genuineRealClassLog K x) * |genuineRealClassLog K x| ^ j)) μ := by
  have hη : Continuous (genuineSpectralJet K χ z j) := by
    have hq := Units.continuous_val.comp
      (quasiClassCharacter_continuous K (genuineNormTwist K χ z))
    have hl := genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K)
    simpa only [Function.comp_def, genuineNormTwist_class_value, genuineSpectralJet]
      using hq.mul (hl.pow j)
  have hmeas : AEStronglyMeasurable
      (fun x => f x * genuineSpectralJet K χ z j x) μ :=
    (hf.mul hη.measurable).aestronglyMeasurable
  simpa only [norm_mul, genuineSpectralJet_norm_radial] using
    (integrable_norm_iff hmeas).symm

/-- Immediate use in the genuine convolution identity. The radial integrals
remain an explicit hypothesis requiring the actual Haar/Hilbert construction. -/
theorem genuineSpectralJet_moment_action_of_radial_integrability
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (hradial : ∀ j ≤ m, Integrable (fun x => ‖f x‖ *
      (Real.exp (z.re * genuineRealClassLog K x) * |genuineRealClassLog K x| ^ j)) μ) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  apply genuineSpectralJet_weighted_moment_action K μ φ f hφ hcφ hf χ z m
  intro j hj
  exact (genuineSpectralJet_moment_integrable_iff_radial K μ f hf χ z j).mpr
    (hradial j hj)

#check genuineSpectralJet_norm_radial
#print axioms genuineSpectralJet_norm_radial
#check genuineSpectralJet_moment_integrable_iff_radial
#print axioms genuineSpectralJet_moment_integrable_iff_radial
#check genuineSpectralJet_moment_action_of_radial_integrability
#print axioms genuineSpectralJet_moment_action_of_radial_integrability
end MasulloGRH

namespace MasulloGRH
open NumberField.InfinitePlace.Completion
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineRealAtPlace (w : NumberField.InfinitePlace K) : ℝ →+* w.Completion := by
  classical
  exact if h : w.IsReal then (ringEquivRealOfIsReal h).symm.toRingHom
    else (ringEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm.toRingHom.comp
      Complex.ofRealHom

omit [NumberField K] in
theorem genuineRealAtPlace_norm (w : NumberField.InfinitePlace K) (r : ℝ) :
    ‖genuineRealAtPlace K w r‖ = |r| := by
  classical
  unfold genuineRealAtPlace
  split_ifs with h
  · simpa only [Real.norm_eq_abs] using
      (isometryEquivRealOfIsReal h).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivRealOfIsReal h).symm) r
  · simpa only [RingHom.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
      (isometryEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm.isometry.norm_map_of_map_zero
        (map_zero (ringEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm) (r : ℂ)

/-- The actual archimedean section candidate, finite components identically one. -/
noncomputable def genuineSectionIdele (w : NumberField.InfinitePlace K) (t : ℝ) :
    HeckeIdeles K := by
  classical
  let a : ℝ := t / (w.mult : ℝ)
  refine ⟨(fun v => genuineRealAtPlace K v (if v = w then Real.exp a else 1), 1),
    (fun v => genuineRealAtPlace K v (if v = w then Real.exp (-a) else 1), 1), ?_, ?_⟩
  · apply Prod.ext
    · funext v
      change genuineRealAtPlace K v _ * genuineRealAtPlace K v _ = 1
      rw [← map_mul]
      split_ifs <;> simp [← Real.exp_add]
    · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul _
  · apply Prod.ext
    · funext v
      change genuineRealAtPlace K v _ * genuineRealAtPlace K v _ = 1
      rw [← map_mul]
      split_ifs <;> simp [← Real.exp_add]
    · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul _

#check genuineRealAtPlace_norm
#print axioms genuineRealAtPlace_norm
#check genuineSectionIdele
#print axioms genuineSectionIdele
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem genuineSectionIdele_modulus (w : NumberField.InfinitePlace K) (t : ℝ) :
    genuineIdeleModulus K (genuineSectionIdele K w t) = Real.exp t := by
  classical
  have hn (v : NumberField.InfinitePlace K) :
      ‖(genuineSectionIdele K w t).val.1 v‖ ^ v.mult =
        if v = w then Real.exp (t / (w.mult : ℝ)) ^ w.mult else 1 := by
    change ‖genuineRealAtPlace K v (if v = w then _ else _)‖ ^ v.mult = _
    rw [genuineRealAtPlace_norm]
    split_ifs with h
    · subst v
      rw [abs_of_pos (Real.exp_pos _)]
    · simp
  unfold genuineIdeleModulus
  simp_rw [hn]
  have hm : (w.mult : ℝ) ≠ 0 := by exact_mod_cast (NumberField.InfinitePlace.mult_ne_zero (w := w))
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]
  change Real.exp (t / (w.mult : ℝ)) ^ w.mult * (∏ᶠ _v : NumberField.FinitePlace K, ‖(1 : LocalField K _v.maximalIdeal)‖) = _
  simp only [norm_one, finprod_one, mul_one]
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hm]

theorem genuineSectionIdele_log (w : NumberField.InfinitePlace K) (t : ℝ) :
    genuineIdeleLog K (genuineSectionIdele K w t) = (t : ℂ) := by
  simp only [genuineIdeleLog, genuineSectionIdele_modulus, Real.log_exp]

noncomputable def genuineSectionClass (w : NumberField.InfinitePlace K) (t : ℝ) :
    HeckeIdeleClasses K := QuotientGroup.mk (genuineSectionIdele K w t)

theorem genuineSectionClass_log (w : NumberField.InfinitePlace K) (t : ℝ) :
    genuineRealClassLog K (genuineSectionClass K w t) = t := by
  change (genuineIdeleLog K (genuineSectionIdele K w t)).re = t
  rw [genuineSectionIdele_log, Complex.ofReal_re]

#check genuineSectionIdele_modulus
#print axioms genuineSectionIdele_modulus
#check genuineSectionIdele_log
#print axioms genuineSectionIdele_log
#check genuineSectionClass_log
#print axioms genuineSectionClass_log
end MasulloGRH

namespace MasulloGRH
open NumberField.InfinitePlace.Completion
variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
theorem genuineRealAtPlace_continuous (w : NumberField.InfinitePlace K) :
    Continuous (genuineRealAtPlace K w) := by
  classical
  unfold genuineRealAtPlace
  split_ifs with h
  · exact (isometryEquivRealOfIsReal h).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (w.not_isReal_iff_isComplex.mp h)).symm.continuous.comp
      Complex.continuous_ofReal

theorem genuineSectionIdele_continuous (w : NumberField.InfinitePlace K) :
    Continuous (genuineSectionIdele K w) := by
  classical
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun t : ℝ =>
      ((fun v => genuineRealAtPlace K v (if v = w then Real.exp (t / (w.mult : ℝ)) else 1)),
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro v
    by_cases h : v = w
    · simp only [h, if_true]
      exact (genuineRealAtPlace_continuous K v).comp
        (Real.continuous_exp.comp (continuous_id.div_const _))
    · simp only [h, if_false]
      exact continuous_const
  · change Continuous (fun t : ℝ =>
      ((fun v => genuineRealAtPlace K v (if v = w then Real.exp (-(t / (w.mult : ℝ))) else 1)),
        (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro v
    by_cases h : v = w
    · simp only [h, if_true]
      exact (genuineRealAtPlace_continuous K v).comp
        (Real.continuous_exp.comp (continuous_id.div_const _).neg)
    · simp only [h, if_false]
      exact continuous_const

theorem genuineSectionIdele_add (w : NumberField.InfinitePlace K) (s t : ℝ) :
    genuineSectionIdele K w (s+t) = genuineSectionIdele K w s * genuineSectionIdele K w t := by
  classical
  apply Units.ext
  apply Prod.ext
  · funext v
    change genuineRealAtPlace K v (if v = w then _ else _) =
      genuineRealAtPlace K v (if v = w then _ else _) *
        genuineRealAtPlace K v (if v = w then _ else _)
    rw [← map_mul]
    congr 1
    split_ifs <;> simp [add_div, Real.exp_add]
  · change (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) = 1 * 1
    exact (one_mul _).symm

theorem genuineSectionClass_continuous (w : NumberField.InfinitePlace K) :
    Continuous (genuineSectionClass K w) :=
  QuotientGroup.continuous_mk.comp (genuineSectionIdele_continuous K w)

theorem genuineSectionClass_add (w : NumberField.InfinitePlace K) (s t : ℝ) :
    genuineSectionClass K w (s+t) = genuineSectionClass K w s * genuineSectionClass K w t := by
  change QuotientGroup.mk (genuineSectionIdele K w (s+t)) = _
  rw [genuineSectionIdele_add]
  rfl

/-- The actual radial coordinate of the coefficient kernels is attained by
this genuine continuous idele-class section, without an abstract replacement. -/
theorem genuineSpectralJet_section_norm (w : NumberField.InfinitePlace K)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (j : ℕ) (t : ℝ) :
    ‖genuineSpectralJet K χ z j (genuineSectionClass K w t)‖ =
      Real.exp (z.re * t) * |t| ^ j := by
  rw [genuineSpectralJet_norm_radial, genuineSectionClass_log]

#check genuineRealAtPlace_continuous
#print axioms genuineRealAtPlace_continuous
#check genuineSectionIdele_continuous
#print axioms genuineSectionIdele_continuous
#check genuineSectionIdele_add
#print axioms genuineSectionIdele_add
#check genuineSectionClass_continuous
#print axioms genuineSectionClass_continuous
#check genuineSectionClass_add
#print axioms genuineSectionClass_add
#check genuineSpectralJet_section_norm
#print axioms genuineSpectralJet_section_norm
end MasulloGRH

/-! Round 71 C: genuine norm-one/radial topological coordinates.
This is the prerequisite for transporting the actual Haar measure in the
weighted-moment estimate; no measure splitting or spectral divisor is assumed. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem genuineRealClassLog_mul (x y : HeckeIdeleClasses K) :
    genuineRealClassLog K (x*y) = genuineRealClassLog K x + genuineRealClassLog K y := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_mul]
  rfl

theorem genuineRealClassLog_inv (x : HeckeIdeleClasses K) :
    genuineRealClassLog K x⁻¹ = -genuineRealClassLog K x := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_inv]
  rfl

theorem genuineRealClassLog_continuous : Continuous (genuineRealClassLog K) :=
  Complex.continuous_re.comp
    (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K))

abbrev GenuineNormOneClass := {x : HeckeIdeleClasses K // genuineRealClassLog K x = 0}

/-- The norm-one factor is the actual zero fiber of the arithmetic logarithm,
with its inherited quotient topology, rather than a replacement group. -/
noncomputable def genuineClassRadialHomeomorph (w : NumberField.InfinitePlace K) :
    HeckeIdeleClasses K ≃ₜ (GenuineNormOneClass K × ℝ) where
  toFun x := (⟨x * (genuineSectionClass K w (genuineRealClassLog K x))⁻¹, by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv, genuineSectionClass_log]
    exact add_neg_cancel _⟩, genuineRealClassLog K x)
  invFun p := p.1.val * genuineSectionClass K w p.2
  left_inv x := by
    dsimp
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  right_inv p := by
    rcases p with ⟨u,t⟩
    have h : genuineRealClassLog K (u.val * genuineSectionClass K w t) = t := by
      rw [genuineRealClassLog_mul, u.property, genuineSectionClass_log, zero_add]
    apply Prod.ext
    · apply Subtype.ext
      change (u.val * genuineSectionClass K w t) *
        (genuineSectionClass K w (genuineRealClassLog K
          (u.val * genuineSectionClass K w t)))⁻¹ = u.val
      rw [h]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    · exact h
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_id.mul
        ((genuineSectionClass_continuous K w).comp (genuineRealClassLog_continuous K)).inv
    · exact genuineRealClassLog_continuous K
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((genuineSectionClass_continuous K w).comp continuous_snd)

/-- Immediate use of these actual coordinates in the spectral coefficient
whose radial integrability is required by the checked moment-action theorem. -/
theorem genuineSpectralJet_radial_coordinates (w : NumberField.InfinitePlace K)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (j : ℕ)
    (u : GenuineNormOneClass K) (t : ℝ) :
    ‖genuineSpectralJet K χ z j ((genuineClassRadialHomeomorph K w).symm (u,t))‖ =
      Real.exp (z.re * t) * |t| ^ j := by
  rw [genuineSpectralJet_norm_radial]
  change Real.exp (z.re * genuineRealClassLog K (u.val * genuineSectionClass K w t)) *
    |genuineRealClassLog K (u.val * genuineSectionClass K w t)| ^ j = _
  rw [genuineRealClassLog_mul, u.property, genuineSectionClass_log, zero_add]

#check genuineRealClassLog_mul
#print axioms genuineRealClassLog_mul
#check genuineRealClassLog_inv
#print axioms genuineRealClassLog_inv
#check genuineRealClassLog_continuous
#print axioms genuineRealClassLog_continuous
#check genuineClassRadialHomeomorph
#print axioms genuineClassRadialHomeomorph
#check genuineSpectralJet_radial_coordinates
#print axioms genuineSpectralJet_radial_coordinates
end MasulloGRH

/-! Round 68 G: actual radial density for the weighted coefficient premise.
The weight is the manuscript symmetric-strip weight at even regularity s=2d.
This is not a construction of normalized global Haar or a spectral divisor. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def genuineClassLogReal (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re

theorem genuineClassLog_eq_real_G (x : HeckeIdeleClasses K) :
    genuineClassLog K (genuineIdeleLog_add K) x = (genuineClassLogReal K x : ℂ) := by
  refine Quotient.inductionOn' x ?_
  intro a
  rfl

theorem genuineSpectralJet_norm (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineSpectralJet K χ z m x‖ =
      Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m := by
  unfold genuineSpectralJet
  rw [genuineClassLog_eq_real_G]
  simp [norm_pow, Complex.norm_exp, Complex.mul_re,
    Complex.norm_real, Real.norm_eq_abs]

noncomputable def genuineStripWeight (α : ℝ) (d : ℕ) (x : HeckeIdeleClasses K) : ℝ :=
  Real.exp (2 * α * |genuineClassLogReal K x|) * (1 + genuineClassLogReal K x ^ 2) ^ d

theorem genuineStripWeight_pos (α : ℝ) (d : ℕ) (x : HeckeIdeleClasses K) :
    0 < genuineStripWeight K α d x := by
  unfold genuineStripWeight
  positivity

/-- Exact squared reciprocal-weight coefficient density. Its integral is the
missing dual L2 norm in the actual global coefficient/trace calculation. -/
theorem genuineSpectralJet_dual_density (α : ℝ) (d : ℕ)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineSpectralJet K χ z m x /
      (Real.sqrt (genuineStripWeight K α d x) : ℂ)‖ ^ 2 =
    (Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m) ^ 2 /
      genuineStripWeight K α d x := by
  rw [norm_div, genuineSpectralJet_norm, div_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (le_of_lt (genuineStripWeight_pos K α d x))]

#check genuineClassLog_eq_real_G
#print axioms genuineClassLog_eq_real_G
#check genuineSpectralJet_norm
#print axioms genuineSpectralJet_norm
#check genuineSpectralJet_dual_density
#print axioms genuineSpectralJet_dual_density
#check MeasureTheory.memLp_two_iff_integrable_sq_norm
#check MeasureTheory.MemLp.integrable_mul

/-- Conditional domain implication, immediately used below. The remaining
radial integral is explicit; its finiteness for canonical Haar is not assumed
proved. The input L2 condition is the actual weight, not a proxy weight. -/
theorem genuineSpectralJet_moment_integrable_of_radial
    (μ : Measure (HeckeIdeleClasses K)) (α : ℝ) (d : ℕ)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ)
    (hrad : Integrable (fun x =>
      (Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m)^2 /
        genuineStripWeight K α d x) μ) :
    Integrable (fun x => f x * genuineSpectralJet K χ z m x) μ := by
  let w := fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ)
  have hL : Continuous (genuineClassLogReal K) :=
    Complex.continuous_re.comp
      (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K))
  have hw : Continuous w := by
    dsimp [w, genuineStripWeight]
    fun_prop
  have hw0 (x) : w x ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (genuineStripWeight_pos K α d x)))
  have hη : Continuous (genuineSpectralJet K χ z m) := by
    have hψ := Units.continuous_val.comp
      (quasiClassCharacter_continuous K (genuineNormTwist K χ z))
    have hℓ := genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K)
    simpa only [Function.comp_def, genuineNormTwist_class_value, genuineSpectralJet] using hψ.mul (hℓ.pow m)
  have hdual : MemLp (fun x => genuineSpectralJet K χ z m x / w x) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm ((hη.div hw hw0).aestronglyMeasurable)).mpr
    simpa only [Pi.div_apply, w, genuineSpectralJet_dual_density] using hrad
  apply (hdual.integrable_mul hf).congr
  filter_upwards [] with x
  change (genuineSpectralJet K χ z m x / w x) * (w x * f x) = _
  field_simp [hw0 x]

#check genuineSpectralJet_moment_integrable_of_radial
#print axioms genuineSpectralJet_moment_integrable_of_radial
theorem genuineSpectralJet_radial_domain_moment_action
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (α : ℝ) (d : ℕ)
    (hweighted : MemLp (fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ)
    (hrad : ∀ j ≤ m, Integrable (fun x =>
      (Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ j)^2 /
        genuineStripWeight K α d x) μ) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  apply genuineSpectralJet_weighted_moment_action K μ φ f hφ hcφ hf χ z m
  intro j hj
  exact genuineSpectralJet_moment_integrable_of_radial K μ α d χ z j f hweighted (hrad j hj)

#check genuineSpectralJet_radial_domain_moment_action
#print axioms genuineSpectralJet_radial_domain_moment_action
end MasulloGRH


/- API evidence for the next exact radial estimate, not additional assumptions. -/
#check integrableOn_rpow_mul_exp_neg_mul_rpow
#check integrableOn_exp_mul_Ioi
#check integrableOn_exp_mul_Iic
#check MeasureTheory.integrable_map_measure

/- Round 70: interior reciprocal-weight estimate and immediate coefficient action.
The canonical global Haar pushforward identity remains an explicit open premise. -/
open MeasureTheory Set
open scoped Pointwise NNReal ENNReal
namespace MasulloGRH

theorem stripRadialMajorant_integrable (c : ℝ) (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ => |t| ^ n * Real.exp (-c * |t|)) := by
  have hp0 := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := (1 : ℝ)) (b := c) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (by norm_num) hc
  have hp : IntegrableOn (fun t : ℝ => |t| ^ n * Real.exp (-c * |t|)) (Ioi 0) := by
    apply hp0.congr_fun _ measurableSet_Ioi
    intro t ht
    simp [Real.rpow_natCast, abs_of_pos (show 0 < t from ht)]
  have hn : IntegrableOn (fun t : ℝ => |t| ^ n * Real.exp (-c * |t|)) (Iio 0) := by
    simpa using hp.comp_neg
  have hz : IntegrableOn (fun t : ℝ => |t| ^ n * Real.exp (-c * |t|)) ({0} : Set ℝ) := by
    simp
  have hu : (Ioi (0 : ℝ) ∪ Iio 0) ∪ {0} = univ := by
    ext t
    simp only [mem_union, mem_Ioi, mem_Iio, mem_singleton_iff, mem_univ, iff_true]
    rcases lt_trichotomy t 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  simpa [hu] using (hp.union hn).union hz

#check stripRadialMajorant_integrable
#print axioms stripRadialMajorant_integrable

theorem stripRadialDensity_integrable (α b : ℝ) (hstrip : |b| < α) (m d : ℕ) :
    Integrable (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
  have hm := stripRadialMajorant_integrable (2*(α-|b|)) (by linarith) (2*m)
  have hcont : Continuous (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  apply hm.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hd : (1+t^2)^d ≠ 0 := by positivity
  have hden : 1 ≤ (1+t^2)^d := one_le_pow₀ (by nlinarith [sq_nonneg t])
  have hrew : (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d) =
      (Real.exp (2*b*t-2*α*|t|) * |t|^(2*m)) / (1+t^2)^d := by
    rw [Real.exp_sub, show 2*b*t = b*t+b*t by ring, Real.exp_add]
    rw [show 2*m = m*2 by omega, pow_mul]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrew]
  have hb : b*t ≤ |b| * |t| := by simpa [abs_mul] using le_abs_self (b*t)
  have he : 2*b*t-2*α*|t| ≤ -(2*(α-|b|))*|t| := by nlinarith
  calc
    _ ≤ Real.exp (2*b*t-2*α*|t|) * |t|^(2*m) :=
      div_le_self (by positivity) hden
    _ ≤ Real.exp (-(2*(α-|b|))*|t|) * |t|^(2*m) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (by positivity)
    _ = _ := by ring
#check stripRadialDensity_integrable
#print axioms stripRadialDensity_integrable
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineSpectralJet_radial_integrable_of_logHaar
    (μ : Measure (HeckeIdeleClasses K)) (α : ℝ) (d : ℕ)
    (z : ℂ) (m : ℕ) (V : ℝ≥0)
    (hpush : Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume)
    (hstrip : |z.re| < α) :
    Integrable (fun x =>
      (Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m)^2 /
        genuineStripWeight K α d x) μ := by
  let g : ℝ → ℝ := fun t => (Real.exp (z.re*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)
  have hg : Continuous g := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  have hL : Continuous (genuineClassLogReal K) :=
    Complex.continuous_re.comp
      (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K))
  have hi : Integrable g (Measure.map (genuineClassLogReal K) μ) := by
    rw [hpush]
    exact (stripRadialDensity_integrable α z.re hstrip m d).smul_measure (by simp)
  have h := (integrable_map_measure hg.aestronglyMeasurable
    hL.measurable.aemeasurable).mp hi
  simpa only [g, Function.comp_def, genuineStripWeight] using h
#check genuineSpectralJet_radial_integrable_of_logHaar
#print axioms genuineSpectralJet_radial_integrable_of_logHaar
theorem genuineSpectralJet_interior_domain_moment_action
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (α : ℝ) (d : ℕ)
    (hweighted : MemLp (fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ)
    (V : ℝ≥0)
    (hpush : Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume)
    (hstrip : |z.re| < α) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  apply genuineSpectralJet_weighted_moment_action K μ φ f hφ hcφ hf χ z m
  intro j hj
  exact genuineSpectralJet_moment_integrable_of_radial K μ α d χ z j f hweighted (genuineSpectralJet_radial_integrable_of_logHaar K μ α d z j V hpush hstrip)


#check genuineSpectralJet_interior_domain_moment_action
#print axioms genuineSpectralJet_interior_domain_moment_action
end MasulloGRH

open MeasureTheory
namespace MasulloGRH
/-- Boundary reciprocal-weight density at even regularity; the strict jet cutoff
is m < d. This is used in the genuine coefficient moment action. -/
theorem stripBoundaryDensity_integrable (α b : ℝ) (hstrip : |b| ≤ α)
    (m d : ℕ) (hmd : m < d) :
    Integrable (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
  have hcont : Continuous (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  apply integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hq : 0 < 1+t^2 := by positivity
  have hq1 : 1 ≤ 1+t^2 := by nlinarith [sq_nonneg t]
  have hrew : (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d) =
      (Real.exp (2*b*t-2*α*|t|) * |t|^(2*m)) / (1+t^2)^d := by
    rw [Real.exp_sub, show 2*b*t = b*t+b*t by ring, Real.exp_add]
    rw [show 2*m = m*2 by omega, pow_mul]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrew, ← one_div]
  have hb : b*t ≤ |b| * |t| := by simpa [abs_mul] using le_abs_self (b*t)
  have hbt := mul_le_mul_of_nonneg_right hstrip (abs_nonneg t)
  have he : Real.exp (2*b*t-2*α*|t|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hp : |t|^(2*m) ≤ (1+t^2)^m := by
    rw [pow_mul, sq_abs]
    exact pow_le_pow_left₀ (sq_nonneg t) (by linarith) m
  apply (div_le_div_iff₀ (pow_pos hq d) hq).mpr
  calc
    _ ≤ (1+t^2)^m * (1+t^2) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_of_le_one_left (by positivity) he).trans hp) (le_of_lt hq)
    _ = (1+t^2)^(m+1) := (pow_succ _ _).symm
    _ ≤ 1 * (1+t^2)^d := by
      simpa only [one_mul] using (pow_le_pow_right₀ hq1 (show m+1 ≤ d by omega))
#check stripBoundaryDensity_integrable
#print axioms stripBoundaryDensity_integrable
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineSpectralJet_boundary_integrable_of_logHaar
    (μ : Measure (HeckeIdeleClasses K)) (α : ℝ) (d : ℕ)
    (z : ℂ) (m : ℕ) (V : ℝ≥0)
    (hpush : Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume)
    (hstrip : |z.re| ≤ α) (hmd : m < d) :
    Integrable (fun x =>
      (Real.exp (z.re * genuineClassLogReal K x) * |genuineClassLogReal K x| ^ m)^2 /
        genuineStripWeight K α d x) μ := by
  let g : ℝ → ℝ := fun t => (Real.exp (z.re*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)
  have hg : Continuous g := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  have hL : Continuous (genuineClassLogReal K) :=
    Complex.continuous_re.comp
      (genuineArithmeticClassLog_continuous K (genuineIdeleLog_continuous K))
  have hi : Integrable g (Measure.map (genuineClassLogReal K) μ) := by
    rw [hpush]
    exact (stripBoundaryDensity_integrable α z.re hstrip m d hmd).smul_measure (by simp)
  have h := (integrable_map_measure hg.aestronglyMeasurable
    hL.measurable.aemeasurable).mp hi
  simpa only [g, Function.comp_def, genuineStripWeight] using h
#check genuineSpectralJet_boundary_integrable_of_logHaar
#print axioms genuineSpectralJet_boundary_integrable_of_logHaar
theorem genuineSpectralJet_boundary_domain_moment_action
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (α : ℝ) (d : ℕ)
    (hweighted : MemLp (fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ)
    (V : ℝ≥0)
    (hpush : Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume)
    (hstrip : |z.re| ≤ α) (hmd : m < d) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  apply genuineSpectralJet_weighted_moment_action K μ φ f hφ hcφ hf χ z m
  intro j hj
  exact genuineSpectralJet_moment_integrable_of_radial K μ α d χ z j f hweighted (genuineSpectralJet_boundary_integrable_of_logHaar K μ α d z j V hpush hstrip (lt_of_le_of_lt hj hmd))


#check genuineSpectralJet_boundary_domain_moment_action
#print axioms genuineSpectralJet_boundary_domain_moment_action
end MasulloGRH


/-! Round 73 A: C/G compatibility review. C's actual radial chart and G's
weighted density refer to the same genuine arithmetic logarithm. This check
proves the exact pushforward composition, NOT Haar factorization or finiteness.
The copied C71 and G72 exact sources/receipts are preserved in evidence/receipts.
-/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem review_CG_log_compatible :
    genuineClassLogReal K = genuineRealClassLog K := rfl

theorem review_CG_radial_density (w : NumberField.InfinitePlace K)
    (α : ℝ) (d : ℕ) (u : GenuineNormOneClass K) (t : ℝ) :
    genuineStripWeight K α d ((genuineClassRadialHomeomorph K w).symm (u,t)) =
      Real.exp (2 * α * |t|) * (1 + t^2)^d := by
  unfold genuineStripWeight
  rw [review_CG_log_compatible]
  change Real.exp (2 * α * |genuineRealClassLog K
      (u.val * genuineSectionClass K w t)|) *
    (1 + genuineRealClassLog K (u.val * genuineSectionClass K w t)^2)^d = _
  rw [genuineRealClassLog_mul, u.property, genuineSectionClass_log, zero_add]

theorem review_CG_pushforward_composition
    [BorelSpace (GenuineNormOneClass K × ℝ)]
    (w : NumberField.InfinitePlace K) (μ : Measure (HeckeIdeleClasses K)) :
    Measure.map (genuineClassLogReal K) μ =
      Measure.map (Prod.snd : GenuineNormOneClass K × ℝ → ℝ)
        (Measure.map (genuineClassRadialHomeomorph K w) μ) := by
  have he : Measurable (genuineClassRadialHomeomorph K w :
      HeckeIdeleClasses K → GenuineNormOneClass K × ℝ) :=
    (genuineClassRadialHomeomorph K w).continuous_toFun.measurable
  exact (Measure.map_map (μ := μ) measurable_snd he).symm

#check review_CG_log_compatible
#print axioms review_CG_log_compatible
#check review_CG_radial_density
#print axioms review_CG_radial_density
#check review_CG_pushforward_composition
#print axioms review_CG_pushforward_composition
end MasulloGRH

/-! Round 74 A: the actual logarithmic Haar bridge. The genuine norm-one
compactness premise is exposed, not asserted as a theorem. No measure is
redefined. The resulting Haar identity is fed to the existing moment action. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem genuineLog_pushforward_addInvariant
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] :
    (Measure.map (genuineClassLogReal K) μ).IsAddLeftInvariant := by
  constructor
  intro t
  have hL : Measurable (genuineClassLogReal K) :=
    (genuineRealClassLog_continuous K).measurable
  have hs : Measurable (fun x : HeckeIdeleClasses K => genuineSectionClass K w t * x) :=
    (continuous_const.mul continuous_id).measurable
  have ht : Measurable (fun x : ℝ => t + x) :=
    (continuous_const.add continuous_id).measurable
  rw [Measure.map_map ht hL]
  have he : (fun x => t + x) ∘ genuineClassLogReal K =
      genuineClassLogReal K ∘ (fun x => genuineSectionClass K w t * x) := by
    funext x
    change t + genuineRealClassLog K x =
      genuineRealClassLog K (genuineSectionClass K w t * x)
    rw [genuineRealClassLog_mul, genuineSectionClass_log]
  rw [he, ← Measure.map_map hL hs, map_mul_left_eq_self]

theorem genuineLog_compact_preimage
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K) {S : Set ℝ} (hS : IsCompact S) :
    IsCompact ((genuineClassLogReal K) ⁻¹' S) := by
  have he : (genuineClassLogReal K) ⁻¹' S =
      (genuineClassRadialHomeomorph K w).symm ''
        ((Set.univ : Set (GenuineNormOneClass K)) ×ˢ S) := by
    ext x
    constructor
    · intro hx
      refine ⟨genuineClassRadialHomeomorph K w x, ?_,
        (genuineClassRadialHomeomorph K w).symm_apply_apply x⟩
      exact ⟨Set.mem_univ _, hx⟩
    · rintro ⟨⟨u,t⟩, ht, rfl⟩
      change genuineRealClassLog K (u.val * genuineSectionClass K w t) ∈ S
      rw [genuineRealClassLog_mul, u.property, genuineSectionClass_log, zero_add]
      exact ht.2
  rw [he]
  exact (isCompact_univ.prod hS).image (genuineClassRadialHomeomorph K w).symm.continuous

theorem genuineLog_pushforward_finiteOnCompacts
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (Measure.map (genuineClassLogReal K) μ) := by
  constructor
  intro S hS
  have hL : Measurable (genuineClassLogReal K) :=
    (genuineRealClassLog_continuous K).measurable
  rw [Measure.map_apply hL hS.isClosed.measurableSet]
  exact (genuineLog_compact_preimage K w hS).measure_lt_top

theorem genuineLog_pushforward_eq_smul_volume
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] :
    ∃ V : ℝ≥0, Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume := by
  letI := genuineLog_pushforward_addInvariant K w μ
  letI := genuineLog_pushforward_finiteOnCompacts K w μ
  refine ⟨(Measure.map (genuineClassLogReal K) μ).addHaarScalarFactor volume, ?_⟩
  exact Measure.isAddLeftInvariant_eq_smul _ volume

theorem genuineSpectralJet_moment_action_of_compact_normOne
    [CompactSpace (GenuineNormOneClass K)]
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (α : ℝ) (d : ℕ)
    (hweighted : MemLp (fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ)
    (hstrip : |z.re| < α) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ z
    Integrable (fun x => ideleClassConvolution K μ φ f x *
      genuineSpectralJet K χ z m x) μ ∧
    (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
      ∑ j ∈ Finset.range (m+1),
        (jetMoment K μ φ ψ ℓ j * (m.choose j : ℂ)) *
          (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  obtain ⟨V, hpush⟩ := genuineLog_pushforward_eq_smul_volume K w μ
  exact genuineSpectralJet_interior_domain_moment_action K μ φ f hφ hcφ hf χ z m
    α d hweighted V hpush hstrip

#check genuineLog_pushforward_addInvariant
#print axioms genuineLog_pushforward_addInvariant
#check genuineLog_compact_preimage
#print axioms genuineLog_compact_preimage
#check genuineLog_pushforward_finiteOnCompacts
#print axioms genuineLog_pushforward_finiteOnCompacts
#check genuineLog_pushforward_eq_smul_volume
#print axioms genuineLog_pushforward_eq_smul_volume
#check genuineSpectralJet_moment_action_of_compact_normOne
#print axioms genuineSpectralJet_moment_action_of_compact_normOne
end MasulloGRH

/-! Round 75 A. The scalar is the mass of the original measure's logarithmic
unit slab. Norm-one compactness remains an explicit arithmetic premise. -/
namespace MasulloGRH
open scoped ENNReal NNReal
variable (K : Type*) [Field K] [NumberField K]

theorem genuineLog_pushforward_positive_unitSlab
    [CompactSpace (GenuineNormOneClass K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume := by
  obtain ⟨V, hpush⟩ := genuineLog_pushforward_eq_smul_volume K w μ
  have hL : Measurable (genuineClassLogReal K) :=
    (genuineRealClassLog_continuous K).measurable
  have hV : V ≠ 0 := by
    intro he
    apply hμ
    have h := congrArg (fun ν : Measure ℝ => ν Set.univ) hpush
    simpa [Measure.map_apply hL MeasurableSet.univ, he] using h
  refine ⟨V, pos_iff_ne_zero.mpr hV, ?_, hpush⟩
  have h := congrArg (fun ν : Measure ℝ => ν (Set.Ioc 0 1)) hpush
  simpa [Measure.map_apply hL measurableSet_Ioc] using h

theorem genuineSpectralJet_boundary_action_with_HaarMass
    [CompactSpace (GenuineNormOneClass K)]
    [BorelSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (w : NumberField.InfinitePlace K)
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ] (hμ : μ Set.univ ≠ 0)
    (φ f : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Measurable f)
    (χ : UnitaryHeckeCharacter K) (z : ℂ) (m : ℕ)
    (α : ℝ) (d : ℕ)
    (hweighted : MemLp (fun x => (Real.sqrt (genuineStripWeight K α d x) : ℂ) * f x) 2 μ)
    (hstrip : |z.re| ≤ α) (hmd : m < d) :
    ∃ V : ℝ≥0, 0 < V ∧
      μ ((genuineClassLogReal K) ⁻¹' Set.Ioc 0 1) = (V : ℝ≥0∞) ∧
      Measure.map (genuineClassLogReal K) μ = (V : ℝ≥0∞) • volume ∧
      Integrable (fun x => ideleClassConvolution K μ φ f x *
        genuineSpectralJet K χ z m x) μ ∧
      (∫ x, ideleClassConvolution K μ φ f x * genuineSpectralJet K χ z m x ∂μ) =
        ∑ j ∈ Finset.range (m+1),
          (jetMoment K μ φ (genuineNormTwist K χ z)
            (genuineClassLog K (genuineIdeleLog_add K)) j * (m.choose j : ℂ)) *
            (∫ y, f y * genuineSpectralJet K χ z (m-j) y ∂μ) := by
  obtain ⟨V, hV, hmass, hpush⟩ := genuineLog_pushforward_positive_unitSlab K w μ hμ
  exact ⟨V, hV, hmass, hpush,
    genuineSpectralJet_boundary_domain_moment_action K μ φ f hφ hcφ hf χ z m
      α d hweighted V hpush hstrip hmd⟩

#check genuineLog_pushforward_positive_unitSlab
#print axioms genuineLog_pushforward_positive_unitSlab
#check genuineSpectralJet_boundary_action_with_HaarMass
#print axioms genuineSpectralJet_boundary_action_with_HaarMass
end MasulloGRH
