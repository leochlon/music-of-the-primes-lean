import Mathlib

/-!
Rounds 54–55 B: a necessary character-action calculation for the actual convolution
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
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Continuous f)
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
    (((hφ.comp (continuous_fst.mul continuous_snd.inv)).mul
      (hf.comp continuous_snd)).mul ((hη m).comp continuous_fst)).aestronglyMeasurable
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
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Continuous f)
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
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hf : Continuous f)
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
