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

/-- Actual left convolution on functions on the genuine idele-class group.
The measure is explicit; its normalized Haar construction is not asserted here. -/
noncomputable def ideleClassConvolution (μ : Measure (HeckeIdeleClasses K))
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

noncomputable def heckeMellin (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ) (χ : UnitaryHeckeCharacter K) : ℂ :=
  ∫ g, φ g * (classCharacter K χ g : ℂ) ∂μ

/-- A direct calculation of the spectral multiplier, with its inverse convention.
Integrability is required explicitly, so this statement does not rely on an
undefined integral being assigned zero. This is not a trace theorem. -/
theorem genuineHecke_convolution_eigencharacter
    (μ : Measure (HeckeIdeleClasses K)) (φ : HeckeIdeleClasses K → ℂ)
    (χ : UnitaryHeckeCharacter K)
    (hφ : Integrable (fun g => φ g * (classCharacter K χ g : ℂ)) μ)
    (x : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * (classCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ)) μ ∧
    ideleClassConvolution K μ φ (fun y => (classCharacter K χ (y⁻¹) : ℂ)) x =
      heckeMellin K μ φ χ * (classCharacter K χ (x⁻¹) : ℂ) := by
  have factor (g : HeckeIdeleClasses K) :
      φ g * (classCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) =
      (φ g * (classCharacter K χ g : ℂ)) *
        (classCharacter K χ (x⁻¹) : ℂ) := by
    have hi : ((g⁻¹ * x)⁻¹ : HeckeIdeleClasses K) = x⁻¹ * g := by
      simp only [mul_inv_rev, inv_inv]
    rw [hi, (classCharacter K χ).map_mul, Circle.coe_mul]
    ring
  constructor
  · simpa only [factor] using hφ.mul_const (classCharacter K χ (x⁻¹) : ℂ)
  · change (∫ g, φ g * (classCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) ∂μ) = _
    simp_rw [factor]
    exact integral_mul_const _ _

#check classCharacter_mk
#print axioms classCharacter_mk
#check genuineHecke_convolution_eigencharacter
#print axioms genuineHecke_convolution_eigencharacter
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

noncomputable def quasiHeckeMellin (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ) (χ : HeckeQuasicharacter K) : ℂ :=
  ∫ g, φ g * (quasiClassCharacter K χ g : ℂ) ∂μ

/-- A direct calculation of the spectral multiplier, with its inverse convention.
Integrability is required explicitly, so this statement does not rely on an
undefined integral being assigned zero. This is not a trace theorem. -/
theorem genuineQuasiHecke_convolution_eigencharacter
    (μ : Measure (HeckeIdeleClasses K)) (φ : HeckeIdeleClasses K → ℂ)
    (χ : HeckeQuasicharacter K)
    (hφ : Integrable (fun g => φ g * (quasiClassCharacter K χ g : ℂ)) μ)
    (x : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * (quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ)) μ ∧
    ideleClassConvolution K μ φ (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ)) x =
      quasiHeckeMellin K μ φ χ * (quasiClassCharacter K χ (x⁻¹) : ℂ) := by
  have factor (g : HeckeIdeleClasses K) :
      φ g * (quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) =
      (φ g * (quasiClassCharacter K χ g : ℂ)) *
        (quasiClassCharacter K χ (x⁻¹) : ℂ) := by
    have hi : ((g⁻¹ * x)⁻¹ : HeckeIdeleClasses K) = x⁻¹ * g := by
      simp only [mul_inv_rev, inv_inv]
    rw [hi, (quasiClassCharacter K χ).map_mul, Units.val_mul]
    ring
  constructor
  · simpa only [factor] using hφ.mul_const (quasiClassCharacter K χ (x⁻¹) : ℂ)
  · change (∫ g, φ g * (quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) ∂μ) = _
    simp_rw [factor]
    exact integral_mul_const _ _


#check quasiClassCharacter_mk
#print axioms quasiClassCharacter_mk
#check genuineQuasiHecke_convolution_eigencharacter
#print axioms genuineQuasiHecke_convolution_eigencharacter

/-- Continuity descends through the genuine principal-idele quotient. -/
theorem quasiClassCharacter_continuous (χ : HeckeQuasicharacter K) :
    Continuous (quasiClassCharacter K χ) := by
  exact (map_continuous χ.character).quotient_lift _

/-- Weighted Mellin integrability holds for all continuous compactly supported
 tests on the genuine quotient and every measure finite on compact sets. -/
theorem genuineQuasiHecke_test_integrable
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K) :
    Integrable (fun g => φ g * (quasiClassCharacter K χ g : ℂ)) μ := by
  apply (hφ.mul (Units.continuous_val.comp
    (quasiClassCharacter_continuous K χ))).integrable_of_hasCompactSupport
  exact hcφ.mul_right

/-- The convolution multiplier now holds on the full continuous compact test
space without a separate weighted-integrability premise. The smooth tests of
Theorem 12.5.1.1 are contained in this space; the trace remains unproved. -/
theorem genuineQuasiHecke_compactTest_action
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (x : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * (quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ)) μ ∧
    ideleClassConvolution K μ φ (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ)) x =
      quasiHeckeMellin K μ φ χ * (quasiClassCharacter K χ (x⁻¹) : ℂ) := by
  exact genuineQuasiHecke_convolution_eigencharacter K μ φ χ
    (genuineQuasiHecke_test_integrable K μ φ hφ hcφ χ) x

#check quasiClassCharacter_continuous
#print axioms quasiClassCharacter_continuous
#check genuineQuasiHecke_test_integrable
#print axioms genuineQuasiHecke_test_integrable
#check genuineQuasiHecke_compactTest_action
#print axioms genuineQuasiHecke_compactTest_action
/-- Kernel coordinates for the actual convolution in (10.4.3.32–35).
Haar invariance is explicit; this does not assert the manuscript normalization. -/
noncomputable def ideleClassKernelConvolution (μ : Measure (HeckeIdeleClasses K))
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ y, φ (x * y⁻¹) * f y ∂μ

/-- Haar substitution on genuine idele classes, used by the spectral/geometric
kernel comparison. No spectral projector or trace equality is assumed. -/
theorem genuine_kernel_eq_convolution
    [MeasurableMul (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
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
end MasulloGRH
