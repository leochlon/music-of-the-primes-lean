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
/-- Actual integrability in kernel coordinates and the exact Mellin multiplier
for continuous compactly supported tests, used in (10.4.3.32–35). -/
theorem genuineQuasiHecke_compactTest_kernel_action
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (x : HeckeIdeleClasses K) :
    Integrable (fun y => φ (x * y⁻¹) * (quasiClassCharacter K χ (y⁻¹) : ℂ)) μ ∧
    ideleClassKernelConvolution K μ φ (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ)) x =
      quasiHeckeMellin K μ φ χ * (quasiClassCharacter K χ (x⁻¹) : ℂ) := by
  obtain ⟨hi, he⟩ := genuineQuasiHecke_compactTest_action K μ φ hφ hcφ χ x
  constructor
  · have h := (integrable_comp_div_left
      (fun g => φ g * (quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ)) x).mpr hi
    have hc (y : HeckeIdeleClasses K) : (x / y)⁻¹ * x = y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    simp_rw [hc] at h
    simpa only [div_eq_mul_inv] using h
  · rw [genuine_kernel_eq_convolution]
    exact he

#check genuineQuasiHecke_compactTest_kernel_action
#print axioms genuineQuasiHecke_compactTest_kernel_action

/-- The jet moment used in the spectral multiplier calculation. The supplied
logarithmic coordinate must still be identified with the genuine idelic modulus. -/
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

/-- Actual first-jet convolution action, conditional only on the explicitly
specified logarithmic-coordinate laws. No trace or zero divisor is assumed. -/
theorem genuine_firstJet_action
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (ℓ : HeckeIdeleClasses K → ℂ) (hℓ : Continuous ℓ)
    (htranslate : ∀ g x, ℓ (g⁻¹ * x) = ℓ x - ℓ g)
    (x : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * ((quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) *
      ℓ (g⁻¹ * x))) μ ∧
    ideleClassConvolution K μ φ (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y) x =
      quasiHeckeMellin K μ φ χ * ((quasiClassCharacter K χ (x⁻¹) : ℂ) * ℓ x) -
      jetMoment K μ φ χ ℓ 1 * (quasiClassCharacter K χ (x⁻¹) : ℂ) := by
  have factor (g : HeckeIdeleClasses K) :
      φ g * ((quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) * ℓ (g⁻¹ * x)) =
      (φ g * (quasiClassCharacter K χ g : ℂ)) *
        ((quasiClassCharacter K χ (x⁻¹) : ℂ) * ℓ x) -
      ((φ g * (quasiClassCharacter K χ g : ℂ)) * ℓ g ^ 1) *
        (quasiClassCharacter K χ (x⁻¹) : ℂ) := by
    rw [htranslate]
    simp only [mul_inv_rev, inv_inv, map_mul, Units.val_mul, pow_one]
    ring
  have h0 := genuineQuasiHecke_test_integrable K μ φ hφ hcφ χ
  have h1 := genuine_jetMoment_integrable K μ φ hφ hcφ χ ℓ hℓ 1
  have hleft := h0.mul_const ((quasiClassCharacter K χ (x⁻¹) : ℂ) * ℓ x)
  have hright := h1.mul_const (quasiClassCharacter K χ (x⁻¹) : ℂ)
  constructor
  · simpa only [factor] using hleft.sub hright
  · unfold ideleClassConvolution
    simp_rw [factor]
    rw [integral_sub hleft hright, integral_mul_const, integral_mul_const]
    rfl

#check genuine_jetMoment_integrable
#print axioms genuine_jetMoment_integrable
#check genuine_firstJet_action
#print axioms genuine_firstJet_action


/-- Finite binomial action of the actual convolution on every logarithmic jet.
This is the multiplier calculation needed for (10.4.2.22). The explicit
coordinate premise is NOT an assertion that the arithmetic modulus exists. -/
theorem genuine_allJets_action
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (ℓ : HeckeIdeleClasses K → ℂ) (hℓ : Continuous ℓ)
    (htranslate : ∀ g x, ℓ (g⁻¹ * x) = ℓ x - ℓ g)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * ((quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) *
      ℓ (g⁻¹ * x) ^ m)) μ ∧
    ideleClassConvolution K μ φ
      (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ χ ℓ j *
        ((quasiClassCharacter K χ (x⁻¹) : ℂ) *
          ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))) := by
  let b := fun j : ℕ => (quasiClassCharacter K χ (x⁻¹) : ℂ) *
    ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))
  have factor (g : HeckeIdeleClasses K) :
      φ g * ((quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) * ℓ (g⁻¹ * x)^m) =
      ∑ j ∈ Finset.range (m + 1),
        ((φ g * (quasiClassCharacter K χ g : ℂ)) * ℓ g ^ j) * b j := by
    rw [htranslate]
    simp only [mul_inv_rev, inv_inv, map_mul, Units.val_mul]
    rw [show ℓ x - ℓ g = -ℓ g + ℓ x by ring, add_pow]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [b]
    rw [neg_eq_neg_one_mul, mul_pow]
    ring
  have hi (j : ℕ) :=
    (genuine_jetMoment_integrable K μ φ hφ hcφ χ ℓ hℓ j).mul_const (b j)
  constructor
  · simp_rw [factor]
    exact integrable_finset_sum _ (fun j _ => hi j)
  · unfold ideleClassConvolution
    simp_rw [factor]
    rw [integral_finset_sum _ (fun j _ => hi j)]
    apply Finset.sum_congr rfl
    intro j hj
    exact integral_mul_const _ _

#check genuine_allJets_action
#print axioms genuine_allJets_action


/-- The same all-order jet action in geometric kernel coordinates, with actual
absolute integrability. This uses the genuine class group, not a model group. -/
theorem genuine_allJets_kernel_action
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (ℓ : HeckeIdeleClasses K → ℂ) (hℓ : Continuous ℓ)
    (htranslate : ∀ g x, ℓ (g⁻¹ * x) = ℓ x - ℓ g)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    Integrable (fun y => φ (x * y⁻¹) *
      ((quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m)) μ ∧
    ideleClassKernelConvolution K μ φ
      (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ χ ℓ j *
        ((quasiClassCharacter K χ (x⁻¹) : ℂ) *
          ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))) := by
  obtain ⟨hi, he⟩ := genuine_allJets_action K μ φ hφ hcφ χ ℓ hℓ htranslate m x
  constructor
  · have h := (integrable_comp_div_left
      (fun g => φ g * ((quasiClassCharacter K χ ((g⁻¹ * x)⁻¹) : ℂ) *
        ℓ (g⁻¹ * x) ^ m)) x).mpr hi
    have hc (y : HeckeIdeleClasses K) : (x / y)⁻¹ * x = y := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
    simp_rw [hc] at h
    simpa only [div_eq_mul_inv] using h
  · rw [genuine_kernel_eq_convolution]
    exact he

#check genuine_allJets_kernel_action
#print axioms genuine_allJets_kernel_action


/-- The compact-log-support factor in the nuclearity estimate (10.3.2.8–11).
The bound retains R^j, which cannot be discarded for unbounded interior jets. -/
theorem genuine_jetMoment_norm_bound
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (ℓ : HeckeIdeleClasses K → ℂ) (hℓ : Continuous ℓ)
    (R : ℝ) (hbound : ∀ g, φ g ≠ 0 → ‖ℓ g‖ ≤ R) (j : ℕ) :
    ‖jetMoment K μ φ χ ℓ j‖ ≤
      (∫ g, ‖φ g * (quasiClassCharacter K χ g : ℂ)‖ ∂μ) * R ^ j := by
  have h0 := (genuineQuasiHecke_test_integrable K μ φ hφ hcφ χ).norm
  have hj := (genuine_jetMoment_integrable K μ φ hφ hcφ χ ℓ hℓ j).norm
  have hb (g : HeckeIdeleClasses K) :
      ‖(φ g * (quasiClassCharacter K χ g : ℂ)) * ℓ g ^ j‖ ≤
        ‖φ g * (quasiClassCharacter K χ g : ℂ)‖ * R ^ j := by
    by_cases hz : φ g = 0
    · simp [hz]
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hbound g hz) j) (norm_nonneg _)
  calc
    ‖jetMoment K μ φ χ ℓ j‖ ≤
        ∫ g, ‖(φ g * (quasiClassCharacter K χ g : ℂ)) * ℓ g ^ j‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ g, ‖φ g * (quasiClassCharacter K χ g : ℂ)‖ * R ^ j ∂μ :=
      integral_mono hj (h0.mul_const _) hb
    _ = _ := integral_mul_const _ _

#check genuine_jetMoment_norm_bound
#print axioms genuine_jetMoment_norm_bound

end MasulloGRH
