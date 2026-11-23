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

/-- The checked kernel action is now tied to the actual local-norm logarithm.
Additivity and quotient continuity of that logarithm remain explicit hypotheses;
no spectral completeness, multiplicity or trace assertion is made. -/
theorem genuineNorm_firstJet_kernel_action
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (hcont : Continuous (genuineClassLog K hadd))
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    ideleClassKernelConvolution K μ φ
      (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ) * genuineClassLog K hadd y ^ m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ χ (genuineClassLog K hadd) j *
        ((quasiClassCharacter K χ (x⁻¹) : ℂ) *
          ((-1 : ℂ)^j * genuineClassLog K hadd x ^ (m-j) * (m.choose j : ℂ))) := by
  exact (genuine_allJets_kernel_action K μ φ hφ hcφ χ
    (genuineClassLog K hadd) hcont (genuineClassLog_translate K hadd) m x).2

#check genuineClassLog_mk
#print axioms genuineClassLog_mk
#check genuineClassLog_translate
#print axioms genuineClassLog_translate
#check genuineNorm_firstJet_kernel_action
#print axioms genuineNorm_firstJet_kernel_action

/-- The quotient logarithm now has proved arithmetic additivity. Only continuity
of the actual idelic logarithm remains as a coordinate premise. -/
theorem genuineArithmeticClassLog_continuous
    (hcont : Continuous (genuineIdeleLog K)) :
    Continuous (genuineClassLog K (genuineIdeleLog_add K)) := by
  exact hcont.quotient_lift _

/-- Arithmetic instantiation of the all-order action in the spectral trace
calculation. This is an action formula, not an assertion of spectral completeness
or a trace identity. The continuity and measure assumptions remain explicit. -/
theorem genuineArithmetic_allJets_kernel_action
    (hcont : Continuous (genuineIdeleLog K))
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    Integrable (fun y => φ (x * y⁻¹) *
      ((quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m)) μ ∧
    ideleClassKernelConvolution K μ φ
      (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ χ ℓ j *
        ((quasiClassCharacter K χ (x⁻¹) : ℂ) *
          ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))) := by
  exact genuine_allJets_kernel_action K μ φ hφ hcφ χ
    (genuineClassLog K (genuineIdeleLog_add K))
    (genuineArithmeticClassLog_continuous K hcont)
    (genuineClassLog_translate K (genuineIdeleLog_add K)) m x
#check genuineArithmeticClassLog_continuous
#print axioms genuineArithmeticClassLog_continuous
#check genuineArithmetic_allJets_kernel_action
#print axioms genuineArithmetic_allJets_kernel_action
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

/-- Discharges the arithmetic-coordinate continuity premise in the spectral
kernel jet action. Genuine spectral identification and trace remain open. -/
theorem genuineArithmetic_continuousJets_kernel_action
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : HeckeQuasicharacter K)
    (m : ℕ) (x : HeckeIdeleClasses K) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    Integrable (fun y => φ (x * y⁻¹) *
      ((quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m)) μ ∧
    ideleClassKernelConvolution K μ φ
      (fun y => (quasiClassCharacter K χ (y⁻¹) : ℂ) * ℓ y ^ m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ χ ℓ j *
        ((quasiClassCharacter K χ (x⁻¹) : ℂ) *
          ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))) := by
  exact genuineArithmetic_allJets_kernel_action K
    (genuineIdeleLog_continuous K) μ φ hφ hcφ χ m x
#check genuineArithmetic_continuousJets_kernel_action
#print axioms genuineArithmetic_continuousJets_kernel_action
/-- Actual arithmetic norm twist used at the shifted Hecke parameter. -/
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

/-- Integration into the actual norm-twisted logarithmic kernel action.
This asserts no spectral completeness, zero multiplicity, or nuclear trace. -/
theorem genuineHecke_normTwistedJets_kernel_action
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (m : ℕ) (x : HeckeIdeleClasses K) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := genuineNormTwist K χ s
    Integrable (fun y => φ (x * y⁻¹) *
      ((quasiClassCharacter K ψ (y⁻¹) : ℂ) * ℓ y ^ m)) μ ∧
    ideleClassKernelConvolution K μ φ
      (fun y => (quasiClassCharacter K ψ (y⁻¹) : ℂ) * ℓ y ^ m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ ψ ℓ j *
        ((quasiClassCharacter K ψ (x⁻¹) : ℂ) *
          ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))) := by
  exact genuineArithmetic_continuousJets_kernel_action K μ φ hφ hcφ
    (genuineNormTwist K χ s) m x
#check genuineNormTwist_class_value
#print axioms genuineNormTwist_class_value
#check genuineHecke_normTwistedJets_kernel_action
#print axioms genuineHecke_normTwistedJets_kernel_action
/-- Inversion on genuine quasicharacters, needed to match the positive-power
coefficient functions of (10.4.2.22) to left convolution. -/
noncomputable def inverseQuasicharacter (χ : HeckeQuasicharacter K) :
    HeckeQuasicharacter K where
  character := {
    toFun a := (χ.character a)⁻¹
    map_one' := by simp
    map_mul' := by intro a b; simp [map_mul, mul_comm]
    continuous_toFun := χ.character.continuous.inv }
  trivial_on_principal := by
    intro a
    change (χ.character (principalIdele K a))⁻¹ = 1
    rw [χ.trivial_on_principal, inv_one]

theorem inverseQuasicharacter_class_inv (χ : HeckeQuasicharacter K)
    (x : HeckeIdeleClasses K) :
    (quasiClassCharacter K (inverseQuasicharacter K χ) (x⁻¹) : ℂ) =
      (quasiClassCharacter K χ x : ℂ) := by
  refine Quotient.inductionOn' x ?_
  intro a
  change (((χ.character (a⁻¹))⁻¹ : ℂˣ) : ℂ) = (χ.character a : ℂ)
  simp only [map_inv, inv_inv]

/-- The actual coefficient function in (10.4.2.22), with z = a+b+it.
No zero or multiplicity is assigned to z by this definition. -/
noncomputable def genuineSpectralJet (χ : UnitaryHeckeCharacter K) (z : ℂ)
    (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  ((classCharacter K χ x : ℂ) *
    Complex.exp (z * genuineClassLog K (genuineIdeleLog_add K) x)) *
      genuineClassLog K (genuineIdeleLog_add K) x ^ m

/-- Integrable convolution action on the manuscript's positive-power coefficient
functions. The inverse-character Mellin convention is explicit. This does not
claim that these functions form the spectral dual or have Hecke multiplicities. -/
theorem genuineSpectralJet_kernel_action
    (μ : Measure (HeckeIdeleClasses K)) [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (m : ℕ) (x : HeckeIdeleClasses K) :
    let ℓ := genuineClassLog K (genuineIdeleLog_add K)
    let ψ := inverseQuasicharacter K (genuineNormTwist K χ z)
    Integrable (fun y => φ (x * y⁻¹) * genuineSpectralJet K χ z m y) μ ∧
    ideleClassKernelConvolution K μ φ (genuineSpectralJet K χ z m) x =
      ∑ j ∈ Finset.range (m + 1), jetMoment K μ φ ψ ℓ j *
        (((classCharacter K χ x : ℂ) * Complex.exp (z * ℓ x)) *
          ((-1 : ℂ)^j * ℓ x ^ (m-j) * (m.choose j : ℂ))) := by
  have h := genuineArithmetic_continuousJets_kernel_action K μ φ hφ hcφ
    (inverseQuasicharacter K (genuineNormTwist K χ z)) m x
  simpa only [inverseQuasicharacter_class_inv, genuineNormTwist_class_value,
    genuineSpectralJet] using h
#check inverseQuasicharacter_class_inv
#print axioms inverseQuasicharacter_class_inv
#check genuineSpectralJet_kernel_action
#print axioms genuineSpectralJet_kernel_action
/-- Positive translation of the genuine coefficient functions is the action
used on the coefficient side of (10.3.2.1). It has the positive Mellin parameter,
unlike left convolution on the coefficient functions themselves. -/
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
end MasulloGRH
