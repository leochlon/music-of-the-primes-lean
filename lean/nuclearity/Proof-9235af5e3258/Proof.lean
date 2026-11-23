import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-! Participant G, round 66; reuses exact checked round-63 source. Genuine adelic definitions reused with attribution
to the exact round-53 F checked source named in VERIFIED_CHECKPOINT.md.
The genuine convolution domain and its Mellin coefficient are pursued here.
The actual spectral quotient, nuclear trace and Hecke divisor remain open. -/
open scoped NumberField

namespace MasulloGRH

variable (K : Type*) [Field K] [NumberField K]

abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ

noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom

noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range

abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K

/-- Genuine continuous unitary idelic character, trivial on principal ideles.
No condition on a positive-real norm section is imposed. -/
structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1


/-- The genuine character descends to the actual idele class group. -/
noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K →* Circle :=
  QuotientGroup.lift (principalIdeles K) χ.character.toMonoidHom (by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact χ.trivial_on_principal a)

/-- The descended character agrees with the original idelic character. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (x : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk x) = χ.character x := rfl

/-- Scalar-valued genuine character, with no spectral indexing assumption. -/
noncomputable def complexClassCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K →* ℂ :=
  Circle.coeHom.comp (classCharacter K χ)

/-- The pointwise convolution formula from manuscript Definition 9.3.1.1.
This does not assert extension to its Hardy--Sobolev space or nuclearity. -/
noncomputable def globalConvolution
    [MeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    (φ f : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

/-- The Mellin coefficient on the genuine inverse-character mode of the
actual left-convolution formula. No assertion that this is a Hecke zero. -/
theorem globalConvolution_inverse_character
    [MeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    (χ : UnitaryHeckeCharacter K)
    (φ : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    globalConvolution K μ φ (fun y => complexClassCharacter K χ (y⁻¹)) x =
      (∫ g, φ g * complexClassCharacter K χ g ∂μ) *
        complexClassCharacter K χ (x⁻¹) := by
  change (∫ g, φ g * complexClassCharacter K χ ((g⁻¹ * x)⁻¹) ∂μ) = _
  rw [← MeasureTheory.integral_mul_const]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with g
  have hi : (g⁻¹ * x)⁻¹ = x⁻¹ * g :=
    (mul_inv_rev (g⁻¹) x).trans (congrArg (fun z => x⁻¹ * z) (inv_inv g))
  calc
    φ g * complexClassCharacter K χ ((g⁻¹ * x)⁻¹) =
        φ g * complexClassCharacter K χ (x⁻¹ * g) :=
      congrArg (fun y => φ g * complexClassCharacter K χ y) hi
    _ = _ := by rw [map_mul]; ring

#check classCharacter_mk
#print axioms classCharacter_mk
#check globalConvolution_inverse_character
#print axioms globalConvolution_inverse_character


theorem classCharacter_continuous (χ : UnitaryHeckeCharacter K) :
    Continuous (classCharacter K χ) := by
  exact (map_continuous χ.character).quotient_lift _

theorem complexClassCharacter_continuous (χ : UnitaryHeckeCharacter K) :
    Continuous (complexClassCharacter K χ) := by
  exact continuous_subtype_val.comp (classCharacter_continuous K χ)

/-- Compactly supported continuous tests make the actual Mellin coefficient
absolutely integrable for every genuine unitary Hecke character. -/
theorem genuineGlobalMellin_integrable
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (χ : UnitaryHeckeCharacter K) (φ : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    MeasureTheory.Integrable (fun g => φ g * complexClassCharacter K χ g) μ := by
  exact (hφ.mul (complexClassCharacter_continuous K χ)).integrable_of_hasCompactSupport
    hc.mul_right

#check classCharacter_continuous
#print axioms classCharacter_continuous
#check genuineGlobalMellin_integrable
#print axioms genuineGlobalMellin_integrable

/-- Both the defining convolution integral and its Mellin coefficient converge.
This is a coefficient calculation, not the nuclear spectral trace theorem. -/
theorem genuineGlobalConvolution_character_converges
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (χ : UnitaryHeckeCharacter K) (φ : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (x : HeckeIdeleClasses K) :
    MeasureTheory.Integrable
      (fun g => φ g * complexClassCharacter K χ ((g⁻¹ * x)⁻¹)) μ ∧
    globalConvolution K μ φ (fun y => complexClassCharacter K χ (y⁻¹)) x =
      (∫ g, φ g * complexClassCharacter K χ g ∂μ) *
        complexClassCharacter K χ (x⁻¹) := by
  constructor
  · exact (hφ.mul ((complexClassCharacter_continuous K χ).comp
      (continuous_inv.mul continuous_const).inv)).integrable_of_hasCompactSupport hc.mul_right
  · exact globalConvolution_inverse_character K μ χ φ x

#check genuineGlobalConvolution_character_converges
#print axioms genuineGlobalConvolution_character_converges

/-- A genuine complex Hecke quasicharacter: continuity and triviality on
principal ideles, with no unitarity restriction. The codomain is multiplicative
complex numbers; the group source forces every value to be nonzero. -/
structure HeckeQuasicharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) ℂ
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

noncomputable def quasiClassCharacter (c : HeckeQuasicharacter K) :
    HeckeIdeleClasses K →* ℂ :=
  QuotientGroup.lift (principalIdeles K) c.character.toMonoidHom (by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact c.trivial_on_principal a)

theorem quasiClassCharacter_continuous (c : HeckeQuasicharacter K) :
    Continuous (quasiClassCharacter K c) :=
  (map_continuous c.character).quotient_lift _

/-- The Mellin coefficient in (12.5.1.4) converges for every continuous
complex Hecke quasicharacter, including nonunitary spectral weights. This
assertion neither selects zeros nor asserts spectral completeness. -/
theorem genuineGlobalQuasiMellin_integrable
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (c : HeckeQuasicharacter K) (φ : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    MeasureTheory.Integrable (fun g => φ g * quasiClassCharacter K c g) μ :=
  (hφ.mul (quasiClassCharacter_continuous K c)).integrable_of_hasCompactSupport
    hc.mul_right

/-- The convergent coefficient of the actual global left-convolution formula
on inverse quasicharacters. Both integrals are proved integrable. This is the
coefficient premise for the desired spectral trace, not the trace identity. -/
theorem genuineGlobalConvolution_quasicharacter_converges
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (c : HeckeQuasicharacter K) (φ : HeckeIdeleClasses K → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (x : HeckeIdeleClasses K) :
    MeasureTheory.Integrable
      (fun g => φ g * quasiClassCharacter K c ((g⁻¹ * x)⁻¹)) μ ∧
    MeasureTheory.Integrable (fun g => φ g * quasiClassCharacter K c g) μ ∧
    globalConvolution K μ φ (fun y => quasiClassCharacter K c (y⁻¹)) x =
      (∫ g, φ g * quasiClassCharacter K c g ∂μ) *
        quasiClassCharacter K c (x⁻¹) := by
  refine ⟨?_, genuineGlobalQuasiMellin_integrable K μ c φ hφ hc, ?_⟩
  · exact (hφ.mul ((quasiClassCharacter_continuous K c).comp
      (continuous_inv.mul continuous_const).inv)).integrable_of_hasCompactSupport hc.mul_right
  · change (∫ g, φ g * quasiClassCharacter K c ((g⁻¹ * x)⁻¹) ∂μ) = _
    rw [← MeasureTheory.integral_mul_const]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with g
    have hi : (g⁻¹ * x)⁻¹ = x⁻¹ * g :=
      (mul_inv_rev (g⁻¹) x).trans (congrArg (fun z => x⁻¹ * z) (inv_inv g))
    calc
      φ g * quasiClassCharacter K c ((g⁻¹ * x)⁻¹) =
          φ g * quasiClassCharacter K c (x⁻¹ * g) :=
        congrArg (fun y => φ g * quasiClassCharacter K c y) hi
      _ = _ := by rw [map_mul]; ring

#check genuineGlobalQuasiMellin_integrable
#print axioms genuineGlobalQuasiMellin_integrable
#check genuineGlobalConvolution_quasicharacter_converges
#print axioms genuineGlobalConvolution_quasicharacter_converges

/-- The unprojected global convolution is defined by an absolutely convergent
integral at every point on every continuous input, for compactly supported
continuous tests. This supplies a domain for the actual formula before its
unproved Hardy--Sobolev extension and spectral projection. -/
theorem globalConvolution_continuousInput_integrable
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (f : C(HeckeIdeleClasses K, ℂ))
    (x : HeckeIdeleClasses K) :
    MeasureTheory.Integrable (fun g => φ g * f (g⁻¹ * x)) μ :=
  (hφ.mul (f.continuous.comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
    hc.mul_right

/-- Actual left-convolution, as a linear map on continuous inputs into functions.
No continuity of its output, bounded extension, projection, or trace is asserted. -/
noncomputable def globalConvolutionOnContinuous
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    C(HeckeIdeleClasses K, ℂ) →ₗ[ℂ] (HeckeIdeleClasses K → ℂ) where
  toFun f := globalConvolution K μ φ f
  map_add' f h := by
    funext x
    change (∫ g, φ g * (f (g⁻¹ * x) + h (g⁻¹ * x)) ∂μ) = _
    simp_rw [mul_add]
    exact MeasureTheory.integral_add
      (globalConvolution_continuousInput_integrable K μ φ hφ hc f x)
      (globalConvolution_continuousInput_integrable K μ φ hφ hc h x)
  map_smul' a f := by
    funext x
    change (∫ g, φ g * (a * f (g⁻¹ * x)) ∂μ) =
      a * (∫ g, φ g * f (g⁻¹ * x) ∂μ)
    simp_rw [mul_left_comm (φ _) a]
    exact MeasureTheory.integral_const_mul a _

/-- The checked convergent quasicharacter coefficient is used in the actual
unprojected global convolution map. Spectral identification and trace remain open. -/
theorem globalConvolutionOnContinuous_quasicharacter
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (c : HeckeQuasicharacter K) :
    globalConvolutionOnContinuous K μ φ hφ hc
      ⟨fun y => quasiClassCharacter K c (y⁻¹),
        (quasiClassCharacter_continuous K c).comp continuous_inv⟩ =
    (fun x => (∫ g, φ g * quasiClassCharacter K c g ∂μ) *
      quasiClassCharacter K c (x⁻¹)) := by
  funext x
  exact (genuineGlobalConvolution_quasicharacter_converges K μ c φ hφ hc x).2.2

#check globalConvolution_continuousInput_integrable
#print axioms globalConvolution_continuousInput_integrable
#check globalConvolutionOnContinuous_quasicharacter
#print axioms globalConvolutionOnContinuous_quasicharacter

/-- The actual global convolution formula preserves continuity. This closes
an output-domain gap in the unprojected formula used before (12.5.1.3).
It does not assert the Hardy--Sobolev extension or a trace. -/
theorem globalConvolution_continuous
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (f : C(HeckeIdeleClasses K, ℂ)) :
    Continuous (globalConvolution K μ φ f) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (μ := μ) hc.isCompact
  · exact ((hφ.comp continuous_snd).mul
      (f.continuous.comp (continuous_snd.inv.mul continuous_fst))).continuousOn
  · intro x g _ hg
    have hz : φ g = 0 := by
      by_contra hz
      exact hg (subset_closure hz)
    simp [hz]

/-- The same genuine convolution formula, now as an endomorphism of continuous
functions on the actual idele class group. This is not the spectral quotient. -/
noncomputable def globalConvolutionEndomorphism
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    C(HeckeIdeleClasses K, ℂ) →ₗ[ℂ] C(HeckeIdeleClasses K, ℂ) where
  toFun f := ⟨globalConvolution K μ φ f,
    globalConvolution_continuous K μ φ hφ hc f⟩
  map_add' f g := by
    apply ContinuousMap.coe_injective
    exact (globalConvolutionOnContinuous K μ φ hφ hc).map_add f g
  map_smul' a f := by
    apply ContinuousMap.coe_injective
    exact (globalConvolutionOnContinuous K μ φ hφ hc).map_smul a f

/-- The convergent Mellin coefficient is used in the genuine convolution
endomorphism. Membership in the genuine Hecke spectral quotient is still open. -/
theorem globalConvolutionEndomorphism_quasicharacter
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (c : HeckeQuasicharacter K) :
    globalConvolutionEndomorphism K μ φ hφ hc
      ⟨fun y => quasiClassCharacter K c (y⁻¹),
        (quasiClassCharacter_continuous K c).comp continuous_inv⟩ =
    (∫ g, φ g * quasiClassCharacter K c g ∂μ) •
      (⟨fun y => quasiClassCharacter K c (y⁻¹),
        (quasiClassCharacter_continuous K c).comp continuous_inv⟩ :
        C(HeckeIdeleClasses K, ℂ)) := by
  apply ContinuousMap.coe_injective
  exact globalConvolutionOnContinuous_quasicharacter K μ φ hφ hc c

#check globalConvolution_continuous
#print axioms globalConvolution_continuous
#check globalConvolutionEndomorphism_quasicharacter
#print axioms globalConvolutionEndomorphism_quasicharacter

/-- The logarithmic mode calculation required for the generalized spectral
coefficients in (10.4.2.29)--(10.4.2.33). The logarithmic modulus law is an
explicit open arithmetic input; it is not a definition of the genuine modulus. -/
theorem globalConvolution_logarithmicMode
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (c : HeckeQuasicharacter K)
    (L : HeckeIdeleClasses K → ℂ) (hL : Continuous L)
    (hshift : ∀ g x, L (g⁻¹ * x) = L x - L g)
    (x : HeckeIdeleClasses K) :
    globalConvolution K μ φ (fun y => quasiClassCharacter K c (y⁻¹) * L y) x =
      (∫ g, φ g * quasiClassCharacter K c g ∂μ) *
        (quasiClassCharacter K c (x⁻¹) * L x) -
      (∫ g, φ g * quasiClassCharacter K c g * L g ∂μ) *
        quasiClassCharacter K c (x⁻¹) := by
  have h0 := genuineGlobalQuasiMellin_integrable K μ c φ hφ hc
  have h1 : MeasureTheory.Integrable
      (fun g => φ g * quasiClassCharacter K c g * L g) μ :=
    ((hφ.mul (quasiClassCharacter_continuous K c)).mul hL).integrable_of_hasCompactSupport
      (hc.mul_right.mul_right)
  change (∫ g, φ g * (quasiClassCharacter K c ((g⁻¹ * x)⁻¹) * L (g⁻¹ * x)) ∂μ) = _
  calc
    _ = ∫ g, (φ g * quasiClassCharacter K c g) *
          (quasiClassCharacter K c (x⁻¹) * L x) -
          (φ g * quasiClassCharacter K c g * L g) *
          quasiClassCharacter K c (x⁻¹) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with g
      have hi : (g⁻¹ * x)⁻¹ = x⁻¹ * g :=
        (mul_inv_rev (g⁻¹) x).trans
          (congrArg (fun z => x⁻¹ * z) (inv_inv g))
      rw [hi, map_mul, hshift]
      ring
    _ = _ := by
      rw [MeasureTheory.integral_sub
        (h0.mul_const _) (h1.mul_const _)]
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]

/-- Integration into the actual unprojected global operator: the first
logarithmic mode is mapped to its diagonal Mellin coefficient times itself,
minus the first Mellin moment times the inverse-character mode. This does
not claim that either mode belongs to the genuine spectral quotient. -/
theorem globalConvolutionEndomorphism_logarithmicMode
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (c : HeckeQuasicharacter K)
    (L : HeckeIdeleClasses K → ℂ) (hL : Continuous L)
    (hshift : ∀ g x, L (g⁻¹ * x) = L x - L g) :
    globalConvolutionEndomorphism K μ φ hφ hc
      ⟨fun y => quasiClassCharacter K c (y⁻¹) * L y,
        ((quasiClassCharacter_continuous K c).comp continuous_inv).mul hL⟩ =
    (∫ g, φ g * quasiClassCharacter K c g ∂μ) •
      (⟨fun y => quasiClassCharacter K c (y⁻¹) * L y,
        ((quasiClassCharacter_continuous K c).comp continuous_inv).mul hL⟩ :
        C(HeckeIdeleClasses K, ℂ)) -
    (∫ g, φ g * quasiClassCharacter K c g * L g ∂μ) •
      (⟨fun y => quasiClassCharacter K c (y⁻¹),
        (quasiClassCharacter_continuous K c).comp continuous_inv⟩ :
        C(HeckeIdeleClasses K, ℂ)) := by
  apply ContinuousMap.coe_injective
  funext x
  exact globalConvolution_logarithmicMode K μ φ hφ hc c L hL hshift x

#check globalConvolution_logarithmicMode
#print axioms globalConvolution_logarithmicMode
#check globalConvolutionEndomorphism_logarithmicMode
#print axioms globalConvolutionEndomorphism_logarithmicMode

/-- All logarithmic orders in the same actual convolution formula. This is
only its finite triangular coefficient formula, conditional on the logarithmic
modulus law. Genuine zero orders and the nuclear sum are not assumed or proved. -/
theorem globalConvolution_generalizedModes
    [MeasurableSpace (HeckeIdeleClasses K)]
    [OpensMeasurableSpace (HeckeIdeleClasses K)]
    (μ : MeasureTheory.Measure (HeckeIdeleClasses K))
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    (φ : HeckeIdeleClasses K → ℂ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (c : HeckeQuasicharacter K)
    (L : HeckeIdeleClasses K → ℂ) (hL : Continuous L)
    (hshift : ∀ g x, L (g⁻¹ * x) = L x - L g)
    (n : ℕ) (x : HeckeIdeleClasses K) :
    globalConvolution K μ φ
      (fun y => quasiClassCharacter K c (y⁻¹) * L y ^ n) x =
    ∑ j ∈ Finset.range (n + 1),
      (∫ g, φ g * quasiClassCharacter K c g * (-L g) ^ j ∂μ) *
        (quasiClassCharacter K c (x⁻¹) * L x ^ (n-j)) * (n.choose j : ℂ) := by
  have hm (j : ℕ) : MeasureTheory.Integrable
      (fun g => φ g * quasiClassCharacter K c g * (-L g) ^ j) μ :=
    ((hφ.mul (quasiClassCharacter_continuous K c)).mul (hL.neg.pow j)).integrable_of_hasCompactSupport
      (hc.mul_right.mul_right)
  change (∫ g, φ g * (quasiClassCharacter K c ((g⁻¹ * x)⁻¹) * L (g⁻¹ * x) ^ n) ∂μ) = _
  calc
    _ = ∫ g, ∑ j ∈ Finset.range (n+1),
        (φ g * quasiClassCharacter K c g * (-L g)^j) *
        (quasiClassCharacter K c (x⁻¹) * L x^(n-j)) * (n.choose j : ℂ) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with g
      have hi : (g⁻¹ * x)⁻¹ = x⁻¹ * g :=
        (mul_inv_rev (g⁻¹) x).trans
          (congrArg (fun z => x⁻¹ * z) (inv_inv g))
      rw [hi, map_mul, hshift, sub_eq_add_neg, add_comm (L x) (-L g), add_pow]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      rw [MeasureTheory.integral_finset_sum _
        (fun j _ => ((hm j).mul_const _).mul_const _)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]

#check globalConvolution_generalizedModes
#print axioms globalConvolution_generalizedModes
end MasulloGRH
