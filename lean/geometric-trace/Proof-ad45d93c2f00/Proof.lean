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

namespace Round175B
/-- Exact native squared weight retained from checked nuclear B177. -/
noncomputable def nativeWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (2 * alpha * |t|) * (1 + t^2) ^ (s/2)
end Round175B

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

namespace SpectralRound9B
open MasulloGRH Round166F MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine complex Mellin jet divided by the native square-root weight.
This is an explicit function on actual classes, not a spectral definition. -/
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)

end SpectralRound9B

namespace SpectralRound10B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped ComplexConjugate

/-- Discharges the Riesz-conjugation premise of the manuscript's BILINEAR
Mellin pairing after square-root-weight normalization. This is an L2 dual
construction, not a spectral operator or a replacement for the native quotient. -/
noncomputable def normalizedBilinearFunctional
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (g : X → ℂ) (hg : MemLp g 2 mu) : Lp ℂ 2 mu →L[ℂ] ℂ :=
  innerSL ℂ (hg.star.toLp (star g))

/-- Exact integral formula, with the conjugation cancelled. This closes the
bilinear-versus-Hermitian convention gap in the normalized ambient L2 space. -/
theorem normalizedBilinearFunctional_apply
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (g : X → ℂ) (hg : MemLp g 2 mu) (f : Lp ℂ 2 mu) :
    normalizedBilinearFunctional mu g hg f = ∫ x, g x * f x ∂mu := by
  change inner ℂ (hg.star.toLp (star g)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.star.coeFn_toLp] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

end SpectralRound10B

namespace SpectralRound11B
open MeasureTheory MasulloGRH Round166F SpectralRound9B

/-- The positive square-root multiplier for the manuscript's native weight.
Its square discharges the pointwise norm premise of the weighted L2 bridge. -/
noncomputable def nativeHalfWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (alpha * |t|) * (1 + t^2) ^ (s/4)

theorem nativeHalfWeight_pos (alpha s t : ℝ) :
    0 < nativeHalfWeight alpha s t := by
  unfold nativeHalfWeight
  positivity

theorem nativeHalfWeight_sq (alpha s t : ℝ) :
    nativeHalfWeight alpha s t ^ 2 = Round175B.nativeWeight alpha s t := by
  have he : Real.exp (alpha * |t|) ^ 2 = Real.exp (2 * alpha * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp : ((1+t^2)^(s/4))^2 = (1+t^2)^(s/2) := by
    rw [pow_two, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
    congr 1
    ring
  unfold nativeHalfWeight Round175B.nativeWeight
  rw [mul_pow, he, hp]

/-- Actual unnormalized Mellin jet from (10.2.2.4), with z-a=b+it.
It is not asserted here that z is a zero of a Hecke L-function. -/
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

/-- Exact native numerator/denominator bridge, preserving the imaginary
Mellin parameter and actual character. Discharges the pairing's multiplier
cancellation premise; it does not establish density of the weighted completion. -/
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

#check nativeHalfWeight_sq
#print axioms nativeHalfWeight_sq
#check genuineMellinJet_normalization
#print axioms genuineMellinJet_normalization
end SpectralRound11B

namespace SpectralRound11B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound10B

/-- Discharges the function-level native weighted norm/membership premise.
This is the exact manuscript weight on actual classes, not a surrogate norm. -/
theorem native_normalization_memLp_iff
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ)
    (f : HeckeIdeleClasses K → ℂ) (hf : AEStronglyMeasurable f mu) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu ↔
      Integrable (fun x => Round175B.nativeWeight alpha s (classLog K x) *
        ‖f x‖^2) mu := by
  have hell := (Round175B.classLog_continuous K).measurable
  have hw : Measurable (fun x : HeckeIdeleClasses K =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ)) := by
    unfold nativeHalfWeight
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) mu :=
    hw.aestronglyMeasurable.mul hf
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have he (x : HeckeIdeleClasses K) :
      ‖(nativeHalfWeight alpha s (classLog K x) : ℂ) * f x‖^2 =
      Round175B.nativeWeight alpha s (classLog K x) * ‖f x‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (nativeHalfWeight_pos alpha s (classLog K x)), nativeHalfWeight_sq]
  simp only [he]

/-- The normalized continuous functional evaluates to the ACTUAL unnormalized
Mellin pairing on every function of finite native weighted norm. This closes
its integral formula; the quotient's theta annihilation is still unresolved. -/
theorem native_pairing_formula
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    normalizedBilinearFunctional mu _ hg (hF.toLp _) =
      ∫ x, genuineMellinJet K chi z a m x * f x ∂mu := by
  rw [normalizedBilinearFunctional_apply]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx, ← mul_assoc, genuineMellinJet_normalization]

#check native_normalization_memLp_iff
#print axioms native_normalization_memLp_iff
#check native_pairing_formula
#print axioms native_pairing_formula
end SpectralRound11B

namespace SpectralRound12B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound10B SpectralRound11B

/-- Discharges surjectivity at the function-representative level of the native
weighted-space normalization required for the actual spectral dual. Density
of the manuscript test completion and theta-quotient descent remain OPEN. -/
theorem native_normalization_surjective
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ) (F : Lp ℂ 2 mu) :
    ∃ f : HeckeIdeleClasses K → ℂ, AEStronglyMeasurable f mu ∧
      Integrable (fun x => Round175B.nativeWeight alpha s (classLog K x) * ‖f x‖^2) mu ∧
      ∀ x, (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x = F x := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hell := (Round175B.classLog_continuous K).measurable
  have hw : Measurable w := by
    dsimp [w, nativeHalfWeight]
    fun_prop
  have hn (x) : w x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (ne_of_gt (nativeHalfWeight_pos alpha s (classLog K x)))
  let f : HeckeIdeleClasses K → ℂ := fun x => (w x)⁻¹ * F x
  have hf : AEStronglyMeasurable f mu :=
    hw.inv.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
  have he : (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) =
      (F : HeckeIdeleClasses K → ℂ) := by
    funext x
    change w x * ((w x)⁻¹ * F x) = F x
    rw [← mul_assoc, mul_inv_cancel₀ (hn x), one_mul]
  have hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu := by
    rw [he]
    exact Lp.memLp F
  exact ⟨f, hf, (native_normalization_memLp_iff K mu alpha s f hf).mp hF,
    fun x => congrFun he x⟩

/-- Discharges absolute integrability of each actual Mellin pairing, before
any infinite trace or zero-series interchange can be considered. The supplied
jet membership is established for admitted orders by the prior sharp criteria. -/
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

#check native_normalization_surjective
#print axioms native_normalization_surjective
#check native_pairing_integrable
#print axioms native_pairing_integrable
end SpectralRound12B

namespace SpectralRound13B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound10B SpectralRound11B SpectralRound12B
open scoped ComplexConjugate

/-- Discharges nonvanishing of each admitted native jet as an ambient L2
functional, needed before any spectral biorthogonality or totality assertion.
The logarithmic Haar pushforward is an explicit unresolved attachment. -/
theorem genuine_jet_not_ae_zero
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) :
    ¬ genuineNormalizedMellinJet K chi z a s alpha m =ᵐ[mu] 0 := by
  have hell := (Round175B.classLog_continuous K).measurable
  have hlog : ∀ᵐ x ∂mu, classLog K x ≠ 0 := by
    rw [ae_iff]
    have h := congrArg (fun nu : Measure ℝ => nu {0}) hmap
    dsimp only at h
    rw [Measure.map_apply hell (measurableSet_singleton 0)] at h
    simpa using h
  have hmu : mu ≠ 0 := by
    intro hzero
    have h := congrArg (fun nu : Measure ℝ => nu (Set.Ioc 0 1)) hmap
    simp [hzero, Measure.smul_apply, Real.volume_Ioc] at h
    exact hc h.symm
  intro he
  have hf : ∀ᵐ x ∂mu, False := by
    filter_upwards [he, hlog] with x hx hnx
    have hphase : (classCharacter K chi x : ℂ) ≠ 0 := by
      intro h
      have hh := Circle.norm_coe (classCharacter K chi x)
      rw [h, norm_zero] at hh
      exact zero_ne_one hh
    have hp : (1 + (classLog K x)^2)^(-s/4) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
    have hn : genuineNormalizedMellinJet K chi z a s alpha m x ≠ 0 := by
      unfold genuineNormalizedMellinJet
      apply mul_ne_zero (mul_ne_zero hphase (Complex.exp_ne_zero _))
      exact_mod_cast (mul_ne_zero (pow_ne_zero _ hnx) hp)
    exact hn hx
  have hmass : mu Set.univ = 0 := by simpa [ae_iff] using hf
  exact hmu (Measure.measure_univ_eq_zero.mp hmass)

/-- An admitted genuine jet has a nonzero continuous bilinear functional.
This is ambient nondegeneracy only; no zero set or spectral operator is defined. -/
theorem genuine_jet_functional_ne_zero
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu) :
    normalizedBilinearFunctional mu _ hg ≠ 0 := by
  let g := genuineNormalizedMellinJet K chi z a s alpha m
  let F := hg.star.toLp (star g)
  intro hz
  have hi : inner ℂ F F = 0 := by
    have h := congrArg (fun L : Lp ℂ 2 mu →L[ℂ] ℂ => L F) hz
    simpa [normalizedBilinearFunctional, F, g] using h
  have hF : F = 0 := (inner_self_eq_zero).mp hi
  have he : g =ᵐ[mu] 0 := by
    filter_upwards [hg.star.coeFn_toLp, Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal)) (μ := mu)] with x hx hzero
    have hx0 : star (g x) = 0 := by
      calc
        star (g x) = F x := hx.symm
        _ = (0 : Lp ℂ 2 mu) x := congrArg (fun u : Lp ℂ 2 mu => u x) hF
        _ = 0 := hzero
    simpa using congrArg star hx0
  exact genuine_jet_not_ae_zero K chi mu c hc hmap z a s alpha m he

#check genuine_jet_not_ae_zero
#print axioms genuine_jet_not_ae_zero
#check genuine_jet_functional_ne_zero
#print axioms genuine_jet_functional_ne_zero
end SpectralRound13B

namespace SpectralRound13B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound10B SpectralRound11B SpectralRound12B

/-- Discharges nontriviality of the actual native Mellin pairing with a
measurable weighted function. The witness is not asserted to be in the
original dense test class; completion density and theta descent remain open. -/
theorem exists_native_pairing_ne_zero
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu) :
    ∃ f : HeckeIdeleClasses K → ℂ, AEStronglyMeasurable f mu ∧
      Integrable (fun x => Round175B.nativeWeight alpha s (classLog K x) * ‖f x‖^2) mu ∧
      Integrable (fun x => genuineMellinJet K chi z a m x * f x) mu ∧
      (∫ x, genuineMellinJet K chi z a m x * f x ∂mu) ≠ 0 := by
  obtain ⟨F, hF⟩ : ∃ F : Lp ℂ 2 mu, normalizedBilinearFunctional mu _ hg F ≠ 0 := by
    by_contra h
    push_neg at h
    apply genuine_jet_functional_ne_zero K chi mu c hc hmap z a s alpha m hg
    ext F
    exact h F
  obtain ⟨f, hf, hi, he⟩ := native_normalization_surjective K mu alpha s F
  have hmem := (native_normalization_memLp_iff K mu alpha s f hf).mpr hi
  have hpair : normalizedBilinearFunctional mu _ hg F =
      ∫ x, genuineMellinJet K chi z a m x * f x ∂mu := by
    rw [normalizedBilinearFunctional_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [← he x, ← mul_assoc, genuineMellinJet_normalization])
  refine ⟨f, hf, hi, native_pairing_integrable K chi mu z a s alpha m hg f hmem, ?_⟩
  rwa [← hpair]

#check exists_native_pairing_ne_zero
#print axioms exists_native_pairing_ne_zero
end SpectralRound13B
