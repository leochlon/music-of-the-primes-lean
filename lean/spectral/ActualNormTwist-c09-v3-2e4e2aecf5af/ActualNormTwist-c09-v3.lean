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
namespace SpectralRound9B
open MasulloGRH Round166F
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)


end SpectralRound9B
namespace SpectralRound11B
open MasulloGRH Round166F
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)


end SpectralRound11B
namespace Spectral31B
open MasulloGRH Round166F SpectralRound9B SpectralRound11B

/-- Exact native-jet collision under a unitary norm twist. This discharges
coordinate invariance needed BEFORE claiming cross-chain independence. -/
theorem genuineMellinJet_norm_twist
    (K : Type*) [Field K] [NumberField K]
    (chi psi : UnitaryHeckeCharacter K) (t : ℝ)
    (htwist : ∀ x, (classCharacter K psi x : ℂ) =
      (classCharacter K chi x : ℂ) * Complex.exp ((t : ℂ) * Complex.I * (classLog K x : ℂ)))
    (z : ℂ) (a : ℝ) (m : ℕ) :
    genuineMellinJet K psi (z - (t : ℂ) * Complex.I) a m =
      genuineMellinJet K chi z a m := by
  funext x
  unfold genuineMellinJet
  rw [htwist x]
  rw [mul_assoc (classCharacter K chi x : ℂ), ← Complex.exp_add]
  congr 2
  ring

/-- The original weighted normalization does not remove this duplicate. -/
theorem genuineNormalizedMellinJet_norm_twist
    (K : Type*) [Field K] [NumberField K]
    (chi psi : UnitaryHeckeCharacter K) (t : ℝ)
    (htwist : ∀ x, (classCharacter K psi x : ℂ) =
      (classCharacter K chi x : ℂ) * Complex.exp ((t : ℂ) * Complex.I * (classLog K x : ℂ)))
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) :
    genuineNormalizedMellinJet K psi (z - (t : ℂ) * Complex.I) a s alpha m =
      genuineNormalizedMellinJet K chi z a s alpha m := by
  funext x
  unfold genuineNormalizedMellinJet
  rw [htwist x]
  rw [mul_assoc (classCharacter K chi x : ℂ), ← Complex.exp_add]
  congr 2
  ring

/-- Strict native admission is unchanged by the compensating shift. -/
theorem norm_twist_preserves_admission
    (z : ℂ) (t a alpha s : ℝ) (m : ℕ) :
    (|(z - (t : ℂ) * Complex.I).re - a| < alpha ∨
      (|(z - (t : ℂ) * Complex.I).re - a| = alpha ∧ (2 : ℝ)*m+1<s)) ↔
    (|z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1<s)) := by
  simp

#print axioms genuineMellinJet_norm_twist
#print axioms genuineNormalizedMellinJet_norm_twist
#print axioms norm_twist_preserves_admission
end Spectral31B

namespace Spectral32B
open MasulloGRH Round166F Round175B SpectralRound9B SpectralRound11B

variable (K : Type*) [Field K] [NumberField K]

/-- The manuscript's actual unitary norm twist on the original ideles. -/
noncomputable def normTwist (chi : UnitaryHeckeCharacter K) (t : ℝ) :
    UnitaryHeckeCharacter K where
  character :=
    { toFun := fun x => chi.character x * Circle.exp (t * Real.log (genuineIdeleModulus K x))
      map_one' := by
        have h1 : genuineIdeleModulus K 1 = 1 := by
          simpa only [map_one] using genuineIdeleModulus_principal K 1
        simp [h1]
      map_mul' := by
        intro x y
        rw [map_mul, genuineIdeleModulus_mul, Real.log_mul
          (genuineIdeleModulus_ne_zero K x) (genuineIdeleModulus_ne_zero K y),
          mul_add, Circle.exp_add]
        ac_rfl
      continuous_toFun := by
        apply chi.character.continuous.mul
        apply continuous_induced_rng.mpr
        change Continuous (fun x : HeckeIdeles K =>
          Complex.exp (((t * Real.log (genuineIdeleModulus K x) : ℝ) : ℂ) * Complex.I))
        exact Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_const.mul
            ((genuineIdeleModulus_continuous K).log
              (genuineIdeleModulus_ne_zero K)))).mul continuous_const) }
  trivial_on_principal := by
    intro u
    change chi.character (principalIdele K u) *
      Circle.exp (t * Real.log (genuineIdeleModulus K (principalIdele K u))) = 1
    simp [chi.trivial_on_principal, genuineIdeleModulus_principal]

/-- The coordinate formula now follows from the actual construction. -/
theorem classCharacter_normTwist (chi : UnitaryHeckeCharacter K) (t : ℝ)
    (x : HeckeIdeleClasses K) :
    (classCharacter K (normTwist K chi t) x : ℂ) =
      (classCharacter K chi x : ℂ) *
        Complex.exp ((t : ℂ) * Complex.I * (classLog K x : ℂ)) := by
  refine Quotient.inductionOn x ?_
  intro y
  change ((chi.character y * Circle.exp (t * Real.log (genuineIdeleModulus K y)) : Circle) : ℂ) = _
  simp only [Circle.coe_mul, Circle.coe_exp, classCharacter_mk]
  congr 2
  change (((t * Real.log (genuineIdeleModulus K y) : ℝ) : ℂ) * Complex.I) =
    (t : ℂ) * Complex.I * (Real.log (genuineIdeleModulus K y) : ℂ)
  push_cast
  ring

/-- Genuine norm-twisted native jets have no assumed twist-formula premise. -/
theorem actual_normTwist_jet (chi : UnitaryHeckeCharacter K) (t : ℝ)
    (z : ℂ) (a : ℝ) (m : ℕ) :
    genuineMellinJet K (normTwist K chi t) (z - (t : ℂ) * Complex.I) a m =
      genuineMellinJet K chi z a m :=
  Spectral31B.genuineMellinJet_norm_twist K chi (normTwist K chi t) t
    (classCharacter_normTwist K chi t) z a m

/-- Same original weighted jets, with the former htwist premise discharged. -/
theorem actual_normTwist_normalized_jet (chi : UnitaryHeckeCharacter K) (t : ℝ)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) :
    genuineNormalizedMellinJet K (normTwist K chi t)
      (z - (t : ℂ) * Complex.I) a s alpha m =
      genuineNormalizedMellinJet K chi z a s alpha m :=
  Spectral31B.genuineNormalizedMellinJet_norm_twist K chi (normTwist K chi t) t
    (classCharacter_normTwist K chi t) z a s alpha m

#print axioms normTwist
#print axioms classCharacter_normTwist
#print axioms actual_normTwist_jet
#print axioms actual_normTwist_normalized_jet
end Spectral32B


namespace Spectral33B
open MasulloGRH Round166F Round175B SpectralRound11B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (HeckeIdeleClasses K) := borel _
local instance : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

/-- Actual cross-character collision classification. Equality of the native
zeroth kernels forces the same real exponent and the actual unitary norm twist;
no twist relation or separation premise is assumed. -/
theorem actual_cross_character_collision
    (chi psi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsOpenPosMeasure]
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (a : ℝ) (z w : ℂ)
    (h : genuineMellinJet K chi z a 0 =ᵐ[mu]
      genuineMellinJet K psi w a 0) :
    z.re = w.re ∧
    classCharacter K psi =
      classCharacter K (Spectral32B.normTwist K chi (z.im - w.im)) := by
  have hrad : ∀ᵐ x ∂mu,
      Real.exp ((z.re-a)*classLog K x) =
      Real.exp ((w.re-a)*classLog K x) := by
    filter_upwards [h] with x hx
    have hn := congrArg norm hx
    simpa [genuineMellinJet, norm_mul, Complex.norm_exp, Complex.mul_re] using hn
  have heq : MeasurableSet {t : ℝ |
      Real.exp ((z.re-a)*t) = Real.exp ((w.re-a)*t)} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
  have hm := (ae_map_iff (classLog_continuous K).measurable.aemeasurable heq).mpr hrad
  rw [hmap] at hm
  have hm0 : (fun t : ℝ => Real.exp ((z.re-a)*t)) =ᵐ[volume]
      (fun t : ℝ => Real.exp ((w.re-a)*t)) := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume
    (show Continuous (fun t : ℝ => Real.exp ((z.re-a)*t)) by fun_prop)
    (show Continuous (fun t : ℝ => Real.exp ((w.re-a)*t)) by fun_prop)).mp hm0
  have hr : z.re = w.re := by
    have ht := Real.exp_injective (congrFun hall 1)
    simp only [mul_one] at ht
    linarith
  refine ⟨hr, ?_⟩
  have hshift : z - ((z.im-w.im : ℝ) : ℂ)*Complex.I = w := by
    apply Complex.ext <;> simp [hr]
  have ht := Spectral32B.actual_normTwist_jet K chi (z.im-w.im) z a 0
  rw [hshift] at ht
  have hchar : (fun x => (classCharacter K psi x : ℂ)) =ᵐ[mu]
      (fun x => (classCharacter K (Spectral32B.normTwist K chi (z.im-w.im)) x : ℂ)) := by
    filter_upwards [h] with x hx
    have he := congrFun ht x
    rw [← he] at hx
    simp only [genuineMellinJet, pow_zero, Complex.ofReal_one, mul_one] at hx
    exact (mul_right_cancel₀ (Complex.exp_ne_zero _) hx).symm
  have hfun := (Continuous.ae_eq_iff_eq mu
    (show Continuous (fun x => (classCharacter K psi x : ℂ)) from
      continuous_subtype_val.comp (classCharacter_continuous K psi))
    (show Continuous (fun x => (classCharacter K (Spectral32B.normTwist K chi (z.im-w.im)) x : ℂ)) from
      continuous_subtype_val.comp (classCharacter_continuous K _))).mp hchar
  funext x
  exact Subtype.ext (congrFun hfun x)

#print axioms actual_cross_character_collision
end Spectral33B

namespace Spectral34B
open MasulloGRH Round166F Round175B SpectralRound9B SpectralRound11B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (HeckeIdeleClasses K) := borel _
local instance : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

/-- Actual normalized collision classification, with the original weight,
logarithm and quotient measure. The weight-cancellation calculation is reused
from SpectralH903.normalized_parameter_injective (spectral_H cycle 7),
now for distinct actual characters; the collision converse is Spectral33B. -/
theorem actual_normalized_cross_character_collision
    (chi psi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsOpenPosMeasure]
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (a s alpha : ℝ) (m : ℕ) (z w : ℂ)
    (h : genuineNormalizedMellinJet K chi z a s alpha m =ᵐ[mu]
      genuineNormalizedMellinJet K psi w a s alpha m) :
    z.re = w.re ∧
    classCharacter K psi =
      classCharacter K (Spectral32B.normTwist K chi (z.im - w.im)) := by
  apply Spectral33B.actual_cross_character_collision K chi psi mu c hc hmap a z w
  have hlog : ∀ᵐ x ∂mu, classLog K x ≠ 0 := by
    have hr : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      rw [ae_iff]
      simp
    have hm : ∀ᵐ t ∂Measure.map (classLog K) mu, t ≠ 0 := by
      rw [hmap]
      exact Measure.ae_smul_measure hr c
    exact (ae_map_iff (Round175B.classLog_continuous K).measurable.aemeasurable
      (by measurability)).mp hm
  filter_upwards [h, hlog] with x hx hxn
  have hn : (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (pow_ne_zero m hxn) (ne_of_gt (Real.rpow_pos_of_pos
      (show (0 : ℝ) < 1 + (classLog K x)^2 by positivity) _))
  simp only [genuineNormalizedMellinJet] at hx
  have he := mul_right_cancel₀ hn hx
  rw [Complex.exp_sub, Complex.exp_sub] at he
  have hz := mul_right_cancel₀
    (inv_ne_zero (Complex.exp_ne_zero (((alpha * |classLog K x| : ℝ) : ℂ))))
    (show ((classCharacter K chi x : ℂ) * Complex.exp ((z-(a:ℂ))*(classLog K x:ℂ))) *
        (Complex.exp (((alpha * |classLog K x| : ℝ) : ℂ)))⁻¹ =
      ((classCharacter K psi x : ℂ) * Complex.exp ((w-(a:ℂ))*(classLog K x:ℂ))) *
        (Complex.exp (((alpha * |classLog K x| : ℝ) : ℂ)))⁻¹ by
      simpa only [div_eq_mul_inv, mul_assoc] using he)
  simpa only [genuineMellinJet, pow_zero, Complex.ofReal_one, mul_one] using hz

#print axioms actual_normalized_cross_character_collision
end Spectral34B

namespace Spectral34B
open MasulloGRH Round166F Round175B SpectralRound9B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Reused FollowupD31.classCharacter_mul, on the original arithmetic quotient. -/
theorem classCharacter_mul (chi : UnitaryHeckeCharacter K)
    (g x : HeckeIdeleClasses K) :
    classCharacter K chi (g*x) = classCharacter K chi g * classCharacter K chi x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  exact map_mul chi.character a b

/-- The actual original weight is invariant under the norm-one subgroup. -/
theorem normalizedJet_norm_one_translate (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (g x : HeckeIdeleClasses K)
    (hg : classLog K g = 0) :
    genuineNormalizedMellinJet K chi z a s alpha m (g*x) =
      (classCharacter K chi g : ℂ) * genuineNormalizedMellinJet K chi z a s alpha m x := by
  simp only [genuineNormalizedMellinJet, classCharacter_mul, Circle.coe_mul,
    classLog_mul, hg, zero_add]
  ring

/-- Actual cross-component orthogonality, manuscript paragraph immediately
before (10.3.1.16), for all orders and original normalized weights.
The distinct compact restrictions are witnessed by a norm-one class g. -/
theorem native_cross_component_integral_zero
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi psi : UnitaryHeckeCharacter K) (z w : ℂ) (a s alpha : ℝ) (m n : ℕ)
    (g : HeckeIdeleClasses K) (hg : classLog K g = 0)
    (hd : (star (classCharacter K chi g : ℂ)) * (classCharacter K psi g : ℂ) ≠ 1) :
    (∫ x, star (genuineNormalizedMellinJet K chi z a s alpha m x) *
      genuineNormalizedMellinJet K psi w a s alpha n x ∂mu) = 0 := by
  let F := fun x => star (genuineNormalizedMellinJet K chi z a s alpha m x) *
    genuineNormalizedMellinJet K psi w a s alpha n x
  have he := integral_mul_left_eq_self (μ := mu) F g
  have hx (x : HeckeIdeleClasses K) : F (g*x) =
      (star (classCharacter K chi g : ℂ) * (classCharacter K psi g : ℂ)) * F x := by
    dsimp [F]
    rw [normalizedJet_norm_one_translate K chi z a s alpha m g x hg,
      normalizedJet_norm_one_translate K psi w a s alpha n g x hg, map_mul]
    ring
  simp_rw [hx] at he
  rw [integral_const_mul] at he
  have hz : ((star (classCharacter K chi g : ℂ) * (classCharacter K psi g : ℂ))-1) *
      (∫ x, F x ∂mu) = 0 := by rw [sub_mul, he, one_mul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hd)

#print axioms normalizedJet_norm_one_translate
#print axioms native_cross_component_integral_zero
end Spectral34B

namespace Spectral35B
open MasulloGRH Round166F SpectralRound9B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The manuscript's compact-character label, on the actual norm-one classes. -/
noncomputable def compactRestriction (chi : UnitaryHeckeCharacter K) :
    {g : HeckeIdeleClasses K // classLog K g = 0} → Circle :=
  fun g => classCharacter K chi g

/-- Distinct actual compact restrictions supply the separating class needed
by Haar orthogonality; neither a witness nor orthogonality is an assumption. -/
theorem native_distinct_component_integral_zero
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi psi : UnitaryHeckeCharacter K)
    (hd : compactRestriction K chi ≠ compactRestriction K psi)
    (z w : ℂ) (a s alpha : ℝ) (m n : ℕ) :
    (∫ x, star (genuineNormalizedMellinJet K chi z a s alpha m x) *
      genuineNormalizedMellinJet K psi w a s alpha n x ∂mu) = 0 := by
  classical
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hd
  apply Spectral34B.native_cross_component_integral_zero K mu chi psi z w a s alpha m n
    g.val g.property
  intro he
  apply hg
  apply Subtype.ext
  have hu : star (classCharacter K chi g.val : ℂ) *
      (classCharacter K chi g.val : ℂ) = 1 := by
    change (starRingEnd ℂ) _ * _ = _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have hn : star (classCharacter K chi g.val : ℂ) ≠ 0 := by
    exact star_ne_zero.mpr (Circle.coe_ne_zero _)
  exact (mul_left_cancel₀ hn (he.trans hu.symm)).symm

/-- Cross-component orthogonality of the ACTUAL conjugated Riesz vectors in
the original half-weight L2 realization, for every admitted pair of orders. -/
theorem native_distinct_component_riesz_orthogonal
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi psi : UnitaryHeckeCharacter K)
    (hd : compactRestriction K chi ≠ compactRestriction K psi)
    (z w : ℂ) (a s alpha : ℝ) (m n : ℕ)
    (hf : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (hg : MemLp (genuineNormalizedMellinJet K psi w a s alpha n) 2 mu) :
    inner ℂ (hf.star.toLp (star (genuineNormalizedMellinJet K chi z a s alpha m)))
      (hg.star.toLp (star (genuineNormalizedMellinJet K psi w a s alpha n))) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, star (genuineNormalizedMellinJet K psi w a s alpha n x) *
        genuineNormalizedMellinJet K chi z a s alpha m x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hf.star.coeFn_toLp, hg.star.coeFn_toLp] with x hx hy
      rw [hx, hy]
      simp [RCLike.inner_apply]
    _ = 0 := native_distinct_component_integral_zero K mu psi chi
      (Ne.symm hd) w z a s alpha n m

#print axioms native_distinct_component_integral_zero
#print axioms native_distinct_component_riesz_orthogonal
end Spectral35B
