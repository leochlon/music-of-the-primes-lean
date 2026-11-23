import Mathlib

/-! Participant E, round 14. This is one necessary arithmetic relation in
constructing the full number-field idele-class norm, not a Hecke divisor proof.
The infinite places retain their real/complex multiplicities. -/
namespace MasulloGRH

/-- Genuine ideles: units in the full adele ring of the number field. -/
abbrev HeckeIdeleGroup (K : Type*) [Field K] [NumberField K] :=
  (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ

noncomputable def principalIdele (K : Type*) [Field K] [NumberField K] :
    Kˣ →* HeckeIdeleGroup K :=
  Units.map (algebraMap K (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)).toMonoidHom

/-- The genuine idele class group, without an analytic assumption. -/
abbrev HeckeIdeleClassGroup (K : Type*) [Field K] [NumberField K] :=
  HeckeIdeleGroup K ⧸ (principalIdele K).range

/-- All continuous unitary Hecke characters; no restriction on the norm section. -/
def UnitaryHeckeCharacter (K : Type*) [Field K] [NumberField K] :=
  {χ : ContinuousMonoidHom (HeckeIdeleClassGroup K) ℂˣ //
    ∀ x, ‖(χ x : ℂ)‖ = 1}

noncomputable def principalIdelicModulus
    (K : Type*) [Field K] [NumberField K] (x : K) : ℝ :=
  (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) *
    ∏ᶠ w : NumberField.FinitePlace K, w x

/-- The actual product formula kills the principal ideles over every number field.
This is the arithmetic relation required before a norm character can descend. -/
theorem principalIdelicModulus_eq_one
    (K : Type*) [Field K] [NumberField K] (x : K) (hx : x ≠ 0) :
    principalIdelicModulus K x = 1 := by
  exact NumberField.prod_abs_eq_one hx

/-- In particular every real norm parameter is trivial on the principal subgroup. -/
theorem principalNormTwist_eq_one
    (K : Type*) [Field K] [NumberField K] (x : K) (hx : x ≠ 0) (τ : ℝ) :
    Complex.exp ((τ : ℂ) * Complex.I *
      (Real.log (principalIdelicModulus K x) : ℂ)) = 1 := by
  rw [principalIdelicModulus_eq_one K x hx]
  simp

#check principalIdelicModulus_eq_one
#print axioms principalIdelicModulus_eq_one
#check principalNormTwist_eq_one
#print axioms principalNormTwist_eq_one

/-- Insert a local element at one finite place and put one at every other place.
This constructs the actual local-to-global map used by the Hecke Euler factors. -/
noncomputable def finitePlaceInsertion
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    v.adicCompletion K →* NumberField.AdeleRing (NumberField.RingOfIntegers K) K := by
  classical
  exact {
    toFun := fun x => (1, ⟨Pi.mulSingle v x, by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      simp [Pi.mulSingle, hw]⟩)
    map_one' := by
      apply Prod.ext
      · rfl
      · apply IsDedekindDomain.FiniteAdeleRing.ext K
        intro w
        change Pi.mulSingle v (1 : v.adicCompletion K) w = 1
        simp
    map_mul' := by
      intro x y
      apply Prod.ext
      · change (1 : NumberField.InfiniteAdeleRing K) = 1 * 1
        simp
      · apply IsDedekindDomain.FiniteAdeleRing.ext K
        intro w
        change Pi.mulSingle v (x * y) w = Pi.mulSingle v x w * Pi.mulSingle v y w
        exact congrFun (Pi.mulSingle_mul v x y) w }

/-- The genuine local multiplicative group maps to the genuine idele class group. -/
noncomputable def finitePlaceClass
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (v.adicCompletion K)ˣ →* HeckeIdeleClassGroup K :=
  (QuotientGroup.mk' (principalIdele K).range).comp
    (Units.map (finitePlaceInsertion K v))

/-- Local character obtained from the full continuous unitary global character. -/
noncomputable def localHeckeCharacter
    (K : Type*) [Field K] [NumberField K] (χ : UnitaryHeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (v.adicCompletion K)ˣ →* ℂˣ :=
  χ.val.toMonoidHom.comp (finitePlaceClass K v)

/-- Local Euler coefficients have unit norm for every allowed Hecke character. -/
theorem localHeckeCharacter_unitary
    (K : Type*) [Field K] [NumberField K] (χ : UnitaryHeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (x : (v.adicCompletion K)ˣ) :
    ‖(localHeckeCharacter K χ v x : ℂ)‖ = 1 :=
  χ.property (finitePlaceClass K v x)

#check localHeckeCharacter_unitary
#print axioms localHeckeCharacter_unitary

noncomputable def localIntegralUnit
    (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (v.adicCompletionIntegers K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom

/-- Unramified means trivial on the actual local integral units. -/
def HeckeUnramifiedAt
    (K : Type*) [Field K] [NumberField K] (χ : UnitaryHeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) : Prop :=
  ∀ u, localHeckeCharacter K χ v (localIntegralUnit K v u) = 1

/-- A local Euler factor with a specified local parameter. To identify this with
its usual canonical factor, the parameter must be a uniformizer. -/
noncomputable def localEulerFactor
    (K : Type*) [Field K] [NumberField K] (χ : UnitaryHeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (π : (v.adicCompletion K)ˣ) (s : ℂ) : ℂ := by
  classical
  exact if HeckeUnramifiedAt K χ v then
    (1 - (localHeckeCharacter K χ v π : ℂ) *
      Complex.exp (-s * (Real.log (Ideal.absNorm v.asIdeal) : ℂ)))⁻¹
  else 1

/-- The arithmetic Euler factor is independent of multiplying the parameter by
an actual integral unit. This is the local choice-independence obligation. -/
theorem localEulerFactor_mul_integralUnit
    (K : Type*) [Field K] [NumberField K] (χ : UnitaryHeckeCharacter K)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (u : (v.adicCompletionIntegers K)ˣ) (π : (v.adicCompletion K)ˣ) (s : ℂ) :
    localEulerFactor K χ v (localIntegralUnit K v u * π) s =
      localEulerFactor K χ v π s := by
  classical
  unfold localEulerFactor
  split_ifs with h
  · rw [map_mul, h u, one_mul]
  · rfl

#check localEulerFactor_mul_integralUnit
#print axioms localEulerFactor_mul_integralUnit
end MasulloGRH
