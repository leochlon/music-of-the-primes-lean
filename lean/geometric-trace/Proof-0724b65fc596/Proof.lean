import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-! D, round 20; carried from frozen round-13 D: genuine all-number-field idelic input to the Hecke divisor.
This file does not assume an analytic Hecke package. The Euler product,
continuation and divisor theorem remain unproved. -/
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

/-- The principal idele construction really embeds the number field's units. -/
theorem principalIdele_injective : Function.Injective (principalIdele K) := by
  intro x y h
  apply Units.ext
  apply NumberField.AdeleRing.algebraMap_injective (𝓞 K) K
  exact congrArg Units.val h


abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
abbrev LocalField (v : FinitePlace K) := v.adicCompletion K

/-- Insert one local value into the genuine finite adele ring. -/
noncomputable def localFiniteAdele (v : FinitePlace K) (x : LocalField K v) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K := by
  classical
  refine ⟨Function.update (fun _ => 1) v x, ?_⟩
  apply Filter.eventually_cofinite.mpr
  apply Set.Finite.subset (Set.finite_singleton v)
  intro w hw
  by_contra h
  have hwv : w ≠ v := by simpa using h
  exact hw (by simp [Function.update_of_ne hwv])

/-- Local units embed as ideles with all other coordinates equal to one. -/
noncomputable def localIdele (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    HeckeIdeles K where
  val := (1, localFiniteAdele K v x)
  inv := (1, localFiniteAdele K v (↑(x⁻¹)))
  val_inv := by
    apply Prod.ext
    · change (1 : NumberField.InfiniteAdeleRing K) * 1 = 1
      exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro w
      classical
      change Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑x) w *
        Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑(x⁻¹)) w = 1
      classical
      by_cases h : w = v
      · subst w; simp
      · simp [Function.update_of_ne h]
  inv_val := by
    apply Prod.ext
    · change (1 : NumberField.InfiniteAdeleRing K) * 1 = 1
      exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro w
      classical
      change Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑(x⁻¹)) w *
        Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑x) w = 1
      classical
      by_cases h : w = v
      · subst w; simp
      · simp [Function.update_of_ne h]

theorem localIdele_mul (v : FinitePlace K) (x y : (LocalField K v)ˣ) :
    localIdele K v (x * y) = localIdele K v x * localIdele K v y := by
  classical
  apply Units.ext
  apply Prod.ext
  · change (1 : NumberField.InfiniteAdeleRing K) = 1 * 1
    simp
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro w
    change Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑(x*y)) w =
      Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑x) w *
      Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑y) w
    by_cases h : w = v
    · subst w; simp
    · simp [Function.update_of_ne h]


/-- This is the local component of the actual idelic character. -/
noncomputable def localCharacter (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : (LocalField K v)ˣ) : Circle := χ.character (localIdele K v x)

/-- A uniformizer chosen in K and then mapped into its actual completion. -/
noncomputable def localUniformizer (v : FinitePlace K) : (LocalField K v)ˣ :=
  Units.map (algebraMap K (LocalField K v)).toMonoidHom
    (Units.mk0 (Classical.choose (v.valuation_exists_uniformizer K))
      (v.valuation_uniformizer_ne_zero K))

/-- Unramified means trivial on every local valuation unit. -/
def IsUnramified (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) : Prop :=
  ∀ x : (LocalField K v)ˣ, Valued.v (x : LocalField K v) = 1 →
    localCharacter K χ v x = 1

theorem localCharacter_mul (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x y : (LocalField K v)ˣ) :
    localCharacter K χ v (x * y) = localCharacter K χ v x * localCharacter K χ v y := by
  unfold localCharacter
  rw [localIdele_mul]
  exact χ.character.map_mul _ _

/-- The unramified coefficient is unchanged by multiplication by any local unit. -/
theorem unramified_local_invariance (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (hχ : IsUnramified K χ v) (x u : (LocalField K v)ˣ)
    (hu : Valued.v (u : LocalField K v) = 1) :
    localCharacter K χ v (x * u) = localCharacter K χ v x := by
  rw [localCharacter_mul, hχ u hu, mul_one]



theorem localUniformizer_valuation (v : FinitePlace K) :
    Valued.v (localUniformizer K v : LocalField K v) = WithZero.exp (-1) := by
  change Valued.v ((Classical.choose (v.valuation_exists_uniformizer K) : K) :
    LocalField K v) = WithZero.exp (-1)
  rw [v.valuedAdicCompletion_eq_valuation']
  exact Classical.choose_spec (v.valuation_exists_uniformizer K)


noncomputable def heckePrimeCoefficient (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) : ℂ := localCharacter K χ v (localUniformizer K v)

theorem heckePrimeCoefficient_norm (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    ‖heckePrimeCoefficient K χ v‖ = 1 :=
  Circle.norm_coe _

/-- The arithmetic local Euler factor; no convergence is assumed. -/
noncomputable def heckeEulerFactor (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) : ℂ := by
  classical
  exact if IsUnramified K χ v then
    (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

/-- Genuine finite truncations. Identification of a convergent L-function remains open. -/
noncomputable def partialHeckeEulerProduct (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (s : ℂ) : ℂ :=
  ∏ v ∈ S, heckeEulerFactor K χ v s


noncomputable def finiteHeckeL (χ : UnitaryHeckeCharacter K) (s : ℂ) : ℂ :=
  ∏' v : FinitePlace K, heckeEulerFactor K χ v s



end MasulloGRH
/-! A, round 1: discharge the uniformizer-choice premise in the bridge from
the checked finite Euler germ to the TateGlobal continuation lead.
No analytic continuation, completed L-function or zero divisor is defined here. -/
namespace MasulloGRH.Round1A
variable (K : Type*) [Field K] [NumberField K]

/-- The actual unramified coefficient is independent of the chosen local
uniformizer. This discharges the uniformizer-choice part of the Euler bridge. -/
theorem localCharacter_uniformizer_independent
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (hχ : IsUnramified K χ v) (π : (LocalField K v)ˣ)
    (hπ : Valued.v (π : LocalField K v) = WithZero.exp (-1)) :
    localCharacter K χ v π = localCharacter K χ v (localUniformizer K v) := by
  have hu : Valued.v
      (((localUniformizer K v)⁻¹ * π : (LocalField K v)ˣ) : LocalField K v) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀,
      localUniformizer_valuation K v, hπ]
    simp
  simpa using unramified_local_invariance K χ v hχ (localUniformizer K v)
    ((localUniformizer K v)⁻¹ * π) hu

/-- The existing finite Euler product has the zero-coefficient ramification
convention used by the supplied TateGlobal completed-product statement, for
any genuine choice of local uniformizers. This is equality of the same tprod;
outside Re(s)>1 it makes no convergence or continuation assertion. -/
theorem finiteHeckeL_eq_uniformizerEulerProduct
    (χ : UnitaryHeckeCharacter K)
    (π : ∀ v : FinitePlace K, (LocalField K v)ˣ)
    (hπ : ∀ v, Valued.v (π v : LocalField K v) = WithZero.exp (-1)) (s : ℂ) :
    finiteHeckeL K χ s =
      ∏' v : FinitePlace K,
        (1 - (if IsUnramified K χ v then (localCharacter K χ v (π v) : ℂ) else 0) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  unfold finiteHeckeL
  apply tprod_congr
  intro v
  by_cases hv : IsUnramified K χ v
  · simp only [heckeEulerFactor, if_pos hv, heckePrimeCoefficient]
    rw [localCharacter_uniformizer_independent K χ v hv (π v) (hπ v)]
  · simp [heckeEulerFactor, hv]


#check localCharacter_uniformizer_independent
#print axioms localCharacter_uniformizer_independent
#check finiteHeckeL_eq_uniformizerEulerProduct
#print axioms finiteHeckeL_eq_uniformizerEulerProduct
end MasulloGRH.Round1A

/-! Round 2 A: discharge the character-codomain premise of the genuine
finite-to-completed bridge. These are properties of the SAME actual idelic
character. Identification with the unavailable TateGlobal named predicates,
local maps, and analytic continuation remains unresolved. -/
namespace MasulloGRH.Round2A
variable (K : Type*) [Field K] [NumberField K]

/-- Canonical complex-unit-valued form of the actual Circle-valued character. -/
noncomputable def complexUnitCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeles K →* ℂˣ where
  toFun a := Units.mk0 (χ.character a : ℂ) (by
    intro hz
    have h := Circle.norm_coe (χ.character a)
    rw [hz, norm_zero] at h
    exact zero_ne_one h)
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp

/-- Discharges continuity of complex values, unitarity, principal triviality,
and equality of the actual local values for the character-codomain bridge.
It asserts no TateGlobal predicate equality, continuation, divisor or trace. -/
theorem complexUnitCharacter_bridge (χ : UnitaryHeckeCharacter K) :
    Continuous (fun a : HeckeIdeles K => (complexUnitCharacter K χ a : ℂ)) ∧
    (∀ a : HeckeIdeles K, ‖(complexUnitCharacter K χ a : ℂ)‖ = 1) ∧
    (∀ a : Kˣ, complexUnitCharacter K χ (principalIdele K a) = 1) ∧
    (∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (complexUnitCharacter K χ (localIdele K v x) : ℂ) =
        (localCharacter K χ v x : ℂ)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Continuous (fun a : HeckeIdeles K => (χ.character a : ℂ))
    exact continuous_subtype_val.comp χ.character.continuous
  · intro a
    exact Circle.norm_coe (χ.character a)
  · intro a
    apply Units.ext
    change (χ.character (principalIdele K a) : ℂ) = 1
    rw [χ.trivial_on_principal]
    rfl
  · intro v x
    rfl

#check complexUnitCharacter_bridge
#print axioms complexUnitCharacter_bridge
end MasulloGRH.Round2A

/-! Reused exact F53 declarations, needed for the local-integrality bridge. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def integralLocalUnit (v : FinitePlace K)
    (u : (v.adicCompletionIntegers K)ˣ) : (LocalField K v)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u

/-- Actual integral units have normalized valuation one. -/
theorem integralLocalUnit_valuation (v : FinitePlace K)
    (u : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (integralLocalUnit K v u : LocalField K v) = 1 := by
  have hu : Valued.v (integralLocalUnit K v u : LocalField K v) ≤ 1 := u.val.property
  have hi : Valued.v (((integralLocalUnit K v u)⁻¹ : (LocalField K v)ˣ) : LocalField K v) ≤ 1 := u.inv.property
  apply le_antisymm hu
  rw [Units.val_inv_eq_inv_val, map_inv₀] at hi
  have hv0 : Valued.v (integralLocalUnit K v u : LocalField K v) ≠ 0 := by
    simpa only [ne_eq, map_eq_zero] using (Units.ne_zero (integralLocalUnit K v u))
  have hm := mul_le_mul_right hi (Valued.v (integralLocalUnit K v u : LocalField K v))
  simpa [hv0] using hm


end MasulloGRH

/-! Round 3 A: the local-integrality premise of the actual finite Euler germ
to completed Tate product bridge. No external local map or continuation is
assumed to match; these theorems use the actual source ideles throughout. -/
namespace MasulloGRH.Round3A
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the local subgroup normalization premise: valuation-one units
are exactly the units whose value and inverse lie in the valuation integers.
The converse reuses the checked F53 integral-unit valuation theorem. -/
theorem valuation_one_iff_integral_and_inverse_integral
    (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    Valued.v (x : LocalField K v) = 1 ↔
      (x : LocalField K v) ∈ v.adicCompletionIntegers K ∧
      ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ∈ v.adicCompletionIntegers K := by
  constructor
  · intro hx
    constructor
    · change Valued.v (x : LocalField K v) ≤ 1
      exact le_of_eq hx
    · change Valued.v ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  · rintro ⟨hx, hi⟩
    let u : (v.adicCompletionIntegers K)ˣ :=
      { val := ⟨x, hx⟩
        inv := ⟨↑(x⁻¹), hi⟩
        val_inv := by apply Subtype.ext; exact x.val_inv
        inv_val := by apply Subtype.ext; exact x.inv_val }
    exact integralLocalUnit_valuation K v u

/-- Discharges the raw unramified-character predicate premise of the supplied
completed-product lead, in the complex-unit codomain of the SAME character.
Equality to its unavailable named predicate still requires matching local maps. -/
theorem isUnramified_iff_integral_local_trivial
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    IsUnramified K χ v ↔
      ∀ x : (LocalField K v)ˣ,
        (x : LocalField K v) ∈ v.adicCompletionIntegers K →
        ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ∈ v.adicCompletionIntegers K →
        Round2A.complexUnitCharacter K χ (localIdele K v x) = 1 := by
  constructor
  · intro h x hx hi
    apply Units.ext
    change (localCharacter K χ v x : ℂ) = 1
    rw [h x ((valuation_one_iff_integral_and_inverse_integral K v x).mpr ⟨hx, hi⟩)]
    rfl
  · intro h x hx
    obtain ⟨hv, hi⟩ := (valuation_one_iff_integral_and_inverse_integral K v x).mp hx
    apply Circle.ext
    exact congrArg (fun u : ℂˣ => (u : ℂ)) (h x hv hi)

/-- The finite Euler product in the precise raw integral-unit and complex-unit
conventions needed by the continuation interface. Reuses round-one uniformizer
independence. For arbitrary s this is a totalized tprod equality only. -/
theorem finiteHeckeL_eq_integralUnitEulerProduct
    (χ : UnitaryHeckeCharacter K)
    (π : ∀ v : FinitePlace K, (LocalField K v)ˣ)
    (hπ : ∀ v, Valued.v (π v : LocalField K v) = WithZero.exp (-1)) (s : ℂ) :
    finiteHeckeL K χ s =
      ∏' v : FinitePlace K,
        (1 - (if (∀ x : (LocalField K v)ˣ,
            (x : LocalField K v) ∈ v.adicCompletionIntegers K →
            ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ∈ v.adicCompletionIntegers K →
            Round2A.complexUnitCharacter K χ (localIdele K v x) = 1)
          then (Round2A.complexUnitCharacter K χ (localIdele K v (π v)) : ℂ) else 0) *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [Round1A.finiteHeckeL_eq_uniformizerEulerProduct K χ π hπ s]
  apply tprod_congr
  intro v
  rw [← isUnramified_iff_integral_local_trivial K χ v]
  rfl

#check valuation_one_iff_integral_and_inverse_integral
#print axioms valuation_one_iff_integral_and_inverse_integral
#check isUnramified_iff_integral_local_trivial
#print axioms isUnramified_iff_integral_local_trivial
#check finiteHeckeL_eq_integralUnitEulerProduct
#print axioms finiteHeckeL_eq_integralUnitEulerProduct
end MasulloGRH.Round3A

/-! Exact F53 finite-ramification dependency closure, reused solely to supply
the finite exceptional set in the completed-product interface. No new credit
is claimed for these unchanged declarations. -/
namespace MasulloGRH
/-- The right closed semicircle contains no nontrivial power-closed subset. -/
theorem circle_eq_one_of_powers_re_nonneg (z : Circle)
    (h : ∀ n : ℕ, 0 ≤ ((z : ℂ)^n).re) : z = 1 := by
  have hn (n : ℕ) : (((z : ℂ)^n).re)^2 + (((z : ℂ)^n).im)^2 = 1 := by
    have hh : Complex.normSq ((z : ℂ)^n) = 1 := by
      rw [Complex.normSq_eq_norm_sq, norm_pow, Circle.norm_coe]
      simp
    simpa only [Complex.normSq_apply, pow_two] using hh
  have hu (n : ℕ) : ((z : ℂ)^n).re ≤ 1 := by
    have hh := hn n
    have hp := h n
    nlinarith [sq_nonneg (((z : ℂ)^n).im)]
  have hd (n : ℕ) : (2 : ℝ)^n * (1 - (z : ℂ).re) ≤
      1 - ((z : ℂ)^(2^n)).re := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hn (2^n)
      have hp := h (2^n)
      have hup := hu (2^n)
      have hmul : 0 ≤ ((z : ℂ)^(2^n)).re * (1 - ((z : ℂ)^(2^n)).re) :=
        mul_nonneg hp (sub_nonneg.mpr hup)
      rw [pow_succ (2 : ℕ), pow_mul, pow_two, Complex.mul_re, pow_succ (2 : ℝ)]
      nlinarith
  have hre : (z : ℂ).re = 1 := by
    have hle : (z : ℂ).re ≤ 1 := by simpa using hu 1
    by_contra he
    have hp : 0 < 1 - (z : ℂ).re := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact sub_pos.mpr hlt
      · exact (he heq).elim
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt (1 / (1 - (z : ℂ).re)) (by norm_num : (1 : ℝ) < 2)
    have hg : 1 < (2 : ℝ)^n * (1 - (z : ℂ).re) := (div_lt_iff₀ hp).mp hn'
    have hd' := hd n
    have hp' := h (2^n)
    linarith
  apply Circle.ext
  apply Complex.ext
  · simpa using hre
  · have hh := hn 1
    simp only [pow_one] at hh
    rw [hre] at hh
    change (z : ℂ).im = 0
    nlinarith [sq_nonneg (z : ℂ).im]
end MasulloGRH


namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem localCharacter_one (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    localCharacter K χ v 1 = 1 := by
  have hh := localCharacter_mul K χ v 1 1
  apply mul_left_cancel (a := localCharacter K χ v 1)
  simpa only [one_mul, mul_one] using hh.symm

/-- The local no-small-subgroups step in finite ramification of the genuine
idelic character: a valuation-unit image in a semicircle must be trivial. -/
theorem isUnramified_of_local_re_nonneg (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K)
    (h : ∀ x : (LocalField K v)ˣ, Valued.v (x : LocalField K v) = 1 →
      0 ≤ (localCharacter K χ v x : ℂ).re) : IsUnramified K χ v := by
  intro x hx
  apply circle_eq_one_of_powers_re_nonneg
  intro n
  have hp : Valued.v ((x^n : (LocalField K v)ˣ) : LocalField K v) = 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  have he : (localCharacter K χ v (x^n) : ℂ) = (localCharacter K χ v x : ℂ)^n := by
    clear hp
    induction n with
    | zero => simp [localCharacter_one]
    | succ n ih => simp only [pow_succ, localCharacter_mul, Circle.coe_mul, ih]
  rw [← he]
  exact h (x^n) hp

end MasulloGRH

namespace MasulloGRH
open Classical
set_option synthInstance.maxHeartbeats 200000
variable (K : Type*) [Field K] [NumberField K]

noncomputable def integralFiniteAdele (x : ∀ v : FinitePlace K, v.adicCompletionIntegers K) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun v : FinitePlace K => LocalField K v)
    (fun v => (v.adicCompletionIntegers K : Set (LocalField K v))) Filter.cofinite x

noncomputable def integralIdele (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    HeckeIdeles K where
  val := (1, integralFiniteAdele K (fun v => (x v).val))
  inv := (1, integralFiniteAdele K (fun v => (x v).inv))
  val_inv := by
    apply Prod.ext
    · change (1 : NumberField.InfiniteAdeleRing K) * 1 = 1
      exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro v
      change ((x v).val : LocalField K v) * ((x v).inv : LocalField K v) = 1
      exact congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).val_inv
  inv_val := by
    apply Prod.ext
    · change (1 : NumberField.InfiniteAdeleRing K) * 1 = 1
      exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro v
      change ((x v).inv : LocalField K v) * ((x v).val : LocalField K v) = 1
      exact congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).inv_val

theorem integralFiniteAdele_continuous : Continuous (integralFiniteAdele K) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

theorem integralIdele_continuous : Continuous (integralIdele K) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_const.prodMk ((integralFiniteAdele_continuous K).comp
      (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)))
  · exact continuous_const.prodMk ((integralFiniteAdele_continuous K).comp
      (continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)))

theorem integralIdele_one : integralIdele K (fun _ => 1) = 1 := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl

theorem integralIdele_update (v : FinitePlace K) (u : (v.adicCompletionIntegers K)ˣ) :
    integralIdele K (Function.update (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v u) = localIdele K v (integralLocalUnit K v u) := by
  classical
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro w
    change ((Function.update (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v u w).val : LocalField K w) =
      Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (integralLocalUnit K v u).val w
    by_cases h : w = v
    · subst w
      simp [integralLocalUnit]
    · simp [Function.update_of_ne h]

/-- Continuity of the genuine character restricts only finitely many integral-unit coordinates. -/
theorem integral_local_re_pos_cofinite (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S, ∀ u : (v.adicCompletionIntegers K)ˣ,
      0 < (localCharacter K χ v (integralLocalUnit K v u) : ℂ).re := by
  classical
  let f := fun x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ =>
    (χ.character (integralIdele K x) : ℂ).re
  have hf : Continuous f := Complex.continuous_re.comp
    (continuous_subtype_val.comp (χ.character.continuous.comp (integralIdele_continuous K)))
  have ho : IsOpen {x | 0 < f x} := isOpen_lt continuous_const hf
  have hone : (fun v : FinitePlace K => (1 : (v.adicCompletionIntegers K)ˣ)) ∈ {x | 0 < f x} := by
    simp [f, integralIdele_one, map_one]
  obtain ⟨S, U, hU, hsub⟩ := isOpen_pi_iff.mp ho (fun v => 1) hone
  refine ⟨S, fun v hv u => ?_⟩
  have hx : Function.update (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v u ∈ (S : Set (FinitePlace K)).pi U := by
    intro w hw
    have hwv : w ≠ v := by intro he; subst w; exact hv hw
    simpa only [Function.update_of_ne hwv] using (hU w hw).2
  have hh := hsub hx
  change 0 < (χ.character (integralIdele K (Function.update (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v u)) : ℂ).re at hh
  rw [integralIdele_update] at hh
  exact hh

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def valuationUnitAsIntegral (v : FinitePlace K) (x : (LocalField K v)ˣ)
    (hx : Valued.v (x : LocalField K v) = 1) : (v.adicCompletionIntegers K)ˣ where
  val := ⟨x, by change Valued.v (x : LocalField K v) ≤ 1; exact le_of_eq hx⟩
  inv := ⟨↑(x⁻¹), by
    change Valued.v ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]⟩
  val_inv := by
    apply Subtype.ext
    exact x.val_inv
  inv_val := by
    apply Subtype.ext
    exact x.inv_val

theorem integralLocalUnit_valuationUnitAsIntegral (v : FinitePlace K)
    (x : (LocalField K v)ˣ) (hx : Valued.v (x : LocalField K v) = 1) :
    integralLocalUnit K v (valuationUnitAsIntegral K v x hx) = x := by
  apply Units.ext
  rfl

/-- Finite ramification for every genuine continuous unitary idelic Hecke character. -/
theorem finite_ramification (χ : UnitaryHeckeCharacter K) :
    {v : FinitePlace K | ¬ IsUnramified K χ v}.Finite := by
  classical
  obtain ⟨S, hS⟩ := integral_local_re_pos_cofinite K χ
  apply Set.Finite.subset S.finite_toSet
  intro v hv
  by_contra hnot
  apply hv
  apply isUnramified_of_local_re_nonneg K χ v
  intro x hx
  have hp := hS v hnot (valuationUnitAsIntegral K v x hx)
  rw [integralLocalUnit_valuationUnitAsIntegral] at hp
  exact le_of_lt hp

end MasulloGRH

namespace MasulloGRH.Round3A
variable (K : Type*) [Field K] [NumberField K]

/-- The actual local restriction, with its multiplicative structure, supplies
the ramified restriction parameter of the completed-product interface. -/
noncomputable def complexLocalCharacter (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) : (LocalField K v)ˣ →* ℂˣ where
  toFun x := Round2A.complexUnitCharacter K χ (localIdele K v x)
  map_one' := by
    apply Units.ext
    change (localCharacter K χ v 1 : ℂ) = 1
    rw [localCharacter_one]
    rfl
  map_mul' x y := by
    apply Units.ext
    change (localCharacter K χ v (x * y) : ℂ) =
      (localCharacter K χ v x : ℂ) * (localCharacter K χ v y : ℂ)
    rw [localCharacter_mul]
    rfl

/-- Discharges existence of the finite exceptional set and actual ramified
local monoid characters required by the continuation lead. The finite-set
existence itself reuses F53 finite_ramification. No analytic assertion or
identity with unavailable TateGlobal definitions is made. -/
theorem exists_finite_continuation_data (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K),
      (∀ v ∉ S, ∀ x : (LocalField K v)ˣ,
        (x : LocalField K v) ∈ v.adicCompletionIntegers K →
        ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ∈ v.adicCompletionIntegers K →
        Round2A.complexUnitCharacter K χ (localIdele K v x) = 1) ∧
      (∀ v ∈ S, ∀ x : (LocalField K v)ˣ,
        Round2A.complexUnitCharacter K χ (localIdele K v x) =
          complexLocalCharacter K χ v x) ∧
      (∀ v (x : (LocalField K v)ˣ), ‖(complexLocalCharacter K χ v x : ℂ)‖ = 1) := by
  classical
  let S := (finite_ramification K χ).toFinset
  refine ⟨S, ?_, ?_, ?_⟩
  · intro v hv
    apply (isUnramified_iff_integral_local_trivial K χ v).mp
    by_contra hn
    exact hv (by simpa [S] using hn)
  · intro v hv x
    rfl
  · intro v x
    exact Circle.norm_coe (localCharacter K χ v x)

#check exists_finite_continuation_data
#print axioms exists_finite_continuation_data
end MasulloGRH.Round3A

/-! Round 4 A: dual-character Euler bridge. This discharges the identification
of the dual product P' in the supplied completed-functional-equation lead.
No continuation, archimedean normalization, or zero divisor is assumed. -/
namespace MasulloGRH.Round4A
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine inverse idelic character, with the same full parameter scope. -/
noncomputable def dualCharacter (χ : UnitaryHeckeCharacter K) :
    UnitaryHeckeCharacter K where
  character :=
    { toFun := fun a => (χ.character a)⁻¹
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_comm]
      continuous_toFun := χ.character.continuous.inv }
  trivial_on_principal := by
    intro a
    change (χ.character (principalIdele K a))⁻¹ = 1
    rw [χ.trivial_on_principal, inv_one]

/-- Discharges preservation of the ramification set for the dual Euler product. -/
theorem dual_isUnramified_iff (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    IsUnramified K (dualCharacter K χ) v ↔ IsUnramified K χ v := by
  change (∀ x : (LocalField K v)ˣ, Valued.v (x : LocalField K v) = 1 →
    (localCharacter K χ v x)⁻¹ = 1) ↔ _
  simp only [inv_eq_one, IsUnramified]

/-- Discharges complex-unit inverse compatibility in the continuation interface. -/
theorem dual_complexUnitCharacter (χ : UnitaryHeckeCharacter K) (a : HeckeIdeles K) :
    Round2A.complexUnitCharacter K (dualCharacter K χ) a =
      (Round2A.complexUnitCharacter K χ a)⁻¹ := by
  apply Units.ext
  change ((χ.character a)⁻¹ : ℂ) = (χ.character a : ℂ)⁻¹
  simp

/-- The dual product in the completed-functional-equation lead is the existing
finite Hecke Euler product of the actual inverse character. Any genuine local
uniformizers may be used. At arbitrary s this is only a tprod identity;
convergence and its integral meaning use the separately checked Re(s)>1 theorem. -/
theorem finiteHeckeL_dual_eq_inverseEulerProduct
    (χ : UnitaryHeckeCharacter K)
    (π : ∀ v : FinitePlace K, (LocalField K v)ˣ)
    (hπ : ∀ v, Valued.v (π v : LocalField K v) = WithZero.exp (-1)) (s : ℂ) :
    finiteHeckeL K (dualCharacter K χ) s =
      ∏' v : FinitePlace K,
        (1 - (if IsUnramified K χ v then
          (((Round2A.complexUnitCharacter K χ (localIdele K v (π v)))⁻¹ : ℂˣ) : ℂ)
          else 0) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [Round1A.finiteHeckeL_eq_uniformizerEulerProduct K (dualCharacter K χ) π hπ]
  apply tprod_congr
  intro v
  rw [dual_isUnramified_iff]
  congr 3

#check dual_isUnramified_iff
#print axioms dual_isUnramified_iff
#check dual_complexUnitCharacter
#print axioms dual_complexUnitCharacter
#check finiteHeckeL_dual_eq_inverseEulerProduct
#print axioms finiteHeckeL_dual_eq_inverseEulerProduct
end MasulloGRH.Round4A

open scoped Classical
namespace MasulloGRH.Round5A
/-- Exact factor-of-two bridge between Mathlib's complex Gamma factor and
Chapter 3's factor. Discharges the archimedean normalization premise. -/
theorem gammaComplex_manuscript_factor (s : ℂ) :
    Complex.Gammaℂ s = 2 * (((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) := by
  rw [Complex.Gammaℂ_def, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- Discharges the constant normalization of all genuine complex places. -/
theorem complexGamma_product_normalization {ι : Type*} (S : Finset ι) (w : ι → ℂ) :
    (∏ v ∈ S, Complex.Gammaℂ (w v)) =
      (2 : ℂ) ^ S.card * ∏ v ∈ S,
        (((2 * Real.pi : ℝ) : ℂ) ^ (-w v) * Complex.Gamma (w v)) := by
  simp only [gammaComplex_manuscript_factor, Finset.prod_mul_distrib, Finset.prod_const]

/-- CONDITIONAL divisor bridge: a nonzero normalization constant preserves
all meromorphic zero/pole orders, including multiplicities. No zero list is
assumed. This supplies the scalar step used by the archimedean bridge below. -/
theorem normalization_preserves_meromorphic_order (f : ℂ → ℂ) (c s : ℂ)
    (hc : c ≠ 0) (hf : MeromorphicAt f s) :
    meromorphicOrderAt (fun z => c * f z) s = meromorphicOrderAt f s := by
  have hm := meromorphicOrderAt_mul ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) s).meromorphicAt) hf
  change meromorphicOrderAt (fun z => c * f z) s = _ at hm
  rw [hm, meromorphicOrderAt_const, if_neg hc, zero_add]

#check gammaComplex_manuscript_factor
#print axioms gammaComplex_manuscript_factor
#check complexGamma_product_normalization
#print axioms complexGamma_product_normalization
#check normalization_preserves_meromorphic_order
#print axioms normalization_preserves_meromorphic_order

open NumberField
variable (K : Type*) [Field K] [NumberField K]

/-- The exact Gamma product appearing in the supplied continuation lead. -/
noncomputable def leadGammaProduct (τ : InfinitePlace K → ℝ)
    (m : InfinitePlace K → ℤ) (s : ℂ) : ℂ := by
  classical
  exact ∏ v : InfinitePlace K,
    if v.IsReal then Complex.Gammaℝ (s + (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
    else Complex.Gammaℂ (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)

/-- Chapter 3's displayed Gamma factors, with the same local arguments.
Identification of τ and m with the actual character is a separate premise. -/
noncomputable def manuscriptGammaProduct (τ : InfinitePlace K → ℝ)
    (m : InfinitePlace K → ℤ) (s : ℂ) : ℂ := by
  classical
  exact ∏ v : InfinitePlace K,
    if v.IsReal then Complex.Gammaℝ (s + (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
    else (((2 * Real.pi : ℝ) : ℂ) ^
      (-(s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)) *
      Complex.Gamma (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2))

/-- Discharges the exact scalar mismatch in the archimedean completion:
one factor 2 for each genuine nonreal infinite place, for all τ, m and s. -/
theorem gammaProduct_normalization (τ : InfinitePlace K → ℝ)
    (m : InfinitePlace K → ℤ) (s : ℂ) :
    leadGammaProduct K τ m s =
      (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2) *
      manuscriptGammaProduct K τ m s := by
  classical
  unfold leadGammaProduct manuscriptGammaProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases h : v.IsReal
  · simp only [if_pos h, one_mul]
  · simp only [if_neg h, gammaComplex_manuscript_factor]

/-- CONDITIONAL completed-divisor bridge, at every complex point, for every
number field and all real norm-shift/integer angular parameters. A genuine
meromorphic continuation f can be inserted without defining a new L-function.
The sole analytic hypothesis is local meromorphicity of its manuscript
completion. This removes the factor-of-two ambiguity for zero/pole orders. -/
theorem completedGamma_normalization_preserves_divisor
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt (fun z => manuscriptGammaProduct K τ m z * f z) s) :
    meromorphicOrderAt (fun z => leadGammaProduct K τ m z * f z) s =
      meromorphicOrderAt (fun z => manuscriptGammaProduct K τ m z * f z) s := by
  classical
  have hC : (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    split_ifs <;> norm_num
  have heq : (fun z => leadGammaProduct K τ m z * f z) =
      (fun z => (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2) *
        (manuscriptGammaProduct K τ m z * f z)) := by
    funext z
    rw [gammaProduct_normalization]
    ring
  rw [heq]
  exact normalization_preserves_meromorphic_order _ _ _ hC hf

#check gammaProduct_normalization
#print axioms gammaProduct_normalization
#check completedGamma_normalization_preserves_divisor
#print axioms completedGamma_normalization_preserves_divisor
end MasulloGRH.Round5A

open Filter Topology
namespace MasulloGRH.Round6A
/-- Discharges uniqueness of an entire continuation from the Euler half-plane.
This proves uniqueness only; existence and the genuine character bridge remain separate. -/
theorem entire_eq_of_rightHalfPlane (F G : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h : ∀ s : ℂ, 1 < s.re → F s = G s) : F = G := by
  have hloc : F =ᶠ[𝓝 (2 : ℂ)] G := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have htwo : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    exact (hopen.eventually_mem htwo).mono (fun z hz => h z hz)
  have haF : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have haG : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  have heq := haF.eqOn_of_preconnected_of_eventuallyEq haG
    isPreconnected_univ (Set.mem_univ (2 : ℂ)) hloc
  exact funext (fun z => heq (Set.mem_univ z))
#check entire_eq_of_rightHalfPlane
#print axioms entire_eq_of_rightHalfPlane
end MasulloGRH.Round6A

namespace MasulloGRH.Round6A
open NumberField
variable (K : Type*) [Field K] [NumberField K]

/-- CONDITIONAL continuation bridge. Two entire pole-cleared candidates attached
on Re(s)>1 to the actual finiteHeckeL and the two audited Gamma conventions
agree globally up to the known normalization. The factor p is supplied; use 1
for non-norm characters and the correctly signed quadratic for norm twists.
No candidate existence, character parameter identification, or pole assertion
is built into this auxiliary. It discharges uniqueness after those bridges. -/
theorem entire_completedEuler_normalization
    (χ : UnitaryHeckeCharacter K) (τ : InfinitePlace K → ℝ)
    (m : InfinitePlace K → ℤ) (p F G : ℂ → ℂ) (A : ℂ)
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFr : ∀ z : ℂ, 1 < z.re →
      F z = A * (p z * (Round5A.leadGammaProduct K τ m z * finiteHeckeL K χ z)))
    (hGr : ∀ z : ℂ, 1 < z.re →
      G z = p z * (Round5A.manuscriptGammaProduct K τ m z * finiteHeckeL K χ z)) :
    F = fun z =>
      (A * (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2)) * G z := by
  classical
  apply entire_eq_of_rightHalfPlane _ _ hF ((differentiable_const _).mul hG)
  intro z hz
  change F z = (A * (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2)) * G z
  rw [hFr z hz, hGr z hz, Round5A.gammaProduct_normalization]
  ring

/-- CONDITIONAL divisor uniqueness of the reconstructed completions F/p and G/p.
The equality includes all meromorphic zero/pole multiplicities, at every point,
without choosing a zero sequence. It discharges the uniqueness premise of the
finite-Euler-germ to genuine completed-divisor bridge, including pole clearing.
Existence and identification of actual completed functions remain unresolved. -/
theorem completedEuler_divisor_unique
    (χ : UnitaryHeckeCharacter K) (τ : InfinitePlace K → ℝ)
    (m : InfinitePlace K → ℤ) (p F G : ℂ → ℂ) (A : ℂ) (hA : A ≠ 0)
    (hp : Differentiable ℂ p) (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFr : ∀ z : ℂ, 1 < z.re →
      F z = A * (p z * (Round5A.leadGammaProduct K τ m z * finiteHeckeL K χ z)))
    (hGr : ∀ z : ℂ, 1 < z.re →
      G z = p z * (Round5A.manuscriptGammaProduct K τ m z * finiteHeckeL K χ z))
    (s : ℂ) :
    meromorphicOrderAt (fun z => F z / p z) s =
      meromorphicOrderAt (fun z => G z / p z) s := by
  classical
  have heq := entire_completedEuler_normalization K χ τ m p F G A hF hG hFr hGr
  have hC : (A * (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2)) ≠ 0 := by
    apply mul_ne_zero hA
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    split_ifs <;> norm_num
  have hm : MeromorphicAt (fun z => G z / p z) s :=
    (hG.analyticAt s).meromorphicAt.div (hp.analyticAt s).meromorphicAt
  have hfun : (fun z => F z / p z) =
      (fun z => (A * (∏ v : InfinitePlace K, if v.IsReal then (1 : ℂ) else 2)) *
        (G z / p z)) := by
    funext z
    rw [congrFun heq z]
    ring
  rw [hfun]
  exact Round5A.normalization_preserves_meromorphic_order _ _ _ hC hm

#check entire_completedEuler_normalization
#print axioms entire_completedEuler_normalization
#check completedEuler_divisor_unique
#print axioms completedEuler_divisor_unique
end MasulloGRH.Round6A

namespace MasulloGRH.Round6A
/-- Discharges the admissibility of the lead's exact norm-twist pole-clearing
quadratic: it is entire and never vanishes on the Euler half-plane. This does
not assert either root is an actual pole of a completed Hecke L-function. -/
theorem normTwist_clearingFactor_entire_and_ne_zero (τ : ℝ) :
    Differentiable ℂ (fun z : ℂ =>
      (z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I))) ∧
    ∀ z : ℂ, 1 < z.re →
      (z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I)) ≠ 0 := by
  constructor
  · fun_prop
  · intro z hz
    apply mul_ne_zero
    · intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    · intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
#check normTwist_clearingFactor_entire_and_ne_zero
#print axioms normTwist_clearingFactor_entire_and_ne_zero
end MasulloGRH.Round6A

open Filter Topology
namespace MasulloGRH.Round7A
/-- CONDITIONAL local divisor calculation. Discharges the simple-pole premise
for reconstruction from an entire cleared numerator at a simple clearing root.
The required nonzero numerator value must be proved for the genuine L-function. -/
theorem quadratic_reconstruction_simple_pole (F : ℂ → ℂ) (a b : ℂ)
    (hF : Differentiable ℂ F) (hab : a ≠ b) (hFa : F a ≠ 0) :
    meromorphicOrderAt (fun z => F z / ((z - a) * (z - b))) a = -1 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z - a) a := analyticAt_id.sub analyticAt_const
  have hb : AnalyticAt ℂ (fun z : ℂ => z - b) a := analyticAt_id.sub analyticAt_const
  have hm : MeromorphicAt (fun z => F z / ((z - a) * (z - b))) a :=
    (hF.analyticAt a).meromorphicAt.div (ha.mul hb).meromorphicAt
  change meromorphicOrderAt (fun z => F z / ((z - a) * (z - b))) a = ((-1 : ℤ) : WithTop ℤ)
  apply (meromorphicOrderAt_eq_int_iff hm).2
  refine ⟨fun z => F z / (z - b),
    (hF.analyticAt a).div hb (sub_ne_zero.mpr hab),
    div_ne_zero hFa (sub_ne_zero.mpr hab), Filter.Eventually.of_forall ?_⟩
  intro z
  simp only [zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- CONDITIONAL exact pole locations and multiplicities for the lead's clearing
quadratic, all real norm parameters. With manuscript convention t0 = -t,
these points are i*t0 and 1+i*t0. No existence or nonzero residue is assumed
silently: the entire numerator and both nonzero values are explicit. -/
theorem normTwist_reconstructed_simple_poles (F : ℂ → ℂ) (t : ℝ)
    (hF : Differentiable ℂ F)
    (h0 : F (-((t : ℂ) * Complex.I)) ≠ 0)
    (h1 : F (1 - (t : ℂ) * Complex.I) ≠ 0) :
    meromorphicOrderAt (fun z => F z /
      ((z + (t : ℂ) * Complex.I) * (z - (1 - (t : ℂ) * Complex.I))))
      (-((t : ℂ) * Complex.I)) = -1 ∧
    meromorphicOrderAt (fun z => F z /
      ((z + (t : ℂ) * Complex.I) * (z - (1 - (t : ℂ) * Complex.I))))
      (1 - (t : ℂ) * Complex.I) = -1 := by
  have hab : -((t : ℂ) * Complex.I) ≠ 1 - (t : ℂ) * Complex.I := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
  constructor
  · simpa only [sub_neg_eq_add] using
      quadratic_reconstruction_simple_pole F _ _ hF hab h0
  · have h := quadratic_reconstruction_simple_pole F _ _ hF hab.symm h1
    simpa only [sub_neg_eq_add, mul_comm] using h

/-- Discharges the no-extra-divisor premise away from the two clearing roots.
An analytic nonvanishing denominator preserves every zero/pole multiplicity. -/
theorem quadratic_reconstruction_order_away (F : ℂ → ℂ) (a b s : ℂ)
    (ha : s ≠ a) (hb : s ≠ b) :
    meromorphicOrderAt (fun z => F z / ((z - a) * (z - b))) s =
      meromorphicOrderAt F s := by
  have hden : AnalyticAt ℂ (fun z : ℂ => (z - a) * (z - b)) s :=
    (analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const)
  have hn : (s - a) * (s - b) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)
  have h := meromorphicOrderAt_mul_of_ne_zero (f := F) (hden.inv hn) (inv_ne_zero hn)
  simpa only [Pi.mul_apply, div_eq_mul_inv, mul_comm] using h

/-- CONDITIONAL complete effect of the actual lead clearing factor on the
reconstructed divisor: simple poles at its two roots if the supplied entire
numerator is nonzero there, and unchanged orders everywhere else. This is
an analytic reconstruction lemma, not a definition of the genuine L-function. -/
theorem normTwist_reconstruction_divisor (F : ℂ → ℂ) (t : ℝ)
    (hF : Differentiable ℂ F)
    (h0 : F (-((t : ℂ) * Complex.I)) ≠ 0)
    (h1 : F (1 - (t : ℂ) * Complex.I) ≠ 0) :
    (meromorphicOrderAt (fun z => F z /
      ((z + (t : ℂ) * Complex.I) * (z - (1 - (t : ℂ) * Complex.I))))
      (-((t : ℂ) * Complex.I)) = -1 ∧
    meromorphicOrderAt (fun z => F z /
      ((z + (t : ℂ) * Complex.I) * (z - (1 - (t : ℂ) * Complex.I))))
      (1 - (t : ℂ) * Complex.I) = -1) ∧
    ∀ s : ℂ, s ≠ -((t : ℂ) * Complex.I) → s ≠ 1 - (t : ℂ) * Complex.I →
      meromorphicOrderAt (fun z => F z /
        ((z + (t : ℂ) * Complex.I) * (z - (1 - (t : ℂ) * Complex.I)))) s =
        meromorphicOrderAt F s := by
  refine ⟨normTwist_reconstructed_simple_poles F t hF h0 h1, ?_⟩
  intro s hs0 hs1
  simpa only [sub_neg_eq_add] using quadratic_reconstruction_order_away F _ _ s hs0 hs1

#check quadratic_reconstruction_order_away
#print axioms quadratic_reconstruction_order_away
#check normTwist_reconstruction_divisor
#print axioms normTwist_reconstruction_divisor
#check quadratic_reconstruction_simple_pole
#print axioms quadratic_reconstruction_simple_pole
#check normTwist_reconstructed_simple_poles
#print axioms normTwist_reconstructed_simple_poles
end MasulloGRH.Round7A
