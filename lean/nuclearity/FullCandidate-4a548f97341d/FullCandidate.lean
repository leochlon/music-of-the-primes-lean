import Mathlib
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

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

#check principalIdele_injective
#print axioms principalIdele_injective

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

#check localIdele_mul
#print axioms localIdele_mul

/-- This is the local component of the actual idelic character. -/
noncomputable def localCharacter (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : (LocalField K v)ˣ) : Circle := χ.character (localIdele K v x)

#check localIdele
#print axioms localIdele
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

#check unramified_local_invariance
#print axioms unramified_local_invariance


end MasulloGRH
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
#check circle_eq_one_of_powers_re_nonneg
#print axioms circle_eq_one_of_powers_re_nonneg
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

#check localCharacter_one
#print axioms localCharacter_one
#check isUnramified_of_local_re_nonneg
#print axioms isUnramified_of_local_re_nonneg
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

noncomputable def integralLocalUnit (v : FinitePlace K)
    (u : (v.adicCompletionIntegers K)ˣ) : (LocalField K v)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u

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

#check integralFiniteAdele_continuous
#print axioms integralFiniteAdele_continuous
#check integralIdele_continuous
#print axioms integralIdele_continuous
#check integral_local_re_pos_cofinite
#print axioms integral_local_re_pos_cofinite
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

#check integralLocalUnit_valuationUnitAsIntegral
#print axioms integralLocalUnit_valuationUnitAsIntegral
#check finite_ramification
#print axioms finite_ramification
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem integralLocalCharacter_continuous (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) :
    Continuous (fun u : (v.adicCompletionIntegers K)ˣ =>
      localCharacter K χ v (integralLocalUnit K v u)) := by
  classical
  have hc : Continuous (fun u : (v.adicCompletionIntegers K)ˣ =>
      χ.character (integralIdele K (Function.update
        (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v u))) := by
    apply χ.character.continuous.comp
    apply (integralIdele_continuous K).comp
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · subst w
      simpa using (continuous_id : Continuous (fun u : (v.adicCompletionIntegers K)ˣ => u))
    · simpa only [Function.update_of_ne hw] using
        (continuous_const : Continuous (fun _ : (v.adicCompletionIntegers K)ˣ =>
          (1 : (w.adicCompletionIntegers K)ˣ)))
  simpa only [integralIdele_update, localCharacter] using hc

/-- Powers stay in the same actual finite-place congruence ball. -/
theorem localUnit_power_sub_one_le (v : FinitePlace K)
    (x : (LocalField K v)ˣ) (hx : Valued.v (x : LocalField K v) = 1) (n : ℕ) :
    Valued.v (((x ^ n : (LocalField K v)ˣ) : LocalField K v) - 1) ≤
      Valued.v ((x : LocalField K v) - 1) := by
  change Valued.v ((x : LocalField K v)^n - 1) ≤ _
  induction n with
  | zero => simp
  | succ n ih =>
    have he : (x : LocalField K v)^(n+1) - 1 =
        ((x : LocalField K v)^n - 1) * (x : LocalField K v) +
          ((x : LocalField K v) - 1) := by ring
    rw [he]
    exact (Valued.v.map_add _ _).trans (max_le
      (by simpa only [map_mul, hx, mul_one] using ih) le_rfl)

/-- A genuine local congruence ball mapped into a semicircle is in the kernel.
The radius-existence step from continuity remains to be proved. -/
theorem localCharacter_trivial_on_congruence_of_re_nonneg
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (r : WithZero (Multiplicative ℤ))
    (hr : ∀ y : (LocalField K v)ˣ, Valued.v (y : LocalField K v) = 1 →
      Valued.v ((y : LocalField K v) - 1) < r →
      0 ≤ (localCharacter K χ v y : ℂ).re)
    (x : (LocalField K v)ˣ) (hx : Valued.v (x : LocalField K v) = 1)
    (hxr : Valued.v ((x : LocalField K v) - 1) < r) :
    localCharacter K χ v x = 1 := by
  apply circle_eq_one_of_powers_re_nonneg
  intro n
  have hp : Valued.v ((x ^ n : (LocalField K v)ˣ) : LocalField K v) = 1 := by
    simp only [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  have hn := hr (x ^ n) hp ((localUnit_power_sub_one_le K v x hx n).trans_lt hxr)
  have he : (localCharacter K χ v (x ^ n) : ℂ) =
      (localCharacter K χ v x : ℂ) ^ n := by
    clear hp hn
    induction n with
    | zero => simp [localCharacter_one]
    | succ n ih => simp only [pow_succ, localCharacter_mul, Circle.coe_mul, ih]
  rwa [he] at hn

#check integralLocalCharacter_continuous
#print axioms integralLocalCharacter_continuous
#check localUnit_power_sub_one_le
#print axioms localUnit_power_sub_one_le
#check localCharacter_trivial_on_congruence_of_re_nonneg
#print axioms localCharacter_trivial_on_congruence_of_re_nonneg
end MasulloGRH

namespace MasulloGRH
open Topology Filter
variable (K : Type*) [Field K] [NumberField K]

noncomputable def integralUnitOfValuationOne (v : FinitePlace K)
    (x : {x : LocalField K v // Valued.v x = 1}) : (v.adicCompletionIntegers K)ˣ where
  val := ⟨x.val, le_of_eq x.property⟩
  inv := ⟨x.val⁻¹, by change Valued.v x.val⁻¹ ≤ 1; rw [map_inv₀, x.property, inv_one]⟩
  val_inv := by
    apply Subtype.ext
    exact mul_inv_cancel₀ (by intro h; have hh := x.property; rw [h, map_zero] at hh; exact zero_ne_one hh)
  inv_val := by
    apply Subtype.ext
    exact inv_mul_cancel₀ (by intro h; have hh := x.property; rw [h, map_zero] at hh; exact zero_ne_one hh)

theorem integralUnitOfValuationOne_continuous (v : FinitePlace K) :
    Continuous (integralUnitOfValuationOne K v) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val.subtype_mk _
  · apply Continuous.subtype_mk
    apply continuous_subtype_val.inv₀
    intro x h
    have hh := x.property
    rw [h, map_zero] at hh
    exact zero_ne_one hh

/-- Every genuine finite local character has an actual congruence ball in its kernel. -/
theorem localCharacter_exists_trivial_congruence
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    ∃ r : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : (LocalField K v)ˣ, Valued.v (x : LocalField K v) = 1 →
        Valued.v ((x : LocalField K v) - 1) < (r : WithZero (Multiplicative ℤ)) →
        localCharacter K χ v x = 1 := by
  let f := fun x : {x : LocalField K v // Valued.v x = 1} =>
    (localCharacter K χ v (integralLocalUnit K v (integralUnitOfValuationOne K v x)) : ℂ).re
  have hf : Continuous f := Complex.continuous_re.comp
    (continuous_subtype_val.comp ((integralLocalCharacter_continuous K χ v).comp
      (integralUnitOfValuationOne_continuous K v)))
  let e : {x : LocalField K v // Valued.v x = 1} := ⟨1, map_one _⟩
  have he : f e = 1 := by
    have hh : integralLocalUnit K v (integralUnitOfValuationOne K v e) = 1 := by
      apply Units.ext
      rfl
    simp [f, hh, localCharacter_one]
  have hn : {x | 0 < f x} ∈ 𝓝 e := (isOpen_lt continuous_const hf).mem_nhds (by simp [he])
  rw [nhds_subtype_eq_comap] at hn
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hn
  obtain ⟨r, hr⟩ := Valued.mem_nhds.mp hU
  refine ⟨r, fun x hx hxr => localCharacter_trivial_on_congruence_of_re_nonneg K χ v r ?_ x hx hxr⟩
  intro y hy hyr
  have hmem : (y : LocalField K v) ∈ U := hr hyr
  have hp := hsub (show (⟨(y : LocalField K v), hy⟩ : {x : LocalField K v // Valued.v x = 1}) ∈ Subtype.val ⁻¹' U from hmem)
  have hh : integralLocalUnit K v (integralUnitOfValuationOne K v ⟨(y : LocalField K v), hy⟩) = y := by
    apply Units.ext
    rfl
  change 0 < (localCharacter K χ v (integralLocalUnit K v (integralUnitOfValuationOne K v ⟨(y : LocalField K v), hy⟩)) : ℂ).re at hp
  rw [hh] at hp
  exact le_of_lt hp

#check integralUnitOfValuationOne_continuous
#print axioms integralUnitOfValuationOne_continuous
#check localCharacter_exists_trivial_congruence
#print axioms localCharacter_exists_trivial_congruence
end MasulloGRH

namespace MasulloGRH
open Topology Filter
variable (K : Type*) [Field K] [NumberField K]

theorem localCharacter_isOpen_kernel (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    IsOpen {x : (LocalField K v)ˣ | localCharacter K χ v x = 1} := by
  let ψ : (LocalField K v)ˣ →* Circle :=
    { toFun := localCharacter K χ v
      map_one' := localCharacter_one K χ v
      map_mul' := localCharacter_mul K χ v }
  change IsOpen (ψ.ker : Set (LocalField K v)ˣ)
  apply ψ.ker.isOpen_of_mem_nhds (g := 1)
  obtain ⟨r, hr⟩ := localCharacter_exists_trivial_congruence K χ v
  have hA : {x : LocalField K v | Valued.v x = 1} ∈ 𝓝 (1 : LocalField K v) := by
    exact (Valued.isClopen_sphere (LocalField K v) (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen.mem_nhds (by simp)
  have hB : {x : LocalField K v | Valued.v (x - 1) < (r : WithZero (Multiplicative ℤ))} ∈ 𝓝 (1 : LocalField K v) :=
    Valued.mem_nhds.mpr ⟨r, Set.Subset.refl _⟩
  have h := (Units.continuous_val.continuousAt (x := (1 : (LocalField K v)ˣ))).preimage_mem_nhds (inter_mem hA hB)
  apply Filter.mem_of_superset h
  intro x hx
  exact hr x hx.1 hx.2

#check localCharacter_isOpen_kernel
#print axioms localCharacter_isOpen_kernel
end MasulloGRH

namespace MasulloGRH
open Topology Filter
variable (K : Type*) [Field K] [NumberField K]

/-- Genuine finite-place characters are locally constant on the whole local unit group. -/
theorem localCharacter_isLocallyConstant (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    IsLocallyConstant (localCharacter K χ v) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hker : {u : (LocalField K v)ˣ | localCharacter K χ v u = 1} ∈ 𝓝 (1 : (LocalField K v)ˣ) :=
    (localCharacter_isOpen_kernel K χ v).mem_nhds (localCharacter_one K χ v)
  have hn : {y : (LocalField K v)ˣ | localCharacter K χ v (x⁻¹ * y) = 1} ∈ 𝓝 x := by
    have hh : {u : (LocalField K v)ˣ | localCharacter K χ v u = 1} ∈ 𝓝 (x⁻¹ * x) := by
      simpa using hker
    exact (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds hh
  filter_upwards [hn] with y hy
  have h := localCharacter_mul K χ v x (x⁻¹ * y)
  simpa only [mul_inv_cancel_left, hy, mul_one] using h

#check localCharacter_isLocallyConstant
#print axioms localCharacter_isLocallyConstant
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem valuationOneLocalUnit_continuous (v : FinitePlace K) :
    Continuous (fun x : {x : LocalField K v // Valued.v x = 1} =>
      integralLocalUnit K v (integralUnitOfValuationOne K v x)) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_subtype_val
  · apply continuous_subtype_val.inv₀
    intro x h
    have hh := x.property
    rw [h, map_zero] at hh
    exact zero_ne_one hh

/-- The actual inverse-character shell test extended to the additive local field. -/
noncomputable def ramifiedAdditiveTest (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    LocallyConstant (LocalField K v) ℂ := by
  classical
  let S : Set (LocalField K v) := {x | Valued.v x = 1}
  have hs : IsClopen S := Valued.isClopen_sphere (LocalField K v)
    (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)
  let f : LocallyConstant S ℂ := ⟨fun x =>
    (localCharacter K χ v (integralLocalUnit K v (integralUnitOfValuationOne K v x)) : ℂ)⁻¹,
    ((localCharacter_isLocallyConstant K χ v).comp_continuous
      (valuationOneLocalUnit_continuous K v)).comp (fun z : Circle => (z : ℂ)⁻¹)⟩
  exact LocallyConstant.piecewise hs.isClosed hs.compl.isClosed (Set.union_compl_self S)
    f (LocallyConstant.const ↥(Sᶜ : Set (LocalField K v)) (0 : ℂ)) (fun _ hx => (hx.2 hx.1).elim)

theorem ramifiedAdditiveTest_eq_inverse (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : (LocalField K v)ˣ) (hx : Valued.v (x : LocalField K v) = 1) :
    ramifiedAdditiveTest K χ v (x : LocalField K v) = (localCharacter K χ v x : ℂ)⁻¹ := by
  classical
  change (if h : Valued.v (x : LocalField K v) = 1 then
    (localCharacter K χ v (integralLocalUnit K v
      (integralUnitOfValuationOne K v ⟨(x : LocalField K v), h⟩)) : ℂ)⁻¹ else 0) = _
  rw [dif_pos hx]
  have hh : integralLocalUnit K v
      (integralUnitOfValuationOne K v ⟨(x : LocalField K v), hx⟩) = x := by
    apply Units.ext
    rfl
  rw [hh]

theorem ramifiedAdditiveTest_zero_off_shell (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : LocalField K v) (hx : Valued.v x ≠ 1) : ramifiedAdditiveTest K χ v x = 0 := by
  classical
  change (if h : Valued.v x = 1 then
    (localCharacter K χ v (integralLocalUnit K v
      (integralUnitOfValuationOne K v ⟨x, h⟩)) : ℂ)⁻¹ else 0) = 0
  rw [dif_neg hx]

#check valuationOneLocalUnit_continuous
#print axioms valuationOneLocalUnit_continuous
#check ramifiedAdditiveTest
#print axioms ramifiedAdditiveTest
#check ramifiedAdditiveTest_eq_inverse
#print axioms ramifiedAdditiveTest_eq_inverse
#check ramifiedAdditiveTest_zero_off_shell
#print axioms ramifiedAdditiveTest_zero_off_shell
end MasulloGRH


namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The full integral ball, with value one also at zero. -/
noncomputable def unramifiedAdditiveTest (v : FinitePlace K) :
    LocallyConstant (LocalField K v) ℂ := by
  classical
  let S : Set (LocalField K v) := {x | Valued.v x ≤ 1}
  have hs : IsClopen S := Valued.isClopen_closedBall (LocalField K v)
    (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)
  exact LocallyConstant.piecewise hs.isClosed hs.compl.isClosed (Set.union_compl_self S)
    (LocallyConstant.const S (1 : ℂ))
    (LocallyConstant.const ↥(Sᶜ : Set (LocalField K v)) (0 : ℂ))
    (fun _ hx => (hx.2 hx.1).elim)

theorem unramifiedAdditiveTest_apply (v : FinitePlace K) (x : LocalField K v) :
    unramifiedAdditiveTest K v x = if Valued.v x ≤ 1 then (1 : ℂ) else 0 := by
  classical
  change (if _h : Valued.v x ≤ 1 then (1 : ℂ) else 0) = _
  split_ifs <;> rfl

/-- The actual local additive test used in the finite Hecke Euler integral. -/
noncomputable def finiteAdditiveTest (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    LocallyConstant (LocalField K v) ℂ := by
  classical
  exact if IsUnramified K χ v then unramifiedAdditiveTest K v else ramifiedAdditiveTest K χ v

attribute [local instance] Classical.propDecidable

/-- Restriction is exactly the integral-ball / inverse-unit-character test. -/
theorem finiteAdditiveTest_restrict (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : (LocalField K v)ˣ) :
    finiteAdditiveTest K χ v (x : LocalField K v) =
      if IsUnramified K χ v then
        (if Valued.v (x : LocalField K v) ≤ 1 then 1 else 0)
      else (if Valued.v (x : LocalField K v) = 1 then
        (localCharacter K χ v x : ℂ)⁻¹ else 0) := by
  classical
  by_cases hχ : IsUnramified K χ v
  · simp only [finiteAdditiveTest, if_pos hχ]
    by_cases hx : Valued.v (x : LocalField K v) ≤ 1
    · simpa [hx] using unramifiedAdditiveTest_apply K v (x : LocalField K v)
    · simpa [hx] using unramifiedAdditiveTest_apply K v (x : LocalField K v)
  · simp only [finiteAdditiveTest, if_neg hχ]
    by_cases hx : Valued.v (x : LocalField K v) = 1
    · rw [if_pos hx]
      exact ramifiedAdditiveTest_eq_inverse K χ v x hx
    · rw [if_neg hx]
      exact ramifiedAdditiveTest_zero_off_shell K χ v x hx

/-- These actual tests are the standard integral-ball test at almost every finite place. -/
theorem finiteAdditiveTest_finite_exceptional_set (χ : UnitaryHeckeCharacter K) :
    {v : FinitePlace K | finiteAdditiveTest K χ v ≠ unramifiedAdditiveTest K v}.Finite := by
  classical
  apply (finite_ramification K χ).subset
  intro v hv hχ
  exact hv (by simp only [finiteAdditiveTest, if_pos hχ])

#check unramifiedAdditiveTest
#print axioms unramifiedAdditiveTest
#check unramifiedAdditiveTest_apply
#print axioms unramifiedAdditiveTest_apply
#check finiteAdditiveTest_restrict
#print axioms finiteAdditiveTest_restrict
#check finiteAdditiveTest_finite_exceptional_set
#print axioms finiteAdditiveTest_finite_exceptional_set
end MasulloGRH

/- Round-35 review integration. The following arithmetic/Haar construction is
   E round-33 exact checked source, db893bcbb26c4d01a599be08216b5750,
   renamed into ReviewHaar to avoid incompatible same-named peer declarations. -/
open scoped NumberField
open MeasureTheory


/-! Round 36: the genuine finite-adelic additive test. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

abbrev FiniteAdeles := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

def integralFiniteAdeles : Set (FiniteAdeles K) :=
  {a | ∀ v : FinitePlace K, Valued.v (a v) ≤ 1}

theorem integralFiniteAdeles_eq_range :
    integralFiniteAdeles K = Set.range (integralFiniteAdele K) := by
  ext a
  constructor
  · intro ha
    refine ⟨fun v => ⟨a v, ha v⟩, ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl
  · rintro ⟨b, rfl⟩
    exact fun v => (b v).property

theorem integralFiniteAdeles_isClopen : IsClopen (integralFiniteAdeles K) := by
  constructor
  · have he : integralFiniteAdeles K =
        ⋂ v : FinitePlace K, {a : FiniteAdeles K | Valued.v (a v) ≤ 1} := by
      ext a
      simp [integralFiniteAdeles]
    rw [he]
    exact isClosed_iInter fun v =>
      (Valued.isClosed_closedBall (LocalField K v) 1).preimage
        (RestrictedProduct.continuous_eval v)
  · exact RestrictedProduct.isOpen_forall_mem
      (fun v : FinitePlace K => Valued.isOpen_valuationSubring (LocalField K v))

noncomputable def finiteAdelicRamifiedProduct (χ : UnitaryHeckeCharacter K) :
    LocallyConstant (FiniteAdeles K) ℂ := by
  classical
  exact ∏ v ∈ (finite_ramification K χ).toFinset,
    (finiteAdditiveTest K χ v).comap
      ⟨fun a : FiniteAdeles K => a v, RestrictedProduct.continuous_eval v⟩

/-- The integral-ball cutoff together with the finitely many ramified local factors. -/
noncomputable def finiteAdelicTest (χ : UnitaryHeckeCharacter K) :
    LocallyConstant (FiniteAdeles K) ℂ := by
  classical
  let S := integralFiniteAdeles K
  have hs : IsClopen S := integralFiniteAdeles_isClopen K
  exact LocallyConstant.piecewise hs.isClosed hs.compl.isClosed (Set.union_compl_self S)
    ((finiteAdelicRamifiedProduct K χ).comap ⟨Subtype.val, continuous_subtype_val⟩)
    (LocallyConstant.const ↥(Sᶜ : Set (FiniteAdeles K)) (0 : ℂ))
    (fun _ hx => (hx.2 hx.1).elim)

theorem finiteAdelicTest_zero_outside (χ : UnitaryHeckeCharacter K)
    (a : FiniteAdeles K) (ha : a ∉ integralFiniteAdeles K) :
    finiteAdelicTest K χ a = 0 := by
  classical
  change (if h : a ∈ integralFiniteAdeles K then _ else (0 : ℂ)) = 0
  rw [dif_neg ha]

#check integralFiniteAdeles_isClopen
#print axioms integralFiniteAdeles_isClopen
end MasulloGRH

/-! Round 37: identify the finite-adelic test as its genuine local tensor product. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

 theorem finiteAdditiveTest_values_hasFiniteMulSupport
    (χ : UnitaryHeckeCharacter K) (a : FiniteAdeles K) :
    {v : FinitePlace K | finiteAdditiveTest K χ v (a v) ≠ 1}.Finite := by
  classical
  have hfin : {v : FinitePlace K | ¬ Valued.v (a v) ≤ 1}.Finite :=
    Filter.eventually_cofinite.mp a.property
  apply ((finite_ramification K χ).union hfin).subset
  intro v hv
  by_contra h
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
  apply hv
  simp only [finiteAdditiveTest, if_pos h.1]
  rw [unramifiedAdditiveTest_apply, if_pos h.2]

theorem finiteAdditiveTest_zero_of_nonintegral (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (x : LocalField K v) (hx : ¬ Valued.v x ≤ 1) :
    finiteAdditiveTest K χ v x = 0 := by
  classical
  by_cases hχ : IsUnramified K χ v
  · simp only [finiteAdditiveTest, if_pos hχ]
    rw [unramifiedAdditiveTest_apply, if_neg hx]
  · simp only [finiteAdditiveTest, if_neg hχ]
    exact ramifiedAdditiveTest_zero_off_shell K χ v x (fun h => hx h.le)

theorem finiteAdelicRamifiedProduct_apply (χ : UnitaryHeckeCharacter K)
    (a : FiniteAdeles K) :
    finiteAdelicRamifiedProduct K χ a =
      ∏ v ∈ (finite_ramification K χ).toFinset, finiteAdditiveTest K χ v (a v) := by
  classical
  exact map_prod (LocallyConstant.evalMonoidHom a)
    (fun v => (finiteAdditiveTest K χ v).comap
      ⟨fun b : FiniteAdeles K => b v, RestrictedProduct.continuous_eval v⟩)
    (finite_ramification K χ).toFinset

theorem finiteAdelicTest_eq_finprod (χ : UnitaryHeckeCharacter K)
    (a : FiniteAdeles K) :
    finiteAdelicTest K χ a = ∏ᶠ v : FinitePlace K, finiteAdditiveTest K χ v (a v) := by
  classical
  by_cases ha : a ∈ integralFiniteAdeles K
  · have heval : finiteAdelicTest K χ a = finiteAdelicRamifiedProduct K χ a := by
      change (if h : a ∈ integralFiniteAdeles K then _ else (0 : ℂ)) = _
      exact dif_pos ha
    rw [heval, finiteAdelicRamifiedProduct_apply]
    symm
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    apply (finite_ramification K χ).mem_toFinset.mpr
    change ¬ IsUnramified K χ v
    intro hχ
    apply hv
    simp only [finiteAdditiveTest, if_pos hχ]
    rw [unramifiedAdditiveTest_apply, if_pos (ha v)]
  · rw [finiteAdelicTest_zero_outside K χ a ha]
    have hf := finiteAdditiveTest_values_hasFiniteMulSupport K χ a
    rw [finprod_eq_prod _ hf]
    change ¬ (∀ v : FinitePlace K, Valued.v (a v) ≤ 1) at ha
    obtain ⟨v, hv⟩ := not_forall.mp ha
    have hz := finiteAdditiveTest_zero_of_nonintegral K χ v (a v) hv
    symm
    apply Finset.prod_eq_zero (i := v)
    · apply hf.mem_toFinset.mpr
      change finiteAdditiveTest K χ v (a v) ≠ 1
      rw [hz]
      exact zero_ne_one
    · exact hz

#check finiteAdditiveTest_values_hasFiniteMulSupport
#print axioms finiteAdditiveTest_values_hasFiniteMulSupport
#check finiteAdditiveTest_zero_of_nonintegral
#print axioms finiteAdditiveTest_zero_of_nonintegral
#check finiteAdelicRamifiedProduct_apply
#print axioms finiteAdelicRamifiedProduct_apply
#check finiteAdelicTest_eq_finprod
#print axioms finiteAdelicTest_eq_finprod
end MasulloGRH

/-! Round 38: global character factorization on the actual product of finite local units.
This is the compact-unit part of the character factorization required for the
finite-adelic zeta integral; it is not a global integration theorem. -/
namespace MasulloGRH
open Filter Topology
variable (K : Type*) [Field K] [NumberField K]

theorem integralIdele_mul
    (x y : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    integralIdele K (x * y) = integralIdele K x * integralIdele K y := by
  apply Units.ext
  apply Prod.ext
  · change (1 : NumberField.InfiniteAdeleRing K) = 1 * 1
    exact (one_mul _).symm
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl

noncomputable def integralUnitCutoff
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ)
    (S : Finset (FinitePlace K)) : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ := by
  classical
  exact fun v => if v ∈ S then x v else 1

theorem integralUnitCutoff_tendsto
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    Tendsto (integralUnitCutoff K x) atTop (𝓝 x) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro v
  apply (tendsto_const_nhds : Tendsto (fun _ : Finset (FinitePlace K) => x v)
    atTop (𝓝 (x v))).congr'
  filter_upwards [eventually_ge_atTop ({v} : Finset (FinitePlace K))] with S hS
  have hv : v ∈ S := hS (Finset.mem_singleton_self v)
  simp [integralUnitCutoff, hv]

theorem integralCharacter_cutoff (χ : UnitaryHeckeCharacter K)
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ)
    (S : Finset (FinitePlace K)) :
    χ.character (integralIdele K (integralUnitCutoff K x S)) =
      ∏ v ∈ S, localCharacter K χ v (integralLocalUnit K v (x v)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : integralUnitCutoff K x ∅ = (fun _ => 1) := by
      funext v
      simp [integralUnitCutoff]
    rw [he, integralIdele_one, map_one, Finset.prod_empty]
  | @insert v S hv ih =>
    have he : integralUnitCutoff K x (insert v S) =
        (Function.update (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v (x v)) *
          integralUnitCutoff K x S := by
      funext w
      by_cases hw : w = v
      · subst w
        simp [integralUnitCutoff, hv]
      · simp [integralUnitCutoff, hw]
    rw [he, integralIdele_mul, map_mul, integralIdele_update, ih,
      Finset.prod_insert hv]
    rfl

/-- The genuine global character equals the convergent product of its local
components on the full compact-unit subgroup, without a finite-support assumption. -/
theorem integralCharacter_hasProd (χ : UnitaryHeckeCharacter K)
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    HasProd (fun v => localCharacter K χ v (integralLocalUnit K v (x v)))
      (χ.character (integralIdele K x)) := by
  have h := (χ.character.continuous.comp (integralIdele_continuous K)).continuousAt.tendsto.comp
    (integralUnitCutoff_tendsto K x)
  change Tendsto (fun S => χ.character (integralIdele K (integralUnitCutoff K x S)))
    atTop (𝓝 (χ.character (integralIdele K x))) at h
  simpa only [integralCharacter_cutoff] using h

#check integralIdele_mul
#print axioms integralIdele_mul
#check integralUnitCutoff_tendsto
#print axioms integralUnitCutoff_tendsto
#check integralCharacter_cutoff
#print axioms integralCharacter_cutoff
#check integralCharacter_hasProd
#print axioms integralCharacter_hasProd
end MasulloGRH

/-! Round 39: finite exceptional-place decomposition of every genuine idele. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def ideleLocalUnit (a : HeckeIdeles K) (v : FinitePlace K) :
    (LocalField K v)ˣ where
  val := a.val.2 v
  inv := a.inv.2 v
  val_inv := congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
  inv_val := congrArg (fun z : HeckeAdeles K => z.2 v) a.inv_val

noncomputable def finiteIdeleComponent (a : HeckeIdeles K) : HeckeIdeles K where
  val := (1, a.val.2)
  inv := (1, a.inv.2)
  val_inv := by
    have h := congrArg (fun z : HeckeAdeles K => z.2) a.val_inv
    exact Prod.ext (one_mul 1) h
  inv_val := by
    have h := congrArg (fun z : HeckeAdeles K => z.2) a.inv_val
    exact Prod.ext (one_mul 1) h

noncomputable def finiteIdeleCutoff (a : HeckeIdeles K) (S : Finset (FinitePlace K)) :
    HeckeIdeles K := ∏ v ∈ S, localIdele K v (ideleLocalUnit K a v)

theorem finiteIdeleCutoff_apply (a : HeckeIdeles K) (S : Finset (FinitePlace K))
    (v : FinitePlace K) :
    (finiteIdeleCutoff K a S).val.2 v = if v ∈ S then a.val.2 v else 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change (1 : LocalField K v) = if v ∈ (∅ : Finset (FinitePlace K)) then a.val.2 v else 1
    simp
  | @insert w S hw ih =>
    have hp : finiteIdeleCutoff K a (insert w S) =
        localIdele K w (ideleLocalUnit K a w) * finiteIdeleCutoff K a S := by
      exact Finset.prod_insert hw
    rw [hp]
    change Function.update (fun u : FinitePlace K => (1 : LocalField K u)) w (a.val.2 w) v *
      (finiteIdeleCutoff K a S).val.2 v = _
    rw [ih]
    by_cases hv : v = w
    · subst v
      simp [hw]
    · simp [hv]

noncomputable def integralIdeleTail (a : HeckeIdeles K) (v : FinitePlace K) :
    (v.adicCompletionIntegers K)ˣ :=
  if h : Valued.v (a.val.2 v) ≤ 1 ∧ Valued.v (a.inv.2 v) ≤ 1 then
    { val := ⟨a.val.2 v, h.1⟩
      inv := ⟨a.inv.2 v, h.2⟩
      val_inv := Subtype.ext (congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv)
      inv_val := Subtype.ext (congrArg (fun z : HeckeAdeles K => z.2 v) a.inv_val) }
  else 1

/-- Every genuine finite idele is a finite product of local ideles times
an integral-unit idele. The exceptional set is proved finite, not assumed. -/
theorem finiteIdeleComponent_decomposition (a : HeckeIdeles K) :
    ∃ S : Finset (FinitePlace K), finiteIdeleComponent K a =
      finiteIdeleCutoff K a S * integralIdele K (integralIdeleTail K a) := by
  classical
  have hbad : {v : FinitePlace K |
      ¬ (Valued.v (a.val.2 v) ≤ 1 ∧ Valued.v (a.inv.2 v) ≤ 1)}.Finite :=
    Filter.eventually_cofinite.mp (a.val.2.property.and a.inv.2.property)
  let S := hbad.toFinset
  refine ⟨S, ?_⟩
  apply Units.ext
  apply Prod.ext
  · change (1 : NumberField.InfiniteAdeleRing K) =
      (finiteIdeleCutoff K a S).val.1 * 1
    have harch : (finiteIdeleCutoff K a S).val.1 = 1 := by
      change (∏ v ∈ S, localIdele K v (ideleLocalUnit K a v)).val.1 = 1
      induction S using Finset.induction_on with
      | empty => simp
      | @insert v T hv ih =>
        rw [Finset.prod_insert hv]
        change 1 * (∏ w ∈ T, localIdele K w (ideleLocalUnit K a w)).val.1 = 1
        rw [one_mul, ih]
    rw [harch, one_mul]
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    change a.val.2 v = (finiteIdeleCutoff K a S).val.2 v *
      ((integralIdeleTail K a v).val : LocalField K v)
    rw [finiteIdeleCutoff_apply]
    by_cases hv : v ∈ S
    · have hb : ¬ (Valued.v (a.val.2 v) ≤ 1 ∧ Valued.v (a.inv.2 v) ≤ 1) :=
        hbad.mem_toFinset.mp hv
      rw [if_pos hv]
      unfold integralIdeleTail
      rw [dif_neg hb]
      exact (mul_one _).symm
    · have hg : Valued.v (a.val.2 v) ≤ 1 ∧ Valued.v (a.inv.2 v) ≤ 1 := by
        by_contra hn
        exact hv (hbad.mem_toFinset.mpr hn)
      rw [if_neg hv]
      unfold integralIdeleTail
      rw [dif_pos hg]
      exact (one_mul _).symm

#check finiteIdeleCutoff_apply
#print axioms finiteIdeleCutoff_apply
#check finiteIdeleComponent_decomposition
#print axioms finiteIdeleComponent_decomposition
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Genuine global character factorization into the finite exceptional local
factors and the convergent integral-unit product, for every finite idele. -/
theorem finiteIdeleCharacter_factorization (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) :
    ∃ S : Finset (FinitePlace K),
      χ.character (finiteIdeleComponent K a) =
        (∏ v ∈ S, localCharacter K χ v (ideleLocalUnit K a v)) *
        ∏' v : FinitePlace K,
          localCharacter K χ v (integralLocalUnit K v (integralIdeleTail K a v)) := by
  obtain ⟨S, hS⟩ := finiteIdeleComponent_decomposition K a
  refine ⟨S, ?_⟩
  rw [hS, map_mul, ← (integralCharacter_hasProd K χ (integralIdeleTail K a)).tprod_eq]
  congr 1
  exact map_prod χ.character.toMonoidHom _ S

#check finiteIdeleCharacter_factorization
#print axioms finiteIdeleCharacter_factorization
end MasulloGRH

/-! Round 40: the product of all finite local character values, on every idele. -/
namespace MasulloGRH
open Filter Topology
variable (K : Type*) [Field K] [NumberField K]

theorem finiteIdeleCutoff_infinite (a : HeckeIdeles K) (S : Finset (FinitePlace K)) :
    (finiteIdeleCutoff K a S).val.1 = 1 := by
  classical
  change (∏ v ∈ S, localIdele K v (ideleLocalUnit K a v)).val.1 = 1
  induction S using Finset.induction_on with
  | empty => simp
  | @insert v T hv ih =>
    rw [Finset.prod_insert hv]
    change 1 * (∏ w ∈ T, localIdele K w (ideleLocalUnit K a w)).val.1 = 1
    rw [one_mul, ih]

theorem finiteIdeleCutoff_decomposition (a : HeckeIdeles K)
    (S T : Finset (FinitePlace K)) (hST : S ⊆ T)
    (hS : finiteIdeleComponent K a =
      finiteIdeleCutoff K a S * integralIdele K (integralIdeleTail K a)) :
    finiteIdeleCutoff K a T = finiteIdeleCutoff K a S *
      integralIdele K (integralUnitCutoff K (integralIdeleTail K a) T) := by
  classical
  apply Units.ext
  apply Prod.ext
  · change (finiteIdeleCutoff K a T).val.1 = (finiteIdeleCutoff K a S).val.1 * 1
    rw [finiteIdeleCutoff_infinite, finiteIdeleCutoff_infinite, one_mul]
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    change (finiteIdeleCutoff K a T).val.2 v = (finiteIdeleCutoff K a S).val.2 v *
      ((integralUnitCutoff K (integralIdeleTail K a) T v).val : LocalField K v)
    rw [finiteIdeleCutoff_apply]
    by_cases hv : v ∈ T
    · rw [if_pos hv]
      have hc := congrArg (fun z : HeckeIdeles K => z.val.2 v) hS
      change a.val.2 v = (finiteIdeleCutoff K a S).val.2 v *
        ((integralIdeleTail K a v).val : LocalField K v) at hc
      simpa only [integralUnitCutoff, if_pos hv] using hc
    · have hvS : v ∉ S := fun h => hv (hST h)
      rw [if_neg hv, finiteIdeleCutoff_apply, if_neg hvS]
      simp [integralUnitCutoff, hv]

/-- The finite local character product converges to the actual global character
of the finite component, for every idele, with no integrality premise. -/
theorem finiteIdeleCharacter_hasProd (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) :
    HasProd (fun v : FinitePlace K => localCharacter K χ v (ideleLocalUnit K a v))
      (χ.character (finiteIdeleComponent K a)) := by
  classical
  obtain ⟨S, hS⟩ := finiteIdeleComponent_decomposition K a
  have ht := (χ.character.continuous.comp (integralIdele_continuous K)).continuousAt.tendsto.comp
    (integralUnitCutoff_tendsto K (integralIdeleTail K a))
  change Tendsto
    (fun T => χ.character (integralIdele K (integralUnitCutoff K (integralIdeleTail K a) T)))
    atTop (𝓝 (χ.character (integralIdele K (integralIdeleTail K a)))) at ht
  have hm := (tendsto_const_nhds (x := χ.character (finiteIdeleCutoff K a S))).mul ht
  change Tendsto (fun T => χ.character (finiteIdeleCutoff K a S) *
    χ.character (integralIdele K (integralUnitCutoff K (integralIdeleTail K a) T)))
    atTop (𝓝 (χ.character (finiteIdeleCutoff K a S) *
      χ.character (integralIdele K (integralIdeleTail K a)))) at hm
  rw [← map_mul, ← hS] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop S] with T hT
  rw [← map_mul, ← finiteIdeleCutoff_decomposition K a S T hT hS]
  exact map_prod χ.character.toMonoidHom _ T

#check finiteIdeleCutoff_infinite
#print axioms finiteIdeleCutoff_infinite
#check finiteIdeleCutoff_decomposition
#print axioms finiteIdeleCutoff_decomposition
#check finiteIdeleCharacter_hasProd
#print axioms finiteIdeleCharacter_hasProd
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual infinite component, with all finite coordinates equal to one. -/
noncomputable def infiniteIdeleComponent (a : HeckeIdeles K) : HeckeIdeles K where
  val := (a.val.1, 1)
  inv := (a.inv.1, 1)
  val_inv := by
    have h := congrArg (fun z : HeckeAdeles K => z.1) a.val_inv
    exact Prod.ext h (one_mul 1)
  inv_val := by
    have h := congrArg (fun z : HeckeAdeles K => z.1) a.inv_val
    exact Prod.ext h (one_mul 1)

theorem idele_eq_infinite_mul_finite (a : HeckeIdeles K) :
    a = infiniteIdeleComponent K a * finiteIdeleComponent K a := by
  apply Units.ext
  apply Prod.ext
  · change a.val.1 = a.val.1 * 1
    exact (mul_one _).symm
  · change a.val.2 = 1 * a.val.2
    exact (one_mul _).symm

/-- Character factorization required in the global Hecke zeta integrand:
the genuine infinite component times the product of all finite local values. -/
theorem ideleCharacter_factorization (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) :
    χ.character a = χ.character (infiniteIdeleComponent K a) *
      ∏' v : FinitePlace K, localCharacter K χ v (ideleLocalUnit K a v) := by
  calc
    χ.character a = χ.character (infiniteIdeleComponent K a * finiteIdeleComponent K a) :=
      congrArg χ.character (idele_eq_infinite_mul_finite K a)
    _ = χ.character (infiniteIdeleComponent K a) * χ.character (finiteIdeleComponent K a) :=
      map_mul χ.character _ _
    _ = _ := congrArg (fun z : Circle => χ.character (infiniteIdeleComponent K a) * z)
      (finiteIdeleCharacter_hasProd K χ a).tprod_eq.symm

#check idele_eq_infinite_mul_finite
#print axioms idele_eq_infinite_mul_finite
#check ideleCharacter_factorization
#print axioms ideleCharacter_factorization
end MasulloGRH

/-! Round 41: genuine finite-adelic test-times-character product. -/
namespace MasulloGRH
open Filter Topology
variable (K : Type*) [Field K] [NumberField K]

/-- The complex-valued local character product has the actual finite component
as its limit; coercion is passed through an established limit. -/
theorem finiteIdeleCharacter_complex_hasProd (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) :
    HasProd (fun v : FinitePlace K =>
      (localCharacter K χ v (ideleLocalUnit K a v) : ℂ))
      (χ.character (finiteIdeleComponent K a) : ℂ) := by
  have h := (continuous_subtype_val : Continuous (fun z : Circle => (z : ℂ))).continuousAt.tendsto.comp
    (finiteIdeleCharacter_hasProd K χ a)
  have hp : ∀ S : Finset (FinitePlace K),
      ((∏ v ∈ S, localCharacter K χ v (ideleLocalUnit K a v) : Circle) : ℂ) =
        ∏ v ∈ S, (localCharacter K χ v (ideleLocalUnit K a v) : ℂ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert v S hv ih => simp only [Finset.prod_insert hv, Circle.coe_mul, ih]
  change Tendsto (fun S : Finset (FinitePlace K) =>
    ((∏ v ∈ S, localCharacter K χ v (ideleLocalUnit K a v) : Circle) : ℂ))
    atTop (𝓝 (χ.character (finiteIdeleComponent K a) : ℂ)) at h
  simpa only [hp] using h

/-- The genuine additive test is the limit of its finite local products. -/
theorem finiteAdelicTest_hasProd (χ : UnitaryHeckeCharacter K)
    (a : FiniteAdeles K) :
    HasProd (fun v : FinitePlace K => finiteAdditiveTest K χ v (a v))
      (finiteAdelicTest K χ a) := by
  classical
  have hf := finiteAdditiveTest_values_hasFiniteMulSupport K χ a
  apply (tendsto_const_nhds (x := finiteAdelicTest K χ a)).congr'
  filter_upwards [eventually_ge_atTop hf.toFinset] with S hS
  rw [finiteAdelicTest_eq_finprod]
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  exact hS (hf.mem_toFinset.mpr hv)

/-- The test-times-character part of the genuine finite zeta integrand is the
convergent product of its actual local factors, for every number field and idele. -/
theorem finiteAdelicTest_character_hasProd (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) :
    HasProd (fun v : FinitePlace K =>
      finiteAdditiveTest K χ v (a.val.2 v) *
        (localCharacter K χ v (ideleLocalUnit K a v) : ℂ))
      (finiteAdelicTest K χ a.val.2 * (χ.character (finiteIdeleComponent K a) : ℂ)) := by
  exact (finiteAdelicTest_hasProd K χ a.val.2).mul
    (finiteIdeleCharacter_complex_hasProd K χ a)

#check finiteIdeleCharacter_complex_hasProd
#print axioms finiteIdeleCharacter_complex_hasProd
#check finiteAdelicTest_hasProd
#print axioms finiteAdelicTest_hasProd
#check finiteAdelicTest_character_hasProd
#print axioms finiteAdelicTest_character_hasProd
end MasulloGRH

/-! Round 43: insert the genuine global character into the finite test product. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The finite test times the full idelic character factors into the actual
infinite character and a convergent product of finite local integrands. -/
theorem finiteAdelicTest_global_character_factorization
    (χ : UnitaryHeckeCharacter K) (a : HeckeIdeles K) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      (χ.character (infiniteIdeleComponent K a) : ℂ) *
        ∏' v : FinitePlace K,
          (finiteAdditiveTest K χ v (a.val.2 v) *
            (localCharacter K χ v (ideleLocalUnit K a v) : ℂ)) := by
  have hc := congrArg (fun z : Circle => (z : ℂ))
    (congrArg χ.character (idele_eq_infinite_mul_finite K a))
  simp only [map_mul, Circle.coe_mul] at hc
  rw [(finiteAdelicTest_character_hasProd K χ a).tprod_eq, hc]
  ring

#check finiteAdelicTest_global_character_factorization
#print axioms finiteAdelicTest_global_character_factorization
end MasulloGRH

/-! Round 44: descend the actual finite zeta integrand to valuation shells. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Multiplying by an integral local unit leaves the genuine local
Tate test-times-character integrand unchanged, including ramified places. -/
theorem finiteAdditiveTest_character_unit_invariant
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x u : (LocalField K v)ˣ) (hu : Valued.v (u : LocalField K v) = 1) :
    finiteAdditiveTest K χ v (↑(x * u)) * (localCharacter K χ v (x * u) : ℂ) =
      finiteAdditiveTest K χ v (↑x) * (localCharacter K χ v x : ℂ) := by
  classical
  have hv : Valued.v ((x * u : (LocalField K v)ˣ) : LocalField K v) =
      Valued.v (x : LocalField K v) := by
    simp only [Units.val_mul, map_mul, hu, mul_one]
  rw [finiteAdditiveTest_restrict, finiteAdditiveTest_restrict]
  by_cases hχ : IsUnramified K χ v
  · simp only [if_pos hχ, hv, localCharacter_mul, hχ u hu, mul_one]
    split_ifs <;> rfl
  · simp only [if_neg hχ, hv]
    by_cases hx : Valued.v (x : LocalField K v) = 1
    · simp only [if_pos hx]
      have hn (z : Circle) : (z : ℂ) ≠ 0 := by
        intro hz
        have hnorm := Circle.norm_coe z
        rw [hz, norm_zero] at hnorm
        exact zero_ne_one hnorm
      rw [inv_mul_cancel₀ (hn _), inv_mul_cancel₀ (hn _)]
    · simp only [if_neg hx, zero_mul]

/-- Integral tuples give genuine valuation-one local units. -/
theorem integralLocalUnit_valuation_one (v : FinitePlace K)
    (u : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (integralLocalUnit K v u : LocalField K v) = 1 := by
  have hle : Valued.v (integralLocalUnit K v u : LocalField K v) ≤ 1 := u.val.property
  have hinv : Valued.v (((integralLocalUnit K v u)⁻¹ : (LocalField K v)ˣ) : LocalField K v) ≤ 1 := u.inv.property
  have hmul : Valued.v (integralLocalUnit K v u : LocalField K v) *
      Valued.v (((integralLocalUnit K v u)⁻¹ : (LocalField K v)ˣ) : LocalField K v) = 1 := by
    rw [← map_mul]
    simp
  apply le_antisymm hle
  calc
    1 = Valued.v (integralLocalUnit K v u : LocalField K v) *
        Valued.v (((integralLocalUnit K v u)⁻¹ : (LocalField K v)ˣ) : LocalField K v) := hmul.symm
    _ ≤ Valued.v (integralLocalUnit K v u : LocalField K v) * 1 :=
      mul_le_mul_right hinv _
    _ = _ := mul_one _

/-- The actual global finite integrand is constant on every integral-unit shell.
Together with the genuine uniformizer coordinates this is the pointwise step
needed to evaluate each compact shell in the finite Hecke Mellin integral. -/
theorem finiteAdelicTest_character_integralUnit_invariant
    (χ : UnitaryHeckeCharacter K) (a : HeckeIdeles K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteAdelicTest K χ (a * integralIdele K u).val.2 *
        (χ.character (finiteIdeleComponent K (a * integralIdele K u)) : ℂ) =
      finiteAdelicTest K χ a.val.2 *
        (χ.character (finiteIdeleComponent K a) : ℂ) := by
  rw [← (finiteAdelicTest_character_hasProd K χ (a * integralIdele K u)).tprod_eq,
    ← (finiteAdelicTest_character_hasProd K χ a).tprod_eq]
  apply tprod_congr
  intro v
  have he : ideleLocalUnit K (a * integralIdele K u) v =
      ideleLocalUnit K a v * integralLocalUnit K v (u v) := by
    apply Units.ext
    rfl
  change finiteAdditiveTest K χ v (↑(ideleLocalUnit K (a * integralIdele K u) v)) * _ = _
  rw [he]
  exact finiteAdditiveTest_character_unit_invariant K χ v
    (ideleLocalUnit K a v) (integralLocalUnit K v (u v))
    (integralLocalUnit_valuation_one K v (u v))

#check finiteAdditiveTest_character_unit_invariant
#print axioms finiteAdditiveTest_character_unit_invariant
#check integralLocalUnit_valuation_one
#print axioms integralLocalUnit_valuation_one
#check finiteAdelicTest_character_integralUnit_invariant
#print axioms finiteAdelicTest_character_integralUnit_invariant
end MasulloGRH


/-! Round 45: the actual norm-weighted finite integrand on integral-unit shells. -/
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The arithmetic finite Mellin weight: order n at v contributes q_v^(-s*n).
The multiplicative valuation has logarithm -n, fixing the sign. -/
noncomputable def finiteMellinWeight (s : ℂ) (a : HeckeIdeles K) : ℂ :=
  ∏ᶠ v : FinitePlace K,
    ((v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (-(Valued.v (a.val.2 v)).log)

/-- The genuine finite test, finite character and arithmetic norm weight. -/
noncomputable def finiteMellinIntegrand (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (a : HeckeIdeles K) : ℂ :=
  (finiteAdelicTest K χ a.val.2 * (χ.character (finiteIdeleComponent K a) : ℂ)) *
    finiteMellinWeight K s a

theorem finiteMellinWeight_integralUnit_invariant (s : ℂ) (a : HeckeIdeles K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteMellinWeight K s (a * integralIdele K u) = finiteMellinWeight K s a := by
  unfold finiteMellinWeight
  apply finprod_congr
  intro v
  have hv : Valued.v ((a * integralIdele K u).val.2 v) = Valued.v (a.val.2 v) := by
    change Valued.v (a.val.2 v * (integralLocalUnit K v (u v) : LocalField K v)) = _
    rw [map_mul, integralLocalUnit_valuation_one, mul_one]
  rw [hv]

theorem finiteMellinIntegrand_integralUnit_invariant
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (a : HeckeIdeles K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteMellinIntegrand K χ s (a * integralIdele K u) =
      finiteMellinIntegrand K χ s a := by
  unfold finiteMellinIntegrand
  rw [finiteAdelicTest_character_integralUnit_invariant,
    finiteMellinWeight_integralUnit_invariant]

/-- Every finite idele has only finitely many nontrivial local norm factors. -/
theorem finiteMellinWeight_finite_support (s : ℂ) (a : HeckeIdeles K) :
    {v : FinitePlace K |
      ((v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (-(Valued.v (a.val.2 v)).log) ≠ 1}.Finite := by
  have hbad : {v : FinitePlace K |
      ¬ (Valued.v (a.val.2 v) ≤ 1 ∧ Valued.v (a.inv.2 v) ≤ 1)}.Finite :=
    Filter.eventually_cofinite.mp (a.val.2.property.and a.inv.2.property)
  apply hbad.subset
  intro v hv
  by_contra hn
  have hg : Valued.v (a.val.2 v) ≤ 1 ∧ Valued.v (a.inv.2 v) ≤ 1 := by
    simpa only [Set.mem_setOf_eq, not_not] using hn
  have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul]
    have he := congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
    change a.val.2 v * a.inv.2 v = 1 at he
    rw [he, map_one]
  have he : Valued.v (a.val.2 v) = 1 := by
    apply le_antisymm hg.1
    calc
      1 = Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) := hm.symm
      _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right hg.2 _
      _ = _ := mul_one _
  exact hv (by simp only [he, WithZero.log_one, neg_zero, zpow_zero])

/-- The normalized unit-shell average of the actual weighted finite integrand.
A probability measure is explicit here; constructing compatible Haar measure
on all finite ideles is a separate, still unresolved obligation. -/
theorem finiteMellinIntegrand_shell_average
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (a : HeckeIdeles K)
    [MeasurableSpace (∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ)]
    (μ : Measure (∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ))
    [IsProbabilityMeasure μ] :
    (∫ u, finiteMellinIntegrand K χ s (a * integralIdele K u) ∂μ) =
      finiteMellinIntegrand K χ s a := by
  simp only [finiteMellinIntegrand_integralUnit_invariant]
  simp

#check finiteMellinWeight_integralUnit_invariant
#print axioms finiteMellinWeight_integralUnit_invariant
#check finiteMellinIntegrand_integralUnit_invariant
#print axioms finiteMellinIntegrand_integralUnit_invariant
#check finiteMellinWeight_finite_support
#print axioms finiteMellinWeight_finite_support
#check finiteMellinIntegrand_shell_average
#print axioms finiteMellinIntegrand_shell_average
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem genuineIdele_integralUnit_representation (a : HeckeIdeles K)
    (hinf : a.val.1 = 1)
    (hval : ∀ v : FinitePlace K, Valued.v (a.val.2 v) = 1) :
    ∃ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
      integralIdele K x = a := by
  have hi (v : FinitePlace K) : Valued.v (a.inv.2 v) = 1 := by
    have he : a.val.2 v * a.inv.2 v = 1 :=
      congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
    have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
      rw [← map_mul, he, map_one]
    simpa only [hval v, one_mul] using hm
  let x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ := fun v =>
    { val := ⟨a.val.2 v, le_of_eq (hval v)⟩
      inv := ⟨a.inv.2 v, le_of_eq (hi v)⟩
      val_inv := by
        apply Subtype.ext
        exact congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
      inv_val := by
        apply Subtype.ext
        exact congrArg (fun b : HeckeAdeles K => b.2 v) a.inv_val }
  refine ⟨x, ?_⟩
  apply Units.ext
  apply Prod.ext
  · exact hinf.symm
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl


theorem integralIdele_coordinate_valuation
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) (v : FinitePlace K) :
    Valued.v ((integralIdele K x).val.2 v) = 1 := by
  change Valued.v ((x v).val : LocalField K v) = 1
  have hm : Valued.v ((x v).val : LocalField K v) *
      Valued.v ((x v).inv : LocalField K v) = 1 := by
    rw [← map_mul]
    have he : ((x v).val : LocalField K v) * ((x v).inv : LocalField K v) = 1 :=
      congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).val_inv
    rw [he, map_one]
  apply le_antisymm (x v).val.property
  calc
    1 = Valued.v ((x v).val : LocalField K v) *
        Valued.v ((x v).inv : LocalField K v) := hm.symm
    _ ≤ Valued.v ((x v).val : LocalField K v) * 1 := by
      gcongr
      exact (x v).inv.property
    _ = _ := mul_one _


theorem genuineFiniteIdele_same_shell_iff (a b : HeckeIdeles K)
    (ha : a.val.1 = 1) (hb : b.val.1 = 1) :
    (∀ v : FinitePlace K, Valued.v (a.val.2 v) = Valued.v (b.val.2 v)) ↔
      ∃ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        a = b * integralIdele K x := by
  constructor
  · intro h
    have hbi : b.inv.1 = 1 := by
      have he := congrArg (fun c : HeckeAdeles K => c.1) b.val_inv
      change b.val.1 * b.inv.1 = 1 at he
      simpa only [hb, one_mul] using he
    have hinf : (a * b⁻¹).val.1 = 1 := by
      change a.val.1 * b.inv.1 = 1
      rw [ha, hbi, one_mul]
    have hval (v : FinitePlace K) : Valued.v ((a * b⁻¹).val.2 v) = 1 := by
      change Valued.v (a.val.2 v * b.inv.2 v) = 1
      rw [map_mul, h v, ← map_mul]
      have he : b.val.2 v * b.inv.2 v = 1 :=
        congrArg (fun c : HeckeAdeles K => c.2 v) b.val_inv
      rw [he, map_one]
    obtain ⟨x, hx⟩ := genuineIdele_integralUnit_representation K (a * b⁻¹) hinf hval
    refine ⟨x, ?_⟩
    rw [hx, mul_left_comm, mul_inv_cancel, mul_one]
  · rintro ⟨x, rfl⟩ v
    change Valued.v (b.val.2 v * (integralIdele K x).val.2 v) = _
    rw [map_mul, integralIdele_coordinate_valuation, mul_one]


def finiteIdelicSubgroup : Subgroup (HeckeIdeles K) where
  carrier := {a | a.val.1 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a.val.1 * b.val.1 = 1
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    have h := congrArg (fun b : HeckeAdeles K => b.1) a.val_inv
    change a.val.1 * a.inv.1 = 1 at h
    change a.val.1 = 1 at ha
    change a.inv.1 = 1
    simpa only [ha, one_mul] using h

noncomputable def finiteIntegralUnit
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteIdelicSubgroup K := ⟨integralIdele K u, rfl⟩

def finiteIntegralUnitSet : Set (finiteIdelicSubgroup K) :=
  Set.range (finiteIntegralUnit K)

def finiteValuationShell (a : finiteIdelicSubgroup K) : Set (finiteIdelicSubgroup K) :=
  {b | ∀ v : FinitePlace K, Valued.v (b.val.val.2 v) = Valued.v (a.val.val.2 v)}

theorem finiteValuationShell_eq_translate (a : finiteIdelicSubgroup K) :
    finiteValuationShell K a = (fun b => a * b) '' finiteIntegralUnitSet K := by
  ext b
  constructor
  · intro hb
    obtain ⟨u, hu⟩ := (genuineFiniteIdele_same_shell_iff K b.val a.val b.property a.property).mp hb
    exact ⟨finiteIntegralUnit K u, ⟨u, rfl⟩, Subtype.ext hu.symm⟩
  · rintro ⟨c, ⟨u, rfl⟩, rfl⟩
    exact (genuineFiniteIdele_same_shell_iff K _ _ (a * finiteIntegralUnit K u).property a.property).mpr ⟨u, rfl⟩

theorem finiteValuationShell_isClosed (a : finiteIdelicSubgroup K) :
    IsClosed (finiteValuationShell K a) := by
  have he : finiteValuationShell K a = ⋂ v : FinitePlace K,
      (fun b : finiteIdelicSubgroup K => b.val.val.2 v) ⁻¹'
        {x : LocalField K v | Valued.v x = Valued.v (a.val.val.2 v)} := by
    ext b
    simp only [finiteValuationShell, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [he]
  apply isClosed_iInter
  intro v
  have hn : Valued.v (a.val.val.2 v) ≠ 0 := by
    have hm : Valued.v (a.val.val.2 v) * Valued.v (a.val.inv.2 v) = 1 := by
      rw [← map_mul]
      have hh := congrArg (fun b : HeckeAdeles K => b.2 v) a.val.val_inv
      change a.val.val.2 v * a.val.inv.2 v = 1 at hh
      rw [hh, map_one]
    intro hz
    rw [hz, zero_mul] at hm
    exact zero_ne_one hm
  exact (Valued.isClopen_sphere (LocalField K v) hn).isClosed.preimage
    (((RestrictedProduct.continuous_eval v).comp
      (continuous_snd.comp Units.continuous_val)).comp continuous_subtype_val)


open MeasureTheory
variable [MeasurableSpace (finiteIdelicSubgroup K)] [BorelSpace (finiteIdelicSubgroup K)]
variable [MeasurableMul (finiteIdelicSubgroup K)]
theorem finiteValuationShell_measure_one
    (μ : Measure (finiteIdelicSubgroup K)) [μ.IsMulLeftInvariant]
    (hU : μ (finiteIntegralUnitSet K) = 1) (a : finiteIdelicSubgroup K) :
    μ (finiteValuationShell K a) = 1 := by
  have he : (fun b : finiteIdelicSubgroup K => a⁻¹ * b) ⁻¹'
      finiteIntegralUnitSet K = finiteValuationShell K a := by
    rw [finiteValuationShell_eq_translate]
    ext b
    constructor
    · intro hb
      exact ⟨a⁻¹ * b, hb, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      simpa only [Set.mem_preimage, inv_mul_cancel_left] using hc
  rw [← he, measure_preimage_mul, hU]


/-- Integration transfer on the actual finite-idele group, to be instantiated
with the genuine finiteMellinIntegrand and its checked unit invariance. -/
theorem finiteValuationShell_integral_of_invariant
    (F : HeckeIdeles K → ℂ)
    (hF : ∀ a u, F (a * integralIdele K u) = F a)
    (μ : Measure (finiteIdelicSubgroup K)) [μ.IsMulLeftInvariant]
    (hU : μ (finiteIntegralUnitSet K) = 1) (a : finiteIdelicSubgroup K) :
    IntegrableOn (fun b : finiteIdelicSubgroup K => F b.val) (finiteValuationShell K a) μ ∧
    (∫ b in finiteValuationShell K a, F b.val ∂μ) = F a.val := by
  have hm := finiteValuationShell_measure_one K μ hU a
  have hs := (finiteValuationShell_isClosed K a).measurableSet
  have hc : ∀ b ∈ finiteValuationShell K a, F b.val = F a.val := by
    intro b hb
    obtain ⟨u, hu⟩ := (genuineFiniteIdele_same_shell_iff K b.val a.val b.property a.property).mp hb
    rw [hu]
    exact hF a.val u
  constructor
  · have hi : IntegrableOn (fun _b : finiteIdelicSubgroup K => F a.val)
        (finiteValuationShell K a) μ :=
      integrableOn_const (by simp [hm])
    exact hi.congr_fun (fun b hb => (hc b hb).symm) hs
  · calc
      _ = ∫ _b in finiteValuationShell K a, F a.val ∂μ :=
        setIntegral_congr_fun hs hc
      _ = _ := by simp [Measure.real, hm]

#check finiteValuationShell_measure_one
#print axioms finiteValuationShell_measure_one
#check finiteValuationShell_integral_of_invariant
#print axioms finiteValuationShell_integral_of_invariant
end MasulloGRH

/- Arithmetic compactness copied from F/r44 Compact.lean, source and receipt
cb158314a00d475a8a92318a701d2562 verified in evidence/frozen_compact_audit.json.
Only dependencies required for actual finite-idelic Haar existence are retained. -/
/- Arithmetic compactness dependencies from F round 41, successful receipt d8361e4bb23c43a687efcb25398d116a. -/
open scoped NumberField Valued WithZero
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
/-- Arithmetic residue-field finiteness suffices for compactness of the actual local integer ring. -/
theorem localInteger_compact_of_finite_residue
    [Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K)))] :
    IsCompact {x : v.adicCompletion K | Valued.v x ≤ 1} := by
  have hd : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  letI : ProperSpace (v.adicCompletion K) :=
    Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
      ⟨inferInstance, hd, inferInstance⟩
  have hc : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  exact isCompact_iff_compactSpace.mpr hc


end MasulloGRH
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open scoped NumberField Valued WithZero
open IsDedekindDomain
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

theorem localInteger_rational_approximation (x : v.adicCompletionIntegers K) :
    ∃ y : K, v.valuation K y ≤ 1 ∧ Valued.v ((y : v.adicCompletion K) - x) < 1 := by
  have hd : DenseRange (fun y : K => (y : v.adicCompletion K)) :=
    UniformSpace.Completion.denseRange_coe.comp
      (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _)
  have ho : IsOpen {y : v.adicCompletion K | Valued.v (y - x) < 1} :=
    (Valued.isOpen_ball (v.adicCompletion K) 1).preimage (continuous_id.sub continuous_const)
  obtain ⟨y, hy⟩ := hd.exists_mem_open ho ⟨x, by simp⟩
  refine ⟨y, ?_, hy⟩
  rw [← v.valuedAdicCompletion_eq_valuation']
  calc
    Valued.v (y : v.adicCompletion K) = Valued.v (((y : v.adicCompletion K) - x) + x) := by rw [sub_add_cancel]
    _ ≤ max (Valued.v ((y : v.adicCompletion K) - x)) (Valued.v (x : v.adicCompletion K)) := Valued.v.map_add _ _
    _ ≤ 1 := max_le (le_of_lt hy) x.property

noncomputable def localIntegerCompletionMap :
    (v.valuation K).valuationSubring →+* v.adicCompletionIntegers K where
  toFun a := ⟨(a : K), by
    change Valued.v ((a : K) : v.adicCompletion K) ≤ 1
    rw [v.valuedAdicCompletion_eq_valuation']
    exact a.property⟩
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' a b := by
    ext
    exact map_add (algebraMap K (v.adicCompletion K)) (a : K) (b : K)
  map_mul' a b := by
    ext
    exact map_mul (algebraMap K (v.adicCompletion K)) (a : K) (b : K)

theorem localResidue_finite_of_rational_residue
    [Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring)] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  let f := (IsLocalRing.residue (v.adicCompletionIntegers K)).comp
    (localIntegerCompletionMap K v)
  have hf : ∀ a ∈ IsLocalRing.maximalIdeal (v.valuation K).valuationSubring, f a = 0 := by
    intro a ha
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    apply (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr
    change Valued.v ((a : K) : v.adicCompletion K) < 1
    rw [v.valuedAdicCompletion_eq_valuation']
    exact (Valuation.mem_maximalIdeal_iff K (v.valuation K)).mp ha
  let g := Ideal.Quotient.lift (IsLocalRing.maximalIdeal (v.valuation K).valuationSubring) f hf
  have hsur : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy, hxy⟩ := localInteger_rational_approximation K v x
    refine ⟨Ideal.Quotient.mk _ ⟨y, hy⟩, ?_⟩
    change IsLocalRing.residue _ (localIntegerCompletionMap K v ⟨y, hy⟩) =
      IsLocalRing.residue _ x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).mpr hxy
  letI : Finite ((v.valuation K).valuationSubring ⧸ IsLocalRing.maximalIdeal (v.valuation K).valuationSubring) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring))
  exact Finite.of_surjective g hsur

#check localInteger_rational_approximation
#print axioms localInteger_rational_approximation
#check localResidue_finite_of_rational_residue
#print axioms localResidue_finite_of_rational_residue
end MasulloGRH
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 600000
open scoped NumberField Valued WithZero
open IsDedekindDomain Localization
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))
local instance : IsDedekindDomain
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isDedekindDomain (𝓞 K) v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)
local instance : IsLocalRing (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) :=
  IsLocalization.AtPrime.isLocalRing
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) v.asIdeal
noncomputable def arithmeticValuationSubring : ValuationSubring K :=
  .ofSubring (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).toSubring fun x =>
    by simpa [IsLocalization.IsInteger] using ValuationRing.isInteger_or_isInteger
        (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) x
instance : Algebra (𝓞 K) (arithmeticValuationSubring K v) :=
  (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors).algebra'
instance : IsDedekindDomain (arithmeticValuationSubring K v) :=
  IsLocalization.AtPrime.isDedekindDomain (𝓞 K) v.asIdeal
    (subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors)
instance : IsLocalization (v.asIdeal.primeCompl) (arithmeticValuationSubring K v) :=
  Localization.subalgebra.isLocalization_ofField K (v.asIdeal.primeCompl) _
theorem arithmeticValuationSubring_le :
    arithmeticValuationSubring K v ≤ (v.valuation K).valuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  suffices (v.valuation K) (a / (s : K)) ≤ 1 by rwa [division_def] at this
  rwa [v.valuation_div_le_one_iff K a (by aesop) (fun _ => by contradiction)]

theorem arithmeticValuationSubring_eq :
    arithmeticValuationSubring K v = (v.valuation K).valuationSubring := by
  apply le_antisymm (arithmeticValuationSubring_le K v)
  intro x hx
  by_cases hzero : x = 0
  · simp [hzero]
  rcases (arithmeticValuationSubring K v).mem_or_inv_mem x with h | h
  · exact h
  rcases h with ⟨a, s, hs, heq⟩
  have ha : a ≠ 0 := by
    intro ha
    apply hzero
    simpa [ha] using heq
  have hxform : x = (s : K) / (a : K) := by
    have hh := congrArg Inv.inv heq
    simpa [div_eq_mul_inv, mul_comm] using hh
  have han : a ∉ v.asIdeal := by
    apply (v.valuation_div_le_one_iff K s ha (fun _ => hs)).mp
    simpa [← hxform] using hx
  exact ⟨s, a, han, by simpa [div_eq_mul_inv] using hxform⟩
theorem rationalResidue_finite :
    Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring) := by
  rw [← arithmeticValuationSubring_eq K v]
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal v.asIdeal
    (arithmeticValuationSubring K v)
  exact Finite.of_surjective e e.surjective
#check rationalResidue_finite
#print axioms rationalResidue_finite
#check arithmeticValuationSubring_eq
#print axioms arithmeticValuationSubring_eq
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem localInteger_compactSpace (v : FinitePlace K) :
    CompactSpace (v.adicCompletionIntegers K) := by
  letI := rationalResidue_finite K v
  letI : Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K))) :=
    localResidue_finite_of_rational_residue K v
  exact isCompact_iff_compactSpace.mp (localInteger_compact_of_finite_residue K v)

theorem localIntegralUnits_compactSpace (v : FinitePlace K) :
    CompactSpace (v.adicCompletionIntegers K)ˣ := by
  letI := localInteger_compactSpace K v
  infer_instance


end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual finite idele group with its units topology. -/
abbrev FiniteIdeles := (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ

noncomputable def finiteIntegralUnitIdele
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) : FiniteIdeles K where
  val := RestrictedProduct.structureMap _ _ Filter.cofinite (fun v => (x v).val)
  inv := RestrictedProduct.structureMap _ _ Filter.cofinite (fun v => (x v).inv)
  val_inv := by
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    exact congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).val_inv
  inv_val := by
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    exact congrArg (fun a : v.adicCompletionIntegers K => (a : LocalField K v)) (x v).inv_val

/-- Integral units require both an adele and its inverse to be integral everywhere. -/
def finiteIntegralUnits : Subgroup (FiniteIdeles K) where
  carrier := {a | (∀ v, a.val v ∈ v.adicCompletionIntegers K) ∧
    (∀ v, a.inv v ∈ v.adicCompletionIntegers K)}
  one_mem' := ⟨fun v => (v.adicCompletionIntegers K).one_mem,
    fun v => (v.adicCompletionIntegers K).one_mem⟩
  mul_mem' := by
    rintro a b ⟨ha, hai⟩ ⟨hb, hbi⟩
    exact ⟨fun v => (v.adicCompletionIntegers K).mul_mem _ _ (ha v) (hb v),
      fun v => (v.adicCompletionIntegers K).mul_mem _ _ (hbi v) (hai v)⟩
  inv_mem' := by
    rintro a ⟨ha, hi⟩
    exact ⟨hi, ha⟩

theorem finiteIntegralUnitIdele_continuous : Continuous (finiteIntegralUnitIdele K) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v))
  · exact RestrictedProduct.isEmbedding_structureMap.continuous.comp
      (continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v))

theorem finiteIntegralUnits_eq_range :
    (finiteIntegralUnits K : Set (FiniteIdeles K)) = Set.range (finiteIntegralUnitIdele K) := by
  ext a
  constructor
  · rintro ⟨ha, hi⟩
    let x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ := fun v =>
      { val := ⟨a.val v, ha v⟩
        inv := ⟨a.inv v, hi v⟩
        val_inv := Subtype.ext (congrArg (fun z : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => z v) a.val_inv)
        inv_val := Subtype.ext (congrArg (fun z : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => z v) a.inv_val) }
    refine ⟨x, Units.ext ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl
  · rintro ⟨x, rfl⟩
    exact ⟨fun v => (x v).val.property, fun v => (x v).inv.property⟩

theorem finiteIntegralUnits_isCompact :
    IsCompact (finiteIntegralUnits K : Set (FiniteIdeles K)) := by
  letI (v : FinitePlace K) : CompactSpace (v.adicCompletionIntegers K)ˣ :=
    localIntegralUnits_compactSpace K v
  rw [finiteIntegralUnits_eq_range]
  exact isCompact_range (finiteIntegralUnitIdele_continuous K)

theorem finiteIntegralUnits_isOpen :
    IsOpen (finiteIntegralUnits K : Set (FiniteIdeles K)) := by
  have ho : IsOpen {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K |
      ∀ v, a v ∈ v.adicCompletionIntegers K} :=
    RestrictedProduct.isOpen_forall_mem (fun v =>
      (Valued.isClopen_closedBall (LocalField K v)
        (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen)
  exact (ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)

noncomputable def finiteIntegralUnitsPositiveCompact : TopologicalSpace.PositiveCompacts (FiniteIdeles K) :=
  ⟨⟨finiteIntegralUnits K, finiteIntegralUnits_isCompact K⟩, by
    rw [(finiteIntegralUnits_isOpen K).interior_eq]
    exact ⟨1, (finiteIntegralUnits K).one_mem⟩⟩

theorem finiteIdeles_locallyCompactSpace : LocallyCompactSpace (FiniteIdeles K) :=
  (finiteIntegralUnitsPositiveCompact K).locallyCompactSpace_of_group

local instance : MeasurableSpace (FiniteIdeles K) := borel _
local instance : BorelSpace (FiniteIdeles K) := ⟨rfl⟩

/-- Actual multiplicative Haar measure, normalized on the full integral-unit subgroup. -/
noncomputable def normalizedFiniteIdeleHaar : MeasureTheory.Measure (FiniteIdeles K) :=
  MeasureTheory.Measure.haarMeasure (finiteIntegralUnitsPositiveCompact K)

theorem normalizedFiniteIdeleHaar_isHaar :
    MeasureTheory.Measure.IsHaarMeasure (normalizedFiniteIdeleHaar K) := by
  unfold normalizedFiniteIdeleHaar
  infer_instance

theorem normalizedFiniteIdeleHaar_units :
    normalizedFiniteIdeleHaar K (finiteIntegralUnits K) = 1 :=
  MeasureTheory.Measure.haarMeasure_self

theorem exists_normalizedFiniteIdeleHaar :
    ∃ μ : MeasureTheory.Measure (FiniteIdeles K),
      MeasureTheory.Measure.IsHaarMeasure μ ∧ μ (finiteIntegralUnits K) = 1 :=
  ⟨normalizedFiniteIdeleHaar K, normalizedFiniteIdeleHaar_isHaar K,
    normalizedFiniteIdeleHaar_units K⟩

#check finiteIntegralUnits_isCompact
#print axioms finiteIntegralUnits_isCompact
#check finiteIntegralUnits_isOpen
#print axioms finiteIntegralUnits_isOpen
#check finiteIdeles_locallyCompactSpace
#print axioms finiteIdeles_locallyCompactSpace
#check normalizedFiniteIdeleHaar_isHaar
#print axioms normalizedFiniteIdeleHaar_isHaar
#check normalizedFiniteIdeleHaar_units
#print axioms normalizedFiniteIdeleHaar_units
#check exists_normalizedFiniteIdeleHaar
#print axioms exists_normalizedFiniteIdeleHaar
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def finiteIdeleToFull (a : FiniteIdeles K) :
    (NumberField.AdeleRing (𝓞 K) K)ˣ where
  val := (1, a.val)
  inv := (1, a.inv)
  val_inv := Prod.ext (one_mul 1) a.val_inv
  inv_val := Prod.ext (one_mul 1) a.inv_val

noncomputable def finiteIdeleFromFull (a : finiteIdelicSubgroup K) : FiniteIdeles K where
  val := a.val.val.2
  inv := a.val.inv.2
  val_inv := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2) a.val.val_inv
  inv_val := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2) a.val.inv_val

noncomputable def finiteIdelesMulEquivSubgroup : FiniteIdeles K ≃* finiteIdelicSubgroup K where
  toFun a := ⟨finiteIdeleToFull K a, rfl⟩
  invFun := finiteIdeleFromFull K
  left_inv a := Units.ext rfl
  right_inv a := by
    apply Subtype.ext
    apply Units.ext
    exact Prod.ext a.property.symm rfl
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    exact Prod.ext (one_mul 1).symm rfl

noncomputable def finiteIdelesHomeomorphSubgroup : FiniteIdeles K ≃ₜ finiteIdelicSubgroup K where
  toEquiv := (finiteIdelesMulEquivSubgroup K).toEquiv
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Units.continuous_iff.mpr
    exact ⟨continuous_const.prodMk Units.continuous_val,
      continuous_const.prodMk Units.continuous_coe_inv⟩
  continuous_invFun := by
    apply Units.continuous_iff.mpr
    exact ⟨continuous_snd.comp (Units.continuous_val.comp continuous_subtype_val),
      continuous_snd.comp (Units.continuous_coe_inv.comp continuous_subtype_val)⟩

/-- The topological identification respects the actual finite coordinates. -/
theorem finiteIdelesSubgroup_finite_coordinate (a : FiniteIdeles K) (v : FinitePlace K) :
    ((finiteIdelesMulEquivSubgroup K a).val).val.2 v = a.val v := rfl

/-- The compact normalization set transported to the existing shell domain. -/
def finiteSubgroupIntegralUnits : Set (finiteIdelicSubgroup K) :=
  (finiteIdelesHomeomorphSubgroup K) '' (finiteIntegralUnits K : Set (FiniteIdeles K))

theorem finiteSubgroupIntegralUnits_isCompact : IsCompact (finiteSubgroupIntegralUnits K) :=
  (finiteIntegralUnits_isCompact K).image (finiteIdelesHomeomorphSubgroup K).continuous

theorem finiteSubgroupIntegralUnits_isOpen : IsOpen (finiteSubgroupIntegralUnits K) :=
  (finiteIdelesHomeomorphSubgroup K).isOpenMap _ (finiteIntegralUnits_isOpen K)

theorem finiteSubgroupIntegralUnits_iff (a : finiteIdelicSubgroup K) :
    a ∈ finiteSubgroupIntegralUnits K ↔
      (∀ v, a.val.val.2 v ∈ v.adicCompletionIntegers K) ∧
      (∀ v, a.val.inv.2 v ∈ v.adicCompletionIntegers K) := by
  change a ∈ (finiteIdelesHomeomorphSubgroup K) '' (finiteIntegralUnits K : Set (FiniteIdeles K)) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    refine ⟨(finiteIdelesHomeomorphSubgroup K).symm a, ha, ?_⟩
    exact (finiteIdelesHomeomorphSubgroup K).apply_symm_apply a

#check finiteIdelesMulEquivSubgroup
#print axioms finiteIdelesMulEquivSubgroup
#check finiteIdelesHomeomorphSubgroup
#print axioms finiteIdelesHomeomorphSubgroup
#check finiteSubgroupIntegralUnits_iff
#print axioms finiteSubgroupIntegralUnits_iff
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def finiteSubgroupUnitsPositiveCompact :
    TopologicalSpace.PositiveCompacts (finiteIdelicSubgroup K) :=
  ⟨⟨finiteSubgroupIntegralUnits K, finiteSubgroupIntegralUnits_isCompact K⟩, by
    rw [(finiteSubgroupIntegralUnits_isOpen K).interior_eq]
    exact ⟨finiteIdelesHomeomorphSubgroup K 1, 1, (finiteIntegralUnits K).one_mem, rfl⟩⟩

local instance : MeasurableSpace (finiteIdelicSubgroup K) := borel _
local instance : BorelSpace (finiteIdelicSubgroup K) := ⟨rfl⟩

noncomputable def normalizedFiniteSubgroupHaar :
    MeasureTheory.Measure (finiteIdelicSubgroup K) :=
  MeasureTheory.Measure.haarMeasure (finiteSubgroupUnitsPositiveCompact K)

theorem exists_normalizedFiniteSubgroupHaar :
    ∃ μ : MeasureTheory.Measure (finiteIdelicSubgroup K),
      MeasureTheory.Measure.IsHaarMeasure μ ∧ μ (finiteSubgroupIntegralUnits K) = 1 := by
  refine ⟨normalizedFiniteSubgroupHaar K, ?_, MeasureTheory.Measure.haarMeasure_self⟩
  unfold normalizedFiniteSubgroupHaar
  infer_instance

/-- The normalization domain is exactly the valuation-zero shell. -/
theorem finiteSubgroupIntegralUnits_valuation_one (a : finiteIdelicSubgroup K) :
    a ∈ finiteSubgroupIntegralUnits K ↔ ∀ v : FinitePlace K,
      Valued.v (a.val.val.2 v) = 1 := by
  rw [finiteSubgroupIntegralUnits_iff]
  constructor
  · rintro ⟨hv, hi⟩ v
    have hvv : Valued.v (a.val.val.2 v) ≤ 1 := hv v
    have hiv : Valued.v (a.val.inv.2 v) ≤ 1 := hi v
    have hm : Valued.v (a.val.val.2 v) * Valued.v (a.val.inv.2 v) = 1 := by
      rw [← map_mul]
      have h := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2 v) a.val.val_inv
      change a.val.val.2 v * a.val.inv.2 v = 1 at h
      rw [h, map_one]
    apply le_antisymm hvv
    calc
      1 = Valued.v (a.val.val.2 v) * Valued.v (a.val.inv.2 v) := hm.symm
      _ ≤ Valued.v (a.val.val.2 v) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hv
    refine ⟨fun v => le_of_eq (hv v), ?_⟩
    intro v
    have hm : Valued.v (a.val.val.2 v) * Valued.v (a.val.inv.2 v) = 1 := by
      rw [← map_mul]
      have h := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2 v) a.val.val_inv
      change a.val.val.2 v * a.val.inv.2 v = 1 at h
      rw [h, map_one]
    rw [hv v, one_mul] at hm
    exact le_of_eq hm

#check exists_normalizedFiniteSubgroupHaar
#print axioms exists_normalizedFiniteSubgroupHaar
#check finiteSubgroupIntegralUnits_valuation_one
#print axioms finiteSubgroupIntegralUnits_valuation_one
end MasulloGRH


namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (finiteIdelicSubgroup K) := borel _
local instance : BorelSpace (finiteIdelicSubgroup K) := ⟨rfl⟩

theorem finiteIntegralUnitSet_eq_normalization :
    finiteIntegralUnitSet K = finiteSubgroupIntegralUnits K := by
  ext a
  rw [finiteSubgroupIntegralUnits_valuation_one]
  constructor
  · rintro ⟨u, rfl⟩
    exact integralIdele_coordinate_valuation K u
  · intro ha
    obtain ⟨u, hu⟩ := genuineIdele_integralUnit_representation K a.val a.property ha
    exact ⟨u, Subtype.ext hu⟩

theorem normalizedFiniteSubgroupHaar_isHaar :
    (normalizedFiniteSubgroupHaar K).IsHaarMeasure := by
  unfold normalizedFiniteSubgroupHaar
  infer_instance

theorem normalizedFiniteSubgroupHaar_unitSet :
    normalizedFiniteSubgroupHaar K (finiteIntegralUnitSet K) = 1 := by
  rw [finiteIntegralUnitSet_eq_normalization]
  exact Measure.haarMeasure_self

theorem normalizedFiniteSubgroupHaar_shell (a : finiteIdelicSubgroup K) :
    normalizedFiniteSubgroupHaar K (finiteValuationShell K a) = 1 := by
  letI := normalizedFiniteSubgroupHaar_isHaar K
  exact finiteValuationShell_measure_one K _ (normalizedFiniteSubgroupHaar_unitSet K) a

/-- The measure is constructed, not assumed. Only the integrand's unit invariance is a premise. -/
theorem normalizedFiniteSubgroupHaar_integral_of_invariant
    (F : HeckeIdeles K → ℂ)
    (hF : ∀ a u, F (a * integralIdele K u) = F a)
    (a : finiteIdelicSubgroup K) :
    IntegrableOn (fun b : finiteIdelicSubgroup K => F b.val)
      (finiteValuationShell K a) (normalizedFiniteSubgroupHaar K) ∧
    (∫ b in finiteValuationShell K a, F b.val ∂normalizedFiniteSubgroupHaar K) = F a.val := by
  letI := normalizedFiniteSubgroupHaar_isHaar K
  exact finiteValuationShell_integral_of_invariant K F hF _
    (normalizedFiniteSubgroupHaar_unitSet K) a

#check finiteIntegralUnitSet_eq_normalization
#print axioms finiteIntegralUnitSet_eq_normalization
#check normalizedFiniteSubgroupHaar_shell
#print axioms normalizedFiniteSubgroupHaar_shell
#check normalizedFiniteSubgroupHaar_integral_of_invariant
#print axioms normalizedFiniteSubgroupHaar_integral_of_invariant
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (finiteIdelicSubgroup K) := borel _
local instance : BorelSpace (finiteIdelicSubgroup K) := ⟨rfl⟩

/-- Genuine finite test and character, with the finite valuation Mellin weight,
integrated on an actual shell against a constructed normalized Haar measure. -/
theorem finiteMellinIntegrand_normalizedHaar_shell
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (a : finiteIdelicSubgroup K) :
    (normalizedFiniteSubgroupHaar K).IsHaarMeasure ∧
    normalizedFiniteSubgroupHaar K (finiteIntegralUnitSet K) = 1 ∧
    normalizedFiniteSubgroupHaar K (finiteValuationShell K a) = 1 ∧
    IntegrableOn (fun b : finiteIdelicSubgroup K => finiteMellinIntegrand K χ s b.val)
      (finiteValuationShell K a) (normalizedFiniteSubgroupHaar K) ∧
    (∫ b in finiteValuationShell K a, finiteMellinIntegrand K χ s b.val
      ∂normalizedFiniteSubgroupHaar K) = finiteMellinIntegrand K χ s a.val := by
  exact ⟨normalizedFiniteSubgroupHaar_isHaar K,
    normalizedFiniteSubgroupHaar_unitSet K, normalizedFiniteSubgroupHaar_shell K a,
    normalizedFiniteSubgroupHaar_integral_of_invariant K (finiteMellinIntegrand K χ s)
      (finiteMellinIntegrand_integralUnit_invariant K χ s) a⟩

#check finiteMellinIntegrand_normalizedHaar_shell
#print axioms finiteMellinIntegrand_normalizedHaar_shell
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
lemma residueNorm_pos (v : FinitePlace K) : 0 < (v.asIdeal.absNorm : ℝ) := by
  exact_mod_cast lt_trans Nat.zero_lt_one
    (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)

lemma residueNorm_nnreal_ne_zero (v : FinitePlace K) :
    (v.asIdeal.absNorm : NNReal) ≠ 0 := by
  exact_mod_cast (ne_of_gt (residueNorm_pos K v))

/-- Product of the normalized local absolute values of the actual finite coordinates. -/
noncomputable def arithmeticFiniteIdeleNorm (a : HeckeIdeles K) : ℝ :=
  ∏ᶠ v : FinitePlace K, ((WithZeroMulInt.toNNReal
    (residueNorm_nnreal_ne_zero K v) (Valued.v (a.val.2 v)) : NNReal) : ℝ)

/-- Actual normalized valuations determine the arithmetic finite norm. -/
theorem arithmeticFiniteIdeleNorm_of_valuations (a : HeckeIdeles K)
    (n : FinitePlace K →₀ ℤ)
    (hn : ∀ v, Valued.v (a.val.2 v) = WithZero.exp (-(n v))) :
    arithmeticFiniteIdeleNorm K a =
      ∏ v ∈ n.support, (v.asIdeal.absNorm : ℝ) ^ (-(n v)) := by
  classical
  have hlocal (v : FinitePlace K) :
      ((WithZeroMulInt.toNNReal (residueNorm_nnreal_ne_zero K v)
        (Valued.v (a.val.2 v)) : NNReal) : ℝ) =
          (v.asIdeal.absNorm : ℝ) ^ (-(n v)) := by
    rw [hn, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp
  unfold arithmeticFiniteIdeleNorm
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := n.support) (by
    intro v hv
    apply Finsupp.mem_support_iff.mpr
    intro hz
    apply hv
    simp [hlocal, hz])]
  exact Finset.prod_congr rfl (fun v _ => hlocal v)

lemma positive_zpow_cpow (q : ℝ) (hq : 0 < q) (m : ℤ) (s : ℂ) :
    ((q ^ (-m) : ℝ) : ℂ) ^ s = ((q : ℂ) ^ (-s)) ^ m := by
  rw [Complex.ofReal_zpow,
    ← Complex.cpow_int_mul' (x := (q : ℂ)) (n := -m)
      (by simp [Complex.arg_ofReal_of_nonneg hq.le, Real.pi_pos])
      (by simpa only [Complex.arg_ofReal_of_nonneg hq.le, mul_zero] using Real.pi_pos.le) s,
    ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

theorem arithmeticFiniteIdeleNorm_cpow_of_valuations (a : HeckeIdeles K)
    (n : FinitePlace K →₀ ℤ)
    (hn : ∀ v, Valued.v (a.val.2 v) = WithZero.exp (-(n v))) (s : ℂ) :
    (arithmeticFiniteIdeleNorm K a : ℂ) ^ s =
      ∏ v ∈ n.support, ((v.asIdeal.absNorm : ℂ) ^ (-s)) ^ n v := by
  classical
  rw [arithmeticFiniteIdeleNorm_of_valuations K a n hn]
  induction n.support using Finset.induction_on with
  | empty => simp
  | @insert v S hv ih =>
      rw [Finset.prod_insert hv, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (le_of_lt (zpow_pos (residueNorm_pos K v) _))
          (Finset.prod_nonneg (fun w _ => le_of_lt (zpow_pos (residueNorm_pos K w) _))),
        ih, Finset.prod_insert hv]
      rw [positive_zpow_cpow _ (residueNorm_pos K v)]
      simp only [Complex.ofReal_natCast]

#check arithmeticFiniteIdeleNorm_of_valuations
#print axioms arithmeticFiniteIdeleNorm_of_valuations
#check arithmeticFiniteIdeleNorm_cpow_of_valuations
#print axioms arithmeticFiniteIdeleNorm_cpow_of_valuations
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (finiteIdelicSubgroup K) := borel _
local instance : BorelSpace (finiteIdelicSubgroup K) := ⟨rfl⟩

theorem arithmeticFiniteIdeleNorm_integralUnit_invariant
    (a : HeckeIdeles K) (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    arithmeticFiniteIdeleNorm K (a * integralIdele K u) = arithmeticFiniteIdeleNorm K a := by
  unfold arithmeticFiniteIdeleNorm
  apply finprod_congr
  intro v
  have hv : Valued.v ((a * integralIdele K u).val.2 v) = Valued.v (a.val.2 v) := by
    change Valued.v (a.val.2 v * (integralIdele K u).val.2 v) = _
    rw [map_mul, integralIdele_coordinate_valuation, mul_one]
  rw [hv]

/-- The actual test, actual character restriction and complex power of the
arithmetic finite idele norm, with no assumed measure or integrability package. -/
noncomputable def actualFiniteMellinIntegrand (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (a : HeckeIdeles K) : ℂ :=
  (finiteAdelicTest K χ a.val.2 * (χ.character (finiteIdeleComponent K a) : ℂ)) *
    (arithmeticFiniteIdeleNorm K a : ℂ) ^ s

theorem actualFiniteMellinIntegrand_integralUnit_invariant
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (a : HeckeIdeles K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    actualFiniteMellinIntegrand K χ s (a * integralIdele K u) =
      actualFiniteMellinIntegrand K χ s a := by
  unfold actualFiniteMellinIntegrand
  rw [finiteAdelicTest_character_integralUnit_invariant,
    arithmeticFiniteIdeleNorm_integralUnit_invariant]

/-- Shell evaluation for every genuine unitary Hecke character, including
real norm twists, against actual constructed normalized multiplicative Haar. -/
theorem actualFiniteMellinIntegrand_normalizedHaar_shell
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (a : finiteIdelicSubgroup K) :
    (normalizedFiniteSubgroupHaar K).IsHaarMeasure ∧
    normalizedFiniteSubgroupHaar K (finiteIntegralUnitSet K) = 1 ∧
    normalizedFiniteSubgroupHaar K (finiteValuationShell K a) = 1 ∧
    IntegrableOn (fun b : finiteIdelicSubgroup K => actualFiniteMellinIntegrand K χ s b.val)
      (finiteValuationShell K a) (normalizedFiniteSubgroupHaar K) ∧
    (∫ b in finiteValuationShell K a, actualFiniteMellinIntegrand K χ s b.val
      ∂normalizedFiniteSubgroupHaar K) = actualFiniteMellinIntegrand K χ s a.val := by
  exact ⟨normalizedFiniteSubgroupHaar_isHaar K,
    normalizedFiniteSubgroupHaar_unitSet K, normalizedFiniteSubgroupHaar_shell K a,
    normalizedFiniteSubgroupHaar_integral_of_invariant K (actualFiniteMellinIntegrand K χ s)
      (actualFiniteMellinIntegrand_integralUnit_invariant K χ s) a⟩

#check actualFiniteMellinIntegrand_normalizedHaar_shell
#print axioms actualFiniteMellinIntegrand_normalizedHaar_shell
end MasulloGRH
