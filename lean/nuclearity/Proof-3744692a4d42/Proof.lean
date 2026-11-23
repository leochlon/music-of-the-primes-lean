import Mathlib
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

/- C, round 32, checked compactness input. The finite-residue premise remains explicit. -/
theorem localInteger_isDiscreteValuationRing (v : FinitePlace K) :
    IsDiscreteValuationRing (Valued.integer (LocalField K v)) := by
  change IsDiscreteValuationRing (v.adicCompletionIntegers K)
  infer_instance

theorem localInteger_compact_of_finite_residue (v : FinitePlace K)
    (hfin : Finite (Valued.ResidueField (LocalField K v))) :
    CompactSpace (Valued.integer (LocalField K v)) := by
  apply Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
  refine ⟨?_, localInteger_isDiscreteValuationRing K v, hfin⟩
  exact (Valued.isClosed_closedBall (LocalField K v) 1).completeSpace_coe

/-- Compactness is in the additive local field, including its actual topology. -/
theorem additiveUnitShell_isCompact_of_finite_residue (v : FinitePlace K)
    (hfin : Finite (Valued.ResidueField (LocalField K v))) :
    IsCompact {x : LocalField K v | Valued.v x = 1} := by
  have hc : IsCompact {x : LocalField K v | Valued.v x ≤ 1} :=
    isCompact_iff_compactSpace.mpr (localInteger_compact_of_finite_residue K v hfin)
  exact hc.of_isClosed_subset
    (Valued.isClopen_sphere (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isClosed
    (fun _ hx => le_of_eq hx)

/-- Compact support for the genuine inverse-character additive shell test. -/
theorem ramifiedAdditiveTest_hasCompactSupport_of_finite_residue
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (hfin : Finite (Valued.ResidueField (LocalField K v))) :
    HasCompactSupport (ramifiedAdditiveTest K χ v : LocalField K v → ℂ) := by
  have hsub : Function.support (ramifiedAdditiveTest K χ v : LocalField K v → ℂ) ⊆
      {x : LocalField K v | Valued.v x = 1} := by
    intro x hx
    by_contra h
    exact hx (ramifiedAdditiveTest_zero_off_shell K χ v x h)
  change IsCompact (closure (Function.support (ramifiedAdditiveTest K χ v : LocalField K v → ℂ)))
  exact (additiveUnitShell_isCompact_of_finite_residue K v hfin).of_isClosed_subset
    isClosed_closure (closure_minimal hsub
      (Valued.isClopen_sphere (LocalField K v)
        (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isClosed)

#check localInteger_compact_of_finite_residue
#print axioms localInteger_compact_of_finite_residue
#check additiveUnitShell_isCompact_of_finite_residue
#print axioms additiveUnitShell_isCompact_of_finite_residue
#check ramifiedAdditiveTest_hasCompactSupport_of_finite_residue
#print axioms ramifiedAdditiveTest_hasCompactSupport_of_finite_residue
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

theorem unramifiedAdditiveTest_hasCompactSupport_of_finite_residue
    (v : FinitePlace K) (hfin : Finite (Valued.ResidueField (LocalField K v))) :
    HasCompactSupport (unramifiedAdditiveTest K v : LocalField K v → ℂ) := by
  have hsub : Function.support (unramifiedAdditiveTest K v : LocalField K v → ℂ) ⊆
      {x : LocalField K v | Valued.v x ≤ 1} := by
    intro x hx
    by_contra h
    change ¬ Valued.v x ≤ 1 at h
    exact hx (by rw [unramifiedAdditiveTest_apply, if_neg h])
  have hc : IsCompact {x : LocalField K v | Valued.v x ≤ 1} :=
    isCompact_iff_compactSpace.mpr (localInteger_compact_of_finite_residue K v hfin)
  change IsCompact (closure (Function.support (unramifiedAdditiveTest K v : LocalField K v → ℂ)))
  exact hc.of_isClosed_subset isClosed_closure
    (closure_minimal hsub (Valued.isClosed_closedBall (LocalField K v) 1))

/-- The actual local additive test used in the finite Hecke Euler integral. -/
noncomputable def finiteAdditiveTest (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) :
    LocallyConstant (LocalField K v) ℂ := by
  classical
  exact if IsUnramified K χ v then unramifiedAdditiveTest K v else ramifiedAdditiveTest K χ v

theorem finiteAdditiveTest_hasCompactSupport_of_finite_residue
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (hfin : Finite (Valued.ResidueField (LocalField K v))) :
    HasCompactSupport (finiteAdditiveTest K χ v : LocalField K v → ℂ) := by
  classical
  unfold finiteAdditiveTest
  split_ifs
  · exact unramifiedAdditiveTest_hasCompactSupport_of_finite_residue K v hfin
  · exact ramifiedAdditiveTest_hasCompactSupport_of_finite_residue K χ v hfin

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
#check unramifiedAdditiveTest_hasCompactSupport_of_finite_residue
#print axioms unramifiedAdditiveTest_hasCompactSupport_of_finite_residue
#check finiteAdditiveTest_hasCompactSupport_of_finite_residue
#print axioms finiteAdditiveTest_hasCompactSupport_of_finite_residue
#check finiteAdditiveTest_restrict
#print axioms finiteAdditiveTest_restrict
#check finiteAdditiveTest_finite_exceptional_set
#print axioms finiteAdditiveTest_finite_exceptional_set
end MasulloGRH

/- Reused C round-28 genuine finite local Mellin calculation; receipt 498d0323d2ed4e169d82d39e6c5310fd. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
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

#check heckePrimeCoefficient_norm
#print axioms heckePrimeCoefficient_norm
theorem localUniformizer_valuation (v : FinitePlace K) :
    Valued.v (localUniformizer K v : LocalField K v) = WithZero.exp (-1) := by
  change Valued.v ((Classical.choose (v.valuation_exists_uniformizer K) : K) :
    LocalField K v) = WithZero.exp (-1)
  rw [v.valuedAdicCompletion_eq_valuation']
  exact Classical.choose_spec (v.valuation_exists_uniformizer K)

/-- Two actual uniformizers give the same unramified Euler coefficient. -/
theorem unramified_uniformizer_independent (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    (x y : (LocalField K v)ˣ)
    (hx : Valued.v (x : LocalField K v) = WithZero.exp (-1))
    (hy : Valued.v (y : LocalField K v) = WithZero.exp (-1)) :
    localCharacter K χ v y = localCharacter K χ v x := by
  have hu : Valued.v ((x⁻¹ * y : (LocalField K v)ˣ) : LocalField K v) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hy]
    simp
  simpa using unramified_local_invariance K χ v hχ x (x⁻¹ * y) hu

#check localUniformizer_valuation
#print axioms localUniformizer_valuation
#check unramified_uniformizer_independent
#print axioms unramified_uniformizer_independent
/-- Exact norm of the arithmetic term in the genuine finite Euler factor. -/
theorem heckeEulerTerm_norm (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) (s : ℂ) :
    ‖heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  rw [norm_mul, heckePrimeCoefficient_norm, one_mul]
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast lt_trans Nat.zero_lt_one
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)
  simpa only [Complex.ofReal_natCast, Complex.neg_re] using
    Complex.norm_cpow_eq_rpow_re_of_pos hq (-s)

/-- No denominator of a genuine local Euler factor vanishes in Re(s)>0. -/
theorem heckeEulerDenominator_ne_zero (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hn : ‖heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
    rw [heckeEulerTerm_norm]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  intro h
  have he := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hn
  exact (lt_irrefl 1) hn

theorem heckeEulerFactor_ne_zero (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    heckeEulerFactor K χ v s ≠ 0 := by
  classical
  unfold heckeEulerFactor
  split_ifs
  · exact inv_ne_zero (heckeEulerDenominator_ne_zero K χ v s hs)
  · exact one_ne_zero

/-- Actual finite arithmetic Euler products are nonzero on the initial half-plane. -/
theorem partialHeckeEulerProduct_ne_zero (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (s : ℂ) (hs : 0 < s.re) :
    partialHeckeEulerProduct K χ S s ≠ 0 := by
  classical
  unfold partialHeckeEulerProduct
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => heckeEulerFactor_ne_zero K χ v s hs)

#check heckeEulerTerm_norm
#print axioms heckeEulerTerm_norm
#check heckeEulerDenominator_ne_zero
#print axioms heckeEulerDenominator_ne_zero
#check heckeEulerFactor_ne_zero
#print axioms heckeEulerFactor_ne_zero
#check partialHeckeEulerProduct_ne_zero
#print axioms partialHeckeEulerProduct_ne_zero
/-- The arithmetic ratio in the unramified local zeta integral. -/
noncomputable def localZetaRatio (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) : ℂ :=
  heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)

/-- Actual unramified Euler factors are the convergent valuation-ray series.
This is the scalar local calculation needed in the adelic Mellin integral;
the Haar-integral identification is not assumed or asserted here. -/
theorem unramified_localZeta_hasSum (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (localZetaRatio K χ v s) ^ n)
      (heckeEulerFactor K χ v s) := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hr : ‖localZetaRatio K χ v s‖ < 1 := by
    rw [localZetaRatio, heckeEulerTerm_norm]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  simpa only [heckeEulerFactor, if_pos hχ, localZetaRatio, one_div] using
    hasSum_geometric_of_norm_lt_one hr

#check unramified_localZeta_hasSum
#print axioms unramified_localZeta_hasSum
/-- The genuine local component as a group homomorphism. -/
noncomputable def localCharacterHom (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) : (LocalField K v)ˣ →* Circle :=
  MonoidHom.mk' (localCharacter K χ v) (localCharacter_mul K χ v)

/-- The summands are the values of the actual local character on valuation shells,
not a new character or analytic proxy. -/
theorem localCharacter_uniformizer_pow (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (n : ℕ) :
    (localCharacter K χ v (localUniformizer K v ^ n) : ℂ) =
      heckePrimeCoefficient K χ v ^ n := by
  change ((localCharacterHom K χ v (localUniformizer K v ^ n) : Circle) : ℂ) = _
  rw [map_pow]
  change ((localCharacter K χ v (localUniformizer K v) ^ n : Circle) : ℂ) =
    (localCharacter K χ v (localUniformizer K v) : ℂ) ^ n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ]
    change (localCharacter K χ v (localUniformizer K v) ^ n : Circle).val *
      (localCharacter K χ v (localUniformizer K v) : ℂ) = _
    rw [ih]

/-- Unramified local Mellin-series calculation for the actual idelic character.
Identifying the normalized multiplicative Haar integral with this shell series
is the remaining local measure-theoretic obligation. -/
theorem unramified_localMellinSeries_hasSum (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun n : ℕ =>
      (localCharacter K χ v (localUniformizer K v ^ n) : ℂ) *
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n)
      (heckeEulerFactor K χ v s) := by
  convert unramified_localZeta_hasSum K χ v hχ s hs using 1
  funext n
  rw [localCharacter_uniformizer_pow, localZetaRatio, mul_pow]

#check localCharacter_uniformizer_pow
#print axioms localCharacter_uniformizer_pow
#check unramified_localMellinSeries_hasSum
#print axioms unramified_localMellinSeries_hasSum
/-- A valuation shell is a coset of the actual local valuation-unit group. -/
theorem uniformizer_shell_unit (v : FinitePlace K) (n : ℕ)
    (x : (LocalField K v)ˣ)
    (hx : Valued.v (x : LocalField K v) =
      Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v)) :
    ∃ u : (LocalField K v)ˣ, Valued.v (u : LocalField K v) = 1 ∧
      x = localUniformizer K v ^ n * u := by
  let y := localUniformizer K v ^ n
  have hy : Valued.v (y : LocalField K v) ≠ 0 := by
    have hh : Valued.v (y : LocalField K v) *
        Valued.v ((y⁻¹ : (LocalField K v)ˣ) : LocalField K v) = 1 := by
      rw [← map_mul]
      simp
    intro h
    rw [h, zero_mul] at hh
    exact zero_ne_one hh
  refine ⟨y⁻¹ * x, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx]
    exact inv_mul_cancel₀ hy
  · simp [y]

/-- The genuine unramified character is constant on each such shell. -/
theorem unramified_shell_character (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v) (n : ℕ)
    (x : (LocalField K v)ˣ)
    (hx : Valued.v (x : LocalField K v) =
      Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v)) :
    localCharacter K χ v x = localCharacter K χ v (localUniformizer K v ^ n) := by
  obtain ⟨u, hu, hxu⟩ := uniformizer_shell_unit K v n x hx
  rw [hxu, unramified_local_invariance K χ v hχ _ u hu]

#check uniformizer_shell_unit
#print axioms uniformizer_shell_unit
#check unramified_shell_character
#print axioms unramified_shell_character

/-- The local Mellin series is independent of every choice of representative
in the genuine nonnegative valuation shells. This is the shell-level input
for the normalized multiplicative Haar-integral calculation. -/
theorem unramified_shellMellinSeries_hasSum (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    (x : ℕ → (LocalField K v)ˣ)
    (hx : ∀ n, Valued.v (x n : LocalField K v) =
      Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v))
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun n : ℕ => (localCharacter K χ v (x n) : ℂ) *
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n)
      (heckeEulerFactor K χ v s) := by
  have he : (fun n : ℕ => (localCharacter K χ v (x n) : ℂ) *
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n) =
      (fun n : ℕ => (localCharacter K χ v (localUniformizer K v ^ n) : ℂ) *
      ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ n) := by
    funext n
    rw [unramified_shell_character K χ v hχ n (x n) (hx n)]
  rw [he]
  exact unramified_localMellinSeries_hasSum K χ v hχ s hs

#check unramified_shellMellinSeries_hasSum
#print axioms unramified_shellMellinSeries_hasSum
/-- Nonzero local elements have nonzero valuation. -/
theorem localUnit_valuation_ne_zero (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    Valued.v (x : LocalField K v) ≠ 0 := by
  have h : Valued.v (x : LocalField K v) *
      Valued.v ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) = 1 := by
    rw [← map_mul]
    simp
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

/-- The actual uniformizer has the expected integer-power valuation. -/
theorem localUniformizer_zpow_valuation (v : FinitePlace K) (n : ℤ) :
    Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v) =
      WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, localUniformizer_valuation,
    ← WithZero.exp_zsmul]
  congr 1
  simp

theorem localUniformizer_pow_valuation (v : FinitePlace K) (n : ℕ) :
    Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v) =
      WithZero.exp (-(n : ℤ)) := by
  simpa only [zpow_natCast] using localUniformizer_zpow_valuation K v (n : ℤ)

/-- The integral nonzero elements are partitioned by the actual nonnegative
uniformizer shells. This discharges the indexing obligation for the local
Haar-integral calculation; no measure identity is assumed here. -/
theorem integral_localUnit_unique_shell (v : FinitePlace K)
    (x : (LocalField K v)ˣ) (hx : Valued.v (x : LocalField K v) ≤ 1) :
    ∃! n : ℕ, Valued.v (x : LocalField K v) =
      Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v) := by
  have hx0 := localUnit_valuation_ne_zero K v x
  have hl : (Valued.v (x : LocalField K v)).log ≤ 0 := by
    apply WithZero.exp_le_exp.mp
    simpa only [WithZero.exp_log hx0, WithZero.exp_zero] using hx
  let n : ℕ := (-(Valued.v (x : LocalField K v)).log).toNat
  have hn : (n : ℤ) = -(Valued.v (x : LocalField K v)).log :=
    Int.toNat_of_nonneg (neg_nonneg.mpr hl)
  have he : Valued.v (x : LocalField K v) =
      Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v) := by
    rw [localUniformizer_pow_valuation, hn, neg_neg, WithZero.exp_log hx0]
  refine ⟨n, he, ?_⟩
  intro m hm
  have hm' := hm.symm.trans he
  rw [localUniformizer_pow_valuation, localUniformizer_pow_valuation] at hm'
  have hi := WithZero.exp_injective hm'
  omega

#check localUnit_valuation_ne_zero
#print axioms localUnit_valuation_ne_zero
#check localUniformizer_zpow_valuation
#print axioms localUniformizer_zpow_valuation
#check localUniformizer_pow_valuation
#print axioms localUniformizer_pow_valuation
#check integral_localUnit_unique_shell
#print axioms integral_localUnit_unique_shell

/-- Each nonzero integral local element has a unique uniformizer-shell index,
a valuation-unit factor, and the corresponding genuine character value. -/
theorem integral_unramified_local_decomposition (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    (x : (LocalField K v)ˣ) (hx : Valued.v (x : LocalField K v) ≤ 1) :
    ∃! n : ℕ, ∃ u : (LocalField K v)ˣ,
      Valued.v (u : LocalField K v) = 1 ∧
      x = localUniformizer K v ^ n * u ∧
      (localCharacter K χ v x : ℂ) = heckePrimeCoefficient K χ v ^ n := by
  obtain ⟨n, hn, huniq⟩ := integral_localUnit_unique_shell K v x hx
  obtain ⟨u, hu, hxu⟩ := uniformizer_shell_unit K v n x hn
  refine ⟨n, ⟨u, hu, hxu, ?_⟩, ?_⟩
  · rw [unramified_shell_character K χ v hχ n x hn,
      localCharacter_uniformizer_pow]
  · intro m hm
    obtain ⟨w, hw, hxw, _⟩ := hm
    apply huniq m
    rw [hxw, Units.val_mul, map_mul, hw, mul_one]

#check integral_unramified_local_decomposition
#print axioms integral_unramified_local_decomposition

/-- The genuine multiplicative valuation shell at a finite place. -/
def localShell (v : FinitePlace K) (n : ℕ) : Set (LocalField K v)ˣ :=
  {x | Valued.v (x : LocalField K v) =
    Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v)}

/-- Every shell is the multiplicative translate of the local valuation-unit group. -/
theorem localShell_eq_mul_image (v : FinitePlace K) (n : ℕ) :
    localShell K v n =
      (fun u : (LocalField K v)ˣ => localUniformizer K v ^ n * u) '' localShell K v 0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, hxu⟩ := uniformizer_shell_unit K v n x hx
    refine ⟨u, ?_, hxu.symm⟩
    simpa [localShell] using hu
  · rintro ⟨u, hu, rfl⟩
    have hu' : Valued.v (u : LocalField K v) = 1 := by
      simpa [localShell] using hu
    change Valued.v ((localUniformizer K v ^ n * u : (LocalField K v)ˣ) :
      LocalField K v) = _
    rw [Units.val_mul, map_mul, hu', mul_one]

/-- Distinct genuine nonnegative valuation shells are disjoint. -/
theorem localShell_disjoint (v : FinitePlace K) {m n : ℕ} (h : m ≠ n) :
    Disjoint (localShell K v m) (localShell K v n) := by
  apply Set.disjoint_left.mpr
  intro x hm hn
  have he := hm.symm.trans hn
  rw [localUniformizer_pow_valuation, localUniformizer_pow_valuation] at he
  have hi := WithZero.exp_injective he
  apply h
  omega

/-- The integral nonzero elements are exactly the union of nonnegative shells. -/
theorem integral_localUnits_eq_iUnion (v : FinitePlace K) :
    {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1} =
      ⋃ n : ℕ, localShell K v n := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn, _⟩ := integral_localUnit_unique_shell K v x hx
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    change Valued.v (x : LocalField K v) ≤ 1
    change Valued.v (x : LocalField K v) = _ at hn
    rw [hn, localUniformizer_pow_valuation]
    have h : -(n : ℤ) ≤ 0 := by omega
    simpa only [WithZero.exp_zero] using (WithZero.exp_le_exp.mpr h)

#check localShell_eq_mul_image
#print axioms localShell_eq_mul_image
#check localShell_disjoint
#print axioms localShell_disjoint
#check integral_localUnits_eq_iUnion
#print axioms integral_localUnits_eq_iUnion


/-- The local Mellin weight uses the integer valuation and the genuine residue norm. -/
noncomputable def localMellinIntegrand (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (x : (LocalField K v)ˣ) : ℂ :=
  (localCharacter K χ v x : ℂ) *
    ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (-(Valued.v (x : LocalField K v)).log)

/-- On an actual shell the Mellin integrand is the geometric-series term. -/
theorem localMellinIntegrand_on_shell (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v) (s : ℂ) (n : ℕ)
    (x : (LocalField K v)ˣ) (hx : x ∈ localShell K v n) :
    localMellinIntegrand K χ v s x = localZetaRatio K χ v s ^ n := by
  unfold localMellinIntegrand
  rw [unramified_shell_character K χ v hχ n x hx, localCharacter_uniformizer_pow]
  have hv : (Valued.v (x : LocalField K v)).log = -(n : ℤ) := by
    change Valued.v (x : LocalField K v) = _ at hx
    rw [hx, localUniformizer_pow_valuation, WithZero.log_exp]
  rw [hv, neg_neg, zpow_natCast]
  exact (mul_pow _ _ _).symm

open MeasureTheory

/-- Left-invariant multiplicative measures give every genuine shell the unit-shell mass. -/
theorem localShell_measure (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant] (n : ℕ) :
    μ (localShell K v n) = μ (localShell K v 0) := by
  have hpre : (fun x : (LocalField K v)ˣ => localUniformizer K v ^ n * x) ⁻¹'
      localShell K v n = localShell K v 0 := by
    rw [localShell_eq_mul_image]
    ext x
    change (∃ u ∈ localShell K v 0,
      localUniformizer K v ^ n * u = localUniformizer K v ^ n * x) ↔ _
    constructor
    · rintro ⟨u, hu, hux⟩
      have he : u = x := mul_left_cancel hux
      simpa only [he] using hu
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h := measure_preimage_mul μ (localUniformizer K v ^ n) (localShell K v n)
  rw [hpre] at h
  exact h.symm

/-- Each unramified local shell contributes exactly the corresponding Euler-series term,
for a normalized invariant measure and a measurable shell. -/
theorem localMellin_shell_integral (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    [MeasurableSpace (LocalField K v)ˣ] [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (n : ℕ)
    (hm : MeasurableSet (localShell K v n)) :
    ∫ x in localShell K v n, localMellinIntegrand K χ v s x ∂μ =
      localZetaRatio K χ v s ^ n := by
  calc
    _ = ∫ _x in localShell K v n, localZetaRatio K χ v s ^ n ∂μ := by
      apply setIntegral_congr_fun hm
      intro x hx
      exact localMellinIntegrand_on_shell K χ v hχ s n x hx
    _ = _ := by
      rw [setIntegral_const, Measure.real, localShell_measure K v μ n, hμ]
      simp

#check localMellinIntegrand_on_shell
#print axioms localMellinIntegrand_on_shell
#check localShell_measure
#print axioms localShell_measure
#check localMellin_shell_integral
#print axioms localMellin_shell_integral


/-- The actual finite-place zeta integral equals its Euler factor for a normalized
invariant measure with measurable shells; integrability is proved from geometric summability. -/
theorem unramified_localIntegral_eq_euler (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    [MeasurableSpace (LocalField K v)ˣ] [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1)
    (hm : ∀ n : ℕ, MeasurableSet (localShell K v n))
    (s : ℂ) (hs : 0 < s.re) :
    ∫ x in {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1},
      localMellinIntegrand K χ v s x ∂μ = heckeEulerFactor K χ v s := by
  have hi : ∀ n : ℕ, IntegrableOn (localMellinIntegrand K χ v s)
      (localShell K v n) μ := by
    intro n
    have hc : IntegrableOn (fun _x : (LocalField K v)ˣ => localZetaRatio K χ v s ^ n)
        (localShell K v n) μ := integrableOn_const (by
      rw [localShell_measure K v μ n, hμ]
      exact ENNReal.one_ne_top)
    exact hc.congr_fun (fun x hx =>
      (localMellinIntegrand_on_shell K χ v hχ s n x hx).symm) (hm n)
  have hn : ∀ n : ℕ,
      (∫ x in localShell K v n, ‖localMellinIntegrand K χ v s x‖ ∂μ) =
        ‖localZetaRatio K χ v s ^ n‖ := by
    intro n
    calc
      _ = ∫ _x in localShell K v n, ‖localZetaRatio K χ v s ^ n‖ ∂μ := by
        apply setIntegral_congr_fun (hm n)
        intro x hx
        exact congrArg norm (localMellinIntegrand_on_shell K χ v hχ s n x hx)
      _ = _ := by
        rw [setIntegral_const, Measure.real, localShell_measure K v μ n, hμ]
        simp
  have hfi : IntegrableOn (localMellinIntegrand K χ v s)
      (⋃ n : ℕ, localShell K v n) μ := by
    apply integrableOn_iUnion_of_summable_integral_norm hi
    simp_rw [hn]
    exact summable_norm_iff.mpr (unramified_localZeta_hasSum K χ v hχ s hs).summable
  rw [integral_localUnits_eq_iUnion]
  rw [integral_iUnion hm (fun m n h => localShell_disjoint K v h) hfi]
  simp_rw [localMellin_shell_integral K χ v hχ μ hμ s _ (hm _)]
  exact (unramified_localZeta_hasSum K χ v hχ s hs).tsum_eq

#check unramified_localIntegral_eq_euler
#print axioms unramified_localIntegral_eq_euler


/-- Actual finite-place valuation shells are clopen in the local multiplicative topology. -/
theorem localShell_isClopen (v : FinitePlace K) (n : ℕ) :
    IsClopen (localShell K v n) := by
  exact (Valued.isClopen_sphere (LocalField K v)
    (localUnit_valuation_ne_zero K v (localUniformizer K v ^ n))).preimage
      Units.continuous_val

/-- Shell measurability follows from the actual Borel topology, without an analytic premise. -/
theorem localShell_measurable (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ] (n : ℕ) :
    MeasurableSet (localShell K v n) :=
  (localShell_isClopen K v n).isClosed.measurableSet

/-- The unramified local zeta integral in the actual Borel space; the shell
measurability and integrability obligations are discharged. -/
theorem unramified_localIntegral_eq_euler_borel (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (hs : 0 < s.re) :
    ∫ x in {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1},
      localMellinIntegrand K χ v s x ∂μ = heckeEulerFactor K χ v s :=
  unramified_localIntegral_eq_euler K χ v hχ μ hμ
    (localShell_measurable K v) s hs

#check localShell_isClopen
#print axioms localShell_isClopen
#check localShell_measurable
#print axioms localShell_measurable
#check unramified_localIntegral_eq_euler_borel
#print axioms unramified_localIntegral_eq_euler_borel
/-- The character-compensated unit-shell test has local zeta integral one,
for every local component including ramified characters. -/
theorem localUnit_character_test_integral (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) (hμ : μ (localShell K v 0) = 1) (s : ℂ) :
    ∫ x in localShell K v 0,
      (localCharacter K χ v x : ℂ)⁻¹ * localMellinIntegrand K χ v s x ∂μ = 1 := by
  calc
    _ = ∫ _x in localShell K v 0, (1 : ℂ) ∂μ := by
      apply setIntegral_congr_fun (localShell_measurable K v 0)
      intro x hx
      have hv : Valued.v (x : LocalField K v) = 1 := by
        simpa [localShell] using hx
      have hc : (localCharacter K χ v x : ℂ) ≠ 0 := by
        exact norm_pos_iff.mp (by rw [Circle.norm_coe]; norm_num)
      simp [localMellinIntegrand, hv, hc]
    _ = _ := by
      rw [setIntegral_const, Measure.real, hμ]
      simp
#check localUnit_character_test_integral
#print axioms localUnit_character_test_integral

/-- The genuine finite-place test: the integral-unit indicator when unramified,
and the inverse character on the unit shell when ramified. Admissibility as an
additive Schwartz-Bruhat function remains a separate obligation. -/
noncomputable def finiteLocalTest (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) : (LocalField K v)ˣ → ℂ := by
  classical
  exact if IsUnramified K χ v then
    {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1}.indicator (fun _ => 1)
  else (localShell K v 0).indicator (fun x => (localCharacter K χ v x : ℂ)⁻¹)

/-- Every genuine finite Euler factor is realized by the explicit local test,
including ramified characters and without a norm-section restriction. -/
theorem finiteLocalTest_integral_eq_euler (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (hs : 0 < s.re) :
    ∫ x, finiteLocalTest K χ v x * localMellinIntegrand K χ v s x ∂μ =
      heckeEulerFactor K χ v s := by
  classical
  by_cases hχ : IsUnramified K χ v
  · have hm : MeasurableSet {x : (LocalField K v)ˣ |
        Valued.v (x : LocalField K v) ≤ 1} := by
      rw [integral_localUnits_eq_iUnion]
      exact MeasurableSet.iUnion (localShell_measurable K v)
    have he : (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) =
        {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1}.indicator
          (localMellinIntegrand K χ v s) := by
      funext x
      by_cases hx : x ∈ {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1}
      · simp [finiteLocalTest, hχ, Set.indicator_of_mem hx]
      · simp [finiteLocalTest, hχ, Set.indicator_of_notMem hx]
    rw [he, integral_indicator hm]
    exact unramified_localIntegral_eq_euler_borel K χ v hχ μ hμ s hs
  · have he : (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) =
        (localShell K v 0).indicator (fun x =>
          (localCharacter K χ v x : ℂ)⁻¹ * localMellinIntegrand K χ v s x) := by
      funext x
      by_cases hx : x ∈ localShell K v 0
      · simp [finiteLocalTest, hχ, Set.indicator_of_mem hx]
      · simp [finiteLocalTest, hχ, Set.indicator_of_notMem hx]
    rw [he, integral_indicator (localShell_measurable K v 0),
      localUnit_character_test_integral K χ v μ hμ s]
    simp [heckeEulerFactor, hχ]

#check finiteLocalTest_integral_eq_euler
#print axioms finiteLocalTest_integral_eq_euler

/-- Absolute integrability of the genuine unramified local Mellin integral. -/
theorem unramified_localIntegral_integrable (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (localMellinIntegrand K χ v s)
      {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1} μ := by
  have hm := localShell_measurable K v
  have hi : ∀ n : ℕ, IntegrableOn (localMellinIntegrand K χ v s)
      (localShell K v n) μ := by
    intro n
    have hc : IntegrableOn (fun _x : (LocalField K v)ˣ => localZetaRatio K χ v s ^ n)
        (localShell K v n) μ := integrableOn_const (by
      rw [localShell_measure K v μ n, hμ]
      exact ENNReal.one_ne_top)
    exact hc.congr_fun (fun x hx =>
      (localMellinIntegrand_on_shell K χ v hχ s n x hx).symm) (hm n)
  have hn : ∀ n : ℕ,
      (∫ x in localShell K v n, ‖localMellinIntegrand K χ v s x‖ ∂μ) =
        ‖localZetaRatio K χ v s ^ n‖ := by
    intro n
    calc
      _ = ∫ _x in localShell K v n, ‖localZetaRatio K χ v s ^ n‖ ∂μ := by
        apply setIntegral_congr_fun (hm n)
        intro x hx
        exact congrArg norm (localMellinIntegrand_on_shell K χ v hχ s n x hx)
      _ = _ := by
        rw [setIntegral_const, Measure.real, localShell_measure K v μ n, hμ]
        simp
  have hfi : IntegrableOn (localMellinIntegrand K χ v s)
      (⋃ n : ℕ, localShell K v n) μ := by
    apply integrableOn_iUnion_of_summable_integral_norm hi
    simp_rw [hn]
    exact summable_norm_iff.mpr (unramified_localZeta_hasSum K χ v hχ s hs).summable
  rw [integral_localUnits_eq_iUnion]
  exact hfi

/-- Integrability of the explicit Euler-factor test for every finite-place character. -/
theorem finiteLocalTest_integrable (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) μ := by
  classical
  by_cases hχ : IsUnramified K χ v
  · have hm : MeasurableSet {x : (LocalField K v)ˣ |
        Valued.v (x : LocalField K v) ≤ 1} := by
      rw [integral_localUnits_eq_iUnion]
      exact MeasurableSet.iUnion (localShell_measurable K v)
    have he : (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) =
        {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1}.indicator
          (localMellinIntegrand K χ v s) := by
      funext x
      by_cases hx : x ∈ {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1}
      · simp [finiteLocalTest, hχ, Set.indicator_of_mem hx]
      · simp [finiteLocalTest, hχ, Set.indicator_of_notMem hx]
    rw [he]
    exact (integrable_indicator_iff hm).mpr
      (unramified_localIntegral_integrable K χ v hχ μ hμ s hs)
  · have he : (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) =
        (localShell K v 0).indicator (fun x =>
          (localCharacter K χ v x : ℂ)⁻¹ * localMellinIntegrand K χ v s x) := by
      funext x
      by_cases hx : x ∈ localShell K v 0
      · simp [finiteLocalTest, hχ, Set.indicator_of_mem hx]
      · simp [finiteLocalTest, hχ, Set.indicator_of_notMem hx]
    rw [he]
    apply (integrable_indicator_iff (localShell_measurable K v 0)).mpr
    have hc : IntegrableOn (fun _x : (LocalField K v)ˣ => (1 : ℂ))
        (localShell K v 0) μ := integrableOn_const (by rw [hμ]; exact ENNReal.one_ne_top)
    apply hc.congr_fun ?_ (localShell_measurable K v 0)
    intro x hx
    have hv : Valued.v (x : LocalField K v) = 1 := by
      simpa [localShell] using hx
    have hn : (localCharacter K χ v x : ℂ) ≠ 0 :=
      norm_pos_iff.mp (by rw [Circle.norm_coe]; norm_num)
    simp [localMellinIntegrand, hv, hn]

/-- Full finite-local calculation, including the absolute integrability needed
for a subsequent global tensor-product integral. Haar existence and Schwartz
admissibility are not asserted by this theorem. -/
theorem finiteLocalTest_integrable_and_integral (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) μ ∧
      (∫ x, finiteLocalTest K χ v x * localMellinIntegrand K χ v s x ∂μ) =
        heckeEulerFactor K χ v s :=
  ⟨finiteLocalTest_integrable K χ v μ hμ s hs,
   finiteLocalTest_integral_eq_euler K χ v μ hμ s hs⟩

#check unramified_localIntegral_integrable
#print axioms unramified_localIntegral_integrable
#check finiteLocalTest_integrable
#print axioms finiteLocalTest_integrable
#check finiteLocalTest_integrable_and_integral
#print axioms finiteLocalTest_integrable_and_integral
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The constructed additive test restricts exactly to C's genuine multiplicative test. -/
theorem finiteAdditiveTest_eq_finiteLocalTest (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    finiteAdditiveTest K χ v (x : LocalField K v) = finiteLocalTest K χ v x := by
  classical
  rw [finiteAdditiveTest_restrict]
  by_cases hχ : IsUnramified K χ v
  · simp only [finiteLocalTest, if_pos hχ]
    by_cases hx : Valued.v (x : LocalField K v) ≤ 1
    · rw [if_pos hx, Set.indicator_of_mem
        (show x ∈ {y : (LocalField K v)ˣ | Valued.v (y : LocalField K v) ≤ 1} from hx)]
    · rw [if_neg hx, Set.indicator_of_notMem
        (show x ∉ {y : (LocalField K v)ˣ | Valued.v (y : LocalField K v) ≤ 1} from hx)]
  · simp only [finiteLocalTest, if_neg hχ]
    have hs : localShell K v 0 = {y : (LocalField K v)ˣ | Valued.v (y : LocalField K v) = 1} := by
      simp [localShell]
    rw [hs]
    by_cases hx : Valued.v (x : LocalField K v) = 1
    · rw [if_pos hx, Set.indicator_of_mem
        (show x ∈ {y : (LocalField K v)ˣ | Valued.v (y : LocalField K v) = 1} from hx)]
    · rw [if_neg hx, Set.indicator_of_notMem
        (show x ∉ {y : (LocalField K v)ˣ | Valued.v (y : LocalField K v) = 1} from hx)]

/-- Absolute local Mellin identification for the actual additive-field test. -/
theorem finiteAdditiveTest_integrable_and_integral (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun x : (LocalField K v)ˣ =>
      finiteAdditiveTest K χ v (x : LocalField K v) * localMellinIntegrand K χ v s x) μ ∧
      (∫ x : (LocalField K v)ˣ,
        finiteAdditiveTest K χ v (x : LocalField K v) * localMellinIntegrand K χ v s x ∂μ) =
        heckeEulerFactor K χ v s := by
  simp_rw [finiteAdditiveTest_eq_finiteLocalTest]
  exact finiteLocalTest_integrable_and_integral K χ v μ hμ s hs

/-- A locally constant compactly supported additive test realizes every finite Hecke
Euler factor. The arithmetic finite-residue and normalized-measure premises are explicit. -/
theorem exists_compact_additiveTest_eulerFactor (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hfin : Finite (Valued.ResidueField (LocalField K v)))
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [μ.IsMulLeftInvariant]
    (hμ : μ (localShell K v 0) = 1) :
    ∃ Φ : LocallyConstant (LocalField K v) ℂ,
      HasCompactSupport (Φ : LocalField K v → ℂ) ∧
      ∀ s : ℂ, 0 < s.re →
        Integrable (fun x : (LocalField K v)ˣ =>
          Φ (x : LocalField K v) * localMellinIntegrand K χ v s x) μ ∧
        (∫ x : (LocalField K v)ˣ,
          Φ (x : LocalField K v) * localMellinIntegrand K χ v s x ∂μ) =
          heckeEulerFactor K χ v s := by
  exact ⟨finiteAdditiveTest K χ v,
    finiteAdditiveTest_hasCompactSupport_of_finite_residue K χ v hfin,
    fun s hs => finiteAdditiveTest_integrable_and_integral K χ v μ hμ s hs⟩

#check finiteAdditiveTest_eq_finiteLocalTest
#print axioms finiteAdditiveTest_eq_finiteLocalTest
#check finiteAdditiveTest_integrable_and_integral
#print axioms finiteAdditiveTest_integrable_and_integral
#check exists_compact_additiveTest_eulerFactor
#print axioms exists_compact_additiveTest_eulerFactor
end MasulloGRH

/- E round 33: normalized Haar construction, continuing E round 32. -/
open scoped NumberField
open MeasureTheory
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem localIntegers_complete (v : FinitePlace K) :
    CompleteSpace (v.adicCompletionIntegers K) := by
  exact (Valued.isClosed_valuationSubring (LocalField K v)).completeSpace_coe

theorem localIntegers_compact_of_finite_residue (v : FinitePlace K)
    [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] :
    CompactSpace (v.adicCompletionIntegers K) := by
  apply Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mpr
  exact ⟨localIntegers_complete K v,
    (show IsDiscreteValuationRing (v.adicCompletionIntegers K) from inferInstance),
    (show Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) from inferInstance)⟩

theorem localUnitSet_compact_of_finite_residue (v : FinitePlace K)
    [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] :
    IsCompact {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = 1} := by
  have hc : IsCompact (v.adicCompletionIntegers K : Set (LocalField K v)) :=
    isCompact_iff_compactSpace.mpr (localIntegers_compact_of_finite_residue K v)
  have hu := Submonoid.units_isCompact (S := (v.adicCompletionIntegers K).toSubring.toSubmonoid) hc
  convert hu using 1
  ext x
  change Valued.v (x : LocalField K v) = 1 ↔
    (Valued.v (x : LocalField K v) ≤ 1 ∧ Valued.v ((x⁻¹ : (LocalField K v)ˣ) : LocalField K v) ≤ 1)
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h; simp [h]
  · intro h
    apply le_antisymm h.1
    have hv0 : Valued.v (x : LocalField K v) ≠ 0 := by
      simpa only [ne_eq, map_eq_zero] using (Units.ne_zero x)
    have hm := mul_le_mul_right h.2 (Valued.v (x : LocalField K v))
    simpa [hv0] using hm

#check localIntegers_complete
#print axioms localIntegers_complete
#check localIntegers_compact_of_finite_residue
#print axioms localIntegers_compact_of_finite_residue
#check localUnitSet_compact_of_finite_residue
#print axioms localUnitSet_compact_of_finite_residue

noncomputable def localUnitPositiveCompact (v : FinitePlace K)
    [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))] :
    TopologicalSpace.PositiveCompacts (LocalField K v)ˣ := by
  refine ⟨⟨{x | Valued.v (x : LocalField K v) = 1},
    localUnitSet_compact_of_finite_residue K v⟩, ?_⟩
  have ho : IsOpen {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = 1} :=
    (Valued.isClopen_sphere (LocalField K v) one_ne_zero).isOpen.preimage Units.continuous_val
  rw [ho.interior_eq]
  exact ⟨1, by simp⟩

theorem exists_normalizedLocalHaar_of_finite_residue (v : FinitePlace K)
    [Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K))]
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ] :
    ∃ μ : Measure (LocalField K v)ˣ, μ.IsHaarMeasure ∧
      μ {x | Valued.v (x : LocalField K v) = 1} = 1 := by
  refine ⟨Measure.haarMeasure (localUnitPositiveCompact K v), inferInstance, ?_⟩
  exact Measure.haarMeasure_self

#check exists_normalizedLocalHaar_of_finite_residue
#print axioms exists_normalizedLocalHaar_of_finite_residue

/-- The arithmetic prime ideal is exactly the kernel of the completed residue map. -/
theorem localResidue_kernel (v : FinitePlace K) (a : 𝓞 K) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) a) = 0 ↔ a ∈ v.asIdeal := by
  rw [IsLocalRing.residue_eq_zero_iff]
  have hm := Valuation.mem_maximalIdeal_iff (LocalField K v)
    (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))
    (a := algebraMap (𝓞 K) (v.adicCompletionIntegers K) a)
  refine hm.trans ?_
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_lt_one_iff_mem a

#check localResidue_kernel
#print axioms localResidue_kernel

noncomputable def localResidueMap (v : FinitePlace K) :
    (𝓞 K ⧸ v.asIdeal) →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  Ideal.Quotient.lift v.asIdeal
    ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K)))
    (fun a ha => (localResidue_kernel K v a).2 ha)

theorem localResidueMap_injective (v : FinitePlace K) :
    Function.Injective (localResidueMap K v) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  exact (localResidueMap K v).injective

#check localResidueMap_injective
#print axioms localResidueMap_injective

/-- The dense number field supplies an integral representative modulo the local maximal ideal. -/
theorem localIntegers_approx_field (v : FinitePlace K) (y : v.adicCompletionIntegers K) :
    ∃ x : K, v.valuation K x ≤ 1 ∧
      Valued.v (algebraMap K (LocalField K v) x - y) < 1 := by
  have ho : IsOpen {z : LocalField K v | Valued.v (z - y) < 1} :=
    (Valued.isOpen_ball (LocalField K v) 1).preimage (continuous_id.sub continuous_const)
  have hd : DenseRange (fun x : WithVal (v.valuation K) =>
      (x : LocalField K v)) := UniformSpace.Completion.denseRange_coe
  obtain ⟨x, hx⟩ := hd.exists_mem_open ho ⟨y, by simp⟩
  have hx' : Valued.v (algebraMap K (LocalField K v) (WithVal.equiv _ x) - y) < 1 := hx
  refine ⟨WithVal.equiv _ x, ?_, hx'⟩
  have hxy : Valued.v (algebraMap K (LocalField K v) (WithVal.equiv _ x)) ≤ 1 := by
    calc
      _ = Valued.v ((algebraMap K (LocalField K v) (WithVal.equiv _ x) - y) + y) := by congr 1; ring
      _ ≤ max (Valued.v (algebraMap K (LocalField K v) (WithVal.equiv _ x) - y)) (Valued.v (y : LocalField K v)) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hx'.le y.property
  simpa only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, RingHom.id_apply,
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hxy

#check localIntegers_approx_field
#print axioms localIntegers_approx_field

theorem localResidue_eq_iff (v : FinitePlace K) (a b : v.adicCompletionIntegers K) :
    IsLocalRing.residue (v.adicCompletionIntegers K) a =
      IsLocalRing.residue (v.adicCompletionIntegers K) b ↔
      Valued.v ((a : LocalField K v) - b) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff (LocalField K v)
    (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))

theorem localVal_algebraMap (v : FinitePlace K) (x : K) :
    Valued.v (algebraMap K (LocalField K v) x) = v.valuation K x := by
  exact v.valuedAdicCompletion_eq_valuation' x

/-- Every completed residue class has a representative in the valued integer subring of K. -/
theorem localResidue_representative (v : FinitePlace K)
    (z : IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :
    ∃ (x : K) (h : Valued.v (algebraMap K (LocalField K v) x) ≤ 1),
      IsLocalRing.residue (v.adicCompletionIntegers K) ⟨algebraMap K (LocalField K v) x, h⟩ = z := by
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨x, hx, hxy⟩ := localIntegers_approx_field K v y
  have h : Valued.v (algebraMap K (LocalField K v) x) ≤ 1 := by
    rw [localVal_algebraMap]
    exact hx
  refine ⟨x, h, ?_⟩
  exact (localResidue_eq_iff K v _ y).2 hxy

#check localResidue_eq_iff
#print axioms localResidue_eq_iff
#check localVal_algebraMap
#print axioms localVal_algebraMap
#check localResidue_representative
#print axioms localResidue_representative


/-- The localization at the finite prime gives a denominator prime to that prime. -/
theorem localIntegral_denominator (v : FinitePlace K) (x : K)
    (hx : v.valuation K x ≤ 1) :
    ∃ (n : 𝓞 K) (d : v.asIdeal.primeCompl),
      x * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n := by
  by_cases hx0 : x = 0
  · subst x
    exact ⟨0, 1, by simp⟩
  let S := Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsDedekindDomain S := IsLocalization.AtPrime.isDedekindDomain (𝓞 K) v.asIdeal S
  letI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S v.asIdeal
  have hor : ∃ (n : 𝓞 K) (d : v.asIdeal.primeCompl),
      x * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K n ∨
      x * algebraMap (𝓞 K) K n = algebraMap (𝓞 K) K d := by
    obtain (⟨r, hr⟩ | ⟨r, hr⟩) := ValuationRing.isInteger_or_isInteger S x
    <;> obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj v.asIdeal.primeCompl r
    <;> use n, d
    <;> apply_fun algebraMap S K at hnd
    <;> simp only [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) S K] at hnd
    · exact Or.inl (by rwa [hr] at hnd)
    · right
      rw [hr] at hnd
      calc
        x * algebraMap (𝓞 K) K n = x * (x⁻¹ * algebraMap (𝓞 K) K d) := by rw [hnd]
        _ = algebraMap (𝓞 K) K d := by field_simp
  obtain ⟨n, d, h | h⟩ := hor
  · exact ⟨n, d, h⟩
  · refine ⟨d, ⟨n, ?_⟩, h⟩
    intro hn
    have hnv : v.valuation K (algebraMap (𝓞 K) K n) < 1 :=
      (v.valuation_lt_one_iff_mem n).2 hn
    have hdv : v.valuation K (algebraMap (𝓞 K) K d) < 1 := by
      rw [← h, map_mul]
      have hm := mul_le_mul_right hx (v.valuation K (algebraMap (𝓞 K) K n))
      rw [mul_one] at hm
      exact lt_of_le_of_lt (by simpa only [mul_comm] using hm) hnv
    exact d.prop ((v.valuation_lt_one_iff_mem d).1 hdv)

#check localIntegral_denominator
#print axioms localIntegral_denominator


theorem localResidueMap_surjective (v : FinitePlace K) :
    Function.Surjective (localResidueMap K v) := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  intro z
  obtain ⟨x, hx, hz⟩ := localResidue_representative K v z
  have hv : v.valuation K x ≤ 1 := by rwa [localVal_algebraMap] at hx
  obtain ⟨n, d, hnd⟩ := localIntegral_denominator K v x hv
  have hd : localResidueMap K v (Ideal.Quotient.mk v.asIdeal d) ≠ 0 := by
    change IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (d : 𝓞 K)) ≠ 0
    intro h
    exact d.prop ((localResidue_kernel K v d).1 h)
  refine ⟨Ideal.Quotient.mk v.asIdeal n / Ideal.Quotient.mk v.asIdeal d, ?_⟩
  rw [map_div₀]
  apply (div_eq_iff hd).2
  rw [← hz]
  change IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) n) =
    IsLocalRing.residue (v.adicCompletionIntegers K) ⟨algebraMap K (LocalField K v) x, hx⟩ *
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) d)
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) n : v.adicCompletionIntegers K) : LocalField K v) =
    algebraMap K (LocalField K v) x *
      ((algebraMap (𝓞 K) (v.adicCompletionIntegers K) d : v.adicCompletionIntegers K) : LocalField K v)
  simpa only [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    map_mul] using (congrArg (algebraMap K (LocalField K v)) hnd).symm

theorem localResidue_finite (v : FinitePlace K) :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  letI : NeZero v.asIdeal := ⟨v.ne_bot⟩
  letI : Finite (𝓞 K ⧸ v.asIdeal) := inferInstance
  exact Finite.of_surjective (localResidueMap K v) (localResidueMap_surjective K v)

theorem exists_normalizedLocalHaar (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ] :
    ∃ μ : Measure (LocalField K v)ˣ, μ.IsHaarMeasure ∧
      μ {x | Valued.v (x : LocalField K v) = 1} = 1 := by
  letI := localResidue_finite K v
  exact exists_normalizedLocalHaar_of_finite_residue K v

#check localResidueMap_surjective
#print axioms localResidueMap_surjective
#check localResidue_finite
#print axioms localResidue_finite
#check exists_normalizedLocalHaar
#print axioms exists_normalizedLocalHaar


/-- Actual normalized Haar measure simultaneously realizes every finite local Euler factor. -/
theorem exists_finiteLocalEulerIntegral (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ] :
    ∃ μ : Measure (LocalField K v)ˣ, μ.IsHaarMeasure ∧
      μ {x | Valued.v (x : LocalField K v) = 1} = 1 ∧
      ∀ (χ : UnitaryHeckeCharacter K) (s : ℂ), 0 < s.re →
        Integrable (fun x => finiteLocalTest K χ v x * localMellinIntegrand K χ v s x) μ ∧
        (∫ x, finiteLocalTest K χ v x * localMellinIntegrand K χ v s x ∂μ) =
          heckeEulerFactor K χ v s := by
  obtain ⟨μ, hμ, hu⟩ := exists_normalizedLocalHaar K v
  refine ⟨μ, hμ, hu, ?_⟩
  letI : μ.IsHaarMeasure := hμ
  intro χ s hs
  apply finiteLocalTest_integrable_and_integral K χ v μ ?_ s hs
  simpa [localShell] using hu

#check exists_finiteLocalEulerIntegral
#print axioms exists_finiteLocalEulerIntegral

/-- The completed residue field has the arithmetic prime norm used in the Euler factor. -/
theorem localResidue_card_eq_absNorm (v : FinitePlace K) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  have h := Nat.card_congr (Equiv.ofBijective (localResidueMap K v)
    ⟨localResidueMap_injective K v, localResidueMap_surjective K v⟩)
  exact h.symm

#check localResidue_card_eq_absNorm
#print axioms localResidue_card_eq_absNorm
end MasulloGRH


/- E round 35 constructive review: compose B's additive tests and C's Mellin
calculation with E's checked arithmetic Haar construction. Structural Borel
and measurable-multiplication assumptions remain explicit. -/
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

theorem exists_finiteLocalSchwartzEuler (v : FinitePlace K)
    [MeasurableSpace (LocalField K v)ˣ] [BorelSpace (LocalField K v)ˣ]
    [MeasurableMul (LocalField K v)ˣ] :
    ∃ μ : Measure (LocalField K v)ˣ, μ.IsHaarMeasure ∧
      μ (localShell K v 0) = 1 ∧
      ∀ χ : UnitaryHeckeCharacter K,
        ∃ Φ : LocallyConstant (LocalField K v) ℂ,
          HasCompactSupport (Φ : LocalField K v → ℂ) ∧
          (∀ x : (LocalField K v)ˣ, Φ (x : LocalField K v) = finiteLocalTest K χ v x) ∧
          ∀ s : ℂ, 0 < s.re →
            Integrable (fun x : (LocalField K v)ˣ =>
              Φ (x : LocalField K v) * localMellinIntegrand K χ v s x) μ ∧
            (∫ x : (LocalField K v)ˣ,
              Φ (x : LocalField K v) * localMellinIntegrand K χ v s x ∂μ) =
              heckeEulerFactor K χ v s := by
  obtain ⟨μ, hμ, hu⟩ := exists_normalizedLocalHaar K v
  letI : μ.IsHaarMeasure := hμ
  have hu' : μ (localShell K v 0) = 1 := by simpa [localShell] using hu
  refine ⟨μ, hμ, hu', ?_⟩
  intro χ
  refine ⟨finiteAdditiveTest K χ v, ?_, ?_, ?_⟩
  · exact finiteAdditiveTest_hasCompactSupport_of_finite_residue K χ v (localResidue_finite K v)
  · exact finiteAdditiveTest_eq_finiteLocalTest K χ v
  · intro s hs
    exact finiteAdditiveTest_integrable_and_integral K χ v μ hu' s hs

#check exists_finiteLocalSchwartzEuler
#print axioms exists_finiteLocalSchwartzEuler
end MasulloGRH
