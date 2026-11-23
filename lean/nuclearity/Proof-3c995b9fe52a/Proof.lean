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



end MasulloGRH

/- H round 36. Actual compact-open support for the finite-adelic Hecke test.
The local arithmetic proof above is E's construction, checked by H in round 35. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev FiniteHeckeAdeles := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

def integralFiniteAdeles : Set (FiniteHeckeAdeles K) :=
  {a | ∀ v : FinitePlace K, a v ∈ v.adicCompletionIntegers K}

theorem integralFiniteAdeles_eq_range :
    integralFiniteAdeles K = Set.range (integralFiniteAdele K) := by
  ext a
  constructor
  · intro ha
    refine ⟨fun v => ⟨a v, ha v⟩, ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl
  · rintro ⟨x, rfl⟩
    intro v
    exact (x v).property

/-- Compactness for every actual number field, with no finite-residue premise. -/
theorem integralFiniteAdeles_isCompact : IsCompact (integralFiniteAdeles K) := by
  letI : ∀ v : FinitePlace K, CompactSpace (v.adicCompletionIntegers K) :=
    fun v => by
      letI := localResidue_finite K v
      exact localIntegers_compact_of_finite_residue K v
  rw [integralFiniteAdeles_eq_range]
  exact isCompact_range (integralFiniteAdele_continuous K)

theorem integralFiniteAdeles_isOpen : IsOpen (integralFiniteAdeles K) := by
  exact RestrictedProduct.isOpen_forall_mem (fun v =>
    (Valued.isClopen_closedBall (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen)

theorem integralFiniteAdeles_isClopen : IsClopen (integralFiniteAdeles K) := by
  refine ⟨?_, integralFiniteAdeles_isOpen K⟩
  have he : integralFiniteAdeles K = ⋂ v : FinitePlace K,
      {a : FiniteHeckeAdeles K | a v ∈ v.adicCompletionIntegers K} := by
    ext a
    simp only [integralFiniteAdeles, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter fun v =>
    (Valued.isClosed_closedBall (LocalField K v) 1).preimage
      (RestrictedProduct.continuous_eval v)

#check integralFiniteAdeles_eq_range
#print axioms integralFiniteAdeles_eq_range
#check integralFiniteAdeles_isCompact
#print axioms integralFiniteAdeles_isCompact
#check integralFiniteAdeles_isOpen
#print axioms integralFiniteAdeles_isOpen
#check integralFiniteAdeles_isClopen
#print axioms integralFiniteAdeles_isClopen
end MasulloGRH

/- UNVERIFIED round-36 continuation candidate. The dependencies up to the
local package have successful receipts, but this assembled target has not
been submitted. The compact-open support block has its own check. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def finiteRamifiedPlaces (χ : UnitaryHeckeCharacter K) :
    Finset (FinitePlace K) := (finite_ramification K χ).toFinset

noncomputable def finiteAdelicTest (χ : UnitaryHeckeCharacter K) :
    LocallyConstant (FiniteHeckeAdeles K) ℂ := by
  classical
  let f : LocallyConstant (FiniteHeckeAdeles K) ℂ :=
    ∏ v ∈ finiteRamifiedPlaces K χ,
      (finiteAdditiveTest K χ v).comap
        ⟨fun a => a v, RestrictedProduct.continuous_eval v⟩
  exact f.indicator (integralFiniteAdeles_isClopen K)

theorem finiteAdelicTest_hasCompactSupport (χ : UnitaryHeckeCharacter K) :
    HasCompactSupport (finiteAdelicTest K χ : FiniteHeckeAdeles K → ℂ) := by
  have hs : Function.support (finiteAdelicTest K χ : FiniteHeckeAdeles K → ℂ) ⊆
      integralFiniteAdeles K := by
    intro a ha
    by_contra h
    apply ha
    classical
    change (integralFiniteAdeles K).indicator _ a = 0
    exact Set.indicator_of_notMem h _
  change IsCompact (closure (Function.support
    (finiteAdelicTest K χ : FiniteHeckeAdeles K → ℂ)))
  exact (integralFiniteAdeles_isCompact K).of_isClosed_subset isClosed_closure
    (closure_minimal hs (integralFiniteAdeles_isClopen K).isClosed)

#check finiteAdelicTest
#print axioms finiteAdelicTest
#check finiteAdelicTest_hasCompactSupport
#print axioms finiteAdelicTest_hasCompactSupport
end MasulloGRH
