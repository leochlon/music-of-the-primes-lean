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

end MasulloGRH


namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

attribute [local instance] Classical.propDecidable

/-- Multiplication of actual integral ideles is coordinatewise. -/
theorem integralIdele_mul (x y : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    integralIdele K (x * y) = integralIdele K x * integralIdele K y := by
  apply Units.ext
  apply Prod.ext
  · change (1 : NumberField.InfiniteAdeleRing K) = 1 * 1
    simp
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl

noncomputable def integralIdeleHom :
    (∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) →* HeckeIdeles K where
  toFun := integralIdele K
  map_one' := integralIdele_one K
  map_mul' := integralIdele_mul K

/-- The genuine global character is trivial on all integral-unit tails outside
one finite coordinate set. This follows from continuity and the no-small-subgroup
property of Circle; no infinite product identity is assumed. -/
theorem integralCharacter_finite_support (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K),
      ∀ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        (∀ v ∈ S, x v = 1) → χ.character (integralIdele K x) = 1 := by
  classical
  let f := fun x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ =>
    (χ.character (integralIdele K x) : ℂ).re
  have hf : Continuous f := Complex.continuous_re.comp
    (continuous_subtype_val.comp (χ.character.continuous.comp (integralIdele_continuous K)))
  have ho : IsOpen {x | 0 < f x} := isOpen_lt continuous_const hf
  have hone : (fun v : FinitePlace K => (1 : (v.adicCompletionIntegers K)ˣ)) ∈ {x | 0 < f x} := by
    simp [f, integralIdele_one, map_one]
  obtain ⟨S, U, hU, hsub⟩ := isOpen_pi_iff.mp ho (fun v => 1) hone
  refine ⟨S, fun x hx => ?_⟩
  apply circle_eq_one_of_powers_re_nonneg
  intro n
  have hmem : x ^ n ∈ (S : Set (FinitePlace K)).pi U := by
    intro v hv
    simpa only [Pi.pow_apply, hx v hv, one_pow] using (hU v hv).2
  have hp : 0 ≤ f (x ^ n) := (show 0 < f (x ^ n) from hsub hmem).le
  change 0 ≤ (χ.character (integralIdele K (x ^ n)) : ℂ).re at hp
  have hi : integralIdele K (x ^ n) = integralIdele K x ^ n :=
    (integralIdeleHom K).map_pow x n
  simpa only [hi, map_pow] using hp


/-- Finite integral-unit tensors are products of the genuine single-place embeddings. -/
theorem integralIdele_truncation (S : Finset (FinitePlace K))
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    integralIdele K (fun v => if v ∈ S then x v else 1) =
      ∏ v ∈ S, localIdele K v (integralLocalUnit K v (x v)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using integralIdele_one K
  | @insert a S ha ih =>
    have he : (fun v => if v ∈ insert a S then x v else 1) =
        Function.update (fun v : FinitePlace K => (1 : (v.adicCompletionIntegers K)ˣ)) a (x a) *
          (fun v => if v ∈ S then x v else 1) := by
      funext v
      by_cases hv : v = a
      · subst v
        simp [ha]
      · simp [hv]
    rw [he, integralIdele_mul, integralIdele_update, ih, Finset.prod_insert ha]

/-- The compact-unit part of an actual Hecke character is an honest finite product
of its local components. This discharges the character factorization needed by the
restricted-tensor Tate integral, without postulating an infinite character product. -/
theorem integralCharacter_finite_factorization (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K),
      ∀ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        χ.character (integralIdele K x) =
          ∏ v ∈ S, localCharacter K χ v (integralLocalUnit K v (x v)) := by
  classical
  obtain ⟨S, hS⟩ := integralCharacter_finite_support K χ
  refine ⟨S, fun x => ?_⟩
  let y := fun v => if v ∈ S then x v else 1
  have ht := hS (x / y) (by intro v hv; simp [y, hv])
  have hd : integralIdele K (x / y) = integralIdele K x / integralIdele K y :=
    (integralIdeleHom K).map_div x y
  rw [hd, map_div] at ht
  have he : χ.character (integralIdele K x) = χ.character (integralIdele K y) :=
    div_eq_one.mp ht
  rw [he]
  change χ.character (integralIdele K (fun v => if v ∈ S then x v else 1)) = _
  rw [integralIdele_truncation, map_prod]
  rfl

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

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

/-- On local integral units the actual additive test is exactly the inverse character,
including the unramified case. -/
theorem finiteAdditiveTest_integralUnit (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (u : (v.adicCompletionIntegers K)ˣ) :
    finiteAdditiveTest K χ v (integralLocalUnit K v u : LocalField K v) =
      (localCharacter K χ v (integralLocalUnit K v u) : ℂ)⁻¹ := by
  classical
  have hv := integralLocalUnit_valuation K v u
  rw [finiteAdditiveTest_restrict]
  by_cases hχ : IsUnramified K χ v
  · simp [hχ, hv, hχ _ hv]
  · simp [hχ, hv]

/-- The genuine local additive tests cancel the genuine global character on the
integral-unit subgroup. All omitted places are unramified, so their standard tests
are one there. This is the unit-shell normalization for the global Tate tensor. -/
theorem exists_finiteTest_character_cancellation (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), (∀ v ∉ S, IsUnramified K χ v) ∧
      ∀ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        (∏ v ∈ S, finiteAdditiveTest K χ v
          (integralLocalUnit K v (x v) : LocalField K v)) *
          (χ.character (integralIdele K x) : ℂ) = 1 := by
  classical
  obtain ⟨S, hS⟩ := integralCharacter_finite_support K χ
  refine ⟨S, ?_, ?_⟩
  · intro v hv x hx
    let u := valuationUnitAsIntegral K v x hx
    have h := hS (Function.update (fun w : FinitePlace K =>
      (1 : (w.adicCompletionIntegers K)ˣ)) v u) (by
        intro w hw
        have hwv : w ≠ v := by intro he; subst w; exact hv hw
        simp [Function.update_of_ne hwv])
    rw [integralIdele_update] at h
    change localCharacter K χ v (integralLocalUnit K v u) = 1 at h
    simpa only [u, integralLocalUnit_valuationUnitAsIntegral] using h
  · intro x
    let y := fun v => if v ∈ S then x v else 1
    have ht := hS (x / y) (by intro v hv; simp [y, hv])
    have hd : integralIdele K (x / y) = integralIdele K x / integralIdele K y :=
      (integralIdeleHom K).map_div x y
    rw [hd, map_div] at ht
    have he : χ.character (integralIdele K x) = χ.character (integralIdele K y) :=
      div_eq_one.mp ht
    have hf : χ.character (integralIdele K x) =
        ∏ v ∈ S, localCharacter K χ v (integralLocalUnit K v (x v)) := by
      rw [he]
      change χ.character (integralIdele K (fun v => if v ∈ S then x v else 1)) = _
      rw [integralIdele_truncation, map_prod]
      rfl
    simp_rw [finiteAdditiveTest_integralUnit]
    rw [Finset.prod_inv_distrib]
    have hc : (χ.character (integralIdele K x) : ℂ) =
        ∏ v ∈ S, (localCharacter K χ v (integralLocalUnit K v (x v)) : ℂ) := by
      rw [hf]
      clear hS ht hd he hf y
      induction S using Finset.induction_on with
      | empty => simp
      | @insert v T hv ih => simp only [Finset.prod_insert hv, Circle.coe_mul, ih]
    rw [← hc]
    apply inv_mul_cancel₀
    intro hz
    have hn := Circle.norm_coe (χ.character (integralIdele K x))
    rw [hz, norm_zero] at hn
    norm_num at hn

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Almost all local Tate tests equal one on each genuine finite adele. -/
theorem finiteAdelicTest_mulSupport_finite (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :
    (Function.mulSupport (fun v : FinitePlace K => finiteAdditiveTest K χ v (a v))).Finite := by
  classical
  have ha : {v : FinitePlace K | a v ∉
      (v.adicCompletionIntegers K : Set (LocalField K v))}.Finite :=
    Filter.eventually_cofinite.mp a.property
  apply Set.Finite.subset ((finite_ramification K χ).union ha)
  intro v hv
  by_contra hn
  have hg : IsUnramified K χ v ∧
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v)) := by
    simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using hn
  have hi : Valued.v (a v) ≤ 1 := hg.2
  exact hv (by simp [finiteAdditiveTest, hg.1, unramifiedAdditiveTest_apply, hi])

/-- The actual finite-adelic restricted tensor of the explicit local Tate tests.
Its product has finite multiplicative support at every finite adele. -/
noncomputable def finiteAdelicTest (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏ᶠ v : FinitePlace K, finiteAdditiveTest K χ v (a v)

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The constructed global finite tensor cancels the genuine Hecke character
on every integral-unit idele. No global integral factorization is assumed. -/
theorem finiteAdelicTest_integralUnit_character (χ : UnitaryHeckeCharacter K)
    (x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteAdelicTest K χ (integralFiniteAdele K (fun v => (x v).val)) *
      (χ.character (integralIdele K x) : ℂ) = 1 := by
  classical
  obtain ⟨S, hun, hcan⟩ := exists_finiteTest_character_cancellation K χ
  have hs : Function.mulSupport (fun v : FinitePlace K =>
      finiteAdditiveTest K χ v ((integralFiniteAdele K (fun v => (x v).val)) v)) ⊆
      (S : Set (FinitePlace K)) := by
    intro v hv
    by_contra hvs
    change finiteAdditiveTest K χ v (integralLocalUnit K v (x v) : LocalField K v) ≠ 1 at hv
    apply hv
    rw [finiteAdditiveTest_integralUnit,
      hun v hvs _ (integralLocalUnit_valuation K v (x v))]
    simp
  unfold finiteAdelicTest
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  exact hcan x

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The global finite tensor vanishes whenever one coordinate is outside its
local integer ball. This is the additive support bound needed for a Tate test. -/
theorem finiteAdelicTest_zero_of_not_integral (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (v : FinitePlace K)
    (hv : ¬ Valued.v (a v) ≤ 1) : finiteAdelicTest K χ a = 0 := by
  classical
  have hz : finiteAdditiveTest K χ v (a v) = 0 := by
    by_cases hu : IsUnramified K χ v
    · simp [finiteAdditiveTest, hu, unramifiedAdditiveTest_apply, hv]
    · simp only [finiteAdditiveTest, if_neg hu]
      exact ramifiedAdditiveTest_zero_off_shell K χ v (a v)
        (by intro h; exact hv (le_of_eq h))
  unfold finiteAdelicTest
  let hf := finiteAdelicTest_mulSupport_finite K χ a
  rw [finprod_eq_prod _ hf, Finset.prod_eq_zero_iff]
  refine ⟨v, ?_, hz⟩
  apply hf.mem_toFinset.mpr
  change finiteAdditiveTest K χ v (a v) ≠ 1
  rw [hz]
  norm_num

/-- Every point in the support of the finite Tate tensor is integral at every
finite place, with no arbitrary cutoff or prescribed finite set of places. -/
theorem finiteAdelicTest_support_integral (χ : UnitaryHeckeCharacter K) :
    Function.support (finiteAdelicTest K χ) ⊆
      {a | ∀ v : FinitePlace K, a v ∈
        (v.adicCompletionIntegers K : Set (LocalField K v))} := by
  intro a ha v
  by_contra hv
  exact ha (finiteAdelicTest_zero_of_not_integral K χ a v hv)

#check finiteAdelicTest_zero_of_not_integral
#print axioms finiteAdelicTest_zero_of_not_integral
#check finiteAdelicTest_support_integral
#print axioms finiteAdelicTest_support_integral
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The integral finite adeles form a clopen set in the genuine restricted product. -/
theorem integralFiniteAdeles_isClopen : IsClopen
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePlace K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} := by
  have hb (v : FinitePlace K) : IsClopen
      (v.adicCompletionIntegers K : Set (LocalField K v)) :=
    Valued.isClopen_closedBall (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)
  have hr : {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePlace K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} =
      Set.range (integralFiniteAdele K) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact fun v => (x v).property
  constructor
  · have he : {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePlace K,
        a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} =
        ⋂ v : FinitePlace K,
          (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => a v) ⁻¹'
            (v.adicCompletionIntegers K : Set (LocalField K v)) := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [he]
    exact isClosed_iInter fun v => (hb v).isClosed.preimage (RestrictedProduct.continuous_eval v)
  · rw [hr]
    exact (RestrictedProduct.isOpenEmbedding_structureMap (fun v => (hb v).isOpen)).isOpen_range

/-- On the integral adeles the infinite tensor is the finite ramified product. -/
theorem finiteAdelicTest_eq_prod_of_integral (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
    (ha : ∀ v : FinitePlace K, a v ∈
      (v.adicCompletionIntegers K : Set (LocalField K v))) :
    finiteAdelicTest K χ a = ∏ v ∈ (finite_ramification K χ).toFinset,
      finiteAdditiveTest K χ v (a v) := by
  classical
  unfold finiteAdelicTest
  apply finprod_eq_prod_of_mulSupport_subset
  intro v hv
  by_contra hn
  have hu : IsUnramified K χ v := by
    by_contra h
    exact hn ((finite_ramification K χ).mem_toFinset.mpr h)
  have hi : Valued.v (a v) ≤ 1 := ha v
  exact hv (by simp [finiteAdditiveTest, hu, unramifiedAdditiveTest_apply, hi])

/-- The genuine restricted tensor is locally constant on the finite adele ring. -/
theorem finiteAdelicTest_isLocallyConstant (χ : UnitaryHeckeCharacter K) :
    IsLocallyConstant (finiteAdelicTest K χ) := by
  classical
  have hp (S : Finset (FinitePlace K)) : IsLocallyConstant
      (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K =>
        ∏ v ∈ S, finiteAdditiveTest K χ v (a v)) := by
    induction S using Finset.induction_on with
    | empty => simpa using (LocallyConstant.const (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) (1 : ℂ)).isLocallyConstant
    | @insert v S hv ih =>
      simp only [Finset.prod_insert hv]
      exact ((finiteAdditiveTest K χ v).isLocallyConstant.comp_continuous
        (RestrictedProduct.continuous_eval v)).mul ih
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  by_cases ha : ∀ v : FinitePlace K, a v ∈
      (v.adicCompletionIntegers K : Set (LocalField K v))
  · have he := (IsLocallyConstant.iff_eventually_eq _).mp
      (hp (finite_ramification K χ).toFinset) a
    filter_upwards [(integralFiniteAdeles_isClopen K).isOpen.mem_nhds ha, he] with b hb heq
    simpa only [finiteAdelicTest_eq_prod_of_integral K χ a ha,
      finiteAdelicTest_eq_prod_of_integral K χ b hb] using heq
  · have hz : finiteAdelicTest K χ a = 0 := by
      by_contra hn
      exact ha (finiteAdelicTest_support_integral K χ hn)
    filter_upwards [(integralFiniteAdeles_isClopen K).isClosed.isOpen_compl.mem_nhds ha] with b hb
    have hbz : finiteAdelicTest K χ b = 0 := by
      by_contra hn
      exact hb (finiteAdelicTest_support_integral K χ hn)
    simp [hz, hbz]

#check integralFiniteAdeles_isClopen
#print axioms integralFiniteAdeles_isClopen
#check finiteAdelicTest_eq_prod_of_integral
#print axioms finiteAdelicTest_eq_prod_of_integral
#check finiteAdelicTest_isLocallyConstant
#print axioms finiteAdelicTest_isLocallyConstant
end MasulloGRH

/-! Arithmetic compactness reused from E through A round 36, receipt 4da12294720c405da529943a22222d5a. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Unit covariance of the actual local Tate test, including at zero. -/
theorem finiteAdditiveTest_mul_integralUnit (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (x : LocalField K v)
    (u : (v.adicCompletionIntegers K)ˣ) :
    finiteAdditiveTest K χ v (x * (integralLocalUnit K v u : LocalField K v)) =
      finiteAdditiveTest K χ v x *
        (localCharacter K χ v (integralLocalUnit K v u) : ℂ)⁻¹ := by
  classical
  have hu := integralLocalUnit_valuation K v u
  have hv : Valued.v (x * (integralLocalUnit K v u : LocalField K v)) =
      Valued.v x := by rw [map_mul, hu, mul_one]
  by_cases hχ : IsUnramified K χ v
  · simp only [finiteAdditiveTest, if_pos hχ, unramifiedAdditiveTest_apply,
      hv, hχ _ hu, Circle.coe_one, inv_one, mul_one]
    split_ifs <;> rfl
  · simp only [finiteAdditiveTest, if_neg hχ]
    by_cases hx : Valued.v x = 1
    · have hx0 : x ≠ 0 := by
        intro he
        rw [he, map_zero] at hx
        exact zero_ne_one hx
      let y : (LocalField K v)ˣ := Units.mk0 x hx0
      have hxy : Valued.v ((y * integralLocalUnit K v u : (LocalField K v)ˣ) :
          LocalField K v) = 1 := by simpa only [Units.val_mul, Units.val_mk0] using hv.trans hx
      have he := ramifiedAdditiveTest_eq_inverse K χ v (y * integralLocalUnit K v u) hxy
      have hy := ramifiedAdditiveTest_eq_inverse K χ v y hx
      change ramifiedAdditiveTest K χ v x = _ at hy
      change ramifiedAdditiveTest K χ v (x * (integralLocalUnit K v u : LocalField K v)) = _ at he
      rw [he, hy, localCharacter_mul, Circle.coe_mul, mul_inv_rev]
      exact mul_comm _ _
    · rw [ramifiedAdditiveTest_zero_off_shell K χ v _ (by simpa only [hv] using hx),
        ramifiedAdditiveTest_zero_off_shell K χ v x hx, zero_mul]

#check finiteAdditiveTest_mul_integralUnit
#print axioms finiteAdditiveTest_mul_integralUnit
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Multiplication of the finite Tate tensor by an integral-unit argument. -/
theorem finiteAdelicTest_mul_integralUnit (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteAdelicTest K χ (a * integralFiniteAdele K (fun v => (u v).val)) =
      finiteAdelicTest K χ a *
        finiteAdelicTest K χ (integralFiniteAdele K (fun v => (u v).val)) := by
  have he (v : FinitePlace K) :
      finiteAdditiveTest K χ v ((a * integralFiniteAdele K (fun w => (u w).val)) v) =
        finiteAdditiveTest K χ v (a v) *
          finiteAdditiveTest K χ v ((integralFiniteAdele K (fun w => (u w).val)) v) := by
    change finiteAdditiveTest K χ v (a v * (integralLocalUnit K v (u v) : LocalField K v)) =
      finiteAdditiveTest K χ v (a v) *
        finiteAdditiveTest K χ v (integralLocalUnit K v (u v) : LocalField K v)
    rw [finiteAdditiveTest_mul_integralUnit, finiteAdditiveTest_integralUnit]
  unfold finiteAdelicTest
  simp_rw [he]
  exact finprod_mul_distrib (finiteAdelicTest_mulSupport_finite K χ a)
    (finiteAdelicTest_mulSupport_finite K χ (integralFiniteAdele K (fun v => (u v).val)))

/-- The finite Tate tensor transforms by the inverse genuine integral-unit character. -/
theorem finiteAdelicTest_integralUnit_covariance (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
    (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteAdelicTest K χ (a * integralFiniteAdele K (fun v => (u v).val)) *
      (χ.character (integralIdele K u) : ℂ) = finiteAdelicTest K χ a := by
  rw [finiteAdelicTest_mul_integralUnit, mul_assoc,
    finiteAdelicTest_integralUnit_character, mul_one]

/-- Unit-shell invariance of the character-weighted finite Tate test on actual ideles. -/
theorem finiteTateTest_integralUnit_invariant (χ : UnitaryHeckeCharacter K)
    (g : HeckeIdeles K) (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    finiteAdelicTest K χ ((g * integralIdele K u).val.2) *
      (χ.character (g * integralIdele K u) : ℂ) =
        finiteAdelicTest K χ g.val.2 * (χ.character g : ℂ) := by
  change finiteAdelicTest K χ (g.val.2 * integralFiniteAdele K (fun v => (u v).val)) *
    (χ.character (g * integralIdele K u) : ℂ) = _
  rw [map_mul, Circle.coe_mul]
  calc
    _ = (finiteAdelicTest K χ (g.val.2 * integralFiniteAdele K (fun v => (u v).val)) *
        (χ.character (integralIdele K u) : ℂ)) * (χ.character g : ℂ) := by ring
    _ = _ := by rw [finiteAdelicTest_integralUnit_covariance]

#check finiteAdelicTest_mul_integralUnit
#print axioms finiteAdelicTest_mul_integralUnit
#check finiteAdelicTest_integralUnit_covariance
#print axioms finiteAdelicTest_integralUnit_covariance
#check finiteTateTest_integralUnit_invariant
#print axioms finiteTateTest_integralUnit_invariant
end MasulloGRH

/- D/r41 classification and repaired uniformizer representative, rechecked here. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Every actual idele has only finitely many nonunit finite coordinates.
This is the finite-support input for its valuation-shell decomposition. -/
theorem genuineIdele_nonunit_finite (a : HeckeIdeles K) :
    {v : FinitePlace K | Valued.v (a.val.2 v) ≠ 1}.Finite := by
  apply Filter.eventually_cofinite.mp
  filter_upwards [a.val.2.property, a.inv.2.property] with v hv hi
  change Valued.v (a.val.2 v) ≤ 1 at hv
  change Valued.v (a.inv.2 v) ≤ 1 at hi
  have he : a.val.2 v * a.inv.2 v = 1 :=
    congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
  have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul, he, map_one]
  apply le_antisymm hv
  calc
    1 = Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) := hm.symm
    _ ≤ Valued.v (a.val.2 v) * 1 := by gcongr
    _ = _ := mul_one _

#check genuineIdele_nonunit_finite
#print axioms genuineIdele_nonunit_finite
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- Actual ideles with infinite component one and unit finite valuations are
exactly in the image of the full product of completed integer unit groups. -/
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

#check genuineIdele_integralUnit_representation
#print axioms genuineIdele_integralUnit_representation
end MasulloGRH

/- D round 40: the actual finite-idelic domain decomposition. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def truncateFiniteAdele (S : Finset (FinitePlace K))
    (x : ∀ v : FinitePlace K, LocalField K v) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K := by
  classical
  refine ⟨fun v => if v ∈ S then x v else 1, ?_⟩
  apply Filter.eventually_cofinite.mpr
  apply Set.Finite.subset S.finite_toSet
  intro v hv
  by_contra hn
  change v ∉ S at hn
  apply hv
  change (if v ∈ S then x v else 1) ∈ v.adicCompletionIntegers K
  rw [if_neg hn]
  exact (v.adicCompletionIntegers K).one_mem

noncomputable def truncateIdele (S : Finset (FinitePlace K)) (a : HeckeIdeles K) :
    HeckeIdeles K where
  val := (1, truncateFiniteAdele K S (fun v => a.val.2 v))
  inv := (1, truncateFiniteAdele K S (fun v => a.inv.2 v))
  val_inv := by
    apply Prod.ext
    · exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro v
      classical
      change (if v ∈ S then a.val.2 v else 1) *
        (if v ∈ S then a.inv.2 v else 1) = 1
      by_cases hv : v ∈ S
      · simp only [if_pos hv]
        exact congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
      · simp [hv]
  inv_val := by
    apply Prod.ext
    · exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro v
      classical
      change (if v ∈ S then a.inv.2 v else 1) *
        (if v ∈ S then a.val.2 v else 1) = 1
      by_cases hv : v ∈ S
      · simp only [if_pos hv]
        exact congrArg (fun b : HeckeAdeles K => b.2 v) a.inv_val
      · simp [hv]

/-- A finite idele is a finite-coordinate idele times an actual integral idele.
The finite exceptional set is derived from its restricted-product membership. -/
theorem genuineFiniteIdele_decomposition (a : HeckeIdeles K) (hinf : a.val.1 = 1) :
    ∃ S : Finset (FinitePlace K),
      ∃ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        a = truncateIdele K S a * integralIdele K x := by
  classical
  let S := (genuineIdele_nonunit_finite K a).toFinset
  let b := a * (truncateIdele K S a)⁻¹
  have hb : b.val.1 = 1 := by
    change a.val.1 * 1 = 1
    rw [hinf, one_mul]
  have hv : ∀ v : FinitePlace K, Valued.v (b.val.2 v) = 1 := by
    intro v
    change Valued.v (a.val.2 v * (if v ∈ S then a.inv.2 v else 1)) = 1
    by_cases hm : v ∈ S
    · rw [if_pos hm]
      have he : a.val.2 v * a.inv.2 v = 1 :=
        congrArg (fun c : HeckeAdeles K => c.2 v) a.val_inv
      rw [he, map_one]
    · rw [if_neg hm, mul_one]
      by_contra hn
      exact hm ((Set.Finite.mem_toFinset (genuineIdele_nonunit_finite K a)).2 hn)
  obtain ⟨x, hx⟩ := genuineIdele_integralUnit_representation K b hb hv
  refine ⟨S, x, ?_⟩
  rw [hx]
  dsimp [b]
  rw [mul_left_comm, mul_inv_cancel, mul_one]

#check genuineFiniteIdele_decomposition
#print axioms genuineFiniteIdele_decomposition
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

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

/-- Equality of genuine finite valuations is precisely the integral-unit coset
relation. This identifies the disjoint shells used by finite-idelic integration. -/
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

#check integralIdele_coordinate_valuation
#print axioms integralIdele_coordinate_valuation
#check genuineFiniteIdele_same_shell_iff
#print axioms genuineFiniteIdele_same_shell_iff
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine finite valuation vector, with the usual positive uniformizer order. -/
noncomputable def finiteIdeleOrder (a : HeckeIdeles K) : FinitePlace K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => -(Valued.v (a.val.2 v)).log) (by
    apply (genuineIdele_nonunit_finite K a).subset
    intro v hv
    change -(Valued.v (a.val.2 v)).log ≠ 0 at hv
    change Valued.v (a.val.2 v) ≠ 1
    intro he
    apply hv
    rw [he]
    simp)

theorem genuineIdele_coordinate_valuation_ne_zero (a : HeckeIdeles K) (v : FinitePlace K) :
    Valued.v (a.val.2 v) ≠ 0 := by
  have he : a.val.2 v * a.inv.2 v = 1 :=
    congrArg (fun b : HeckeAdeles K => b.2 v) a.val_inv
  have hm : Valued.v (a.val.2 v) * Valued.v (a.inv.2 v) = 1 := by
    rw [← map_mul, he, map_one]
  intro hz
  rw [hz, zero_mul] at hm
  exact zero_ne_one hm

theorem finiteIdeleOrder_valuation (a : HeckeIdeles K) (v : FinitePlace K) :
    Valued.v (a.val.2 v) = WithZero.exp (-(finiteIdeleOrder K a v)) := by
  change Valued.v (a.val.2 v) = WithZero.exp (-(-(Valued.v (a.val.2 v)).log))
  rw [neg_neg, WithZero.exp_log (genuineIdele_coordinate_valuation_ne_zero K a v)]

theorem finiteIdeleOrder_eq_iff (a b : HeckeIdeles K) :
    finiteIdeleOrder K a = finiteIdeleOrder K b ↔
      ∀ v : FinitePlace K, Valued.v (a.val.2 v) = Valued.v (b.val.2 v) := by
  constructor
  · intro h v
    rw [finiteIdeleOrder_valuation K a v, finiteIdeleOrder_valuation K b v, h]
  · intro h
    ext v
    change -(Valued.v (a.val.2 v)).log = -(Valued.v (b.val.2 v)).log
    rw [h v]

/-- The finitely supported integer order vector classifies finite-idelic
integral-unit cosets; this is the shell index for the genuine Mellin integral. -/
theorem finiteIdeleOrder_classifies (a b : HeckeIdeles K)
    (ha : a.val.1 = 1) (hb : b.val.1 = 1) :
    finiteIdeleOrder K a = finiteIdeleOrder K b ↔
      ∃ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        a = b * integralIdele K x := by
  rw [finiteIdeleOrder_eq_iff, genuineFiniteIdele_same_shell_iff K a b ha hb]

#check genuineIdele_coordinate_valuation_ne_zero
#print axioms genuineIdele_coordinate_valuation_ne_zero
#check finiteIdeleOrder_valuation
#print axioms finiteIdeleOrder_valuation
#check finiteIdeleOrder_eq_iff
#print axioms finiteIdeleOrder_eq_iff
#check finiteIdeleOrder_classifies
#print axioms finiteIdeleOrder_classifies
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem localUniformizer_valuation (v : FinitePlace K) :
    Valued.v (localUniformizer K v : LocalField K v) = WithZero.exp (-1) := by
  change Valued.v ((Classical.choose (v.valuation_exists_uniformizer K) : K) :
    LocalField K v) = WithZero.exp (-1)
  rw [v.valuedAdicCompletion_eq_valuation']
  exact Classical.choose_spec (v.valuation_exists_uniformizer K)

theorem localUniformizer_zpow_valuation (v : FinitePlace K) (n : ℤ) :
    Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v) =
      WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, localUniformizer_valuation,
    ← WithZero.exp_zsmul]
  congr 1
  simp

/-- An actual idele representing a finitely supported integer valuation vector. -/
noncomputable def finiteOrderRepresentative (n : FinitePlace K →₀ ℤ) : HeckeIdeles K where
  val := (1, truncateFiniteAdele K n.support
    (fun v => ((localUniformizer K v ^ n v : (LocalField K v)ˣ) : LocalField K v)))
  inv := (1, truncateFiniteAdele K n.support
    (fun v => (localUniformizer K v ^ n v).inv))
  val_inv := by
    apply Prod.ext
    · exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro v
      classical
      change (if v ∈ n.support then (localUniformizer K v ^ n v).val else 1) *
        (if v ∈ n.support then (localUniformizer K v ^ n v).inv else 1) = 1
      by_cases hv : v ∈ n.support
      · simp only [if_pos hv]
        exact (localUniformizer K v ^ n v).val_inv
      · simp [hv]
  inv_val := by
    apply Prod.ext
    · exact one_mul 1
    · apply IsDedekindDomain.FiniteAdeleRing.ext K
      intro v
      classical
      change (if v ∈ n.support then (localUniformizer K v ^ n v).inv else 1) *
        (if v ∈ n.support then (localUniformizer K v ^ n v).val else 1) = 1
      by_cases hv : v ∈ n.support
      · simp only [if_pos hv]
        exact (localUniformizer K v ^ n v).inv_val
      · simp [hv]

theorem finiteOrderRepresentative_coordinate (n : FinitePlace K →₀ ℤ)
    (v : FinitePlace K) :
    (finiteOrderRepresentative K n).val.2 v =
      ((localUniformizer K v ^ n v : (LocalField K v)ˣ) : LocalField K v) := by
  classical
  change (if v ∈ n.support then (localUniformizer K v ^ n v).val else 1) = _
  by_cases hv : v ∈ n.support
  · rw [if_pos hv]
  · have hn : n v = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hv
    rw [if_neg hv, hn, zpow_zero]
    rfl

theorem finiteOrderRepresentative_order (n : FinitePlace K →₀ ℤ) :
    finiteIdeleOrder K (finiteOrderRepresentative K n) = n := by
  ext v
  change -(Valued.v ((finiteOrderRepresentative K n).val.2 v)).log = n v
  rw [finiteOrderRepresentative_coordinate, localUniformizer_zpow_valuation,
    WithZero.log_exp, neg_neg]

/-- Every genuine finite idele belongs to the unit coset of its uniformizer representative. -/
theorem genuineFiniteIdele_uniformizer_decomposition (a : HeckeIdeles K)
    (ha : a.val.1 = 1) :
    ∃ x : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
      a = finiteOrderRepresentative K (finiteIdeleOrder K a) * integralIdele K x := by
  apply (finiteIdeleOrder_classifies K a
    (finiteOrderRepresentative K (finiteIdeleOrder K a)) ha rfl).mp
  exact (finiteOrderRepresentative_order K (finiteIdeleOrder K a)).symm

/-- The integer shell index is genuinely onto, with infinite component one. -/
theorem finiteIdeleOrder_surjective :
    ∀ n : FinitePlace K →₀ ℤ, ∃ a : HeckeIdeles K,
      a.val.1 = 1 ∧ finiteIdeleOrder K a = n := by
  intro n
  exact ⟨finiteOrderRepresentative K n, rfl, finiteOrderRepresentative_order K n⟩

#check localUniformizer_valuation
#print axioms localUniformizer_valuation
#check localUniformizer_zpow_valuation
#print axioms localUniformizer_zpow_valuation
#check finiteOrderRepresentative_coordinate
#print axioms finiteOrderRepresentative_coordinate
#check finiteOrderRepresentative_order
#print axioms finiteOrderRepresentative_order
#check genuineFiniteIdele_uniformizer_decomposition
#print axioms genuineFiniteIdele_uniformizer_decomposition
#check finiteIdeleOrder_surjective
#print axioms finiteIdeleOrder_surjective
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual weighted finite Tate test depends only on the finite valuation shell. -/
theorem finiteTateTest_eq_of_order_eq (χ : UnitaryHeckeCharacter K)
    (a b : HeckeIdeles K) (ha : a.val.1 = 1) (hb : b.val.1 = 1)
    (h : finiteIdeleOrder K a = finiteIdeleOrder K b) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      finiteAdelicTest K χ b.val.2 * (χ.character b : ℂ) := by
  obtain ⟨u, rfl⟩ := (finiteIdeleOrder_classifies K a b ha hb).mp h
  exact finiteTateTest_integralUnit_invariant K χ b u

/-- Evaluation on an actual finite idele reduces to its explicit uniformizer representative. -/
theorem finiteTateTest_eq_representative (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) (ha : a.val.1 = 1) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      finiteAdelicTest K χ (finiteOrderRepresentative K (finiteIdeleOrder K a)).val.2 *
        (χ.character (finiteOrderRepresentative K (finiteIdeleOrder K a)) : ℂ) := by
  apply finiteTateTest_eq_of_order_eq K χ a _ ha rfl
  exact (finiteOrderRepresentative_order K (finiteIdeleOrder K a)).symm

#check finiteTateTest_eq_of_order_eq
#print axioms finiteTateTest_eq_of_order_eq
#check finiteTateTest_eq_representative
#print axioms finiteTateTest_eq_representative
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Exact local value at an integer uniformizer power, including negative shells. -/
theorem finiteAdditiveTest_uniformizer_zpow (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (n : ℤ) :
    finiteAdditiveTest K χ v
      ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v) =
      if IsUnramified K χ v then (if 0 ≤ n then 1 else 0)
      else (if n = 0 then 1 else 0) := by
  classical
  rw [finiteAdditiveTest_restrict, localUniformizer_zpow_valuation]
  have hle : WithZero.exp (-n) ≤ (1 : WithZero (Multiplicative ℤ)) ↔ 0 ≤ n := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have heq : WithZero.exp (-n) = (1 : WithZero (Multiplicative ℤ)) ↔ n = 0 := by
    constructor
    · intro h
      have hh := congrArg WithZero.log h
      simp only [WithZero.log_exp, WithZero.log_one] at hh
      omega
    · rintro rfl
      simp
  by_cases hn : n = 0
  · subst n
    simp [localCharacter_one]
  · simp only [hle, heq, hn, if_false]

/-- Precisely the shells that contribute to the genuine finite Euler integral. -/
def AdmissibleFiniteOrder (χ : UnitaryHeckeCharacter K) (n : FinitePlace K →₀ ℤ) : Prop :=
  ∀ v, 0 ≤ n v ∧ (¬ IsUnramified K χ v → n v = 0)

/-- The actual restricted Tate tensor on every uniformizer representative. -/
theorem finiteAdelicTest_representative (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) :
    finiteAdelicTest K χ (finiteOrderRepresentative K n).val.2 =
      if AdmissibleFiniteOrder K χ n then 1 else 0 := by
  classical
  by_cases hn : AdmissibleFiniteOrder K χ n
  · rw [if_pos hn]
    unfold finiteAdelicTest
    have he (v : FinitePlace K) :
        finiteAdditiveTest K χ v ((finiteOrderRepresentative K n).val.2 v) = 1 := by
      rw [finiteOrderRepresentative_coordinate, finiteAdditiveTest_uniformizer_zpow]
      by_cases hu : IsUnramified K χ v
      · simp [hu, (hn v).1]
      · simp [hu, (hn v).2 hu]
    simp_rw [he]
    simp
  · rw [if_neg hn]
    have hex : ∃ v, ¬ (0 ≤ n v ∧ (¬ IsUnramified K χ v → n v = 0)) := by
      simpa only [AdmissibleFiniteOrder, not_forall] using hn
    obtain ⟨v, hv⟩ := hex
    have hz : finiteAdditiveTest K χ v ((finiteOrderRepresentative K n).val.2 v) = 0 := by
      rw [finiteOrderRepresentative_coordinate, finiteAdditiveTest_uniformizer_zpow]
      by_cases hu : IsUnramified K χ v
      · have hh : ¬ 0 ≤ n v := by
          intro h
          exact hv ⟨h, fun hnu => (hnu hu).elim⟩
        simp [hu, hh]
      · have hh : n v ≠ 0 := by
          intro h
          exact hv ⟨by omega, fun _ => h⟩
        simp [hu, hh]
    unfold finiteAdelicTest
    let hf := finiteAdelicTest_mulSupport_finite K χ (finiteOrderRepresentative K n).val.2
    rw [finprod_eq_prod _ hf, Finset.prod_eq_zero_iff]
    refine ⟨v, ?_, hz⟩
    apply hf.mem_toFinset.mpr
    change finiteAdditiveTest K χ v ((finiteOrderRepresentative K n).val.2 v) ≠ 1
    rw [hz]
    norm_num

/-- Shell evaluation for the actual finite-idelic character-weighted Tate test. -/
theorem finiteTateTest_shell_value (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) (ha : a.val.1 = 1) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      if AdmissibleFiniteOrder K χ (finiteIdeleOrder K a) then
        (χ.character (finiteOrderRepresentative K (finiteIdeleOrder K a)) : ℂ)
      else 0 := by
  rw [finiteTateTest_eq_representative K χ a ha, finiteAdelicTest_representative]
  split_ifs <;> simp

#check finiteAdditiveTest_uniformizer_zpow
#print axioms finiteAdditiveTest_uniformizer_zpow
#check finiteAdelicTest_representative
#print axioms finiteAdelicTest_representative
#check finiteTateTest_shell_value
#print axioms finiteTateTest_shell_value
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The shell representative is the actual product of local uniformizer ideles. -/
theorem finiteOrderRepresentative_eq_localProduct (n : FinitePlace K →₀ ℤ) :
    finiteOrderRepresentative K n =
      ∏ v ∈ n.support, localIdele K v (localUniformizer K v ^ n v) := by
  classical
  apply Units.ext
  apply Prod.ext
  · let ev : HeckeIdeles K →* NumberField.InfiniteAdeleRing K :=
      { toFun := fun a => a.val.1, map_one' := rfl, map_mul' := fun _ _ => rfl }
    change 1 = ev (∏ v ∈ n.support, localIdele K v (localUniformizer K v ^ n v))
    rw [map_prod]
    change 1 = ∏ _v ∈ n.support, (1 : NumberField.InfiniteAdeleRing K)
    simp
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    let ev : HeckeIdeles K →* LocalField K v :=
      { toFun := fun a => a.val.2 v, map_one' := rfl, map_mul' := fun _ _ => rfl }
    change (finiteOrderRepresentative K n).val.2 v =
      ev (∏ w ∈ n.support, localIdele K w (localUniformizer K w ^ n w))
    rw [finiteOrderRepresentative_coordinate, map_prod]
    rw [Finset.prod_eq_single v]
    · change _ = Function.update (fun w : FinitePlace K => (1 : LocalField K w))
        v ((localUniformizer K v ^ n v).val) v
      simp
    · intro w _hw hwv
      change Function.update (fun w : FinitePlace K => (1 : LocalField K w))
        w ((localUniformizer K w ^ n w).val) v = 1
      simp [Function.update_of_ne (Ne.symm hwv)]
    · intro hv
      have hn : n v = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hv
      change Function.update (fun w : FinitePlace K => (1 : LocalField K w))
        v ((localUniformizer K v ^ n v).val) v = 1
      simp [hn]

/-- The local character has the usual integer-power law, with no order restriction. -/
theorem localCharacter_zpow (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : (LocalField K v)ˣ) (n : ℤ) :
    localCharacter K χ v (x ^ n) = localCharacter K χ v x ^ n := by
  let f : (LocalField K v)ˣ →* Circle :=
    { toFun := localCharacter K χ v
      map_one' := localCharacter_one K χ v
      map_mul' := localCharacter_mul K χ v }
  exact f.map_zpow x n

/-- Exact finite Euler coefficient from the genuine idelic character. -/
theorem character_finiteOrderRepresentative (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) :
    χ.character (finiteOrderRepresentative K n) =
      ∏ v ∈ n.support, localCharacter K χ v (localUniformizer K v) ^ n v := by
  rw [finiteOrderRepresentative_eq_localProduct, map_prod]
  apply Finset.prod_congr rfl
  intro v _hv
  exact localCharacter_zpow K χ v (localUniformizer K v) (n v)

/-- Complete finite Euler coefficient on each genuine finite-idelic valuation shell. -/
theorem finiteTateTest_shell_eulerCoefficient (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) (ha : a.val.1 = 1) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      if AdmissibleFiniteOrder K χ (finiteIdeleOrder K a) then
        ((∏ v ∈ (finiteIdeleOrder K a).support,
          localCharacter K χ v (localUniformizer K v) ^ finiteIdeleOrder K a v : Circle) : ℂ)
      else 0 := by
  rw [finiteTateTest_shell_value K χ a ha, character_finiteOrderRepresentative]

#check finiteOrderRepresentative_eq_localProduct
#print axioms finiteOrderRepresentative_eq_localProduct
#check localCharacter_zpow
#print axioms localCharacter_zpow
#check character_finiteOrderRepresentative
#print axioms character_finiteOrderRepresentative
#check finiteTateTest_shell_eulerCoefficient
#print axioms finiteTateTest_shell_eulerCoefficient
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Natural Euler exponents, with ramified factors suppressed. -/
def UnramifiedExponents (χ : UnitaryHeckeCharacter K) :=
  {m : FinitePlace K →₀ ℕ // ∀ v, ¬ IsUnramified K χ v → m v = 0}

/-- The exact reindexing needed to sum the genuine Tate integrand over its nonzero shells. -/
noncomputable def admissibleOrderEquiv (χ : UnitaryHeckeCharacter K) :
    {n : FinitePlace K →₀ ℤ // AdmissibleFiniteOrder K χ n} ≃
      UnramifiedExponents K χ where
  toFun n := ⟨n.val.mapRange Int.toNat (by simp), by
    intro v hv
    change (n.val v).toNat = 0
    rw [(n.property v).2 hv]
    rfl⟩
  invFun m := ⟨m.val.mapRange (fun k : ℕ => (k : ℤ)) (by simp), by
    intro v
    change 0 ≤ (m.val v : ℤ) ∧ (¬ IsUnramified K χ v → (m.val v : ℤ) = 0)
    exact ⟨Int.natCast_nonneg _, fun h => by rw [m.property v h]; rfl⟩⟩
  left_inv n := by
    apply Subtype.ext
    ext v
    change ((n.val v).toNat : ℤ) = n.val v
    exact Int.toNat_of_nonneg (n.property v).1
  right_inv m := by
    apply Subtype.ext
    ext v
    change (m.val v : ℤ).toNat = m.val v
    simp

/-- Reindexing preserves the exact finite support, so no Euler place is lost. -/
theorem admissibleOrderEquiv_support (χ : UnitaryHeckeCharacter K)
    (n : {n : FinitePlace K →₀ ℤ // AdmissibleFiniteOrder K χ n}) :
    (admissibleOrderEquiv K χ n).val.support = n.val.support := by
  classical
  ext v
  simp only [Finsupp.mem_support_iff]
  change (n.val v).toNat ≠ 0 ↔ n.val v ≠ 0
  have hcast : ((n.val v).toNat : ℤ) = n.val v := Int.toNat_of_nonneg (n.property v).1
  omega

/-- The natural exponent shell gives precisely the genuine finite Euler coefficient. -/
theorem finiteTateTest_natural_shell (χ : UnitaryHeckeCharacter K)
    (m : UnramifiedExponents K χ) :
    let n := ((admissibleOrderEquiv K χ).symm m).val
    finiteAdelicTest K χ (finiteOrderRepresentative K n).val.2 *
      (χ.character (finiteOrderRepresentative K n) : ℂ) =
      ((∏ v ∈ m.val.support,
        localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) := by
  dsimp only
  let n := (admissibleOrderEquiv K χ).symm m
  change finiteAdelicTest K χ (finiteOrderRepresentative K n.val).val.2 *
    (χ.character (finiteOrderRepresentative K n.val) : ℂ) = _
  rw [finiteTateTest_shell_eulerCoefficient K χ _ rfl,
    finiteOrderRepresentative_order, if_pos n.property]
  have hs : n.val.support = m.val.support := by
    have h := admissibleOrderEquiv_support K χ n
    rw [(admissibleOrderEquiv K χ).apply_symm_apply] at h
    exact h.symm
  rw [hs]
  congr 1

#check admissibleOrderEquiv
#print axioms admissibleOrderEquiv
#check admissibleOrderEquiv_support
#print axioms admissibleOrderEquiv_support
#check finiteTateTest_natural_shell
#print axioms finiteTateTest_natural_shell
end MasulloGRH

/-! H/r47: convergence-level assembly of the checked shell reindexing.
The weight remains explicit until genuine norm compatibility is established. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def weightedFiniteShell (χ : UnitaryHeckeCharacter K)
    (W : (FinitePlace K →₀ ℤ) → ℂ) (n : FinitePlace K →₀ ℤ) : ℂ :=
  (finiteAdelicTest K χ (finiteOrderRepresentative K n).val.2 *
    (χ.character (finiteOrderRepresentative K n) : ℂ)) * W n

/-- The full integer-shell series and the natural Euler exponent series have
exactly the same HasSum witnesses, including the vanishing inadmissible terms. -/
theorem weightedFiniteShell_hasSum_iff (χ : UnitaryHeckeCharacter K)
    (W : (FinitePlace K →₀ ℤ) → ℂ) (L : ℂ) :
    HasSum (weightedFiniteShell K χ W) L ↔
      HasSum (fun m : UnramifiedExponents K χ =>
        ((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val) L := by
  classical
  let f := weightedFiniteShell K χ W
  have hf : Function.support f ⊆ {n | AdmissibleFiniteOrder K χ n} := by
    intro n hn
    by_contra h
    change ¬ AdmissibleFiniteOrder K χ n at h
    apply hn
    dsimp [f, weightedFiniteShell]
    rw [finiteAdelicTest_representative, if_neg h, zero_mul, zero_mul]
  have hr : HasSum (fun n : {n // AdmissibleFiniteOrder K χ n} => f n.val) L ↔
      HasSum f L := hasSum_subtype_iff_of_support_subset hf
  have he : (fun m : UnramifiedExponents K χ =>
      f ((admissibleOrderEquiv K χ).symm m).val) =
      (fun m : UnramifiedExponents K χ =>
        ((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val) := by
    funext m
    dsimp [f, weightedFiniteShell]
    rw [finiteTateTest_natural_shell]
  calc
    HasSum f L ↔ HasSum (fun n : {n // AdmissibleFiniteOrder K χ n} => f n.val) L := hr.symm
    _ ↔ HasSum (fun m : UnramifiedExponents K χ =>
        f ((admissibleOrderEquiv K χ).symm m).val) L :=
      ((admissibleOrderEquiv K χ).symm.hasSum_iff).symm
    _ ↔ _ := by rw [he]

/-- This transports convergence, not just Lean's default value of tsum. -/
theorem weightedFiniteShell_summable_iff (χ : UnitaryHeckeCharacter K)
    (W : (FinitePlace K →₀ ℤ) → ℂ) :
    Summable (weightedFiniteShell K χ W) ↔
      Summable (fun m : UnramifiedExponents K χ =>
        ((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val) := by
  exact exists_congr (fun L => weightedFiniteShell_hasSum_iff K χ W L)

#check weightedFiniteShell_hasSum_iff
#print axioms weightedFiniteShell_hasSum_iff
#check weightedFiniteShell_summable_iff
#print axioms weightedFiniteShell_summable_iff
end MasulloGRH

set_option synthInstance.maxHeartbeats 200000
/- F/r47 exact checked integration source, with shared definitions reused above. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
theorem finiteIdele_orderFiber_isClosed (n : FinitePlace K →₀ ℤ) :
    IsClosed {a : HeckeIdeles K | finiteIdeleOrder K a = n} := by
  have he : {a : HeckeIdeles K | finiteIdeleOrder K a = n} =
      ⋂ v : FinitePlace K, (fun a : HeckeIdeles K => a.val.2 v) ⁻¹'
        {x : LocalField K v | Valued.v x = WithZero.exp (-(n v))} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h v
      rw [finiteIdeleOrder_valuation, h]
    · intro h
      ext v
      change -(Valued.v (a.val.2 v)).log = n v
      rw [h v, WithZero.log_exp, neg_neg]
  rw [he]
  apply isClosed_iInter
  intro v
  exact (Valued.isClopen_sphere (LocalField K v) (by exact WithZero.exp_ne_zero : WithZero.exp (-(n v)) ≠ 0)).isClosed.preimage
    ((RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val))

/-- Closed shell inside the genuine finite-idelic integration subgroup. -/
theorem finiteIdele_relativeShell_isClosed (n : FinitePlace K →₀ ℤ) :
    IsClosed {a : {a : HeckeIdeles K // a.val.1 = 1} | finiteIdeleOrder K a.val = n} :=
  (finiteIdele_orderFiber_isClosed K n).preimage continuous_subtype_val

theorem finiteIdele_relativeShell_measurable (n : FinitePlace K →₀ ℤ) :
    @MeasurableSet {a : HeckeIdeles K // a.val.1 = 1}
      (borel {a : HeckeIdeles K // a.val.1 = 1})
      {a | finiteIdeleOrder K a.val = n} := by
  letI : MeasurableSpace {a : HeckeIdeles K // a.val.1 = 1} := borel _
  letI : BorelSpace {a : HeckeIdeles K // a.val.1 = 1} := ⟨rfl⟩
  exact (finiteIdele_relativeShell_isClosed K n).measurableSet

#check finiteIdele_orderFiber_isClosed
#print axioms finiteIdele_orderFiber_isClosed
#check finiteIdele_relativeShell_isClosed
#print axioms finiteIdele_relativeShell_isClosed
#check finiteIdele_relativeShell_measurable
#print axioms finiteIdele_relativeShell_measurable
end MasulloGRH
/- F round 47: integration on the actual finite-idelic subgroup.
D/r46 supplies the checked Borel valuation fibers. -/
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

abbrev FiniteIdelicDomain := {a : HeckeIdeles K // a.val.1 = 1}
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

def finiteIdelicShell (n : FinitePlace K →₀ ℤ) : Set (FiniteIdelicDomain K) :=
  {a | finiteIdeleOrder K a.val = n}

theorem finiteIdelicShell_index_countable : Countable (FinitePlace K →₀ ℤ) := by
  letI : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  letI : Countable (𝓞 K) := (IsFractionRing.injective (𝓞 K) K).countable
  have hsurj : Function.Surjective
      (fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) := by
    intro I
    exact IsNoetherian.noetherian I
  letI : Countable (Ideal (𝓞 K)) := hsurj.countable
  letI : Countable (FinitePlace K) :=
    (show Function.Injective (fun v : FinitePlace K => v.asIdeal) from
      fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h).countable
  infer_instance

theorem finiteIdelicShell_measurable (n : FinitePlace K →₀ ℤ) :
    MeasurableSet (finiteIdelicShell K n) :=
  finiteIdele_relativeShell_measurable K n

theorem finiteIdelicShell_disjoint :
    Pairwise (fun n m : FinitePlace K →₀ ℤ =>
      Disjoint (finiteIdelicShell K n) (finiteIdelicShell K m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro a hn hm
  exact hnm (hn.symm.trans hm)

theorem finiteIdelicShell_cover :
    (⋃ n : FinitePlace K →₀ ℤ, finiteIdelicShell K n) = Set.univ := by
  ext a
  simp [finiteIdelicShell]

/-- The summability hypothesis concerns integrals of norms, not norms of integrals. -/
theorem finiteIdelic_integrable_of_shell_norm_sum
    (μ : Measure (FiniteIdelicDomain K)) (f : FiniteIdelicDomain K → ℂ)
    (hi : ∀ n : FinitePlace K →₀ ℤ, IntegrableOn f (finiteIdelicShell K n) μ)
    (hs : Summable (fun n : FinitePlace K →₀ ℤ =>
      ∫ a in finiteIdelicShell K n, ‖f a‖ ∂μ)) : Integrable f μ := by
  letI := finiteIdelicShell_index_countable K
  have h := integrableOn_iUnion_of_summable_integral_norm hi hs
  simpa only [finiteIdelicShell_cover K, integrableOn_univ] using h

/-- No global integrability assumption: shell absolute summability discharges it.
The measure is still explicit; normalized Haar construction is a separate obligation. -/
theorem finiteIdelic_integral_eq_tsum_of_shell_norm_sum
    (μ : Measure (FiniteIdelicDomain K)) (f : FiniteIdelicDomain K → ℂ)
    (hi : ∀ n : FinitePlace K →₀ ℤ, IntegrableOn f (finiteIdelicShell K n) μ)
    (hs : Summable (fun n : FinitePlace K →₀ ℤ =>
      ∫ a in finiteIdelicShell K n, ‖f a‖ ∂μ)) :
    (∫ a, f a ∂μ) = ∑' n : FinitePlace K →₀ ℤ,
      ∫ a in finiteIdelicShell K n, f a ∂μ := by
  letI := finiteIdelicShell_index_countable K
  have hf := finiteIdelic_integrable_of_shell_norm_sum K μ f hi hs
  have hu : IntegrableOn f (⋃ n, finiteIdelicShell K n) μ := by
    simpa only [finiteIdelicShell_cover K, integrableOn_univ] using hf
  have h := integral_iUnion (finiteIdelicShell_measurable K)
    (finiteIdelicShell_disjoint K) hu
  simpa only [finiteIdelicShell_cover K, Measure.restrict_univ] using h

#check finiteIdelicShell_index_countable
#print axioms finiteIdelicShell_index_countable
#check finiteIdelicShell_measurable
#print axioms finiteIdelicShell_measurable
#check finiteIdelicShell_disjoint
#print axioms finiteIdelicShell_disjoint
#check finiteIdelicShell_cover
#print axioms finiteIdelicShell_cover
#check finiteIdelic_integrable_of_shell_norm_sum
#print axioms finiteIdelic_integrable_of_shell_norm_sum
#check finiteIdelic_integral_eq_tsum_of_shell_norm_sum
#print axioms finiteIdelic_integral_eq_tsum_of_shell_norm_sum
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

/-- Assembly interface for the genuine Tate shell coefficients: normalized shell
masses and absolute coefficient summability imply absolute integrability and the
shell-sum identity. Normalized Haar construction and coefficient estimates remain
explicit obligations of the full Mellin theorem. -/
theorem finiteIdelic_integral_of_normalized_shell_coefficients
    (μ : Measure (FiniteIdelicDomain K))
    (hm : ∀ n : FinitePlace K →₀ ℤ, μ (finiteIdelicShell K n) = 1)
    (f : FiniteIdelicDomain K → ℂ) (c : (FinitePlace K →₀ ℤ) → ℂ)
    (hc : ∀ a, f a = c (finiteIdeleOrder K a.val))
    (hs : Summable (fun n => ‖c n‖)) :
    Integrable f μ ∧ (∫ a, f a ∂μ) = ∑' n, c n := by
  have he (n : FinitePlace K →₀ ℤ) :
      f =ᵐ[μ.restrict (finiteIdelicShell K n)] (fun _ => c n) := by
    filter_upwards [ae_restrict_mem (finiteIdelicShell_measurable K n)] with a ha
    rw [hc a, ha]
  have hp (n : FinitePlace K →₀ ℤ) :
      IsProbabilityMeasure (μ.restrict (finiteIdelicShell K n)) := by
    constructor
    simpa only [Measure.restrict_apply_univ] using hm n
  have hi (n : FinitePlace K →₀ ℤ) : IntegrableOn f (finiteIdelicShell K n) μ := by
    letI := hp n
    exact (integrable_const (c n)).congr (he n).symm
  have hn (n : FinitePlace K →₀ ℤ) :
      (∫ a in finiteIdelicShell K n, ‖f a‖ ∂μ) = ‖c n‖ := by
    letI := hp n
    calc
      _ = ∫ _a in finiteIdelicShell K n, ‖c n‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards [he n] with a ha
        rw [ha]
      _ = _ := by simp
  have hs' : Summable (fun n : FinitePlace K →₀ ℤ =>
      ∫ a in finiteIdelicShell K n, ‖f a‖ ∂μ) := by
    simpa only [hn] using hs
  refine ⟨finiteIdelic_integrable_of_shell_norm_sum K μ f hi hs', ?_⟩
  rw [finiteIdelic_integral_eq_tsum_of_shell_norm_sum K μ f hi hs']
  apply tsum_congr
  intro n
  letI := hp n
  calc
    _ = ∫ _a in finiteIdelicShell K n, c n ∂μ := integral_congr_ae (he n)
    _ = _ := by simp

#check finiteIdelic_integral_of_normalized_shell_coefficients
#print axioms finiteIdelic_integral_of_normalized_shell_coefficients
end MasulloGRH

/- H/r48: absolute convergence transport and actual Tate-integral assembly. -/
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

/-- Natural-exponent absolute summability is exactly integer-shell absolute
summability, with inadmissible shells removed by the genuine Tate support. -/
theorem weightedFiniteShell_norm_hasSum_iff (χ : UnitaryHeckeCharacter K)
    (W : (FinitePlace K →₀ ℤ) → ℂ) (L : ℝ) :
    HasSum (fun n => ‖weightedFiniteShell K χ W n‖) L ↔
      HasSum (fun m : UnramifiedExponents K χ =>
        ‖((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val‖) L := by
  classical
  let f := fun n => ‖weightedFiniteShell K χ W n‖
  have hf : Function.support f ⊆ {n | AdmissibleFiniteOrder K χ n} := by
    intro n hn
    by_contra h
    change ¬ AdmissibleFiniteOrder K χ n at h
    apply hn
    dsimp [f, weightedFiniteShell]
    rw [finiteAdelicTest_representative, if_neg h, zero_mul, zero_mul, norm_zero]
  have hr : HasSum (fun n : {n // AdmissibleFiniteOrder K χ n} => f n.val) L ↔
      HasSum f L := hasSum_subtype_iff_of_support_subset hf
  have he : (fun m : UnramifiedExponents K χ =>
      f ((admissibleOrderEquiv K χ).symm m).val) =
      (fun m : UnramifiedExponents K χ =>
        ‖((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val‖) := by
    funext m
    dsimp [f, weightedFiniteShell]
    rw [finiteTateTest_natural_shell]
  calc
    HasSum f L ↔ HasSum (fun n : {n // AdmissibleFiniteOrder K χ n} => f n.val) L := hr.symm
    _ ↔ HasSum (fun m : UnramifiedExponents K χ =>
        f ((admissibleOrderEquiv K χ).symm m).val) L :=
      ((admissibleOrderEquiv K χ).symm.hasSum_iff).symm
    _ ↔ _ := by rw [he]

theorem weightedFiniteShell_norm_summable_iff (χ : UnitaryHeckeCharacter K)
    (W : (FinitePlace K →₀ ℤ) → ℂ) :
    Summable (fun n => ‖weightedFiniteShell K χ W n‖) ↔
      Summable (fun m : UnramifiedExponents K χ =>
        ‖((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val‖) :=
  exists_congr (fun L => weightedFiniteShell_norm_hasSum_iff K χ W L)

/-- The actual finite Tate test, integrated on the actual infinite-component-one
idele subgroup, equals its absolutely convergent natural Euler exponent series.
This is conditional on shell mass one and absolute convergence. The valuation
weight W still must be identified with the actual positive finite norm power. -/
theorem finiteTate_integral_eq_naturalEulerSeries
    (χ : UnitaryHeckeCharacter K) (W : (FinitePlace K →₀ ℤ) → ℂ)
    (μ : Measure (FiniteIdelicDomain K))
    (hm : ∀ n : FinitePlace K →₀ ℤ, μ (finiteIdelicShell K n) = 1)
    (hs : Summable (fun m : UnramifiedExponents K χ =>
      ‖((∏ v ∈ m.val.support,
        localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
        W ((admissibleOrderEquiv K χ).symm m).val‖)) :
    let f := fun a : FiniteIdelicDomain K =>
      (finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ)) *
        W (finiteIdeleOrder K a.val)
    Integrable f μ ∧ (∫ a, f a ∂μ) =
      ∑' m : UnramifiedExponents K χ,
        ((∏ v ∈ m.val.support,
          localCharacter K χ v (localUniformizer K v) ^ m.val v : Circle) : ℂ) *
          W ((admissibleOrderEquiv K χ).symm m).val := by
  dsimp only
  have hs' := (weightedFiniteShell_norm_summable_iff K χ W).mpr hs
  have hc (a : FiniteIdelicDomain K) :
      (finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ)) *
        W (finiteIdeleOrder K a.val) =
        weightedFiniteShell K χ W (finiteIdeleOrder K a.val) := by
    unfold weightedFiniteShell
    rw [finiteTateTest_eq_representative K χ a.val a.property]
  obtain ⟨hi, he⟩ := finiteIdelic_integral_of_normalized_shell_coefficients K μ hm
    _ (weightedFiniteShell K χ W) hc hs'
  refine ⟨hi, he.trans ?_⟩
  have hnat := (weightedFiniteShell_summable_iff K χ W).mp hs'.of_norm
  exact ((weightedFiniteShell_hasSum_iff K χ W _).mpr hnat.hasSum).tsum_eq

#check weightedFiniteShell_norm_hasSum_iff
#print axioms weightedFiniteShell_norm_hasSum_iff
#check weightedFiniteShell_norm_summable_iff
#print axioms weightedFiniteShell_norm_summable_iff
#check finiteTate_integral_eq_naturalEulerSeries
#print axioms finiteTate_integral_eq_naturalEulerSeries
end MasulloGRH
