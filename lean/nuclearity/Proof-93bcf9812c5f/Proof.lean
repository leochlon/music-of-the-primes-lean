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

end MasulloGRH

/-! Round 43 G: checked A r40 covariance plus checked D r41 shell classification.
Source hashes and exact successful receipts: evidence/reused_sources.json. -/
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

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual character-weighted finite Tate test depends only on its finite
valuation vector when the infinite component is one. This is the descent
needed for the shell sum in the genuine finite-idelic Mellin integral. -/
theorem finiteTateTest_eq_of_same_order (χ : UnitaryHeckeCharacter K)
    (a b : HeckeIdeles K) (ha : a.val.1 = 1) (hb : b.val.1 = 1)
    (horder : finiteIdeleOrder K a = finiteIdeleOrder K b) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      finiteAdelicTest K χ b.val.2 * (χ.character b : ℂ) := by
  obtain ⟨u, hu⟩ := (finiteIdeleOrder_classifies K a b ha hb).mp horder
  rw [hu]
  exact finiteTateTest_integralUnit_invariant K χ b u

end MasulloGRH

/-! Shell representatives adapted from D r41 final candidate. That extension
had no successful frozen receipt; it is checked anew with this combined source. -/
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

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- A concrete value on every integer valuation shell, using genuine uniformizers. -/
noncomputable def finiteTateShellValue (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) : ℂ :=
  finiteAdelicTest K χ (finiteOrderRepresentative K n).val.2 *
    (χ.character (finiteOrderRepresentative K n) : ℂ)

/-- The genuine weighted Tate test factors through its finitely supported order
vector; no surjectivity or analytic integration premise is assumed. -/
theorem finiteTateTest_eq_shellValue (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) (ha : a.val.1 = 1) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      finiteTateShellValue K χ (finiteIdeleOrder K a) := by
  unfold finiteTateShellValue
  exact finiteTateTest_eq_of_same_order K χ a
    (finiteOrderRepresentative K (finiteIdeleOrder K a)) ha rfl
    (finiteOrderRepresentative_order K (finiteIdeleOrder K a)).symm

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Ramified Euler factors contribute only the zero valuation shell. -/
theorem finiteTateShellValue_zero_of_ramified_order (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) (v : FinitePlace K)
    (hu : ¬ IsUnramified K χ v) (hn : n v ≠ 0) :
    finiteTateShellValue K χ n = 0 := by
  classical
  have hv : Valued.v ((finiteOrderRepresentative K n).val.2 v) ≠ 1 := by
    intro he
    have hh := congrArg WithZero.log he
    rw [finiteOrderRepresentative_coordinate, localUniformizer_zpow_valuation,
      WithZero.log_exp] at hh
    exact hn (by simpa using hh)
  have hz : finiteAdditiveTest K χ v ((finiteOrderRepresentative K n).val.2 v) = 0 := by
    simp only [finiteAdditiveTest, if_neg hu]
    exact ramifiedAdditiveTest_zero_off_shell K χ v _ hv
  have hzero : finiteAdelicTest K χ (finiteOrderRepresentative K n).val.2 = 0 := by
    unfold finiteAdelicTest
    let hf := finiteAdelicTest_mulSupport_finite K χ (finiteOrderRepresentative K n).val.2
    rw [finprod_eq_prod _ hf, Finset.prod_eq_zero_iff]
    refine ⟨v, ?_, hz⟩
    apply hf.mem_toFinset.mpr
    change finiteAdditiveTest K χ v ((finiteOrderRepresentative K n).val.2 v) ≠ 1
    rw [hz]
    norm_num
  unfold finiteTateShellValue
  rw [hzero, zero_mul]

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Exactly the integer shells permitted by the actual finite Tate test. -/
def AdmissibleFiniteOrder (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) : Prop :=
  (∀ v, 0 ≤ n v) ∧ ∀ v, ¬ IsUnramified K χ v → n v = 0

theorem finiteOrderRepresentative_integral_iff (n : FinitePlace K →₀ ℤ)
    (v : FinitePlace K) :
    Valued.v ((finiteOrderRepresentative K n).val.2 v) ≤ 1 ↔ 0 ≤ n v := by
  rw [finiteOrderRepresentative_coordinate, localUniformizer_zpow_valuation]
  change WithZero.exp (-(n v)) ≤ WithZero.exp (0 : ℤ) ↔ _
  rw [WithZero.exp_le_exp]
  exact neg_nonpos

/-- Negative valuation orders cannot occur in the finite Euler shell sum. -/
theorem finiteTateShellValue_zero_of_negative_order (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) (v : FinitePlace K) (hn : n v < 0) :
    finiteTateShellValue K χ n = 0 := by
  have hz := finiteAdelicTest_zero_of_not_integral K χ
    (finiteOrderRepresentative K n).val.2 v
    (fun hv => (not_le_of_gt hn) ((finiteOrderRepresentative_integral_iff K n v).mp hv))
  unfold finiteTateShellValue
  rw [hz, zero_mul]

/-- On every admissible shell the additive test is exactly one at the actual
uniformizer representative; this determines the arithmetic shell coefficient. -/
theorem finiteAdelicTest_representative_eq_one (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) (hn : AdmissibleFiniteOrder K χ n) :
    finiteAdelicTest K χ (finiteOrderRepresentative K n).val.2 = 1 := by
  classical
  have hone (v : FinitePlace K) :
      finiteAdditiveTest K χ v ((finiteOrderRepresentative K n).val.2 v) = 1 := by
    by_cases hu : IsUnramified K χ v
    · have hv := (finiteOrderRepresentative_integral_iff K n v).mpr (hn.1 v)
      simp [finiteAdditiveTest, hu, unramifiedAdditiveTest_apply, hv]
    · rw [finiteOrderRepresentative_coordinate, finiteAdditiveTest_restrict,
        if_neg hu, hn.2 v hu, zpow_zero]
      simp [localCharacter_one]
  unfold finiteAdelicTest
  simp_rw [hone]
  simp

/-- The exact finite Tate shell coefficient, before the residue-norm Mellin weight. -/
theorem finiteTateShellValue_eq_ite (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) :
    finiteTateShellValue K χ n =
      if AdmissibleFiniteOrder K χ n then
        (χ.character (finiteOrderRepresentative K n) : ℂ) else 0 := by
  classical
  by_cases hn : AdmissibleFiniteOrder K χ n
  · rw [if_pos hn]
    unfold finiteTateShellValue
    rw [finiteAdelicTest_representative_eq_one K χ n hn, one_mul]
  · rw [if_neg hn]
    by_cases hp : ∀ v, 0 ≤ n v
    · have hr : ∃ v, ¬ IsUnramified K χ v ∧ n v ≠ 0 := by
        by_contra hh
        apply hn
        refine ⟨hp, ?_⟩
        intro v hv
        by_contra hz
        exact hh ⟨v, hv, hz⟩
      obtain ⟨v, hu, hv⟩ := hr
      exact finiteTateShellValue_zero_of_ramified_order K χ n v hu hv
    · obtain ⟨v, hv⟩ := not_forall.mp hp
      exact finiteTateShellValue_zero_of_negative_order K χ n v (lt_of_not_ge hv)

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The chosen genuine shell representative is the finite product of its local
uniformizer ideles, with no omitted infinite component. -/
theorem finiteOrderRepresentative_eq_prod (n : FinitePlace K →₀ ℤ) :
    finiteOrderRepresentative K n =
      ∏ v ∈ n.support, localIdele K v (localUniformizer K v ^ n v) := by
  classical
  apply Units.ext
  apply Prod.ext
  · let f : HeckeIdeles K →* NumberField.InfiniteAdeleRing K :=
      { toFun := fun a => a.val.1
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    change 1 = f (∏ v ∈ n.support, localIdele K v (localUniformizer K v ^ n v))
    rw [map_prod]
    symm
    apply Finset.prod_eq_one
    intro v hv
    rfl
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rw [finiteOrderRepresentative_coordinate]
    let f : HeckeIdeles K →* LocalField K v :=
      { toFun := fun a => a.val.2 v
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    change _ = f (∏ w ∈ n.support, localIdele K w (localUniformizer K w ^ n w))
    rw [map_prod]
    symm
    calc
      (∏ w ∈ n.support, f (localIdele K w (localUniformizer K w ^ n w))) =
          f (localIdele K v (localUniformizer K v ^ n v)) := by
        apply Finset.prod_eq_single v
        · intro w hw hwv
          change Function.update (fun w : FinitePlace K => (1 : LocalField K w)) w
            (↑(localUniformizer K w ^ n w)) v = 1
          simp [Function.update_of_ne hwv.symm]
        · intro hv
          have hn : n v = 0 := by
            simpa only [Finsupp.mem_support_iff, not_not] using hv
          change Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v
            (↑(localUniformizer K v ^ n v)) v = 1
          simp [hn]
      _ = ↑(localUniformizer K v ^ n v) := by
        change Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v
          (↑(localUniformizer K v ^ n v)) v = _
        simp

/-- Exact arithmetic coefficient: the actual character at the genuine shell
representative is the product of its local uniformizer eigenvalues. -/
theorem character_finiteOrderRepresentative (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) :
    (χ.character (finiteOrderRepresentative K n) : ℂ) =
      ∏ v ∈ n.support, (localCharacter K χ v (localUniformizer K v) : ℂ) ^ n v := by
  classical
  let f : HeckeIdeles K →* ℂ :=
    { toFun := fun a => (χ.character a : ℂ)
      map_one' := by simp
      map_mul' := by intro a b; simp }
  change f (finiteOrderRepresentative K n) = _
  rw [finiteOrderRepresentative_eq_prod, map_prod]
  apply Finset.prod_congr rfl
  intro v hv
  let g : (LocalField K v)ˣ →* ℂ :=
    { toFun := fun x => (localCharacter K χ v x : ℂ)
      map_one' := by simp [localCharacter_one]
      map_mul' := by intro x y; simp [localCharacter_mul] }
  exact map_zpow g (localUniformizer K v) (n v)

/-- The finite Tate shell coefficients are precisely the unramified geometric
Euler coefficients. Norm weights and summation are separate analytic obligations. -/
theorem finiteTateShellValue_eq_eulerCoefficient (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) :
    finiteTateShellValue K χ n =
      if AdmissibleFiniteOrder K χ n then
        ∏ v ∈ n.support, (localCharacter K χ v (localUniformizer K v) : ℂ) ^ n v
      else 0 := by
  rw [finiteTateShellValue_eq_ite, character_finiteOrderRepresentative]

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Direct formula for the actual finite-idelic Tate integrand on every valuation
shell, retaining an arbitrary genuine unitary Hecke character. -/
theorem finiteTateTest_eq_eulerCoefficient (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) (ha : a.val.1 = 1) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) =
      if AdmissibleFiniteOrder K χ (finiteIdeleOrder K a) then
        ∏ v ∈ (finiteIdeleOrder K a).support,
          (localCharacter K χ v (localUniformizer K v) : ℂ) ^ (finiteIdeleOrder K a) v
      else 0 := by
  rw [finiteTateTest_eq_shellValue K χ a ha, finiteTateShellValue_eq_eulerCoefficient]

/-- Exact absolute value of the arithmetic shell coefficient, for the subsequent
norm-weighted absolute-convergence argument. -/
theorem norm_finiteTateShellValue (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) :
    ‖finiteTateShellValue K χ n‖ = if AdmissibleFiniteOrder K χ n then 1 else 0 := by
  classical
  rw [finiteTateShellValue_eq_ite]
  split_ifs <;> simp

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual residue-norm Mellin weight on a finite valuation shell. -/
noncomputable def finiteShellMellinWeight (n : FinitePlace K →₀ ℤ) (s : ℂ) : ℂ :=
  ∏ v ∈ n.support, ((v.asIdeal.absNorm : ℂ) ^ (-s)) ^ n v

/-- Pointwise weighted Euler coefficient, preceding every infinite summation or
integration. This is not an interchange theorem. -/
theorem finiteWeightedTateShell_eq_product (χ : UnitaryHeckeCharacter K)
    (n : FinitePlace K →₀ ℤ) (s : ℂ) :
    finiteTateShellValue K χ n * finiteShellMellinWeight K n s =
      if AdmissibleFiniteOrder K χ n then
        ∏ v ∈ n.support,
          ((localCharacter K χ v (localUniformizer K v) : ℂ) *
            (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ n v
      else 0 := by
  classical
  rw [finiteTateShellValue_eq_eulerCoefficient]
  by_cases hn : AdmissibleFiniteOrder K χ n
  · rw [if_pos hn, if_pos hn]
    unfold finiteShellMellinWeight
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v hv
    exact (mul_zpow _ _ _).symm
  · rw [if_neg hn, if_neg hn, zero_mul]

end MasulloGRH


/-! E/r47: arithmetic estimates reused from checked E/r21 Checkpoint.lean, receipt 113a910a348646f28ee35ddc9e57edd2. -/
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
open scoped NumberField
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- Actual prime fibers have uniformly bounded cardinality, the arithmetic
counting input for the Hecke Euler-product comparison. -/
theorem rationalPrime_fiber_card_le (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) :
    (primesOverFinset p (𝓞 K)).card ≤ Module.finrank ℚ K :=
  Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp


/-- Norm comparison for the actual prime-ideal fibers used in the convergence proof. -/
theorem primeIdeal_absNorm_ge (p : ℤ) (hp : Prime p) (P : Ideal (𝓞 K))
    [(Ideal.span {p}).IsMaximal] [P.LiesOver (Ideal.span {p})] :
    p.natAbs ≤ Ideal.absNorm P := by
  rw [Ideal.absNorm_eq_pow_inertiaDeg P hp]
  have hf := Ideal.inertiaDeg_pos (Ideal.span {p}) P
  cases h : (Ideal.span {p}).inertiaDeg P with
  | zero => omega
  | succ n =>
    rw [pow_succ]
    have ha : 0 < p.natAbs := Int.natAbs_pos.mpr hp.ne_zero
    have hb : 0 < p.natAbs ^ n := pow_pos ha n
    nlinarith


/-- Prime-fiber domination for the all-number-field Hecke convergence proof. -/
theorem primeFiber_rpow_sum_le (p : ℤ) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (σ : ℝ) (hσ : 0 ≤ σ) :
    ∑ P ∈ primesOverFinset (Ideal.span {p}) (𝓞 K), (Ideal.absNorm P : ℝ) ^ (-σ) ≤
      (Module.finrank ℚ K : ℝ) * (p.natAbs : ℝ) ^ (-σ) := by
  classical
  have hp0 : (Ideal.span {p} : Ideal ℤ) ≠ ⊥ := by
    intro h
    exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  have hpR : (0 : ℝ) < p.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hp.ne_zero
  calc
    _ ≤ ∑ P ∈ primesOverFinset (Ideal.span {p}) (𝓞 K), (p.natAbs : ℝ) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hmem := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp hP
      letI : P.LiesOver (Ideal.span {p}) := hmem.2
      exact Real.rpow_le_rpow_of_nonpos hpR (by exact_mod_cast primeIdeal_absNorm_ge K p hp P)
        (neg_nonpos.mpr hσ)
    _ = ((primesOverFinset (Ideal.span {p}) (𝓞 K)).card : ℝ) * (p.natAbs : ℝ) ^ (-σ) := by
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast rationalPrime_fiber_card_le K (Ideal.span {p}) hp0)
      (Real.rpow_nonneg (le_of_lt hpR) _)


/-- Summability of the actual prime-fiber norm sums for every number field. -/
theorem primeFiber_norm_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes =>
      ∑ P ∈ primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K),
        (Ideal.absNorm P : ℝ) ^ (-σ)) := by
  classical
  have hrat : Summable (fun p : Nat.Primes =>
      (Module.finrank ℚ K : ℝ) * (p : ℝ) ^ (-σ)) :=
    (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left _
  apply hrat.of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun P _ =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _))]
  have hp : Prime (p : ℤ) := by
    simpa only [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] using p.property
  have hp0 : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    intro h
    exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp h)
  letI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
    (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  letI : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp0
  simpa only [Int.natAbs_natCast] using
    primeFiber_rpow_sum_le K (p : ℤ) hp σ (le_of_lt (lt_trans zero_lt_one hσ))



/-- The genuine rational prime below a finite place, needed to reindex the norm sum. -/
noncomputable def rationalPlaceBelow
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := Ideal.under ℤ v.asIdeal
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot ℤ v.ne_bot

theorem rationalPlaceBelow_span
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Ideal.span {(Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v) : ℤ)} =
      Ideal.under ℤ v.asIdeal := by
  have he : (Rat.IsIntegralClosure.intEquiv ℤ).toRingHom = RingHom.id ℤ := Subsingleton.elim _ _
  have h := Rat.HeightOneSpectrum.span_natGenerator (rationalPlaceBelow K v)
  change Ideal.span {(Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v) : ℤ)} =
    Ideal.map (Rat.IsIntegralClosure.intEquiv ℤ).toRingHom (rationalPlaceBelow K v).asIdeal at h
  rw [he, Ideal.map_id] at h
  exact h


/-- The generator of the contracted genuine prime is a rational prime. -/
theorem rationalPlaceBelow_generator_prime
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Nat.Prime (Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v)) := by
  let n := Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v)
  have hspan : Ideal.span {(n : ℤ)} = Ideal.under ℤ v.asIdeal :=
    rationalPlaceBelow_span K v
  have hn : (n : ℤ) ≠ 0 := by
    intro h
    apply Ideal.under_ne_bot ℤ v.ne_bot
    rw [← hspan, h]
    simp
  have hp : (Ideal.span {(n : ℤ)} : Ideal ℤ).IsPrime := by
    rw [hspan]
    infer_instance
  have hprime : Prime (n : ℤ) := (Ideal.span_singleton_prime hn).mp hp
  simpa only [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] using hprime

noncomputable def rationalPrimeBelow
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Nat.Primes :=
  ⟨Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v),
    rationalPlaceBelow_generator_prime K v⟩

abbrev PrimeFiberIndex := (p : Nat.Primes) ×
  {P : Ideal (𝓞 K) // P ∈ primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)}

/-- Each genuine finite place is assigned its actual rational-prime fiber. -/
noncomputable def finitePlaceFiberIndex
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : PrimeFiberIndex K := by
  classical
  refine ⟨rationalPrimeBelow K v, v.asIdeal, ?_⟩
  change v.asIdeal ∈ primesOverFinset
    (Ideal.span {(Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v) : ℤ)}) (𝓞 K)
  rw [rationalPlaceBelow_span]
  letI : (Ideal.under ℤ v.asIdeal).IsMaximal := (rationalPlaceBelow K v).isMaximal
  exact (mem_primesOverFinset_iff (Ideal.under_ne_bot ℤ v.ne_bot) (𝓞 K)).mpr
    ⟨v.isPrime, inferInstance⟩

theorem finitePlaceFiberIndex_injective : Function.Injective (finitePlaceFiberIndex K) := by
  intro v w h
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact congrArg (fun t : PrimeFiberIndex K => t.2.val) h

/-- Unconditional prime-ideal norm summability over every number field. This
removes the arithmetic hypothesis from the genuine Hecke-product construction. -/
theorem finitePlace_norm_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) := by
  classical
  have h : Summable (fun t : PrimeFiberIndex K =>
      (Ideal.absNorm t.2.val : ℝ) ^ (-σ)) := by
    apply (summable_sigma_of_nonneg (fun t => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
    constructor
    · intro p
      exact (hasSum_fintype _).summable
    · have he : (fun p : Nat.Primes => ∑' P :
          {P : Ideal (𝓞 K) // P ∈ primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)},
          (Ideal.absNorm P.val : ℝ) ^ (-σ)) =
          (fun p : Nat.Primes => ∑ P ∈ primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K),
          (Ideal.absNorm P : ℝ) ^ (-σ)) := by
        funext p
        rw [tsum_fintype]
        exact (Finset.sum_subtype
          (primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))
          (fun _ => Iff.rfl)
          (fun P : Ideal (𝓞 K) => (Ideal.absNorm P : ℝ) ^ (-σ))).symm
      rw [he]
      exact primeFiber_norm_summable K σ hσ
  have hc := h.comp_injective (finitePlaceFiberIndex_injective K)
  simpa only [finitePlaceFiberIndex] using hc

end MasulloGRH

namespace MasulloGRH

/-- Finite-subset product expansion bound, adapted from Mathlib master
Analysis/SpecialFunctions/Log/Summable.lean (the server version lacks its export). -/
theorem summable_finset_product_nonneg {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f) :
    Summable (fun s : Finset ι => ∏ i ∈ s, f i) := by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' i, f i))
    (fun s => Finset.prod_nonneg fun i _ => hf i) fun T => ?_
  calc
    ∑ s ∈ T, ∏ i ∈ s, f i ≤
        ∑ s ∈ (T.biUnion id).powerset, ∏ i ∈ s, f i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun s hs => Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hs))
        (fun s _ _ => Finset.prod_nonneg fun i _ => hf i)
    _ = ∏ i ∈ T.biUnion id, (1 + f i) := (Finset.prod_one_add _).symm
    _ ≤ ∏ i ∈ T.biUnion id, Real.exp (f i) := by
      apply Finset.prod_le_prod
      · intro i hi; linarith [hf i]
      · intro i hi; linarith [Real.add_one_le_exp (f i)]
    _ = Real.exp (∑ i ∈ T.biUnion id, f i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' i, f i) :=
      Real.exp_le_exp.mpr (hfs.sum_le_tsum _ fun _ _ => hf _)

/-- Absolute shell majorant: summability over finite exponent vectors follows
from summability of prime weights and one uniform geometric ratio bound. -/
theorem summable_finsupp_geometric {ι : Type*} (r : ι → ℝ)
    (hr : Summable r) (hr0 : ∀ i, 0 ≤ r i)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hrc : ∀ i, r i ≤ c) :
    Summable (fun m : ι →₀ ℕ => ∏ i ∈ m.support, r i ^ m i) := by
  classical
  let f : ι × ℕ → ℝ := fun p => if p.2 = 0 then 0 else r p.1 ^ p.2
  have hc : Summable (fun n : ℕ => c ^ (n - 1)) := by
    apply (summable_nat_add_iff 1).mp
    simpa using summable_geometric_of_lt_one hc0 hc1
  have hb : Summable (fun p : ι × ℕ => r p.1 * c ^ (p.2 - 1)) :=
    hr.mul_of_nonneg hc hr0 (fun n => pow_nonneg hc0 _)
  have hf : Summable f := hb.of_nonneg_of_le (by
    intro p
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (hr0 _) _) (by
    rintro ⟨i, n⟩
    cases n with
    | zero => simp [f, hr0]
    | succ n =>
      simp only [f, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hr0 i) (hrc i) n) (hr0 i))
  have hfin := summable_finset_product_nonneg (f := f) (by
    intro p
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact pow_nonneg (hr0 _) _) hf
  have hg := hfin.comp_injective (Finsupp.graph_injective ι ℕ)
  refine hg.congr fun m => ?_
  change (∏ p ∈ m.graph, f p) = _
  simp only [Finsupp.graph, Finset.prod_map, Function.Embedding.coeFn_mk]
  apply Finset.prod_congr rfl
  intro i hi
  simp [f, Finsupp.mem_support_iff.mp hi]


/-- Summability of the genuine residue-norm valuation-shell majorant on Re(s)>1. -/
theorem finiteShell_normWeight_summable
    (K : Type*) [Field K] [NumberField K] (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun m : IsDedekindDomain.HeightOneSpectrum (𝓞 K) →₀ ℕ =>
      ∏ v ∈ m.support, ((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) ^ m v) := by
  apply summable_finsupp_geometric _ (finitePlace_norm_summable K σ hσ)
    (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _) ((2 : ℝ) ^ (-σ))
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  intro v
  apply Real.rpow_le_rpow_of_nonpos (by norm_num)
  · exact_mod_cast Nat.succ_le_of_lt
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)
  · linarith

end MasulloGRH


namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Absolute convergence for the genuine finite Euler monomials over every
natural valuation vector. Restricting to unramified exponents preserves it. -/
theorem genuineShellEuler_abs_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun m : FinitePlace K →₀ ℕ =>
      ‖∏ v ∈ m.support,
        ((localCharacter K χ v (localUniformizer K v) : ℂ) *
          Complex.exp (-s * (Real.log (Ideal.absNorm v.asIdeal) : ℂ))) ^ m v‖) := by
  refine (finiteShell_normWeight_summable K s.re hs).congr fun m => ?_
  symm
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro v hv
  rw [norm_pow, norm_mul]
  have hu : ‖(localCharacter K χ v (localUniformizer K v) : ℂ)‖ = 1 := by simp
  rw [hu, one_mul, Complex.norm_exp]
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast lt_trans Nat.zero_lt_one
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)
  rw [Real.rpow_def_of_pos hq]
  congr 2
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The actual ramification support is a subfamily of the absolutely summable
natural-shell Euler coefficients. -/
theorem genuineUnramifiedShellEuler_abs_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun m : {m : FinitePlace K →₀ ℕ //
        ∀ v, ¬ IsUnramified K χ v → m v = 0} =>
      ‖∏ v ∈ m.val.support,
        ((localCharacter K χ v (localUniformizer K v) : ℂ) *
          Complex.exp (-s * (Real.log (Ideal.absNorm v.asIdeal) : ℂ))) ^ m.val v‖) :=
  (genuineShellEuler_abs_summable K χ s hs).subtype _

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
    rw [n.property.2 v hv]
    rfl⟩
  invFun m := ⟨m.val.mapRange (fun k : ℕ => (k : ℤ)) (by simp), by
    constructor
    · intro v; exact Int.natCast_nonneg _
    · intro v h; change (m.val v : ℤ) = 0; rw [m.property v h]; rfl⟩
  left_inv n := by
    apply Subtype.ext
    ext v
    change ((n.val v).toNat : ℤ) = n.val v
    exact Int.toNat_of_nonneg (n.property.1 v)
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
  have hcast : ((n.val v).toNat : ℤ) = n.val v := Int.toNat_of_nonneg (n.property.1 v)
  omega


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

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

lemma residueNorm_cpow_eq_exp (v : FinitePlace K) (s : ℂ) :
    (v.asIdeal.absNorm : ℂ) ^ (-s) =
      Complex.exp (-s * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
  have hq := residueNorm_pos K v
  have hqC : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hl : Complex.log (v.asIdeal.absNorm : ℂ) =
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
    simp only [← Complex.ofReal_natCast, Complex.ofReal_log hq.le]
  rw [Complex.cpow_def_of_ne_zero hqC, hl]
  congr 1
  ring

/-- Absolute summability of the actual weighted shell values, indexed by every
integer valuation vector. Non-admissible shells vanish by the checked Tate test. -/
theorem finiteWeightedTateShell_abs_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun n : FinitePlace K →₀ ℤ =>
      ‖finiteTateShellValue K χ n * finiteShellMellinWeight K n s‖) := by
  classical
  have ha : Summable (fun n : {n : FinitePlace K →₀ ℤ // AdmissibleFiniteOrder K χ n} =>
      ‖finiteTateShellValue K χ n.val * finiteShellMellinWeight K n.val s‖) := by
    have h := (genuineUnramifiedShellEuler_abs_summable K χ s hs).comp_injective
      (admissibleOrderEquiv K χ).injective
    refine h.congr fun n => ?_
    change ‖∏ v ∈ (admissibleOrderEquiv K χ n).val.support,
      ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        Complex.exp (-s * (Real.log (Ideal.absNorm v.asIdeal) : ℂ))) ^
        (admissibleOrderEquiv K χ n).val v‖ = _
    rw [finiteWeightedTateShell_eq_product, if_pos n.property,
      admissibleOrderEquiv_support K χ n]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    rw [residueNorm_cpow_eq_exp]
    change _ ^ (n.val v).toNat = _ ^ (n.val v)
    rw [← zpow_natCast, Int.toNat_of_nonneg (n.property.1 v)]
  apply (summable_subtype_and_compl
    (s := {n : FinitePlace K →₀ ℤ | AdmissibleFiniteOrder K χ n})).mp
  refine ⟨ha, ?_⟩
  have hz : (fun n : {n : FinitePlace K →₀ ℤ //
        n ∈ ({n | AdmissibleFiniteOrder K χ n} : Set _)ᶜ} =>
      ‖finiteTateShellValue K χ n.val * finiteShellMellinWeight K n.val s‖) =
      fun _ => (0 : ℝ) := by
    funext n
    have hn : ¬ AdmissibleFiniteOrder K χ n.val := n.property
    simp [finiteWeightedTateShell_eq_product, hn]
  rw [hz]
  exact summable_zero

/-- Arithmetic finite norm compatibility with no valuation hypothesis remaining. -/
theorem arithmeticFiniteIdeleNorm_cpow (a : HeckeIdeles K) (s : ℂ) :
    (arithmeticFiniteIdeleNorm K a : ℂ) ^ s =
      finiteShellMellinWeight K (finiteIdeleOrder K a) s :=
  arithmeticFiniteIdeleNorm_cpow_of_valuations K a (finiteIdeleOrder K a)
    (finiteIdeleOrder_valuation K a) s

/-- Actual weighted Tate integrand is the absolutely summable shell coefficient. -/
theorem actualWeightedTate_eq_shell (χ : UnitaryHeckeCharacter K)
    (a : HeckeIdeles K) (ha : a.val.1 = 1) (s : ℂ) :
    finiteAdelicTest K χ a.val.2 * (χ.character a : ℂ) *
        (arithmeticFiniteIdeleNorm K a : ℂ) ^ s =
      finiteTateShellValue K χ (finiteIdeleOrder K a) *
        finiteShellMellinWeight K (finiteIdeleOrder K a) s := by
  rw [finiteTateTest_eq_shellValue K χ a ha, arithmeticFiniteIdeleNorm_cpow]

#check finiteWeightedTateShell_abs_summable
#print axioms finiteWeightedTateShell_abs_summable
#check arithmeticFiniteIdeleNorm_cpow
#print axioms arithmeticFiniteIdeleNorm_cpow
end MasulloGRH

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

end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

/-- Positivity of the actual arithmetic norm, without an assumed norm package. -/
theorem arithmeticFiniteIdeleNorm_pos (a : HeckeIdeles K) :
    0 < arithmeticFiniteIdeleNorm K a := by
  rw [arithmeticFiniteIdeleNorm_of_valuations K a (finiteIdeleOrder K a)
    (finiteIdeleOrder_valuation K a)]
  exact Finset.prod_pos (fun v _ => zpow_pos (residueNorm_pos K v) _)

/-- Absolute integrability and the shell sum for the actual finite Tate test.
Only normalized shell masses remain as a measure hypothesis; neither integrability,
coefficient summability, nor arithmetic norm compatibility is assumed. -/
theorem actualFiniteMellin_integrable_of_shell_mass_one
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re)
    (μ : Measure (FiniteIdelicDomain K))
    (hm : ∀ n : FinitePlace K →₀ ℤ, μ (finiteIdelicShell K n) = 1) :
    Integrable (fun a : FiniteIdelicDomain K =>
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s) μ ∧
    (∫ a : FiniteIdelicDomain K,
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s ∂μ) =
      ∑' n : FinitePlace K →₀ ℤ,
        finiteTateShellValue K χ n * finiteShellMellinWeight K n s := by
  apply finiteIdelic_integral_of_normalized_shell_coefficients K μ hm
    (c := fun n => finiteTateShellValue K χ n * finiteShellMellinWeight K n s)
  · intro a
    exact actualWeightedTate_eq_shell K χ a.val a.property s
  · exact finiteWeightedTateShell_abs_summable K χ s hs

#check arithmeticFiniteIdeleNorm_pos
#print axioms arithmeticFiniteIdeleNorm_pos
end MasulloGRH

/- A/r48 constructed Haar source, integrated by F/r49. -/
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

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual full-idele subgroup used in the existing valuation-shell proofs. -/
def finiteIdeleSubgroup : Subgroup ((NumberField.AdeleRing (𝓞 K) K)ˣ) where
  carrier := {a | a.val.1 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a.val.1 * b.val.1 = 1
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    have h := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.1) a.val_inv
    change a.val.1 * a.inv.1 = 1 at h
    rwa [ha, one_mul] at h

noncomputable def finiteIdeleToFull (a : FiniteIdeles K) :
    (NumberField.AdeleRing (𝓞 K) K)ˣ where
  val := (1, a.val)
  inv := (1, a.inv)
  val_inv := Prod.ext (one_mul 1) a.val_inv
  inv_val := Prod.ext (one_mul 1) a.inv_val

noncomputable def finiteIdeleFromFull (a : finiteIdeleSubgroup K) : FiniteIdeles K where
  val := a.val.val.2
  inv := a.val.inv.2
  val_inv := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2) a.val.val_inv
  inv_val := congrArg (fun z : NumberField.AdeleRing (𝓞 K) K => z.2) a.val.inv_val

noncomputable def finiteIdelesMulEquivSubgroup : FiniteIdeles K ≃* finiteIdeleSubgroup K where
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

noncomputable def finiteIdelesHomeomorphSubgroup : FiniteIdeles K ≃ₜ finiteIdeleSubgroup K where
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
def finiteSubgroupIntegralUnits : Set (finiteIdeleSubgroup K) :=
  (finiteIdelesHomeomorphSubgroup K) '' (finiteIntegralUnits K : Set (FiniteIdeles K))

theorem finiteSubgroupIntegralUnits_isCompact : IsCompact (finiteSubgroupIntegralUnits K) :=
  (finiteIntegralUnits_isCompact K).image (finiteIdelesHomeomorphSubgroup K).continuous

theorem finiteSubgroupIntegralUnits_isOpen : IsOpen (finiteSubgroupIntegralUnits K) :=
  (finiteIdelesHomeomorphSubgroup K).isOpenMap _ (finiteIntegralUnits_isOpen K)

theorem finiteSubgroupIntegralUnits_iff (a : finiteIdeleSubgroup K) :
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

end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

noncomputable def finiteSubgroupUnitsPositiveCompact :
    TopologicalSpace.PositiveCompacts (finiteIdeleSubgroup K) :=
  ⟨⟨finiteSubgroupIntegralUnits K, finiteSubgroupIntegralUnits_isCompact K⟩, by
    rw [(finiteSubgroupIntegralUnits_isOpen K).interior_eq]
    exact ⟨finiteIdelesHomeomorphSubgroup K 1, 1, (finiteIntegralUnits K).one_mem, rfl⟩⟩

local instance : MeasurableSpace (finiteIdeleSubgroup K) := borel _
local instance : BorelSpace (finiteIdeleSubgroup K) := ⟨rfl⟩

noncomputable def normalizedFiniteSubgroupHaar :
    MeasureTheory.Measure (finiteIdeleSubgroup K) :=
  MeasureTheory.Measure.haarMeasure (finiteSubgroupUnitsPositiveCompact K)

theorem exists_normalizedFiniteSubgroupHaar :
    ∃ μ : MeasureTheory.Measure (finiteIdeleSubgroup K),
      MeasureTheory.Measure.IsHaarMeasure μ ∧ μ (finiteSubgroupIntegralUnits K) = 1 := by
  refine ⟨normalizedFiniteSubgroupHaar K, ?_, MeasureTheory.Measure.haarMeasure_self⟩
  unfold normalizedFiniteSubgroupHaar
  infer_instance

/-- The normalization domain is exactly the valuation-zero shell. -/
theorem finiteSubgroupIntegralUnits_valuation_one (a : finiteIdeleSubgroup K) :
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
end MasulloGRH
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (finiteIdeleSubgroup K) := borel _
local instance : BorelSpace (finiteIdeleSubgroup K) := ⟨rfl⟩

/-- Every integer valuation shell has mass one for the constructed global Haar measure. -/
theorem normalizedFiniteSubgroupHaar_shell (n : FinitePlace K →₀ ℤ) :
    normalizedFiniteSubgroupHaar K (finiteIdelicShell K n) = 1 := by
  let a : finiteIdeleSubgroup K := ⟨finiteOrderRepresentative K n, rfl⟩
  have ha : finiteIdeleOrder K a.val = n := finiteOrderRepresentative_order K n
  have he : (fun b : finiteIdeleSubgroup K => a⁻¹ * b) ⁻¹'
      finiteSubgroupIntegralUnits K = finiteIdelicShell K n := by
    ext b
    change a⁻¹ * b ∈ finiteSubgroupIntegralUnits K ↔ finiteIdeleOrder K b.val = n
    rw [finiteSubgroupIntegralUnits_valuation_one]
    constructor
    · intro hb
      ext v
      have h := hb v
      change Valued.v (a.val.inv.2 v * b.val.val.2 v) = 1 at h
      have hm : Valued.v (a.val.val.2 v) * Valued.v (a.val.inv.2 v) = 1 := by
        rw [← map_mul]
        have h' := congrArg (fun z : HeckeAdeles K => z.2 v) a.val.val_inv
        change a.val.val.2 v * a.val.inv.2 v = 1 at h'
        rw [h', map_one]
      have hh := congrArg (fun z => Valued.v (a.val.val.2 v) * z) h
      change Valued.v (a.val.val.2 v) * Valued.v (a.val.inv.2 v * b.val.val.2 v) =
        Valued.v (a.val.val.2 v) * 1 at hh
      rw [map_mul, ← mul_assoc, hm, one_mul, mul_one] at hh
      change -(Valued.v (b.val.val.2 v)).log = n v
      rw [hh]
      exact congrArg (fun m : FinitePlace K →₀ ℤ => m v) ha
    · intro hb v
      have hv : Valued.v (b.val.val.2 v) = Valued.v (a.val.val.2 v) := by
        rw [finiteIdeleOrder_valuation, finiteIdeleOrder_valuation, hb, ha]
      change Valued.v (a.val.inv.2 v * b.val.val.2 v) = 1
      rw [map_mul, hv, ← map_mul]
      have h' := congrArg (fun z : HeckeAdeles K => z.2 v) a.val.inv_val
      change a.val.inv.2 v * a.val.val.2 v = 1 at h'
      rw [h', map_one]
  letI : (normalizedFiniteSubgroupHaar K).IsHaarMeasure := by
    unfold normalizedFiniteSubgroupHaar
    infer_instance
  rw [← he, measure_preimage_mul]
  exact Measure.haarMeasure_self

/-- The actual normalized Haar measure supplies all measure hypotheses in the
checked shell assembly. Only the genuine integrand's coefficient identity and
absolute coefficient summability remain to instantiate the Mellin theorem. -/
theorem normalizedFiniteIdelic_integral_of_shell_coefficients
    (f : FiniteIdelicDomain K → ℂ) (c : (FinitePlace K →₀ ℤ) → ℂ)
    (hc : ∀ a, f a = c (finiteIdeleOrder K a.val))
    (hs : Summable (fun n => ‖c n‖)) :
    Integrable f (normalizedFiniteSubgroupHaar K) ∧
      (∫ a, f a ∂normalizedFiniteSubgroupHaar K) = ∑' n, c n :=
  finiteIdelic_integral_of_normalized_shell_coefficients K
    (normalizedFiniteSubgroupHaar K) (normalizedFiniteSubgroupHaar_shell K) f c hc hs

#check normalizedFiniteSubgroupHaar_shell
#print axioms normalizedFiniteSubgroupHaar_shell
end MasulloGRH
namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

/-- Actual normalized finite-idelic Mellin integrability and shell evaluation.
Identification of this shell sum with the existing Euler product remains separate. -/
theorem normalizedActualFiniteMellin_integrable_and_shell_sum
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun a : FiniteIdelicDomain K =>
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s)
      (normalizedFiniteSubgroupHaar K) ∧
    (∫ a : FiniteIdelicDomain K,
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s ∂normalizedFiniteSubgroupHaar K) =
      ∑' n : FinitePlace K →₀ ℤ,
        finiteTateShellValue K χ n * finiteShellMellinWeight K n s :=
  actualFiniteMellin_integrable_of_shell_mass_one K χ s hs
    (normalizedFiniteSubgroupHaar K) (normalizedFiniteSubgroupHaar_shell K)

#check normalizedActualFiniteMellin_integrable_and_shell_sum
#print axioms normalizedActualFiniteMellin_integrable_and_shell_sum
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

/-- The countable disjoint Borel partition justifies the actual integral/sum
interchange once arithmetic absolute convergence has established integrability. -/
theorem normalizedActualFiniteMellin_integral_eq_tsum_shell_integrals
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    (∫ a : FiniteIdelicDomain K,
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s ∂normalizedFiniteSubgroupHaar K) =
    ∑' n : FinitePlace K →₀ ℤ,
      ∫ a : FiniteIdelicDomain K in finiteIdelicShell K n,
        finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
          (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s ∂normalizedFiniteSubgroupHaar K := by
  letI := finiteIdelicShell_index_countable K
  have hi := (normalizedActualFiniteMellin_integrable_and_shell_sum K χ s hs).1
  have he := integral_iUnion (finiteIdelicShell_measurable K)
    (finiteIdelicShell_disjoint K) (hi.integrableOn (s := ⋃ n, finiteIdelicShell K n))
  simpa only [finiteIdelicShell_cover K, Measure.restrict_univ] using he

#check normalizedActualFiniteMellin_integral_eq_tsum_shell_integrals
#print axioms normalizedActualFiniteMellin_integral_eq_tsum_shell_integrals
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩

/-- Exact reindexing into the natural-shell coefficients used by G/r49's
checked Euler-product limiting theorem. Ramified exponents vanish. -/
theorem actualWeightedShell_tsum_eq_natural
    (χ : UnitaryHeckeCharacter K) (s : ℂ) :
    (∑' n : FinitePlace K →₀ ℤ,
      finiteTateShellValue K χ n * finiteShellMellinWeight K n s) =
    ∑' m : UnramifiedExponents K χ,
      ∏ v ∈ m.val.support,
        ((localCharacter K χ v (localUniformizer K v) : ℂ) *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v := by
  classical
  let c := fun n => finiteTateShellValue K χ n * finiteShellMellinWeight K n s
  let f := fun m : UnramifiedExponents K χ =>
    ∏ v ∈ m.val.support,
      ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v
  have hi : ({n | AdmissibleFiniteOrder K χ n} : Set (FinitePlace K →₀ ℤ)).indicator
      c = c := by
    funext n
    by_cases hn : AdmissibleFiniteOrder K χ n
    · simp [hn]
    · simp [hn, c, finiteWeightedTateShell_eq_product]
  have he (n : {n : FinitePlace K →₀ ℤ // AdmissibleFiniteOrder K χ n}) :
      c n.val = f (admissibleOrderEquiv K χ n) := by
    change finiteTateShellValue K χ n.val * finiteShellMellinWeight K n.val s = _
    rw [finiteWeightedTateShell_eq_product, if_pos n.property]
    dsimp only [f]
    rw [admissibleOrderEquiv_support K χ n]
    apply Finset.prod_congr rfl
    intro v hv
    change _ ^ n.val v = _ ^ (n.val v).toNat
    rw [← zpow_natCast, Int.toNat_of_nonneg (n.property.1 v)]
  calc
    _ = ∑' n : {n : FinitePlace K →₀ ℤ // AdmissibleFiniteOrder K χ n}, c n.val := by
      have ht := tsum_subtype
        ({n | AdmissibleFiniteOrder K χ n} : Set (FinitePlace K →₀ ℤ)) c
      rw [hi] at ht
      exact ht.symm
    _ = ∑' n : {n : FinitePlace K →₀ ℤ // AdmissibleFiniteOrder K χ n},
        f (admissibleOrderEquiv K χ n) := tsum_congr he
    _ = _ := (admissibleOrderEquiv K χ).tsum_eq f

/-- The actual normalized Mellin integral equals the exact arithmetic natural
shell series. No assumed measure, shell masses or integrability package occurs. -/
theorem normalizedActualFiniteMellin_integral_eq_natural_shell_sum
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    (∫ a : FiniteIdelicDomain K,
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s ∂normalizedFiniteSubgroupHaar K) =
    ∑' m : UnramifiedExponents K χ,
      ∏ v ∈ m.val.support,
        ((localCharacter K χ v (localUniformizer K v) : ℂ) *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v :=
  (normalizedActualFiniteMellin_integrable_and_shell_sum K χ s hs).2.trans
    (actualWeightedShell_tsum_eq_natural K χ s)

#check actualWeightedShell_tsum_eq_natural
#print axioms actualWeightedShell_tsum_eq_natural
#check normalizedActualFiniteMellin_integral_eq_natural_shell_sum
#print axioms normalizedActualFiniteMellin_integral_eq_natural_shell_sum
end MasulloGRH

/- G/r52 exact checked arithmetic extension, receipt 1ae55014245c4efa988ddd7ccf99b0d5. -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Match the exponential convention in E/r47 to the existing complex-power Euler weights. -/
theorem residue_cpow_eq_exp (v : FinitePlace K) (s : ℂ) :
    (v.asIdeal.absNorm : ℂ) ^ (-s) =
      Complex.exp (-s * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) := by
  have hq := residueNorm_pos K v
  have hn : (v.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  rw [Complex.cpow_def_of_ne_zero hn]
  have hl : Complex.log (v.asIdeal.absNorm : ℂ) =
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) := by
    simp
  rw [hl, mul_comm]

/-- The genuine admissible Euler shell coefficients are absolutely summable in
exactly the complex-power convention of the arithmetic norm formula. -/
theorem genuineUnramifiedShellCpow_abs_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun m : {m : FinitePlace K →₀ ℕ //
        ∀ v, ¬ IsUnramified K χ v → m v = 0} =>
      ‖∏ v ∈ m.val.support,
        ((localCharacter K χ v (localUniformizer K v) : ℂ) *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v‖) := by
  simpa only [residue_cpow_eq_exp K] using
    genuineUnramifiedShellEuler_abs_summable K χ s hs

#check residue_cpow_eq_exp
#print axioms residue_cpow_eq_exp
#check genuineUnramifiedShellCpow_abs_summable
#print axioms genuineUnramifiedShellCpow_abs_summable
end MasulloGRH

namespace MasulloGRH
open scoped Topology
open Classical
variable (K : Type*) [Field K] [NumberField K]

/-- Exhausting the finite places commutes with the actual admissible shell sum.
This discharges the infinite limiting step without assuming global integrability. -/
theorem genuineUnramifiedShellCpow_tendsto (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Filter.Tendsto
      (fun S : Finset (FinitePlace K) =>
        ∑' m : {m : FinitePlace K →₀ ℕ //
          ∀ v, ¬ IsUnramified K χ v → m v = 0},
        if m.val.support ⊆ S then
          (∏ v ∈ m.val.support,
            ((localCharacter K χ v (localUniformizer K v) : ℂ) *
              (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v) else 0)
      Filter.atTop
      (𝓝 (∑' m : {m : FinitePlace K →₀ ℕ //
          ∀ v, ¬ IsUnramified K χ v → m v = 0},
          ∏ v ∈ m.val.support,
            ((localCharacter K χ v (localUniformizer K v) : ℂ) *
              (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence
    (genuineUnramifiedShellCpow_abs_summable K χ s hs)
  · intro m
    apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop m.val.support] with S hS
    rw [if_pos (show m.val.support ⊆ S from hS)]
  · apply Filter.Eventually.of_forall
    intro S m
    split_ifs
    · exact le_rfl
    · simpa using norm_nonneg
        (∏ v ∈ m.val.support,
          ((localCharacter K χ v (localUniformizer K v) : ℂ) *
            (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v)

#check genuineUnramifiedShellCpow_tendsto
#print axioms genuineUnramifiedShellCpow_tendsto
end MasulloGRH

namespace MasulloGRH
open scoped Topology
open Classical
variable (K : Type*) [Field K] [NumberField K]
/- The following Euler-factor and Euler-germ definitions are copied verbatim
from D/r21, receipt e09d66a145ae4ebfa8ce1f503cbfb33c. -/
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


abbrev AdmissibleNaturalShell (χ : UnitaryHeckeCharacter K) :=
  {m : FinitePlace K →₀ ℕ // ∀ v, ¬ IsUnramified K χ v → m v = 0}

noncomputable def genuineShellCpowCoefficient (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (m : AdmissibleNaturalShell K χ) : ℂ :=
  ∏ v ∈ m.val.support,
    ((localCharacter K χ v (localUniformizer K v) : ℂ) *
      (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v

/-- The infinite passage to the existing arithmetic Euler germ is justified.
The only additional premise is the explicitly displayed finite-stage identity,
which remains to be proved by finite geometric-series factorization. -/
theorem genuineShellSum_eq_finiteHeckeL_of_finite_stage
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re)
    (hstage : ∀ S : Finset (FinitePlace K),
      (∑' m : AdmissibleNaturalShell K χ,
        if m.val.support ⊆ S then genuineShellCpowCoefficient K χ s m else 0) =
        partialHeckeEulerProduct K χ S s) :
    (∑' m : AdmissibleNaturalShell K χ, genuineShellCpowCoefficient K χ s m) =
      finiteHeckeL K χ s := by
  have ht := genuineUnramifiedShellCpow_tendsto K χ s hs
  have hp : HasProd (fun v : FinitePlace K => heckeEulerFactor K χ v s)
      (∑' m : AdmissibleNaturalShell K χ, genuineShellCpowCoefficient K χ s m) := by
    change Filter.Tendsto
      (fun S : Finset (FinitePlace K) => ∏ v ∈ S, heckeEulerFactor K χ v s)
      Filter.atTop (𝓝 _)
    convert ht using 1
    funext S
    exact (hstage S).symm
  exact hp.tprod_eq.symm

#check genuineShellSum_eq_finiteHeckeL_of_finite_stage
#print axioms genuineShellSum_eq_finiteHeckeL_of_finite_stage
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Every genuine unramified ratio lies strictly inside the geometric disk. -/
theorem genuinePrimeRatio_norm_lt_one (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 1 < s.re) :
    ‖(localCharacter K χ v (localUniformizer K v) : ℂ) *
      (v.asIdeal.absNorm : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Circle.norm_coe, one_mul, residue_cpow_eq_exp K,
    Complex.norm_exp]
  apply Real.exp_lt_one_iff.mpr
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.log_pos hq)

/-- Geometric expansion with exactly the existing genuine Hecke local factor. -/
theorem genuineLocalEuler_hasSum (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 1 < s.re)
    (hv : IsUnramified K χ v) :
    HasSum (fun n : ℕ =>
      ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ n)
      (heckeEulerFactor K χ v s) := by
  simpa [heckeEulerFactor, hv, heckePrimeCoefficient] using
    hasSum_geometric_of_norm_lt_one (genuinePrimeRatio_norm_lt_one K χ v s hs)

#check genuinePrimeRatio_norm_lt_one
#print axioms genuinePrimeRatio_norm_lt_one
#check genuineLocalEuler_hasSum
#print axioms genuineLocalEuler_hasSum
end MasulloGRH

namespace MasulloGRH
open Classical

/-- Restriction to a finite set of allowed places, with inverse extension by zero.
Used for the finite Euler-product expansion of admissible valuation shells. -/
noncomputable def supportedAllowedEquiv {ι : Type*} (S : Finset ι) (P : ι → Prop) :
    {m : ι →₀ ℕ // m.support ⊆ S ∧ ∀ i, ¬ P i → m i = 0} ≃
      ({i : ι // i ∈ S ∧ P i} → ℕ) where
  toFun m i := m.val i.val
  invFun f :=
    ⟨Finsupp.onFinset S (fun i => if h : i ∈ S ∧ P i then f ⟨i, h⟩ else 0)
      (by intro i hi; by_contra hn; simp [hn] at hi), by
      constructor
      · intro i hi
        by_contra hn
        have hz : (Finsupp.onFinset S
            (fun i => if h : i ∈ S ∧ P i then f ⟨i, h⟩ else 0)
            (by intro i hi; by_contra hn; simp [hn] at hi)) i = 0 := by
          simp [hn]
        exact (Finsupp.mem_support_iff.mp hi) hz
      · intro i hi
        simp [hi]⟩
  left_inv m := by
    apply Subtype.ext
    ext i
    change (if h : i ∈ S ∧ P i then m.val i else 0) = m.val i
    split_ifs with h
    · rfl
    · symm
      by_cases hi : i ∈ S
      · exact m.property.2 i (fun hp => h ⟨hi, hp⟩)
      · by_contra hz
        exact hi (m.property.1 (Finsupp.mem_support_iff.mpr hz))
  right_inv f := by
    funext i
    change (if h : i.val ∈ S ∧ P i.val then f ⟨i.val, h⟩ else 0) = f i
    simp [i.property]

/-- The coefficient product may be enlarged to any finite supporting set.
This applies to the actual Hecke ratios after restricting by supportedAllowedEquiv. -/
theorem supportedCoefficient_eq_prod {ι : Type*} (S : Finset ι)
    (q : ι → ℂ) (m : ι →₀ ℕ) (hm : m.support ⊆ S) :
    (∏ i ∈ m.support, q i ^ m i) = ∏ i ∈ S, q i ^ m i := by
  classical
  exact Finset.prod_subset hm (fun i _ hi => by
    have hz : m i = 0 := by
      by_contra hz
      exact hi (Finsupp.mem_support_iff.mpr hz)
    rw [hz, pow_zero])

#check supportedAllowedEquiv
#print axioms supportedAllowedEquiv
#check supportedCoefficient_eq_prod
#print axioms supportedCoefficient_eq_prod
end MasulloGRH

namespace MasulloGRH
open Classical
variable (K : Type*) [Field K] [NumberField K]

/-- Actual admissible shells supported on S are precisely finite tuples of
nonnegative exponents at its unramified places. -/
noncomputable def finiteAdmissibleShellEquiv (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) :
    {m : AdmissibleNaturalShell K χ // m.val.support ⊆ S} ≃
      ({v : FinitePlace K // v ∈ S ∧ IsUnramified K χ v} → ℕ) :=
  (show {m : AdmissibleNaturalShell K χ // m.val.support ⊆ S} ≃
    {m : FinitePlace K →₀ ℕ // m.support ⊆ S ∧
      ∀ v, ¬ IsUnramified K χ v → m v = 0} from
    { toFun := fun m => ⟨m.val.val, m.property, m.val.property⟩
      invFun := fun m => ⟨⟨m.val, m.property.2⟩, m.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans
    (supportedAllowedEquiv S (IsUnramified K χ))

/-- Reindex the exact finite-stage shell sum without assuming an integral or
an Euler identity. The remaining finite Fubini step acts on the tuple sum. -/
theorem genuineFiniteStage_reindex (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (s : ℂ) :
    (∑' m : AdmissibleNaturalShell K χ,
      if m.val.support ⊆ S then genuineShellCpowCoefficient K χ s m else 0) =
    ∑' f : ({v : FinitePlace K // v ∈ S ∧ IsUnramified K χ v} → ℕ),
      genuineShellCpowCoefficient K χ s
        ((finiteAdmissibleShellEquiv K χ S).symm f).val := by
  calc
    _ = ∑' m : {m : AdmissibleNaturalShell K χ // m.val.support ⊆ S},
        genuineShellCpowCoefficient K χ s m.val := by
      simpa only [Set.indicator_apply, Set.mem_setOf_eq] using
        (tsum_subtype {m : AdmissibleNaturalShell K χ | m.val.support ⊆ S}
          (genuineShellCpowCoefficient K χ s)).symm
    _ = _ := ((finiteAdmissibleShellEquiv K χ S).symm.tsum_eq
      (fun m : {m : AdmissibleNaturalShell K χ // m.val.support ⊆ S} =>
        genuineShellCpowCoefficient K χ s m.val)).symm

/-- The actual coefficient is the product of genuine ratios over the stage. -/
theorem genuineSupportedCoefficient_eq_prod (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (s : ℂ) (m : AdmissibleNaturalShell K χ)
    (hm : m.val.support ⊆ S) :
    genuineShellCpowCoefficient K χ s m =
      ∏ v ∈ S, ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ m.val v :=
  supportedCoefficient_eq_prod S _ m.val hm

#check finiteAdmissibleShellEquiv
#print axioms finiteAdmissibleShellEquiv
#check genuineFiniteStage_reindex
#print axioms genuineFiniteStage_reindex
#check genuineSupportedCoefficient_eq_prod
#print axioms genuineSupportedCoefficient_eq_prod
end MasulloGRH

/- Round 52: repair of G/r50 finite Fubini, followed by unconditional Euler identification. -/

set_option maxHeartbeats 800000
set_option linter.unnecessarySimpa false

namespace MasulloGRH
/- Candidate finite Fubini induction for the exact remaining finite Euler stage.
   This file is experimental until its own successful receipt is recorded. -/
theorem finiteTuple_geometric {ι : Type*} [Fintype ι] :
    ∀ q : ι → ℂ, (∀ i, ‖q i‖ < 1) →
    Summable (fun n : ι → ℕ => ‖∏ i, q i ^ n i‖) ∧
    HasSum (fun n : ι → ℕ => ∏ i, q i ^ n i) (∏ i, (1 - q i)⁻¹) := by
  classical
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ q : ι → ℂ, (∀ i, ‖q i‖ < 1) →
      Summable (fun n : ι → ℕ => ‖∏ i, q i ^ n i‖) ∧
      HasSum (fun n : ι → ℕ => ∏ i, q i ^ n i) (∏ i, (1 - q i)⁻¹))
    ?_ ?_ ?_ ι
  · intro α β _ e ih q hq
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let E : (β → ℕ) ≃ (α → ℕ) := (e.arrowCongr (Equiv.refl ℕ)).symm
    have h := ih (fun i => q (e i)) (fun i => hq (e i))
    have he (n : β → ℕ) :
        (∏ i : α, q (e i) ^ E n i) = ∏ i : β, q i ^ n i := by
      exact Fintype.prod_equiv e _ _ (fun i => rfl)
    have hp : (∏ i : α, (1 - q (e i))⁻¹) = ∏ i : β, (1 - q i)⁻¹ :=
      Fintype.prod_equiv e _ _ (fun i => rfl)
    constructor
    · simpa only [Function.comp_def, he] using (E.summable_iff.mpr h.1)
    · simpa only [Function.comp_def, he, hp] using (E.hasSum_iff.mpr h.2)
  · intro q hq
    constructor
    · exact (hasSum_fintype _).summable
    · simpa using (hasSum_fintype (fun n : PEmpty → ℕ => ∏ i, q i ^ n i))
  · intro α _ ih q hq
    let E : (Option α → ℕ) ≃ ℕ × (α → ℕ) := Equiv.piOptionEquivProd
    have h := ih (fun i => q (some i)) (fun i => hq (some i))
    have h0 : Summable (fun n : ℕ => ‖q none ^ n‖) := by
      simpa only [norm_pow] using summable_geometric_of_lt_one
        (norm_nonneg (q none)) (hq none)
    constructor
    · have hh : Summable (fun p : ℕ × (α → ℕ) =>
          ‖q none ^ p.1 * ∏ i, q (some i) ^ p.2 i‖) := Summable.mul_norm
            (f := fun n : ℕ => q none ^ n)
            (g := fun n : α → ℕ => ∏ i, q (some i) ^ n i) h0 h.1
      have ht := E.summable_iff.mpr hh
      change Summable (fun n : Option α → ℕ =>
        ‖q none ^ n none * ∏ i, q (some i) ^ n (some i)‖) at ht
      simpa only [Fintype.prod_option] using ht
    · have hh := (hasSum_geometric_of_norm_lt_one (hq none)).mul h.2
        (summable_mul_of_summable_norm
          (f := fun n : ℕ => q none ^ n)
          (g := fun n : α → ℕ => ∏ i, q (some i) ^ n i) h0 h.1)
      have ht := E.hasSum_iff.mpr hh
      change HasSum (fun n : Option α → ℕ =>
        q none ^ n none * ∏ i, q (some i) ^ n (some i))
        ((1 - q none)⁻¹ * ∏ i, (1 - q (some i))⁻¹) at ht
      simpa only [Fintype.prod_option] using ht

#check finiteTuple_geometric
#print axioms finiteTuple_geometric
end MasulloGRH

namespace MasulloGRH
open Classical
variable (K : Type*) [Field K] [NumberField K]

/-- Finite supported genuine shell series equals the existing finite Euler product. -/
theorem genuineFiniteStage_eq_partialHeckeEulerProduct
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re)
    (S : Finset (FinitePlace K)) :
    (∑' m : AdmissibleNaturalShell K χ,
      if m.val.support ⊆ S then genuineShellCpowCoefficient K χ s m else 0) =
      partialHeckeEulerProduct K χ S s := by
  classical
  let I := {v : FinitePlace K // v ∈ S ∧ IsUnramified K χ v}
  letI : Fintype I := Fintype.ofFinset (S.filter (IsUnramified K χ))
    (by intro v; exact Finset.mem_filter)
  let q : FinitePlace K → ℂ := fun v =>
    (localCharacter K χ v (localUniformizer K v) : ℂ) *
      (v.asIdeal.absNorm : ℂ) ^ (-s)
  let e := finiteAdmissibleShellEquiv K χ S
  have hcoef (f : I → ℕ) :
      genuineShellCpowCoefficient K χ s (e.symm f).val =
        ∏ v : I, q v.val ^ f v := by
    let m := (e.symm f).val
    have hm : m.val.support ⊆ S.filter (IsUnramified K χ) := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨(e.symm f).property hv, ?_⟩
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hv) (m.property v hn)
    rw [genuineSupportedCoefficient_eq_prod K χ _ s m hm]
    have he (v : I) : m.val v.val = f v := by
      have hh := congrFun (e.apply_symm_apply f) v
      exact hh
    change (∏ v ∈ S.filter (IsUnramified K χ), q v ^ m.val v) = _
    rw [Finset.prod_subtype (S.filter (IsUnramified K χ))
      (p := fun v => v ∈ S ∧ IsUnramified K χ v)
      (by intro v; exact Finset.mem_filter) (fun v => q v ^ m.val v)]
    exact Finset.prod_congr rfl (fun v _ => congrArg (fun n => q v.val ^ n) (he v))
  have hgeom := (finiteTuple_geometric (fun v : I => q v.val)
    (fun v => genuinePrimeRatio_norm_lt_one K χ v.val s hs)).2.tsum_eq
  rw [genuineFiniteStage_reindex]
  calc
    _ = ∑' f : I → ℕ, ∏ v : I, q v.val ^ f v := tsum_congr hcoef
    _ = ∏ v : I, (1 - q v.val)⁻¹ := hgeom
    _ = partialHeckeEulerProduct K χ S s := by
      change _ = ∏ v ∈ S, heckeEulerFactor K χ v s
      calc
        _ = ∏ v ∈ S.filter (IsUnramified K χ), (1 - q v)⁻¹ :=
          (Finset.prod_subtype _ (p := fun v => v ∈ S ∧ IsUnramified K χ v)
            (by intro v; exact Finset.mem_filter) _).symm
        _ = _ := by
          rw [Finset.prod_filter]
          apply Finset.prod_congr rfl
          intro v hv
          rfl

/-- Unconditional arithmetic shell-series equality with the pre-existing Euler germ. -/
theorem genuineShellSum_eq_finiteHeckeL
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    (∑' m : AdmissibleNaturalShell K χ, genuineShellCpowCoefficient K χ s m) =
      finiteHeckeL K χ s :=
  genuineShellSum_eq_finiteHeckeL_of_finite_stage K χ s hs
    (genuineFiniteStage_eq_partialHeckeEulerProduct K χ s hs)

#check genuineFiniteStage_eq_partialHeckeEulerProduct
#print axioms genuineFiniteStage_eq_partialHeckeEulerProduct
#check genuineShellSum_eq_finiteHeckeL
#print axioms genuineShellSum_eq_finiteHeckeL
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (FiniteIdelicDomain K) := borel _
local instance : BorelSpace (FiniteIdelicDomain K) := ⟨rfl⟩
local instance : MeasurableSpace (finiteIdeleSubgroup K) := borel _
local instance : BorelSpace (finiteIdeleSubgroup K) := ⟨rfl⟩

/-- The actual normalized finite-idelic Mellin integral equals the existing
arithmetic Euler product. Only the half-plane hypothesis is required. -/
theorem normalizedActualFiniteMellin_eq_finiteHeckeL
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    (∫ a : FiniteIdelicDomain K,
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s ∂normalizedFiniteSubgroupHaar K) =
      finiteHeckeL K χ s :=
  (normalizedActualFiniteMellin_integral_eq_natural_shell_sum K χ s hs).trans
    (genuineShellSum_eq_finiteHeckeL K χ s hs)

/-- Full normalized Mellin statement on the actual idele subgroup with infinite
component one. The measure is constructed, and all analytic premises are discharged. -/
theorem normalizedGlobalFiniteIdelicMellin
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    let μ := normalizedFiniteSubgroupHaar K
    let f : FiniteIdelicDomain K → ℂ := fun a =>
      finiteAdelicTest K χ a.val.val.2 * (χ.character a.val : ℂ) *
        (arithmeticFiniteIdeleNorm K a.val : ℂ) ^ s
    μ.IsHaarMeasure ∧
      μ (finiteSubgroupIntegralUnits K) = 1 ∧
      Integrable f μ ∧
      (∀ n : FinitePlace K →₀ ℤ, μ (finiteIdelicShell K n) = 1) ∧
      (∫ a, f a ∂μ) =
        (∑' n : FinitePlace K →₀ ℤ, ∫ a in finiteIdelicShell K n, f a ∂μ) ∧
      (∫ a, f a ∂μ) =
        (∑' m : AdmissibleNaturalShell K χ, genuineShellCpowCoefficient K χ s m) ∧
      (∑' m : AdmissibleNaturalShell K χ, genuineShellCpowCoefficient K χ s m) =
        finiteHeckeL K χ s ∧
      (∫ a, f a ∂μ) = finiteHeckeL K χ s := by
  dsimp only
  refine ⟨?_, ?_, (normalizedActualFiniteMellin_integrable_and_shell_sum K χ s hs).1,
    normalizedFiniteSubgroupHaar_shell K,
    normalizedActualFiniteMellin_integral_eq_tsum_shell_integrals K χ s hs,
    normalizedActualFiniteMellin_integral_eq_natural_shell_sum K χ s hs,
    genuineShellSum_eq_finiteHeckeL K χ s hs,
    normalizedActualFiniteMellin_eq_finiteHeckeL K χ s hs⟩
  · unfold normalizedFiniteSubgroupHaar
    infer_instance
  · exact Measure.haarMeasure_self

#check normalizedActualFiniteMellin_eq_finiteHeckeL
#print axioms normalizedActualFiniteMellin_eq_finiteHeckeL
#check normalizedGlobalFiniteIdelicMellin
#print axioms normalizedGlobalFiniteIdelicMellin
end MasulloGRH
