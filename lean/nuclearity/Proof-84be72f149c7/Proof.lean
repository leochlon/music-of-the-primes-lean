import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! A, round 24; checked round-22 source retained; round-23 failed explicit formula repaired. Reuses the exact checked D round-21 Euler-product baseline.
Repairs its finite-product holomorphy extension to establish the genuine initial
analytic germ and its zero divisor on Re(s)>1. Global continuation remains open. -/
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
/-- Quantitative convergence estimate for the actual arithmetic Euler factor. -/
theorem heckeEulerFactor_sub_one_norm_le (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    ‖heckeEulerFactor K χ v s - 1‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) /
        (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) := by
  classical
  let a := heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)
  let r := (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hr : 0 < r := Real.rpow_pos_of_pos (lt_trans zero_lt_one hq) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  have ha : ‖a‖ = r := heckeEulerTerm_norm K χ v s
  have hd : 1 - a ≠ 0 := heckeEulerDenominator_ne_zero K χ v s hs
  by_cases hχ : IsUnramified K χ v
  · have he : (1 - a)⁻¹ - 1 = a / (1 - a) := by
      field_simp
      ring
    change ‖(if IsUnramified K χ v then (1 - a)⁻¹ else 1) - 1‖ ≤ r / (1-r)
    rw [if_pos hχ, he, norm_div, ha]
    apply div_le_div_of_nonneg_left (le_of_lt hr) (sub_pos.mpr hr1)
    have hh := norm_sub_norm_le (1 : ℂ) a
    simpa only [norm_one, ha] using hh
  · simp only [heckeEulerFactor, if_neg hχ, sub_self, norm_zero]
    exact div_nonneg (le_of_lt hr) (le_of_lt (sub_pos.mpr hr1))

#check heckeEulerFactor_sub_one_norm_le
#print axioms heckeEulerFactor_sub_one_norm_le
/-- Uniform domination of the actual Euler factors in any closed right half-plane. -/
theorem heckeEulerFactor_sub_one_uniform_bound (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (σ : ℝ) (hσ : 0 < σ) (hs : σ ≤ s.re) :
    ‖heckeEulerFactor K χ v s - 1‖ ≤
      (1 - (2 : ℝ) ^ (-σ))⁻¹ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hq2 : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
    exact_mod_cast (Nat.succ_le_of_lt
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v))
  have hpos : 0 < s.re := lt_of_lt_of_le hσ hs
  have hpow : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hq) (neg_le_neg hs)
  have htwo : (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (neg_nonpos.mpr (le_of_lt hσ))
  have ht1 : (2 : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hσ)
  have hrs : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1 :=
    lt_of_le_of_lt (le_trans hpow htwo) ht1
  calc
    _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) /
        (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) :=
      heckeEulerFactor_sub_one_norm_le K χ v s hpos
    _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) /
        (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re)) :=
      div_le_div_of_nonneg_right hpow (le_of_lt (sub_pos.mpr hrs))
    _ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) / (1 - (2 : ℝ) ^ (-σ)) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hq)) _)
        (sub_pos.mpr ht1) (sub_le_sub_left (le_trans hpow htwo) 1)
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

#check heckeEulerFactor_sub_one_uniform_bound
#print axioms heckeEulerFactor_sub_one_uniform_bound

/-- Concrete infinite Euler product, before proving its convergence. -/
noncomputable def finiteHeckeL (χ : UnitaryHeckeCharacter K) (s : ℂ) : ℂ :=
  ∏' v : FinitePlace K, heckeEulerFactor K χ v s

/-- The analytic convergence step for the actual idelic Euler factors.
The arithmetic prime-norm summability premise is still an open obligation. -/
theorem heckeEulerProduct_multipliable_of_prime_norm_summable
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 0 < s.re)
    (hn : Summable (fun v : FinitePlace K =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re))) :
    Multipliable (fun v : FinitePlace K => heckeEulerFactor K χ v s) := by
  have hE : Summable (fun v : FinitePlace K => heckeEulerFactor K χ v s - 1) :=
    (Summable.mul_left ((1 - (2 : ℝ) ^ (-s.re))⁻¹) hn).of_norm_bounded
      (fun v => heckeEulerFactor_sub_one_uniform_bound K χ v s s.re hs le_rfl)
  simpa using Complex.multipliable_one_add_of_summable hE

/-- Convergence to the concrete product, conditional only on the stated arithmetic sum. -/
theorem finiteHeckeL_hasProd_of_prime_norm_summable
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 0 < s.re)
    (hn : Summable (fun v : FinitePlace K =>
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re))) :
    HasProd (fun v : FinitePlace K => heckeEulerFactor K χ v s) (finiteHeckeL K χ s) :=
  (heckeEulerProduct_multipliable_of_prime_norm_summable K χ s hs hn).hasProd

#check heckeEulerProduct_multipliable_of_prime_norm_summable
#print axioms heckeEulerProduct_multipliable_of_prime_norm_summable
#check finiteHeckeL_hasProd_of_prime_norm_summable
#print axioms finiteHeckeL_hasProd_of_prime_norm_summable

/-- Actual prime fibers have uniformly bounded cardinality, the arithmetic
counting input for the Hecke Euler-product comparison. -/
theorem rationalPrime_fiber_card_le (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) :
    (primesOverFinset p (𝓞 K)).card ≤ Module.finrank ℚ K :=
  Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp

#check rationalPrime_fiber_card_le
#print axioms rationalPrime_fiber_card_le

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

#check primeIdeal_absNorm_ge
#print axioms primeIdeal_absNorm_ge

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

#check primeFiber_rpow_sum_le
#print axioms primeFiber_rpow_sum_le

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

#check primeFiber_norm_summable
#print axioms primeFiber_norm_summable


/-- The actual rational prime ideal below a finite place. -/
noncomputable def rationalPlaceBelow (v : FinitePlace K) :
    IsDedekindDomain.HeightOneSpectrum ℤ where
  asIdeal := Ideal.under ℤ v.asIdeal
  isPrime := inferInstance
  ne_bot := Ideal.under_ne_bot ℤ v.ne_bot

theorem rationalPlaceBelow_span (v : FinitePlace K) :
    Ideal.span {(Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v) : ℤ)} =
      Ideal.under ℤ v.asIdeal := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (rationalPlaceBelow K v)
  have he : (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) = RingHom.id ℤ :=
    Subsingleton.elim _ _
  change Ideal.span {(Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v) : ℤ)} =
    Ideal.map (Rat.IsIntegralClosure.intEquiv ℤ : ℤ →+* ℤ) (rationalPlaceBelow K v).asIdeal at h
  rw [he, Ideal.map_id] at h
  exact h

#check rationalPlaceBelow_span
#print axioms rationalPlaceBelow_span

noncomputable def rationalPrimeBelow (v : FinitePlace K) : Nat.Primes :=
  ⟨Rat.HeightOneSpectrum.natGenerator (rationalPlaceBelow K v),
   Rat.HeightOneSpectrum.prime_natGenerator (rationalPlaceBelow K v)⟩

noncomputable def PrimeFiberIndex :=
  Σ p : Nat.Primes, ↥(primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))

/-- Place each actual finite place in its rational-prime fiber. -/
noncomputable def finitePlacePrimeFiber (v : FinitePlace K) : PrimeFiberIndex K := by
  classical
  refine ⟨rationalPrimeBelow K v, ⟨v.asIdeal, ?_⟩⟩
  have he : Ideal.span {((rationalPrimeBelow K v : Nat.Primes) : ℤ)} =
      Ideal.under ℤ v.asIdeal := rationalPlaceBelow_span K v
  have hp0 : (Ideal.span {((rationalPrimeBelow K v : Nat.Primes) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [he]
    exact Ideal.under_ne_bot ℤ v.ne_bot
  letI : (Ideal.span {((rationalPrimeBelow K v : Nat.Primes) : ℤ)} : Ideal ℤ).IsPrime := by
    rw [he]
    infer_instance
  letI : (Ideal.span {((rationalPrimeBelow K v : Nat.Primes) : ℤ)} : Ideal ℤ).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hp0
  exact (mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨v.isPrime, ⟨he⟩⟩

theorem finitePlacePrimeFiber_injective : Function.Injective (finitePlacePrimeFiber K) := by
  intro v w h
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact congrArg (fun t : PrimeFiberIndex K => t.2.val) h

/-- Unconditional prime-norm summability over all genuine finite places. -/
theorem finitePlace_norm_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun v : FinitePlace K => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) := by
  classical
  have hf : Summable (fun t : PrimeFiberIndex K => (Ideal.absNorm t.2.val : ℝ) ^ (-σ)) := by
    apply (summable_sigma_of_nonneg (fun t => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr
    constructor
    · intro p
      exact (hasSum_fintype _).summable
    · change Summable (fun p : Nat.Primes =>
        ∑' P : ↥(primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)),
          (Ideal.absNorm P.val : ℝ) ^ (-σ))
      convert primeFiber_norm_summable K σ hσ using 1
      funext p
      exact Finset.tsum_subtype (primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))
        (fun P : Ideal (𝓞 K) => (Ideal.absNorm P : ℝ)^(-σ))
  have hg := hf.comp_injective (finitePlacePrimeFiber_injective K)
  change Summable (fun v : FinitePlace K =>
    (Ideal.absNorm (finitePlacePrimeFiber K v).2.val : ℝ)^(-σ)) at hg
  exact hg

/-- The actual all-number-field Hecke Euler product converges on Re(s)>1,
without an assumed arithmetic or analytic package. -/
theorem finiteHeckeL_hasProd (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : FinitePlace K => heckeEulerFactor K χ v s) (finiteHeckeL K χ s) :=
  finiteHeckeL_hasProd_of_prime_norm_summable K χ s (lt_trans zero_lt_one hs)
    (finitePlace_norm_summable K s.re hs)

#check finitePlacePrimeFiber_injective
#print axioms finitePlacePrimeFiber_injective
#check finitePlace_norm_summable
#print axioms finitePlace_norm_summable
#check finiteHeckeL_hasProd
#print axioms finiteHeckeL_hasProd

/-- Absolute convergence of the genuine local-factor perturbations. -/
theorem heckeEulerFactor_sub_one_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : FinitePlace K => heckeEulerFactor K χ v s - 1) :=
  ((finitePlace_norm_summable K s.re hs).mul_left ((1 - (2 : ℝ)^(-s.re))⁻¹)).of_norm_bounded
    (fun v => heckeEulerFactor_sub_one_uniform_bound K χ v s s.re
      (lt_trans zero_lt_one hs) le_rfl)

/-- Nonvanishing of the genuine finite Hecke Euler product on Re(s)>1. -/
theorem finiteHeckeL_ne_zero (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    finiteHeckeL K χ s ≠ 0 := by
  have hn := (heckeEulerFactor_sub_one_summable K χ s hs).norm
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun v : FinitePlace K => heckeEulerFactor K χ v s - 1)
    (fun v => by simpa using heckeEulerFactor_ne_zero K χ v s (lt_trans zero_lt_one hs)) hn
  simpa only [add_sub_cancel, finiteHeckeL] using h

#check heckeEulerFactor_sub_one_summable
#print axioms heckeEulerFactor_sub_one_summable
#check finiteHeckeL_ne_zero
#print axioms finiteHeckeL_ne_zero

/-- Holomorphy of the genuine finite-place Euler factor on the positive half-plane. -/
theorem heckeEulerFactor_differentiableOn (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) :
    DifferentiableOn ℂ (heckeEulerFactor K χ v) {s : ℂ | 0 < s.re} := by
  classical
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)))
  unfold heckeEulerFactor
  split_ifs with hχ
  · apply DifferentiableOn.inv
    · fun_prop (disch := aesop)
    · intro s hs
      exact heckeEulerDenominator_ne_zero K χ v s hs
  · fun_prop

#check heckeEulerFactor_differentiableOn
#print axioms heckeEulerFactor_differentiableOn

/-- Uniform Euler-product convergence on a compact subset of a closed half-plane. -/
theorem finiteHeckeL_hasProdUniformlyOn (χ : UnitaryHeckeCharacter K)
    (T : Set ℂ) (hT : IsCompact T) (σ : ℝ) (hσ : 1 < σ)
    (hTσ : ∀ s ∈ T, σ ≤ s.re) :
    HasProdUniformlyOn (fun v : FinitePlace K => heckeEulerFactor K χ v)
      (finiteHeckeL K χ) T := by
  have hu := (finitePlace_norm_summable K σ hσ).mul_left ((1 - (2 : ℝ)^(-σ))⁻¹)
  have hb : ∀ᶠ v : FinitePlace K in Filter.cofinite, ∀ s ∈ T,
      ‖heckeEulerFactor K χ v s - 1‖ ≤
        (1 - (2 : ℝ)^(-σ))⁻¹ * (Ideal.absNorm v.asIdeal : ℝ)^(-σ) :=
    Filter.Eventually.of_forall (fun v s hs =>
      heckeEulerFactor_sub_one_uniform_bound K χ v s σ (lt_trans zero_lt_one hσ)
        (hTσ s hs))
  have hc : ∀ v : FinitePlace K, ContinuousOn (fun s => heckeEulerFactor K χ v s - 1) T := by
    intro v
    exact ((heckeEulerFactor_differentiableOn K χ v).continuousOn.mono
      (fun s hs => lt_of_lt_of_le (lt_trans zero_lt_one hσ) (hTσ s hs))).sub
        continuousOn_const
  simpa only [add_sub_cancel, finiteHeckeL] using
    (Summable.hasProdUniformlyOn_one_add hT hu hb hc)

#check finiteHeckeL_hasProdUniformlyOn
#print axioms finiteHeckeL_hasProdUniformlyOn

/-- Locally uniform convergence of the genuine all-number-field finite Euler product. -/
theorem finiteHeckeL_hasProdLocallyUniformlyOn (χ : UnitaryHeckeCharacter K) :
    HasProdLocallyUniformlyOn (fun v : FinitePlace K => heckeEulerFactor K χ v)
      (finiteHeckeL K χ) {s : ℂ | 1 < s.re} := by
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const Complex.continuous_re)
  intro T hsub hT
  by_cases hne : T.Nonempty
  · obtain ⟨s₀, hs₀, hmin⟩ := hT.exists_isMinOn hne Complex.continuous_re.continuousOn
    exact finiteHeckeL_hasProdUniformlyOn K χ T hT s₀.re (hsub hs₀)
      (fun s hs => hmin hs)
  · apply finiteHeckeL_hasProdUniformlyOn K χ T hT 2 (by norm_num)
    intro s hs
    exact (hne ⟨s, hs⟩).elim

#check finiteHeckeL_hasProdLocallyUniformlyOn
#print axioms finiteHeckeL_hasProdLocallyUniformlyOn
/-- Each genuine finite Euler product is holomorphic on Re(s)>1. -/
theorem partialHeckeEulerProduct_differentiableOn (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) :
    DifferentiableOn ℂ (partialHeckeEulerProduct K χ S) {s : ℂ | 1 < s.re} := by
  classical
  have heq : partialHeckeEulerProduct K χ S =
      (∏ v ∈ S, heckeEulerFactor K χ v) := by
    funext s
    simp only [partialHeckeEulerProduct, Finset.prod_apply]
  rw [heq]
  apply DifferentiableOn.finset_prod
  intro v hv
  exact (heckeEulerFactor_differentiableOn K χ v).mono
    (fun (s : ℂ) (hs : 1 < s.re) => lt_trans zero_lt_one hs)

#check partialHeckeEulerProduct_differentiableOn
#print axioms partialHeckeEulerProduct_differentiableOn

/-- Holomorphy of the actual arithmetic Hecke product on its convergence half-plane. -/
theorem finiteHeckeL_differentiableOn (χ : UnitaryHeckeCharacter K) :
    DifferentiableOn ℂ (finiteHeckeL K χ) {s : ℂ | 1 < s.re} := by
  have h := finiteHeckeL_hasProdLocallyUniformlyOn K χ
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  apply h.differentiableOn (Filter.Eventually.of_forall (fun S => ?_))
    (isOpen_lt continuous_const Complex.continuous_re)
  exact partialHeckeEulerProduct_differentiableOn K χ S

#check finiteHeckeL_differentiableOn
#print axioms finiteHeckeL_differentiableOn

/-- The derivatives of genuine finite Euler products converge locally uniformly. -/
theorem finiteHeckeL_deriv_tendstoLocallyUniformlyOn (χ : UnitaryHeckeCharacter K) :
    TendstoLocallyUniformlyOn
      (fun S : Finset (FinitePlace K) => deriv (partialHeckeEulerProduct K χ S))
      (deriv (finiteHeckeL K χ)) Filter.atTop {s : ℂ | 1 < s.re} := by
  have h := finiteHeckeL_hasProdLocallyUniformlyOn K χ
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  exact h.deriv (Filter.Eventually.of_forall (fun S =>
    partialHeckeEulerProduct_differentiableOn K χ S))
    (isOpen_lt continuous_const Complex.continuous_re)

#check finiteHeckeL_deriv_tendstoLocallyUniformlyOn
#print axioms finiteHeckeL_deriv_tendstoLocallyUniformlyOn
/-- Analyticity of the genuine Hecke Euler product on its initial domain. -/
theorem finiteHeckeL_analyticOnNhd (χ : UnitaryHeckeCharacter K) :
    AnalyticOnNhd ℂ (finiteHeckeL K χ) {s : ℂ | 1 < s.re} :=
  (finiteHeckeL_differentiableOn K χ).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

/-- The genuine finite Hecke function has neither zeros nor poles on Re(s)>1. -/
theorem finiteHeckeL_meromorphicOrderAt_eq_zero (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    meromorphicOrderAt (finiteHeckeL K χ) s = 0 := by
  have ha := finiteHeckeL_analyticOnNhd K χ s hs
  rw [ha.meromorphicOrderAt_eq,
    ha.analyticOrderAt_eq_zero.mpr (finiteHeckeL_ne_zero K χ s hs)]
  simp

/-- Actual signed divisor coefficients vanish throughout the initial half-plane. -/
theorem finiteHeckeL_divisor_apply_eq_zero (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    MeromorphicOn.divisor (finiteHeckeL K χ) {z : ℂ | 1 < z.re} s = 0 := by
  rw [(finiteHeckeL_analyticOnNhd K χ).meromorphicOn.divisor_apply hs,
    finiteHeckeL_meromorphicOrderAt_eq_zero K χ s hs]
  rfl

/-- The logarithmic derivative needed for the divisor is analytic on Re(s)>1. -/
theorem finiteHeckeL_logDeriv_differentiableOn (χ : UnitaryHeckeCharacter K) :
    DifferentiableOn ℂ (fun s => deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)
      {s : ℂ | 1 < s.re} := by
  exact ((finiteHeckeL_differentiableOn K χ).deriv
    (isOpen_lt continuous_const Complex.continuous_re)).div
      (finiteHeckeL_differentiableOn K χ) (fun s hs => finiteHeckeL_ne_zero K χ s hs)

#check finiteHeckeL_analyticOnNhd
#print axioms finiteHeckeL_analyticOnNhd
#check finiteHeckeL_meromorphicOrderAt_eq_zero
#print axioms finiteHeckeL_meromorphicOrderAt_eq_zero
#check finiteHeckeL_divisor_apply_eq_zero
#print axioms finiteHeckeL_divisor_apply_eq_zero
#check finiteHeckeL_logDeriv_differentiableOn
#print axioms finiteHeckeL_logDeriv_differentiableOn

/-- Arithmetic logarithmic-derivative sum for the actual Hecke Euler product.
This is the initial-half-plane identity used to link the product to its divisor. -/
theorem finiteHeckeL_logDeriv_hasSum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun v : FinitePlace K => logDeriv (heckeEulerFactor K χ v) s)
      (logDeriv (finiteHeckeL K χ) s) := by
  classical
  have hd := (finiteHeckeL_deriv_tendstoLocallyUniformlyOn K χ).tendsto_at hs
  have hv : Filter.Tendsto
      (fun S : Finset (FinitePlace K) => partialHeckeEulerProduct K χ S s)
      Filter.atTop (nhds (finiteHeckeL K χ s)) := finiteHeckeL_hasProd K χ s hs
  have hlim := hd.div hv (finiteHeckeL_ne_zero K χ s hs)
  have heq : (fun S : Finset (FinitePlace K) =>
      ∑ v ∈ S, logDeriv (heckeEulerFactor K χ v) s) =
      (fun S => deriv (partialHeckeEulerProduct K χ S) s /
        partialHeckeEulerProduct K χ S s) := by
    funext S
    symm
    change logDeriv (fun z => ∏ v ∈ S, heckeEulerFactor K χ v z) s = _
    apply logDeriv_prod
    · intro v hv
      exact heckeEulerFactor_ne_zero K χ v s (lt_trans zero_lt_one hs)
    · intro v hv
      exact (heckeEulerFactor_differentiableOn K χ v).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (lt_trans zero_lt_one hs))
  change Filter.Tendsto
    (fun S : Finset (FinitePlace K) => ∑ v ∈ S, logDeriv (heckeEulerFactor K χ v) s)
    Filter.atTop (nhds (deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s))
  rw [heq]
  exact hlim

#check finiteHeckeL_logDeriv_hasSum
#print axioms finiteHeckeL_logDeriv_hasSum

attribute [local instance] Classical.propDecidable

/-- Explicit arithmetic logarithmic derivative of a genuine local Hecke factor.
This is the prime term of the logarithmic derivative used to identify its divisor. -/
theorem heckeEulerFactor_logDeriv (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    logDeriv (heckeEulerFactor K χ v) s =
      if IsUnramified K χ v then
        -Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
          (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) /
          (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      else 0 := by
  classical
  by_cases hχ : IsUnramified K χ v
  · rw [if_pos hχ]
    have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)))
    have ht : HasDerivAt
        (fun z : ℂ => heckePrimeCoefficient K χ v *
          (Ideal.absNorm v.asIdeal : ℂ) ^ (-z))
        (-Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
          (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))) s := by
      convert (((hasDerivAt_id s).neg.const_cpow (Or.inl hq0)).const_mul
        (heckePrimeCoefficient K χ v)) using 1
      dsimp
      ring
    have hn := heckeEulerDenominator_ne_zero K χ v s hs
    have hd := ((hasDerivAt_const s (1 : ℂ)).sub ht).inv hn
    have heq : heckeEulerFactor K χ v = fun z =>
        (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-z))⁻¹ := by
      funext z
      simp [heckeEulerFactor, hχ]
    have hd' : HasDerivAt (fun z : ℂ =>
        (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-z))⁻¹)
        (-Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
          (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) /
          (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))^2) s := by
      convert hd using 1
      dsimp
      ring
    rw [heq, logDeriv_apply, hd'.deriv]
    field_simp [hn]
  · rw [if_neg hχ]
    have heq : heckeEulerFactor K χ v = fun _ => (1 : ℂ) := by
      funext z
      simp [heckeEulerFactor, hχ]
    simp [heq, logDeriv_apply]

/-- The genuine Euler product has the explicit arithmetic prime logarithmic derivative
on its domain of absolute convergence, over every number field and unitary character. -/
theorem finiteHeckeL_logDeriv_prime_hasSum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun v : FinitePlace K =>
      if IsUnramified K χ v then
        -Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
          (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) /
          (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))
      else 0) (logDeriv (finiteHeckeL K χ) s) := by
  classical
  convert finiteHeckeL_logDeriv_hasSum K χ s hs using 1
  funext v
  exact (heckeEulerFactor_logDeriv K χ v s (lt_trans zero_lt_one hs)).symm

/-- Actual local prime-power terms sum to the local logarithmic derivative.
The integer m+1 is the positive prime-power exponent, so the multiplicity weight
is log(Nv), with the sign prescribed by the inverse Euler factor. -/
theorem heckeEulerFactor_logDeriv_primePower_hasSum (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun m : ℕ =>
      if IsUnramified K χ v then
        -Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
          (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (m+1)
      else 0) (logDeriv (heckeEulerFactor K χ v) s) := by
  classical
  rw [heckeEulerFactor_logDeriv K χ v s hs]
  by_cases hχ : IsUnramified K χ v
  · simp only [if_pos hχ]
    have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hn : ‖heckePrimeCoefficient K χ v *
        (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
      rw [heckeEulerTerm_norm]
      exact Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
    have h := (hasSum_geometric_of_norm_lt_one hn).mul_left
      (-Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
        (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)))
    convert h using 1
    funext m
    simp only [pow_succ]
    ring
  · simp only [if_neg hχ]
    exact hasSum_zero

#check heckeEulerFactor_logDeriv
#print axioms heckeEulerFactor_logDeriv
#check finiteHeckeL_logDeriv_prime_hasSum
#print axioms finiteHeckeL_logDeriv_prime_hasSum
#check heckeEulerFactor_logDeriv_primePower_hasSum
#print axioms heckeEulerFactor_logDeriv_primePower_hasSum

/-- The prime-power expansion is incorporated into the genuine whole-product
logarithmic derivative. This is an iterated sum, not an unproved exchange of sums. -/
theorem finiteHeckeL_logDeriv_eq_primePower_tsum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    logDeriv (finiteHeckeL K χ) s =
      ∑' v : FinitePlace K, ∑' m : ℕ,
        if IsUnramified K χ v then
          -Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
            (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ (m+1)
        else 0 := by
  rw [← (finiteHeckeL_logDeriv_hasSum K χ s hs).tsum_eq]
  congr 1
  funext v
  exact (heckeEulerFactor_logDeriv_primePower_hasSum K χ v s
    (lt_trans zero_lt_one hs)).tsum_eq.symm

#check finiteHeckeL_logDeriv_eq_primePower_tsum
#print axioms finiteHeckeL_logDeriv_eq_primePower_tsum

/-- The actual arithmetic prime-power summand, with positive exponent m+1. -/
noncomputable def heckePrimePowerTerm (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (m : ℕ) (s : ℂ) : ℂ :=
  if IsUnramified K χ v then
    -Complex.log (Ideal.absNorm v.asIdeal : ℂ) *
      (heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s))^(m+1)
  else 0

/-- A geometric bound for the actual prime-power terms, expressed using the
already summable genuine local logarithmic derivatives. -/
theorem heckePrimePowerTerm_norm_bound (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (m : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖heckePrimePowerTerm K χ v m s‖ ≤
      (2 * ‖logDeriv (heckeEulerFactor K χ v) s‖) * ((2 : ℝ)^(-s.re))^m := by
  let a := heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s)
  have hr : (2 : ℝ)^(-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs)
  have hq : (2 : ℝ) ≤ Ideal.absNorm v.asIdeal := by
    exact_mod_cast Nat.succ_le_of_lt
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)
  have ha : ‖a‖ ≤ (2 : ℝ)^(-s.re) := by
    rw [heckeEulerTerm_norm]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hq (neg_nonpos.mpr (le_of_lt hs))
  have hn : 1 - a ≠ 0 := heckeEulerDenominator_ne_zero K χ v s hs
  by_cases hu : IsUnramified K χ v
  · rw [heckePrimePowerTerm, if_pos hu]
    change ‖-Complex.log (Ideal.absNorm v.asIdeal : ℂ) * a^(m+1)‖ ≤ _
    have hid : -Complex.log (Ideal.absNorm v.asIdeal : ℂ) * a =
        logDeriv (heckeEulerFactor K χ v) s * (1-a) := by
      rw [heckeEulerFactor_logDeriv K χ v s hs, if_pos hu]
      exact (div_mul_cancel₀ _ hn).symm
    have hb : ‖1-a‖ ≤ 2 := by
      have hh := norm_sub_le (1 : ℂ) a
      rw [norm_one] at hh
      linarith
    have hc : ‖-Complex.log (Ideal.absNorm v.asIdeal : ℂ) * a‖ ≤
        2 * ‖logDeriv (heckeEulerFactor K χ v) s‖ := by
      rw [hid, norm_mul]
      calc
        _ ≤ ‖logDeriv (heckeEulerFactor K χ v) s‖ * 2 :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = _ := mul_comm _ _
    calc
      _ = ‖-Complex.log (Ideal.absNorm v.asIdeal : ℂ) * a‖ * ‖a‖^m := by
        rw [pow_succ', ← mul_assoc, norm_mul, norm_pow]
      _ ≤ _ := by gcongr
  · rw [heckePrimePowerTerm, if_neg hu, norm_zero]
    positivity

/-- Absolute convergence over both genuine finite places and positive powers.
This permits subsequent interchanges in the arithmetic side of the divisor formula. -/
theorem finiteHeckeL_primePower_norm_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun t : Σ _v : FinitePlace K, ℕ =>
      ‖heckePrimePowerTerm K χ t.1 t.2 s‖) := by
  let r : ℝ := (2 : ℝ)^(-s.re)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num) (neg_neg_of_pos (lt_trans zero_lt_one hs))
  have hg : Summable (fun m : ℕ => r^m) :=
    (hasSum_geometric_of_norm_lt_one (show ‖r‖ < 1 by
      rwa [Real.norm_eq_abs, abs_of_nonneg hr0])).summable
  have ho : Summable (fun v : FinitePlace K =>
      ‖logDeriv (heckeEulerFactor K χ v) s‖) :=
    (finiteHeckeL_logDeriv_hasSum K χ s hs).summable.norm
  have hb : Summable (fun t : Σ _v : FinitePlace K, ℕ =>
      (2 * ‖logDeriv (heckeEulerFactor K χ t.1) s‖) * r^t.2) := by
    apply (summable_sigma_of_nonneg (fun t => by positivity)).mpr
    constructor
    · intro v
      change Summable (fun m : ℕ =>
        (2 * ‖logDeriv (heckeEulerFactor K χ v) s‖) * r^m)
      exact hg.mul_left (2 * ‖logDeriv (heckeEulerFactor K χ v) s‖)
    · simpa only [tsum_mul_left] using
        (ho.mul_left 2).mul_right (∑' m : ℕ, r^m)
  apply hb.of_norm_bounded
  intro t
  simpa only [norm_norm] using
    heckePrimePowerTerm_norm_bound K χ t.1 t.2 s (lt_trans zero_lt_one hs)

#check heckePrimePowerTerm_norm_bound
#print axioms heckePrimePowerTerm_norm_bound
#check finiteHeckeL_primePower_norm_summable
#print axioms finiteHeckeL_primePower_norm_summable

/-- Absolutely convergent arithmetic expansion over all actual prime powers.
Unlike the iterated formula, this is a single unconditional sum over the sigma type. -/
theorem finiteHeckeL_logDeriv_primePower_hasSum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun t : Σ _v : FinitePlace K, ℕ => heckePrimePowerTerm K χ t.1 t.2 s)
      (logDeriv (finiteHeckeL K χ) s) := by
  apply (finiteHeckeL_logDeriv_hasSum K χ s hs).sigma_of_hasSum
  · intro v
    exact heckeEulerFactor_logDeriv_primePower_hasSum K χ v s
      (lt_trans zero_lt_one hs)
  · exact (finiteHeckeL_primePower_norm_summable K χ s hs).of_norm

#check finiteHeckeL_logDeriv_primePower_hasSum
#print axioms finiteHeckeL_logDeriv_primePower_hasSum


/-- Exact arithmetic domination on a closed right half-plane. The majorant is
itself the norm of the same genuine prime-power term at the real boundary. -/
theorem heckePrimePowerTerm_norm_le_real (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (m : ℕ) (s : ℂ) (σ : ℝ) (hs : σ ≤ s.re) :
    ‖heckePrimePowerTerm K χ v m s‖ ≤
      ‖heckePrimePowerTerm K χ v m (σ : ℂ)‖ := by
  by_cases hu : IsUnramified K χ v
  · have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    have hp : (Ideal.absNorm v.asIdeal : ℝ)^(-s.re) ≤
        (Ideal.absNorm v.asIdeal : ℝ)^(-σ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hq) (neg_le_neg hs)
    calc
      _ = ‖-Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ *
          ((Ideal.absNorm v.asIdeal : ℝ)^(-s.re))^(m+1) := by
        rw [heckePrimePowerTerm, if_pos hu, norm_mul, norm_pow, heckeEulerTerm_norm]
      _ ≤ ‖-Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ *
          ((Ideal.absNorm v.asIdeal : ℝ)^(-σ))^(m+1) := by
        gcongr
      _ = _ := by
        rw [heckePrimePowerTerm, if_pos hu, norm_mul, norm_pow,
          heckeEulerTerm_norm, Complex.ofReal_re]
  · simp [heckePrimePowerTerm, hu]

/-- Uniform convergence of the actual prime-power logarithmic-derivative series
on every closed half-plane Re(s) ≥ σ > 1. This provides the arithmetic limiting
operation needed before a contour form of the genuine divisor identity. -/
theorem finiteHeckeL_primePower_tendstoUniformlyOn (χ : UnitaryHeckeCharacter K)
    (σ : ℝ) (hσ : 1 < σ) :
    TendstoUniformlyOn
      (fun S : Finset (Σ _v : FinitePlace K, ℕ) => fun s : ℂ =>
        ∑ t ∈ S, heckePrimePowerTerm K χ t.1 t.2 s)
      (logDeriv (finiteHeckeL K χ)) Filter.atTop {s : ℂ | σ ≤ s.re} := by
  have hb := finiteHeckeL_primePower_norm_summable K χ (σ : ℂ)
    (by simpa using hσ)
  have ht : TendstoUniformlyOn
      (fun S : Finset (Σ _v : FinitePlace K, ℕ) => fun s : ℂ =>
        ∑ t ∈ S, heckePrimePowerTerm K χ t.1 t.2 s)
      (fun s : ℂ => ∑' t : Σ _v : FinitePlace K, ℕ,
        heckePrimePowerTerm K χ t.1 t.2 s)
      Filter.atTop {s : ℂ | σ ≤ s.re} :=
    tendstoUniformlyOn_tsum hb (fun t s hs =>
      heckePrimePowerTerm_norm_le_real K χ t.1 t.2 s σ hs)
  rw [Metric.tendstoUniformlyOn_iff] at ht ⊢
  intro ε hε
  filter_upwards [ht ε hε] with S hS s hs
  have heq := (finiteHeckeL_logDeriv_primePower_hasSum K χ s
    (lt_of_lt_of_le hσ hs)).tsum_eq
  simpa only [heq] using hS s hs

#check heckePrimePowerTerm_norm_le_real
#print axioms heckePrimePowerTerm_norm_le_real
#check finiteHeckeL_primePower_tendstoUniformlyOn
#print axioms finiteHeckeL_primePower_tendstoUniformlyOn

end MasulloGRH
