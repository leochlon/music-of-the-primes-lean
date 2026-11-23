import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

/-! D, round 33; repair of the frozen round-32 candidate. Inherits D rounds 21–28 genuine arithmetic Euler product
and logarithmic derivative construction. This round repairs sharp norm cutoff
convergence and proves uniform convergence along those actual finite cutoffs.
No analytic Hecke package is assumed. Global continuation and divisor remain open. -/
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
  change DifferentiableOn ℂ (fun s : ℂ => ∏ v ∈ S, heckeEulerFactor K χ v s)
    {s : ℂ | 1 < s.re}
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiableOn_const (1 : ℂ)
  | @insert v S hv ih =>
    simp only [Finset.prod_insert hv]
    have hd : DifferentiableOn ℂ (heckeEulerFactor K χ v) {s : ℂ | 1 < s.re} :=
      (heckeEulerFactor_differentiableOn K χ v).mono
        (fun (s : ℂ) (hs : 1 < s.re) => lt_trans zero_lt_one hs)
    exact hd.mul ih

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
attribute [local instance] Classical.propDecidable
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-- The local arithmetic logarithmic-derivative input to the genuine divisor.
No pole or continuation premise is used: the denominator is proved nonzero. -/
theorem heckeEulerFactor_hasDerivAt (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (heckeEulerFactor K χ v)
      (if IsUnramified K χ v then
        -(heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s) *
          Complex.log (Ideal.absNorm v.asIdeal : ℂ)) /
          (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s))^2
      else 0) s := by
  classical
  have hq0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)))
  change HasDerivAt (fun z : ℂ =>
    if IsUnramified K χ v then
      (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-z))⁻¹
    else 1) _ s
  by_cases hχ : IsUnramified K χ v
  · simp only [if_pos hχ]
    have hp := ((hasDerivAt_id s).neg).const_cpow (Or.inl hq0)
    have ha := hp.const_mul (heckePrimeCoefficient K χ v)
    have hi := ((hasDerivAt_const s (1 : ℂ)).sub ha).inv
      (heckeEulerDenominator_ne_zero K χ v s hs)
    change HasDerivAt (fun z : ℂ =>
      (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-z))⁻¹)
      (-(0 - heckePrimeCoefficient K χ v *
        ((Ideal.absNorm v.asIdeal : ℂ)^(-s) *
          Complex.log (Ideal.absNorm v.asIdeal : ℂ) * -1)) /
        (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s))^2) s at hi
    convert hi using 1 <;> ring
  · simp only [if_neg hχ]
    exact hasDerivAt_const s (1 : ℂ)

#check heckeEulerFactor_hasDerivAt
#print axioms heckeEulerFactor_hasDerivAt

/-- Prime contribution to L'/L, with zero contribution at ramified places. -/
noncomputable def heckePrimeLogDerivative (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) : ℂ := by
  classical
  exact if IsUnramified K χ v then
    -(heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s) *
      Complex.log (Ideal.absNorm v.asIdeal : ℂ)) /
      (1 - heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s))
    else 0

/-- Exact local logarithmic derivative for the actual idelic Euler factor. -/
theorem heckeEulerFactor_hasDerivAt_logDerivative (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (heckeEulerFactor K χ v)
      (heckeEulerFactor K χ v s * heckePrimeLogDerivative K χ v s) s := by
  classical
  have h := heckeEulerFactor_hasDerivAt K χ v s hs
  have hd := heckeEulerDenominator_ne_zero K χ v s hs
  by_cases hχ : IsUnramified K χ v
  · simp only [if_pos hχ] at h
    convert h using 1
    simp only [heckeEulerFactor, heckePrimeLogDerivative, if_pos hχ]
    field_simp [hd]
  · simpa only [heckeEulerFactor, heckePrimeLogDerivative, if_neg hχ, mul_zero] using h

/-- Finite arithmetic L'/L identity, used to pass the prime sum to the genuine L germ. -/
theorem partialHeckeEulerProduct_hasDerivAt (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (s : ℂ) (hs : 0 < s.re) :
    HasDerivAt (partialHeckeEulerProduct K χ S)
      (partialHeckeEulerProduct K χ S s * ∑ v ∈ S, heckePrimeLogDerivative K χ v s) s := by
  classical
  change HasDerivAt (fun z : ℂ => ∏ v ∈ S, heckeEulerFactor K χ v z)
    ((∏ v ∈ S, heckeEulerFactor K χ v s) * ∑ v ∈ S, heckePrimeLogDerivative K χ v s) s
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const s (1 : ℂ)
  | @insert v S hv ih =>
    simp only [Finset.prod_insert hv, Finset.sum_insert hv]
    convert (heckeEulerFactor_hasDerivAt_logDerivative K χ v s hs).mul ih using 1 <;> ring

/-- Exact finite prime-sum formula, without an assumed L-function package. -/
theorem partialHeckeEulerProduct_logDeriv (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (s : ℂ) (hs : 0 < s.re) :
    deriv (partialHeckeEulerProduct K χ S) s / partialHeckeEulerProduct K χ S s =
      ∑ v ∈ S, heckePrimeLogDerivative K χ v s := by
  rw [(partialHeckeEulerProduct_hasDerivAt K χ S s hs).deriv]
  exact mul_div_cancel_left₀ _ (partialHeckeEulerProduct_ne_zero K χ S s hs)

#check heckeEulerFactor_hasDerivAt_logDerivative
#print axioms heckeEulerFactor_hasDerivAt_logDerivative
#check partialHeckeEulerProduct_hasDerivAt
#print axioms partialHeckeEulerProduct_hasDerivAt
#check partialHeckeEulerProduct_logDeriv
#print axioms partialHeckeEulerProduct_logDeriv

/-- The arithmetic prime-sum identity for the logarithmic derivative of the
actual all-number-field Hecke L-function on its convergence half-plane. -/
theorem finiteHeckeL_logDeriv_hasSum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun v : FinitePlace K => heckePrimeLogDerivative K χ v s)
      (deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s) := by
  have hd : Filter.Tendsto
      (fun S : Finset (FinitePlace K) => deriv (partialHeckeEulerProduct K χ S) s)
      Filter.atTop (nhds (deriv (finiteHeckeL K χ) s)) :=
    (finiteHeckeL_deriv_tendstoLocallyUniformlyOn K χ).tendsto_at hs
  have hp : Filter.Tendsto
      (fun S : Finset (FinitePlace K) => partialHeckeEulerProduct K χ S s)
      Filter.atTop (nhds (finiteHeckeL K χ s)) := finiteHeckeL_hasProd K χ s hs
  have h := hd.div hp (finiteHeckeL_ne_zero K χ s hs)
  change Filter.Tendsto
    (fun S : Finset (FinitePlace K) => ∑ v ∈ S, heckePrimeLogDerivative K χ v s)
    Filter.atTop (nhds (deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s))
  convert h using 1
  funext S
  exact (partialHeckeEulerProduct_logDeriv K χ S s (lt_trans zero_lt_one hs)).symm

#check finiteHeckeL_logDeriv_hasSum
#print axioms finiteHeckeL_logDeriv_hasSum
/-- Absolute convergence of the genuine arithmetic logarithmic-derivative sum. -/
theorem heckePrimeLogDerivative_norm_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : FinitePlace K => ‖heckePrimeLogDerivative K χ v s‖) :=
  (finiteHeckeL_logDeriv_hasSum K χ s hs).summable.norm

/-- Arithmetic identification of the initial-domain logarithmic derivative. -/
theorem finiteHeckeL_logDeriv_eq_tsum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s =
      ∑' v : FinitePlace K, heckePrimeLogDerivative K χ v s :=
  (finiteHeckeL_logDeriv_hasSum K χ s hs).tsum_eq.symm

#check heckePrimeLogDerivative_norm_summable
#print axioms heckePrimeLogDerivative_norm_summable
#check finiteHeckeL_logDeriv_eq_tsum
#print axioms finiteHeckeL_logDeriv_eq_tsum

/-- The genuine prime-power term in the arithmetic logarithmic derivative.
The sign is negative for L'/L with local factor (1-a)⁻¹. -/
noncomputable def heckePrimePowerLogTerm (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (n : ℕ) : ℂ :=
  if IsUnramified K χ v then
    -((heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s))^(n+1) *
      Complex.log (Ideal.absNorm v.asIdeal : ℂ))
  else 0

/-- The exact local prime-power expansion used by the genuine divisor argument. -/
theorem heckePrimeLogDerivative_hasSum_primePowers (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (hs : 0 < s.re) :
    HasSum (heckePrimePowerLogTerm K χ v s) (heckePrimeLogDerivative K χ v s) := by
  classical
  by_cases hχ : IsUnramified K χ v
  · let a := heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s)
    have ha : ‖a‖ < 1 := by
      rw [heckeEulerTerm_norm]
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
      · exact neg_neg_of_pos hs
    have h := (hasSum_geometric_of_norm_lt_one ha).mul_left
      (-(a * Complex.log (Ideal.absNorm v.asIdeal : ℂ)))
    convert h using 1
    · funext n
      simp only [heckePrimePowerLogTerm, if_pos hχ, pow_succ]
      dsimp [a] <;> ring
    · simp only [heckePrimeLogDerivative, if_pos hχ, div_eq_mul_inv]
      dsimp [a]
  · change HasSum (fun n : ℕ => heckePrimePowerLogTerm K χ v s n)
      (heckePrimeLogDerivative K χ v s)
    simpa only [heckePrimePowerLogTerm, heckePrimeLogDerivative, if_neg hχ] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

/-- Identification with the actual arithmetic prime-power series on Re(s)>1.
The order of summation is explicit; no unproved interchange is used. -/
theorem finiteHeckeL_logDeriv_eq_primePower_tsum (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s =
      ∑' v : FinitePlace K, ∑' n : ℕ, heckePrimePowerLogTerm K χ v s n := by
  rw [finiteHeckeL_logDeriv_eq_tsum K χ s hs]
  congr 1
  funext v
  exact (heckePrimeLogDerivative_hasSum_primePowers K χ v s
    (lt_trans zero_lt_one hs)).tsum_eq.symm

#check heckePrimeLogDerivative_hasSum_primePowers
#print axioms heckePrimeLogDerivative_hasSum_primePowers
#check finiteHeckeL_logDeriv_eq_primePower_tsum
#print axioms finiteHeckeL_logDeriv_eq_primePower_tsum

/-- Absolute convergence of the genuine double prime-power series, needed to
rearrange the arithmetic input to the global divisor on its initial domain. -/
theorem heckePrimePowerLogTerm_sigma_summable (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : (Σ _v : FinitePlace K, ℕ) =>
      heckePrimePowerLogTerm K χ p.1 s p.2) := by
  classical
  let R : ℝ := (2 : ℝ)^(-s.re)
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hR1 : R < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    (by linarith)
  have hg : HasSum (fun n : ℕ => R^n) (1-R)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs, abs_of_nonneg hR0])
  have hm : Summable (fun p : (Σ _v : FinitePlace K, ℕ) =>
      (2 * ‖heckePrimeLogDerivative K χ p.1 s‖) * R^p.2) := by
    apply (summable_sigma_of_nonneg (fun p =>
      mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (pow_nonneg hR0 _))).mpr
    constructor
    · intro v
      exact hg.summable.mul_left (2 * ‖heckePrimeLogDerivative K χ v s‖)
    · convert ((heckePrimeLogDerivative_norm_summable K χ s hs).mul_left 2).mul_right
        ((1-R)⁻¹) using 1
      funext v
      exact (hg.mul_left (2 * ‖heckePrimeLogDerivative K χ v s‖)).tsum_eq
  apply hm.of_norm_bounded
  rintro ⟨v, n⟩
  by_cases hχ : IsUnramified K χ v
  · let a : ℂ := heckePrimeCoefficient K χ v * (Ideal.absNorm v.asIdeal : ℂ)^(-s)
    have haR : ‖a‖ ≤ R := by
      rw [heckeEulerTerm_norm]
      apply Real.rpow_le_rpow_of_nonpos (by norm_num)
      · exact_mod_cast Nat.succ_le_of_lt
          (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)
      · linarith
    have ha1 : ‖a‖ < 1 := lt_of_le_of_lt haR hR1
    have hd : 1-a ≠ 0 := heckeEulerDenominator_ne_zero K χ v s
      (lt_trans zero_lt_one hs)
    have he : a * Complex.log (Ideal.absNorm v.asIdeal : ℂ) =
        -(heckePrimeLogDerivative K χ v s * (1-a)) := by
      simp only [heckePrimeLogDerivative, if_pos hχ]
      change a * Complex.log (Ideal.absNorm v.asIdeal : ℂ) =
        -(-(a * Complex.log (Ideal.absNorm v.asIdeal : ℂ)) / (1-a) * (1-a))
      field_simp [hd]
    have hb : ‖1-a‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) a
      rw [norm_one] at h
      linarith
    have hn : ‖a * Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ ≤
        2 * ‖heckePrimeLogDerivative K χ v s‖ := by
      rw [he, norm_neg, norm_mul]
      nlinarith [norm_nonneg (heckePrimeLogDerivative K χ v s)]
    calc
      ‖heckePrimePowerLogTerm K χ v s n‖ =
          ‖a * Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ * ‖a‖^n := by
        simp only [heckePrimePowerLogTerm, if_pos hχ]
        change ‖-(a^(n+1) * Complex.log (Ideal.absNorm v.asIdeal : ℂ))‖ = _
        simp only [norm_neg, norm_mul, norm_pow, pow_succ]
        ring
      _ ≤ (2 * ‖heckePrimeLogDerivative K χ v s‖) * R^n :=
        mul_le_mul hn (pow_le_pow_left₀ (norm_nonneg a) haR n)
          (pow_nonneg (norm_nonneg a) n)
          (mul_nonneg (by norm_num) (norm_nonneg _))
  · simp only [heckePrimePowerLogTerm, if_neg hχ, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (pow_nonneg hR0 n)

#check heckePrimePowerLogTerm_sigma_summable
#print axioms heckePrimePowerLogTerm_sigma_summable

/-- Unconditional single-series arithmetic formula for the genuine L logarithmic
 derivative. Absolute convergence justifies the prime/power rearrangement. -/
theorem finiteHeckeL_logDeriv_eq_primePower_sigma (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s =
      ∑' p : (Σ _v : FinitePlace K, ℕ), heckePrimePowerLogTerm K χ p.1 s p.2 := by
  rw [finiteHeckeL_logDeriv_eq_primePower_tsum K χ s hs]
  exact (heckePrimePowerLogTerm_sigma_summable K χ s hs).tsum_sigma.symm

#check finiteHeckeL_logDeriv_eq_primePower_sigma
#print axioms finiteHeckeL_logDeriv_eq_primePower_sigma

/-- An explicit uniform majorant for the genuine prime-power series on a closed
right half-plane, needed for the initial-domain cutoff limit in the divisor argument. -/
theorem heckePrimePowerLogTerm_norm_le_real (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (s : ℂ) (σ : ℝ) (hs : σ ≤ s.re) (n : ℕ) :
    ‖heckePrimePowerLogTerm K χ v s n‖ ≤
      ‖heckePrimePowerLogTerm K χ v (σ : ℂ) n‖ := by
  classical
  by_cases hχ : IsUnramified K χ v
  · have he (z : ℂ) : ‖heckePrimePowerLogTerm K χ v z n‖ =
        ((Ideal.absNorm v.asIdeal : ℝ)^(-z.re))^(n+1) *
          ‖Complex.log (Ideal.absNorm v.asIdeal : ℂ)‖ := by
      rw [heckePrimePowerLogTerm, if_pos hχ, norm_neg, norm_mul, norm_pow,
        heckeEulerTerm_norm]
    rw [he, he, Complex.ofReal_re]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast le_of_lt
        (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)
    · exact neg_le_neg hs
  · simp only [heckePrimePowerLogTerm, if_neg hχ, norm_zero, le_refl]

/-- A summable arithmetic majorant, uniform over each closed half-plane Re(s)≥σ>1.
This supplies the prime-power domination required for the initial-domain limit. -/
theorem heckePrimePowerLogTerm_uniform_summable_majorant (χ : UnitaryHeckeCharacter K)
    (σ : ℝ) (hσ : 1 < σ) :
    ∃ M : (Σ _v : FinitePlace K, ℕ) → ℝ, Summable M ∧
      ∀ s : ℂ, σ ≤ s.re → ∀ p : (Σ _v : FinitePlace K, ℕ),
        ‖heckePrimePowerLogTerm K χ p.1 s p.2‖ ≤ M p := by
  refine ⟨(fun p => ‖heckePrimePowerLogTerm K χ p.1 (σ : ℂ) p.2‖),
    (heckePrimePowerLogTerm_sigma_summable K χ (σ : ℂ) (by simpa using hσ)).norm, ?_⟩
  intro s hs p
  exact heckePrimePowerLogTerm_norm_le_real K χ p.1 s σ hs p.2

#check heckePrimePowerLogTerm_norm_le_real
#print axioms heckePrimePowerLogTerm_norm_le_real
#check heckePrimePowerLogTerm_uniform_summable_majorant
#print axioms heckePrimePowerLogTerm_uniform_summable_majorant

/-- Uniform convergence of the genuine prime-power series on Re(s)≥σ>1.
Combined with finiteHeckeL_logDeriv_eq_primePower_sigma, its limit is L′/L there. -/
theorem heckePrimePowerLogTerm_hasSumUniformlyOn (χ : UnitaryHeckeCharacter K)
    (σ : ℝ) (hσ : 1 < σ) :
    HasSumUniformlyOn
      (fun p : (Σ _v : FinitePlace K, ℕ) => fun s : ℂ =>
        heckePrimePowerLogTerm K χ p.1 s p.2)
      (fun s : ℂ => ∑' p : (Σ _v : FinitePlace K, ℕ),
        heckePrimePowerLogTerm K χ p.1 s p.2)
      {s : ℂ | σ ≤ s.re} := by
  obtain ⟨M, hM, hb⟩ := heckePrimePowerLogTerm_uniform_summable_majorant K χ σ hσ
  exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    (tendstoUniformlyOn_tsum hM (fun p s hs => hb s hs p))

#check heckePrimePowerLogTerm_hasSumUniformlyOn
#print axioms heckePrimePowerLogTerm_hasSumUniformlyOn

/-- The genuine arithmetic series converges uniformly to the actual L′/L,
not merely to an unidentified infinite sum, throughout every closed initial half-plane. -/
theorem finiteHeckeL_logDeriv_hasSumUniformlyOn (χ : UnitaryHeckeCharacter K)
    (σ : ℝ) (hσ : 1 < σ) :
    HasSumUniformlyOn
      (fun p : (Σ _v : FinitePlace K, ℕ) => fun s : ℂ =>
        heckePrimePowerLogTerm K χ p.1 s p.2)
      (fun s : ℂ => deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)
      {s : ℂ | σ ≤ s.re} := by
  apply (heckePrimePowerLogTerm_hasSumUniformlyOn K χ σ hσ).congr_right
  intro s hs
  exact (finiteHeckeL_logDeriv_eq_primePower_sigma K χ s (lt_of_lt_of_le hσ hs)).symm

#check finiteHeckeL_logDeriv_hasSumUniformlyOn
#print axioms finiteHeckeL_logDeriv_hasSumUniformlyOn

/-- Bounded arithmetic cutoffs tend to the genuine logarithmic derivative on its
initial half-plane. This supplies the cutoff step of manuscript §1.4.4; the
mollifier, global continuation and divisor identification are not assumed here. -/
theorem finiteHeckeL_logDeriv_cutoff_tendsto (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re)
    (c : ℕ → (Σ _v : FinitePlace K, ℕ) → ℂ)
    (hc : ∀ j p, ‖c j p‖ ≤ 1)
    (hlim : ∀ p, Filter.Tendsto (fun j => c j p) Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun j => ∑' p : (Σ _v : FinitePlace K, ℕ),
        c j p * heckePrimePowerLogTerm K χ p.1 s p.2)
      Filter.atTop (nhds (deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)) := by
  rw [finiteHeckeL_logDeriv_eq_primePower_sigma K χ s hs]
  apply tendsto_tsum_of_dominated_convergence
    (heckePrimePowerLogTerm_sigma_summable K χ s hs).norm
  · intro p
    simpa only [one_mul] using
      (hlim p).mul_const (heckePrimePowerLogTerm K χ p.1 s p.2)
  · exact Filter.Eventually.of_forall (fun j p => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc j p))

#check finiteHeckeL_logDeriv_cutoff_tendsto
#print axioms finiteHeckeL_logDeriv_cutoff_tendsto

/-- Sharp arithmetic norm cutoffs for the genuine logarithmic derivative. -/
theorem finiteHeckeL_logDeriv_normCutoff_tendsto (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Filter.Tendsto
      (fun j : ℕ => ∑' p : (Σ _v : FinitePlace K, ℕ),
        (if Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) ≤ j then (1 : ℂ) else 0) *
          heckePrimePowerLogTerm K χ p.1 s p.2)
      Filter.atTop (nhds (deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)) := by
  classical
  apply finiteHeckeL_logDeriv_cutoff_tendsto K χ s hs
  · intro j p
    split_ifs <;> simp
  · intro p
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop
      (Ideal.absNorm p.1.asIdeal ^ (p.2 + 1))] with j hj
    simp only [if_pos hj]

#check finiteHeckeL_logDeriv_normCutoff_tendsto
#print axioms finiteHeckeL_logDeriv_normCutoff_tendsto

theorem heckePrimePower_norm_exponent_lt (v : FinitePlace K) (n : ℕ) :
    n < Ideal.absNorm v.asIdeal ^ (n + 1) := by
  have hq := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  induction n with
  | zero => simpa using lt_trans Nat.zero_lt_one hq
  | succ n ih =>
    rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
    nlinarith

/-- Every bound contains only finitely many genuine prime-ideal powers. -/
theorem heckePrimePower_norm_bounded_finite (j : ℕ) :
    {p : (Σ _v : FinitePlace K, ℕ) |
      Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) ≤ j}.Finite := by
  let f : (Σ _v : FinitePlace K, ℕ) → Ideal (𝓞 K) × ℕ :=
    fun p => (p.1.asIdeal, p.2)
  have hi : Function.Injective f := by
    intro a b h
    exact Sigma.ext (IsDedekindDomain.HeightOneSpectrum.ext (congrArg Prod.fst h))
      (heq_of_eq (congrArg Prod.snd h))
  have hf := (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) j).prod (Set.finite_Iio j)
  apply (hf.preimage hi.injOn).subset
  intro p hp
  exact ⟨le_trans (Nat.le_pow (Nat.succ_pos p.2)) hp,
    lt_of_lt_of_le (heckePrimePower_norm_exponent_lt K p.1 p.2) hp⟩

#check heckePrimePower_norm_exponent_lt
#print axioms heckePrimePower_norm_exponent_lt
#check heckePrimePower_norm_bounded_finite
#print axioms heckePrimePower_norm_bounded_finite

/-- Exact finite truncations of the genuine arithmetic prime-power index. -/
noncomputable def heckePrimePowerNormFinset (j : ℕ) : Finset (Σ _v : FinitePlace K, ℕ) :=
  (heckePrimePower_norm_bounded_finite K j).toFinset

theorem heckeNormCutoff_tsum_eq_sum (j : ℕ)
    (f : (Σ _v : FinitePlace K, ℕ) → ℂ) :
    (∑' p, (if Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) ≤ j then (1 : ℂ) else 0) * f p) =
      ∑ p ∈ heckePrimePowerNormFinset K j, f p := by
  classical
  have hm (p : (Σ _v : FinitePlace K, ℕ)) :
      p ∈ heckePrimePowerNormFinset K j ↔
        Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) ≤ j := by
    exact (heckePrimePower_norm_bounded_finite K j).mem_toFinset
  rw [tsum_eq_sum (s := heckePrimePowerNormFinset K j) (fun p hp => by
    simp only [if_neg ((hm p).not.mp hp), zero_mul])]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [if_pos ((hm p).mp hp), one_mul]

/-- Genuine finite prime-power norm truncations converge to the actual L′/L
for all number fields and unitary Hecke characters in the initial half-plane. -/
theorem finiteHeckeL_logDeriv_normFinset_tendsto (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Filter.Tendsto
      (fun j : ℕ => ∑ p ∈ heckePrimePowerNormFinset K j,
        heckePrimePowerLogTerm K χ p.1 s p.2)
      Filter.atTop (nhds (deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)) := by
  simpa only [heckeNormCutoff_tsum_eq_sum] using
    finiteHeckeL_logDeriv_normCutoff_tendsto K χ s hs

#check heckeNormCutoff_tsum_eq_sum
#print axioms heckeNormCutoff_tsum_eq_sum
#check finiteHeckeL_logDeriv_normFinset_tendsto
#print axioms finiteHeckeL_logDeriv_normFinset_tendsto

/-- Bounded arithmetic bump cutoffs converge uniformly to the genuine L′/L
on each closed initial half-plane. This is the bump limit in §1.4.4 only. -/
theorem finiteHeckeL_logDeriv_boundedCutoff_tendstoUniformlyOn
    (χ : UnitaryHeckeCharacter K) (σ : ℝ) (hσ : 1 < σ)
    (c : ℕ → (Σ _v : FinitePlace K, ℕ) → ℂ)
    (hc : ∀ j p, ‖c j p‖ ≤ 1)
    (hlim : ∀ p, Filter.Tendsto (fun j => c j p) Filter.atTop (nhds 1)) :
    TendstoUniformlyOn
      (fun j : ℕ => fun s : ℂ => ∑' p : (Σ _v : FinitePlace K, ℕ),
        c j p * heckePrimePowerLogTerm K χ p.1 s p.2)
      (fun s : ℂ => deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)
      Filter.atTop {s : ℂ | σ ≤ s.re} := by
  let B : (Σ _v : FinitePlace K, ℕ) → ℝ :=
    fun p => ‖heckePrimePowerLogTerm K χ p.1 (σ : ℂ) p.2‖
  have hB : Summable B :=
    (heckePrimePowerLogTerm_sigma_summable K χ (σ : ℂ) (by simpa using hσ)).norm
  have hB0 (p : (Σ _v : FinitePlace K, ℕ)) : 0 ≤ B p := norm_nonneg _
  have hc2 (j : ℕ) (p : (Σ _v : FinitePlace K, ℕ)) : ‖c j p - 1‖ ≤ 2 := by
    have h := norm_sub_le (c j p) (1 : ℂ)
    rw [norm_one] at h
    linarith [hc j p]
  have hb (j : ℕ) (p : (Σ _v : FinitePlace K, ℕ)) :
      ‖‖c j p - 1‖ * B p‖ ≤ 2 * B p := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hB0 p))]
    exact mul_le_mul_of_nonneg_right (hc2 j p) (hB0 p)
  have hE (j : ℕ) : Summable (fun p => ‖c j p - 1‖ * B p) :=
    (hB.mul_left 2).of_norm_bounded (hb j)
  have hT : Filter.Tendsto (fun j => ∑' p, ‖c j p - 1‖ * B p)
      Filter.atTop (nhds 0) := by
    have h := tendsto_tsum_of_dominated_convergence (hB.mul_left 2)
      (fun p => (hlim p).sub_const (1 : ℂ) |>.norm |>.mul_const (B p))
      (Filter.Eventually.of_forall hb)
    simpa using h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with j hj
  intro s hs
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have hS := heckePrimePowerLogTerm_sigma_summable K χ s hs1
  have hC : Summable (fun p : (Σ _v : FinitePlace K, ℕ) =>
      c j p * heckePrimePowerLogTerm K χ p.1 s p.2) := by
    apply hB.of_norm_bounded
    intro p
    rw [norm_mul]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (hc j p))
      (heckePrimePowerLogTerm_norm_le_real K χ p.1 s σ hs p.2)
  rw [dist_comm, dist_eq_norm, finiteHeckeL_logDeriv_eq_primePower_sigma K χ s hs1]
  calc
    ‖(∑' p : (Σ _v : FinitePlace K, ℕ), c j p *
        heckePrimePowerLogTerm K χ p.1 s p.2) -
        ∑' p : (Σ _v : FinitePlace K, ℕ), heckePrimePowerLogTerm K χ p.1 s p.2‖ =
        ‖∑' p : (Σ _v : FinitePlace K, ℕ), (c j p - 1) *
          heckePrimePowerLogTerm K χ p.1 s p.2‖ := by
      congr 1
      simp only [sub_mul, one_mul]
      exact (hC.tsum_sub hS).symm
    _ ≤ ∑' p, ‖c j p - 1‖ * B p := by
      apply tsum_of_norm_bounded (hE j).hasSum
      intro p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (heckePrimePowerLogTerm_norm_le_real K χ p.1 s σ hs p.2) (norm_nonneg _)
    _ < ε := hj

#check finiteHeckeL_logDeriv_boundedCutoff_tendstoUniformlyOn
#print axioms finiteHeckeL_logDeriv_boundedCutoff_tendstoUniformlyOn

/-- Sharp finite norm truncations are a special case of bounded arithmetic cutoffs. -/
theorem finiteHeckeL_logDeriv_normFinset_tendstoUniformlyOn
    (χ : UnitaryHeckeCharacter K) (σ : ℝ) (hσ : 1 < σ) :
    TendstoUniformlyOn
      (fun j : ℕ => fun s : ℂ => ∑ p ∈ heckePrimePowerNormFinset K j,
        heckePrimePowerLogTerm K χ p.1 s p.2)
      (fun s : ℂ => deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)
      Filter.atTop {s : ℂ | σ ≤ s.re} := by
  classical
  have h := finiteHeckeL_logDeriv_boundedCutoff_tendstoUniformlyOn K χ σ hσ
    (fun j p => if Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) ≤ j then (1 : ℂ) else 0)
    (fun j p => by dsimp only; split_ifs <;> simp)
    (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop
        (Ideal.absNorm p.1.asIdeal ^ (p.2 + 1))] with j hj
      simp only [if_pos hj])
  simpa only [heckeNormCutoff_tsum_eq_sum] using h

#check finiteHeckeL_logDeriv_normFinset_tendstoUniformlyOn
#print axioms finiteHeckeL_logDeriv_normFinset_tendstoUniformlyOn

/-- Real bumps from manuscript §1.4.2, evaluated at the actual prime-power norms,
converge uniformly to the genuine L′/L on the initial half-plane. Admissibility
and convolution smoothing are separate obligations, not hypotheses hidden here. -/
theorem finiteHeckeL_logDeriv_realBump_tendstoUniformlyOn
    (χ : UnitaryHeckeCharacter K) (σ : ℝ) (hσ : 1 < σ)
    (h : ℕ → ℝ → ℝ)
    (hb : ∀ j t, 1 < t → 0 ≤ h j t ∧ h j t ≤ 1)
    (hlim : ∀ t : ℝ, 1 < t →
      Filter.Tendsto (fun j => h j t) Filter.atTop (nhds 1)) :
    TendstoUniformlyOn
      (fun j : ℕ => fun s : ℂ => ∑' p : (Σ _v : FinitePlace K, ℕ),
        (h j (Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) : ℝ) : ℂ) *
          heckePrimePowerLogTerm K χ p.1 s p.2)
      (fun s : ℂ => deriv (finiteHeckeL K χ) s / finiteHeckeL K χ s)
      Filter.atTop {s : ℂ | σ ≤ s.re} := by
  have hp (p : (Σ _v : FinitePlace K, ℕ)) :
      (1 : ℝ) < (Ideal.absNorm p.1.asIdeal ^ (p.2 + 1) : ℕ) := by
    exact_mod_cast lt_of_lt_of_le
      (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm p.1)
      (Nat.le_pow (Nat.succ_pos p.2))
  apply finiteHeckeL_logDeriv_boundedCutoff_tendstoUniformlyOn K χ σ hσ
  · intro j p
    have ht := hb j _ (by simpa only [Nat.cast_pow] using hp p)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2
  · intro p
    have ht := hlim _ (by simpa only [Nat.cast_pow] using hp p)
    simpa using (Complex.continuous_ofReal.tendsto 1).comp ht

#check finiteHeckeL_logDeriv_realBump_tendstoUniformlyOn
#print axioms finiteHeckeL_logDeriv_realBump_tendstoUniformlyOn

end MasulloGRH
