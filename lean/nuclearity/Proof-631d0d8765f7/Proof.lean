import Mathlib
open scoped NumberField Valued WithZero
open MeasureTheory TopologicalSpace
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

/-- Compactness of actual valuation-one units, with the remaining arithmetic hypothesis explicit. -/
theorem localValuationUnits_compact_of_finite_residue
    [Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K)))] :
    IsCompact {x : (v.adicCompletion K)ˣ | Valued.v (x : v.adicCompletion K) = 1} := by
  let S : Submonoid (v.adicCompletion K) := (Valued.integer (v.adicCompletion K)).toSubmonoid
  have hc : IsCompact (S : Set (v.adicCompletion K)) :=
    localInteger_compact_of_finite_residue K v
  convert S.units_isCompact hc using 1
  ext x
  symm
  change (Valued.v (x : v.adicCompletion K) ≤ 1 ∧
    Valued.v ((x⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1) ↔ _
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  have hn : Valued.v (x : v.adicCompletion K) ≠ 0 :=
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).ne_zero_iff.mpr x.ne_zero
  rw [inv_le_one₀ (bot_lt_iff_ne_bot.mpr hn)]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- A genuine normalized local multiplicative Haar measure, reduced only to finite residue. -/
theorem exists_normalized_localHaar_of_finite_residue
    [Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K)))]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] :
    ∃ μ : Measure (v.adicCompletion K)ˣ, μ.IsMulLeftInvariant ∧
      μ {x : (v.adicCompletion K)ˣ | Valued.v (x : v.adicCompletion K) = 1} = 1 := by
  let U : Set (v.adicCompletion K)ˣ := {x | Valued.v (x : v.adicCompletion K) = 1}
  have ho : IsOpen U := (Valued.isClopen_sphere (v.adicCompletion K) one_ne_zero).isOpen.preimage
    Units.continuous_val
  let P : PositiveCompacts (v.adicCompletion K)ˣ :=
    ⟨⟨U, localValuationUnits_compact_of_finite_residue K v⟩,
      by rw [ho.interior_eq]; exact ⟨1, by simp [U]⟩⟩
  exact ⟨Measure.haarMeasure P, inferInstance, Measure.haarMeasure_self⟩

#check localInteger_compact_of_finite_residue
#print axioms localInteger_compact_of_finite_residue
#check localValuationUnits_compact_of_finite_residue
#print axioms localValuationUnits_compact_of_finite_residue
#check exists_normalized_localHaar_of_finite_residue
#print axioms exists_normalized_localHaar_of_finite_residue
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

namespace MasulloGRH
open MeasureTheory
open scoped NumberField Valued WithZero
variable (K : Type*) [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
/-- The normalization hypothesis is reduced to the residue field before completion. -/
theorem exists_normalized_localHaar_of_rational_residue
    [Finite (IsLocalRing.ResidueField (v.valuation K).valuationSubring)]
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] :
    ∃ μ : Measure (v.adicCompletion K)ˣ, μ.IsMulLeftInvariant ∧
      μ {x : (v.adicCompletion K)ˣ | Valued.v (x : v.adicCompletion K) = 1} = 1 := by
  letI : Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K))) :=
    localResidue_finite_of_rational_residue K v
  exact exists_normalized_localHaar_of_finite_residue K v
#check exists_normalized_localHaar_of_rational_residue
#print axioms exists_normalized_localHaar_of_rational_residue
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
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
/-- No arithmetic or measure-existence premise remains. -/
theorem exists_normalized_localHaar
    [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ] :
    ∃ μ : Measure (v.adicCompletion K)ˣ, μ.IsMulLeftInvariant ∧
      μ {x : (v.adicCompletion K)ˣ | Valued.v (x : v.adicCompletion K) = 1} = 1 := by
  letI := rationalResidue_finite K v
  exact exists_normalized_localHaar_of_rational_residue K v
#check exists_normalized_localHaar
#print axioms exists_normalized_localHaar
end MasulloGRH


open scoped NumberField Valued WithZero
open MeasureTheory TopologicalSpace
set_option maxHeartbeats 600000

open scoped NumberField Valued WithZero
open MeasureTheory TopologicalSpace
set_option maxHeartbeats 600000
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

/-- Continuity of the actual local unit character. -/
theorem integralLocalCharacter_continuous (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) :
    Continuous (fun u : (v.adicCompletionIntegers K)ˣ =>
      localCharacter K χ v (integralLocalUnit K v u)) := by
  classical
  have hc : Continuous (fun u : (v.adicCompletionIntegers K)ˣ =>
      Function.update (fun w : FinitePlace K => (1 : (w.adicCompletionIntegers K)ˣ)) v u) := by
    apply continuous_pi
    intro w
    by_cases hw : w = v
    · subst w
      simpa using (continuous_id : Continuous (fun u : (v.adicCompletionIntegers K)ˣ => u))
    · simpa [Function.update_of_ne hw] using
        (continuous_const : Continuous (fun _ : (v.adicCompletionIntegers K)ˣ =>
          (1 : (w.adicCompletionIntegers K)ˣ)))
  simpa only [Function.comp_def, integralIdele_update, localCharacter] using
    χ.character.continuous.comp ((integralIdele_continuous K).comp hc)

#check integralLocalCharacter_continuous
#print axioms integralLocalCharacter_continuous
end MasulloGRH


namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Multiplication in the actual integral finite-idelic subgroup. -/
theorem integralIdele_mul
    (u w : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) :
    integralIdele K (u * w) = integralIdele K u * integralIdele K w := by
  apply Units.ext
  apply Prod.ext
  · change (1 : NumberField.InfiniteAdeleRing K) = 1 * 1
    simp
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl

noncomputable def integralCharacterHom (χ : UnitaryHeckeCharacter K) :
    (∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) →* Circle where
  toFun u := χ.character (integralIdele K u)
  map_one' := by
    change χ.character (integralIdele K (fun _ => 1)) = 1
    rw [integralIdele_one, map_one]
  map_mul' u w := by rw [integralIdele_mul, map_mul]

/-- The genuine global character kills the entire infinite tail of integral units. -/
theorem integralCharacter_trivial_tail (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K),
      ∀ u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        (∀ v ∈ S, u v = 1) → χ.character (integralIdele K u) = 1 := by
  classical
  let f := integralCharacterHom K χ
  have hf : Continuous (fun u => (f u : ℂ).re) :=
    Complex.continuous_re.comp (continuous_subtype_val.comp
      (χ.character.continuous.comp (integralIdele_continuous K)))
  have ho : IsOpen {u | 0 < (f u : ℂ).re} := isOpen_lt continuous_const hf
  have h1 : (1 : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ) ∈
      {u | 0 < (f u : ℂ).re} := by simp
  obtain ⟨S, U, hU, hsub⟩ := isOpen_pi_iff.mp ho 1 h1
  refine ⟨S, ?_⟩
  intro u hu
  change f u = 1
  apply circle_eq_one_of_powers_re_nonneg
  intro n
  have hp : u ^ n ∈ (S : Set (FinitePlace K)).pi U := by
    intro v hv
    have hcoord : (u ^ n) v = 1 := by simp [hu v hv]
    rw [hcoord]
    exact (hU v hv).2
  have hh : 0 ≤ (f (u ^ n) : ℂ).re := le_of_lt (hsub hp)
  simpa using hh

#check integralIdele_mul
#print axioms integralIdele_mul
#check integralCharacter_trivial_tail
#print axioms integralCharacter_trivial_tail
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Exact local factorization on every integral finite idele, including tuples
with infinitely many nonidentity coordinates. -/
theorem integralCharacter_finite_factorization (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K),
      ∀ u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ,
        χ.character (integralIdele K u) =
          ∏ v ∈ S, localCharacter K χ v (integralLocalUnit K v (u v)) := by
  classical
  obtain ⟨S, hS⟩ := integralCharacter_trivial_tail K χ
  refine ⟨S, ?_⟩
  intro u
  let f := integralCharacterHom K χ
  let p : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ :=
    ∏ v ∈ S, Function.update 1 v (u v)
  have hp (v : FinitePlace K) (hv : v ∈ S) : p v = u v := by
    simp only [p, Finset.prod_apply]
    rw [Finset.prod_eq_single v]
    · simp
    · intro w _hw hwv
      simp [Function.update_of_ne hwv.symm]
    · intro hn
      exact (hn hv).elim
  have hk : f (u * p⁻¹) = 1 := by
    apply hS
    intro v hv
    change u v * (p v)⁻¹ = 1
    rw [hp v hv, mul_inv_cancel]
  have he : f u = f p := by
    apply mul_inv_eq_one.mp
    simpa only [map_mul, map_inv] using hk
  change f u = _
  rw [he]
  simp only [p, map_prod]
  apply Finset.prod_congr rfl
  intro v _hv
  change χ.character (integralIdele K (Function.update 1 v (u v))) = _
  exact congrArg χ.character (integralIdele_update K v (u v))

#check integralCharacter_finite_factorization
#print axioms integralCharacter_finite_factorization
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

abbrev GenuineFiniteIdeles := (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ

/-- Embed the actual finite ideles with archimedean component one. -/
noncomputable def finiteIdele (x : GenuineFiniteIdeles K) : HeckeIdeles K where
  val := (1, x.val)
  inv := (1, x.inv)
  val_inv := by
    apply Prod.ext
    · exact one_mul 1
    · exact x.val_inv
  inv_val := by
    apply Prod.ext
    · exact one_mul 1
    · exact x.inv_val

noncomputable def finiteIdeleComponent (x : GenuineFiniteIdeles K)
    (v : FinitePlace K) : (LocalField K v)ˣ where
  val := x.val v
  inv := x.inv v
  val_inv := congrArg (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => a v) x.val_inv
  inv_val := congrArg (fun a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K => a v) x.inv_val

/-- Every actual finite idele is integral and invertibly integral off a finite set. -/
theorem finiteIdele_integral_off_finset (x : GenuineFiniteIdeles K) :
    ∃ T : Finset (FinitePlace K), ∀ v ∉ T,
      x.val v ∈ v.adicCompletionIntegers K ∧ x.inv v ∈ v.adicCompletionIntegers K := by
  classical
  have h := x.val.2.and x.inv.2
  refine ⟨(Filter.eventually_cofinite.mp h).toFinset, ?_⟩
  intro v hv
  simpa using hv

/-- Actual finite-idelic decomposition, with no finite-support assumption on x. -/
theorem finiteIdele_decomposition (x : GenuineFiniteIdeles K) :
    ∃ (T : Finset (FinitePlace K))
      (u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ),
      (∀ v ∈ T, u v = 1) ∧
      (∀ v ∉ T, integralLocalUnit K v (u v) = finiteIdeleComponent K x v) ∧
      finiteIdele K x =
        (∏ v ∈ T, localIdele K v (finiteIdeleComponent K x v)) * integralIdele K u := by
  classical
  obtain ⟨T, hT⟩ := finiteIdele_integral_off_finset K x
  let u : ∀ v : FinitePlace K, (v.adicCompletionIntegers K)ˣ := fun v =>
    if hv : v ∈ T then 1 else
      { val := ⟨x.val v, (hT v hv).1⟩
        inv := ⟨x.inv v, (hT v hv).2⟩
        val_inv := Subtype.ext ((finiteIdeleComponent K x v).val_inv)
        inv_val := Subtype.ext ((finiteIdeleComponent K x v).inv_val) }
  have hu (v : FinitePlace K) (hv : v ∈ T) : u v = 1 := by simp [u, hv]
  have hu' (v : FinitePlace K) (hv : v ∉ T) :
      integralLocalUnit K v (u v) = finiteIdeleComponent K x v := by
    apply Units.ext
    simp [u, hv, integralLocalUnit, finiteIdeleComponent]
  refine ⟨T, u, hu, hu', ?_⟩
  apply Units.ext
  apply Prod.ext
  · let ev : HeckeIdeles K →* NumberField.InfiniteAdeleRing K :=
      { toFun := fun a => a.val.1
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    change (1 : NumberField.InfiniteAdeleRing K) = ev
      ((∏ v ∈ T, localIdele K v (finiteIdeleComponent K x v)) * integralIdele K u)
    rw [map_mul, map_prod]
    change (1 : NumberField.InfiniteAdeleRing K) = (∏ _v ∈ T, 1) * 1
    simp
  · apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro w
    let ev : HeckeIdeles K →* LocalField K w :=
      { toFun := fun a => a.val.2 w
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    change x.val w = ev
      ((∏ v ∈ T, localIdele K v (finiteIdeleComponent K x v)) * integralIdele K u)
    rw [map_mul, map_prod]
    change x.val w =
      (∏ v ∈ T, Function.update (fun z : FinitePlace K => (1 : LocalField K z)) v
        (x.val v) w) * ((u w).val : LocalField K w)
    by_cases hw : w ∈ T
    · rw [hu w hw]
      simp only [Units.val_one, OneMemClass.coe_one, mul_one]
      rw [Finset.prod_eq_single w]
      · simp
      · intro v _hv hvw
        simp [Function.update_of_ne hvw.symm]
      · exact fun hn => (hn hw).elim
    · have hprod : (∏ v ∈ T, Function.update
          (fun z : FinitePlace K => (1 : LocalField K z)) v (x.val v) w) = 1 := by
        apply Finset.prod_eq_one
        intro v hv
        have hwv : w ≠ v := fun he => hw (he ▸ hv)
        simp [Function.update_of_ne hwv]
      rw [hprod, one_mul]
      exact (congrArg Units.val (hu' w hw)).symm

#check finiteIdele_integral_off_finset
#print axioms finiteIdele_integral_off_finset
#check finiteIdele_decomposition
#print axioms finiteIdele_decomposition
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Exact factorization of the genuine global character on every finite idele.
The character fixes a finite set S; each idele requires only finitely many extra places. -/
theorem finiteCharacter_finite_factorization (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), ∀ x : GenuineFiniteIdeles K,
      ∃ U : Finset (FinitePlace K), S ⊆ U ∧
        χ.character (finiteIdele K x) =
          ∏ v ∈ U, localCharacter K χ v (finiteIdeleComponent K x v) := by
  classical
  obtain ⟨S, hS⟩ := integralCharacter_finite_factorization K χ
  refine ⟨S, ?_⟩
  intro x
  obtain ⟨T, u, hu, hu', hx⟩ := finiteIdele_decomposition K x
  refine ⟨T ∪ (S \ T), ?_, ?_⟩
  · intro v hv
    by_cases hvt : v ∈ T
    · exact Finset.mem_union_left _ hvt
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hvt⟩)
  · have hred : (∏ v ∈ S, localCharacter K χ v (integralLocalUnit K v (u v))) =
        ∏ v ∈ S \ T, localCharacter K χ v (finiteIdeleComponent K x v) := by
      calc
        _ = ∏ v ∈ S \ T, localCharacter K χ v (integralLocalUnit K v (u v)) := by
          symm
          apply Finset.prod_subset Finset.sdiff_subset
          intro v hv hnot
          have hvt : v ∈ T := by
            by_contra hn
            exact hnot (Finset.mem_sdiff.mpr ⟨hv, hn⟩)
          rw [hu v hvt]
          have hi : integralLocalUnit K v 1 = 1 := by simp [integralLocalUnit]
          rw [hi, localCharacter_one]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [hu' v (Finset.mem_sdiff.mp hv).2]
    have hdis : Disjoint T (S \ T) := by
      apply Finset.disjoint_left.mpr
      intro v hv hvs
      exact (Finset.mem_sdiff.mp hvs).2 hv
    rw [hx, map_mul, map_prod, hS u, hred, Finset.prod_union hdis]
    rfl

#check finiteCharacter_finite_factorization
#print axioms finiteCharacter_finite_factorization
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Exact factorization of the genuine global character on every finite idele.
The character fixes a finite set S; each idele requires only finitely many extra places. -/
theorem finiteCharacter_supported_factorization (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), ∀ x : GenuineFiniteIdeles K,
      ∃ U : Finset (FinitePlace K), S ⊆ U ∧
        (∀ v ∉ U, localCharacter K χ v (finiteIdeleComponent K x v) = 1) ∧
        χ.character (finiteIdele K x) =
          ∏ v ∈ U, localCharacter K χ v (finiteIdeleComponent K x v) := by
  classical
  obtain ⟨S, hS⟩ := integralCharacter_finite_factorization K χ
  refine ⟨S, ?_⟩
  intro x
  obtain ⟨T, u, hu, hu', hx⟩ := finiteIdele_decomposition K x
  refine ⟨T ∪ (S \ T), ?_, ?_, ?_⟩
  · intro v hv
    by_cases hvt : v ∈ T
    · exact Finset.mem_union_left _ hvt
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hvt⟩)
  · intro v hv
    have hvT : v ∉ T := fun ht => hv (Finset.mem_union_left _ ht)
    have hvS : v ∉ S := fun hs => hv
      (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hs, hvT⟩))
    rw [← hu' v hvT]
    change χ.character (localIdele K v (integralLocalUnit K v (u v))) = 1
    rw [← integralIdele_update, hS]
    apply Finset.prod_eq_one
    intro w hw
    have hwv : w ≠ v := by
      intro he
      subst w
      exact hvS hw
    rw [Function.update_of_ne hwv]
    have hi : integralLocalUnit K w 1 = 1 := by simp [integralLocalUnit]
    rw [hi, localCharacter_one]
  · have hred : (∏ v ∈ S, localCharacter K χ v (integralLocalUnit K v (u v))) =
        ∏ v ∈ S \ T, localCharacter K χ v (finiteIdeleComponent K x v) := by
      calc
        _ = ∏ v ∈ S \ T, localCharacter K χ v (integralLocalUnit K v (u v)) := by
          symm
          apply Finset.prod_subset Finset.sdiff_subset
          intro v hv hnot
          have hvt : v ∈ T := by
            by_contra hn
            exact hnot (Finset.mem_sdiff.mpr ⟨hv, hn⟩)
          rw [hu v hvt]
          have hi : integralLocalUnit K v 1 = 1 := by simp [integralLocalUnit]
          rw [hi, localCharacter_one]
        _ = _ := by
          apply Finset.prod_congr rfl
          intro v hv
          rw [hu' v (Finset.mem_sdiff.mp hv).2]
    have hdis : Disjoint T (S \ T) := by
      apply Finset.disjoint_left.mpr
      intro v hv hvs
      exact (Finset.mem_sdiff.mp hvs).2 hv
    rw [hx, map_mul, map_prod, hS u, hred, Finset.prod_union hdis]
    rfl

#check finiteCharacter_supported_factorization
#print axioms finiteCharacter_supported_factorization
end MasulloGRH

/- Finite ramification from B r33 checked source (originating in F). -/
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
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
open scoped NumberField Valued WithZero
variable (K : Type*) [Field K] [NumberField K]
def localShell (v : FinitePlace K) (n : ℕ) : Set (LocalField K v)ˣ :=
  {x | Valued.v (x : LocalField K v) =
    Valued.v ((localUniformizer K v ^ n : (LocalField K v)ˣ) : LocalField K v)}

noncomputable def finiteLocalTest (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) : (LocalField K v)ˣ → ℂ := by
  classical
  exact if IsUnramified K χ v then
    {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) ≤ 1}.indicator (fun _ => 1)
  else (localShell K v 0).indicator (fun x => (localCharacter K χ v x : ℂ)⁻¹)


/-- Extension to the actual additive local field, with the correct value at zero. -/
noncomputable def finiteLocalAdditiveTest (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (x : LocalField K v) : ℂ := by
  classical
  exact if hx : x = 0 then (if IsUnramified K χ v then 1 else 0)
    else finiteLocalTest K χ v (Units.mk0 x hx)

theorem finiteLocalAdditiveTest_restrict (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    finiteLocalAdditiveTest K χ v x = finiteLocalTest K χ v x := by
  classical
  simp only [finiteLocalAdditiveTest, dif_neg x.ne_zero]
  congr 1
  exact Units.ext rfl

theorem finiteLocalAdditiveTest_support (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) :
    Function.support (finiteLocalAdditiveTest K χ v) ⊆
      {x : LocalField K v | Valued.v x ≤ 1} := by
  classical
  intro x hx
  by_contra hv
  change ¬ Valued.v x ≤ 1 at hv
  have hz : x ≠ 0 := by intro hz; apply hv; simp [hz]
  have hn : Valued.v x ≠ 1 := fun h => hv h.le
  have he : finiteLocalAdditiveTest K χ v x = 0 := by
    by_cases hχ : IsUnramified K χ v
    · simp [finiteLocalAdditiveTest, hz, finiteLocalTest, hχ, hv]
    · simp [finiteLocalAdditiveTest, hz, finiteLocalTest, hχ, localShell, hn]
  exact hx he


end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The repaired unramified identity compares the actual additive extension. -/
theorem finiteLocalAdditiveTest_unramified (χ : UnitaryHeckeCharacter K)
    (v : FinitePlace K) (hχ : IsUnramified K χ v) :
    finiteLocalAdditiveTest K χ v =
      {x : LocalField K v | Valued.v x ≤ 1}.indicator (fun _ => (1 : ℂ)) := by
  classical
  funext x
  by_cases hx : x = 0
  · subst x
    simp [finiteLocalAdditiveTest, hχ]
  · by_cases hv : Valued.v x ≤ 1 <;>
      simp [finiteLocalAdditiveTest, hx, finiteLocalTest, hχ, hv]


end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Intrinsic product identity for the genuine character on finite ideles. -/
theorem finiteCharacter_hasProd (χ : UnitaryHeckeCharacter K)
    (x : GenuineFiniteIdeles K) :
    HasProd (fun v => localCharacter K χ v (finiteIdeleComponent K x v))
      (χ.character (finiteIdele K x)) := by
  obtain ⟨S, hS⟩ := finiteCharacter_supported_factorization K χ
  obtain ⟨U, _hSU, htail, heq⟩ := hS x
  rw [heq]
  exact hasProd_prod_of_ne_finset_one htail

/-- The restricted tensor product of the actual additive local Euler tests. -/
noncomputable def finiteAdeleTest (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) : ℂ :=
  ∏' v, finiteLocalAdditiveTest K χ v (a v)

/-- The tensor product has only finitely many nonunit factors at every genuine adele. -/
theorem finiteAdeleTest_finite_support (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :
    {v : FinitePlace K | finiteLocalAdditiveTest K χ v (a v) ≠ 1}.Finite := by
  classical
  have ha : {v : FinitePlace K | ¬ a v ∈ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  apply ((finite_ramification K χ).union ha).subset
  intro v hv
  by_contra hn
  have hχ : IsUnramified K χ v := by simpa using (not_or.mp hn).1
  have hav : a v ∈ v.adicCompletionIntegers K := by simpa using (not_or.mp hn).2
  apply hv
  rw [finiteLocalAdditiveTest_unramified K χ v hχ]
  have hval : Valued.v (a v) ≤ 1 := hav
  exact Set.indicator_of_mem (s := {x : LocalField K v | Valued.v x ≤ 1}) hval
    (fun _ : LocalField K v => (1 : ℂ))

/-- Every finite truncation containing the nonunit factors gives the same actual test. -/
theorem finiteAdeleTest_eq_prod (χ : UnitaryHeckeCharacter K)
    (a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
    (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, finiteLocalAdditiveTest K χ v (a v) = 1) :
    finiteAdeleTest K χ a = ∏ v ∈ S, finiteLocalAdditiveTest K χ v (a v) := by
  exact (hasProd_prod_of_ne_finset_one hS).tprod_eq

#check finiteCharacter_hasProd
#print axioms finiteCharacter_hasProd
#check finiteAdeleTest_finite_support
#print axioms finiteAdeleTest_finite_support
#check finiteAdeleTest_eq_prod
#print axioms finiteAdeleTest_eq_prod
end MasulloGRH


namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- The tensor test vanishes unless every coordinate is an actual local integer. -/
theorem finiteAdeleTest_support (χ : UnitaryHeckeCharacter K) :
    Function.support (finiteAdeleTest K χ) ⊆ Set.range (integralFiniteAdele K) := by
  classical
  intro a ha
  have hfin := finiteAdeleTest_finite_support K χ a
  let S := hfin.toFinset
  have hS : ∀ v ∉ S, finiteLocalAdditiveTest K χ v (a v) = 1 := by
    intro v hv
    simpa [S] using hv
  have hprod : (∏ v ∈ S, finiteLocalAdditiveTest K χ v (a v)) ≠ 0 := by
    rw [← finiteAdeleTest_eq_prod K χ a S hS]
    exact ha
  have hall : ∀ v : FinitePlace K, a v ∈ v.adicCompletionIntegers K := by
    intro v
    by_contra hv
    have hf : finiteLocalAdditiveTest K χ v (a v) = 0 := by
      by_contra hn
      exact hv (finiteLocalAdditiveTest_support K χ v hn)
    have hvS : v ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [hf]
      exact zero_ne_one
    exact hprod (Finset.prod_eq_zero hvS hf)
  refine ⟨(fun v => ⟨a v, hall v⟩), ?_⟩
  apply IsDedekindDomain.FiniteAdeleRing.ext K
  intro v
  rfl


#check finiteAdeleTest_support
#print axioms finiteAdeleTest_support
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- A fixed finite set containing ramification determines the tensor on the compact
integral finite adeles; it is zero outside that actual arithmetic subset. -/
theorem finiteAdeleTest_eq_indicator (χ : UnitaryHeckeCharacter K)
    (S : Finset (FinitePlace K)) (hS : ∀ v ∉ S, IsUnramified K χ v) :
    finiteAdeleTest K χ = (Set.range (integralFiniteAdele K)).indicator
      (fun a => ∏ v ∈ S, finiteLocalAdditiveTest K χ v (a v)) := by
  classical
  funext a
  by_cases ha : a ∈ Set.range (integralFiniteAdele K)
  · rw [Set.indicator_of_mem ha]
    apply finiteAdeleTest_eq_prod
    intro v hv
    obtain ⟨b, rfl⟩ := ha
    rw [finiteLocalAdditiveTest_unramified K χ v (hS v hv)]
    exact Set.indicator_of_mem (s := {x : LocalField K v | Valued.v x ≤ 1}) (b v).property (fun _ : LocalField K v => (1 : ℂ))
  · rw [Set.indicator_of_notMem ha]
    by_contra hn
    exact ha (finiteAdeleTest_support K χ hn)

/-- The finite set in the preceding formula exists for every character in the full scope. -/
theorem finiteAdeleTest_exists_indicator (χ : UnitaryHeckeCharacter K) :
    ∃ S : Finset (FinitePlace K), finiteAdeleTest K χ =
      (Set.range (integralFiniteAdele K)).indicator
        (fun a => ∏ v ∈ S, finiteLocalAdditiveTest K χ v (a v)) := by
  classical
  refine ⟨(finite_ramification K χ).toFinset, finiteAdeleTest_eq_indicator K χ _ ?_⟩
  intro v hv
  simpa using hv

#check finiteAdeleTest_eq_indicator
#print axioms finiteAdeleTest_eq_indicator
#check finiteAdeleTest_exists_indicator
#print axioms finiteAdeleTest_exists_indicator
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

theorem integralFiniteAdele_range :
    Set.range (integralFiniteAdele K) =
      {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v, Valued.v (a v) ≤ 1} := by
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    exact fun v => (u v).property
  · intro h
    refine ⟨(fun v => ⟨a v, h v⟩), ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext K
    intro v
    rfl

/-- Closedness is proved coordinatewise without a new separation assumption. -/
theorem integralFiniteAdeles_isClosed :
    IsClosed (Set.range (integralFiniteAdele K)) := by
  rw [integralFiniteAdele_range]
  simp only [Set.setOf_forall]
  exact isClosed_iInter (fun v =>
    (Valued.isClopen_closedBall (LocalField K v) one_ne_zero).isClosed.preimage
      (RestrictedProduct.continuous_eval v))

theorem integralFiniteAdeles_isCompact :
    IsCompact (Set.range (integralFiniteAdele K)) := by
  letI (v : FinitePlace K) : CompactSpace (v.adicCompletionIntegers K) := by
    letI := rationalResidue_finite K v
    letI : Finite (IsLocalRing.ResidueField (Valued.integer (v.adicCompletion K))) :=
      localResidue_finite_of_rational_residue K v
    exact isCompact_iff_compactSpace.mp (localInteger_compact_of_finite_residue K v)
  exact isCompact_range (integralFiniteAdele_continuous K)

/-- Compact support of the actual finite-adelic restricted tensor. -/
theorem finiteAdeleTest_hasCompactSupport (χ : UnitaryHeckeCharacter K) :
    HasCompactSupport (finiteAdeleTest K χ) := by
  exact (integralFiniteAdeles_isCompact K).of_isClosed_subset isClosed_closure
    (closure_minimal (finiteAdeleTest_support K χ) (integralFiniteAdeles_isClosed K))

#check integralFiniteAdeles_isClosed
#print axioms integralFiniteAdeles_isClosed
#check integralFiniteAdeles_isCompact
#print axioms integralFiniteAdeles_isCompact
#check finiteAdeleTest_hasCompactSupport
#print axioms finiteAdeleTest_hasCompactSupport
end MasulloGRH
