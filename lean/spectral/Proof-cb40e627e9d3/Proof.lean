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
variable (K : Type*) [Field K] [NumberField K]
lemma residueNorm_pos (v : FinitePlace K) : 0 < (v.asIdeal.absNorm : ℝ) := by
  exact_mod_cast lt_trans Nat.zero_lt_one
    (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v)

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

end MasulloGRH

namespace CriticalLineF
/-- Round 5. Discharges the local Euler-factor sign premise of §1.4.4-5.
The positive prime-power expression is MINUS the logarithmic derivative.
Here c and ell are the genuine coefficient and log norm when instantiated. -/
theorem negative_logDeriv_localEuler
    (c ell s : ℂ) (hden : 1 - c * Complex.exp (-s * ell) ≠ 0) :
    -logDeriv (fun z => (1 - c * Complex.exp (-z * ell))⁻¹) s =
      ell * (c * Complex.exp (-s * ell)) / (1 - c * Complex.exp (-s * ell)) := by
  have hq := ((((hasDerivAt_id s).neg).mul_const ell).cexp).const_mul c
  have hd := ((hasDerivAt_const s (1 : ℂ)).sub hq).inv hden
  change -(deriv (fun z => (1 - c * Complex.exp (-z * ell))⁻¹) s /
    (1 - c * Complex.exp (-s * ell))⁻¹) = _
  have hd' := hd.deriv
  change deriv (fun z : ℂ => (1 - c * Complex.exp (-z * ell))⁻¹) s = _ at hd'
  rw [hd']
  dsimp
  field_simp
  ring

/-- Round 5. Derives local prime-power convergence, without assuming a
summability premise. This is the single-place input to the Euler germ in
§1.4.5; the infinite-place derivative interchange is still required. -/
theorem localEuler_primePower_hasSum
    (c ell s : ℂ) (hq : ‖c * Complex.exp (-s * ell)‖ < 1) :
    HasSum (fun n : ℕ => ell * (c * Complex.exp (-s * ell)) ^ (n + 1))
      (-logDeriv (fun z => (1 - c * Complex.exp (-z * ell))⁻¹) s) := by
  have hden : 1 - c * Complex.exp (-s * ell) ≠ 0 := by
    intro h
    have he : c * Complex.exp (-s * ell) = 1 := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hq
    exact (lt_irrefl _ hq)
  rw [negative_logDeriv_localEuler c ell s hden]
  convert (hasSum_geometric_of_norm_lt_one hq).mul_left
    (ell * (c * Complex.exp (-s * ell))) using 1
  · funext n
    simp only [pow_succ]
    ring

#check negative_logDeriv_localEuler
#print axioms negative_logDeriv_localEuler
#check localEuler_primePower_hasSum
#print axioms localEuler_primePower_hasSum
end CriticalLineF


namespace MasulloGRH.Round5F
variable (K : Type*) [Field K] [NumberField K]
/-- Round 5. The genuine unramified local Hecke Euler factor has the signed
prime-power expansion needed by manuscript §1.4.4-5, for every source-defined
unitary Hecke character and Re(s)>1. The norm-disk and summability premises
are proved from the existing arithmetic definitions. This does not interchange
the derivative with the infinite product over places. -/
theorem genuineLocalEuler_primePower_hasSum
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) (s : ℂ)
    (hs : 1 < s.re) (hv : IsUnramified K χ v) :
    HasSum (fun n : ℕ => (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
      ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (n + 1))
      (-logDeriv (heckeEulerFactor K χ v) s) := by
  have hfun : heckeEulerFactor K χ v = fun z =>
      (1 - (localCharacter K χ v (localUniformizer K v) : ℂ) *
        Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)))⁻¹ := by
    funext z
    simp only [heckeEulerFactor, if_pos hv, heckePrimeCoefficient, residue_cpow_eq_exp K]
  rw [hfun]
  have hq := genuinePrimeRatio_norm_lt_one K χ v s hs
  rw [residue_cpow_eq_exp K] at hq
  simpa only [residue_cpow_eq_exp K] using
    CriticalLineF.localEuler_primePower_hasSum
      (localCharacter K χ v (localUniformizer K v) : ℂ)
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) s hq

#check genuineLocalEuler_primePower_hasSum
#print axioms genuineLocalEuler_primePower_hasSum
end MasulloGRH.Round5F

namespace MasulloGRH.Round6F
variable (K : Type*) [Field K] [NumberField K]
/-- Discharges the all-finite-place regularity and signed local-series
premises for the Euler germ in manuscript 1.4.4-5. Ramified factors are the
actual source-defined constant one. No global zero-free or summability
assumption is supplied; differentiation of the infinite product is separate. -/
theorem genuineLocalEuler_regular_and_primePower
    (χ : UnitaryHeckeCharacter K) (v : FinitePlace K) (s : ℂ)
    (hs : 1 < s.re) :
    heckeEulerFactor K χ v s ≠ 0 ∧
    DifferentiableAt ℂ (heckeEulerFactor K χ v) s ∧
    HasSum (fun n : ℕ => if IsUnramified K χ v then
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
      ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (n + 1) else 0)
      (-logDeriv (heckeEulerFactor K χ v) s) := by
  classical
  by_cases hv : IsUnramified K χ v
  · have hfun : heckeEulerFactor K χ v = fun z =>
        (1 - (localCharacter K χ v (localUniformizer K v) : ℂ) *
          Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)))⁻¹ := by
      funext z
      simp only [heckeEulerFactor, if_pos hv, heckePrimeCoefficient, residue_cpow_eq_exp K]
    have hq := genuinePrimeRatio_norm_lt_one K χ v s hs
    rw [residue_cpow_eq_exp K] at hq
    have hden : 1 - (localCharacter K χ v (localUniformizer K v) : ℂ) *
        Complex.exp (-s * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)) ≠ 0 := by
      intro h
      have he := (sub_eq_zero.mp h).symm
      rw [he, norm_one] at hq
      exact lt_irrefl _ hq
    refine ⟨?_, ?_, ?_⟩
    · rw [hfun]
      exact inv_ne_zero hden
    · rw [hfun]
      have hd := ((((hasDerivAt_id s).neg).mul_const
        (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)).cexp).const_mul
        (localCharacter K χ v (localUniformizer K v) : ℂ)
      exact (((hasDerivAt_const s (1 : ℂ)).sub hd).inv hden).differentiableAt
    · simpa only [if_pos hv] using
        Round5F.genuineLocalEuler_primePower_hasSum K χ v s hs hv
  · have hfun : heckeEulerFactor K χ v = fun _ => (1 : ℂ) := by
      funext z
      simp only [heckeEulerFactor, if_neg hv]
    rw [hfun]
    refine ⟨one_ne_zero, differentiableAt_const 1, ?_⟩
    simpa [hv, logDeriv] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

/-- Discharges the finite-truncation denominator condition before passing
from finite logarithmic derivatives to the genuine Euler-product limit.
This proves no nonvanishing statement for the infinite product. -/
theorem partialHeckeEulerProduct_ne_zero
    (χ : UnitaryHeckeCharacter K) (S : Finset (FinitePlace K)) (s : ℂ)
    (hs : 1 < s.re) : partialHeckeEulerProduct K χ S s ≠ 0 := by
  unfold partialHeckeEulerProduct
  exact Finset.prod_ne_zero_iff.mpr fun v _ =>
    (genuineLocalEuler_regular_and_primePower K χ v s hs).1

#check genuineLocalEuler_regular_and_primePower
#print axioms genuineLocalEuler_regular_and_primePower
#check partialHeckeEulerProduct_ne_zero
#print axioms partialHeckeEulerProduct_ne_zero
end MasulloGRH.Round6F

namespace MasulloGRH.Round7F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the finite-product differentiation premise of the Euler germ
in manuscript 1.4.4-5. This elementary rule is used only for genuine factors. -/
theorem logDeriv_mul_at (f g : ℂ → ℂ) (s : ℂ)
    (hf : DifferentiableAt ℂ f s) (hg : DifferentiableAt ℂ g s)
    (hf0 : f s ≠ 0) (hg0 : g s ≠ 0) :
    logDeriv (fun z => f z * g z) s = logDeriv f s + logDeriv g s := by
  change deriv (fun z => f z * g z) s / (f s * g s) =
    deriv f s / f s + deriv g s / g s
  have hd := (hf.hasDerivAt.mul hg.hasDerivAt).deriv
  change deriv (fun z : ℂ => f z * g z) s = _ at hd
  rw [hd]
  field_simp

/-- Finite differentiation of the actual arithmetic Euler product. The
nonvanishing premises are derived, with all unitary characters allowed. -/
theorem partialHeckeEulerProduct_differentiable_logDeriv
    (χ : UnitaryHeckeCharacter K) (S : Finset (FinitePlace K)) (s : ℂ)
    (hs : 1 < s.re) :
    DifferentiableAt ℂ (partialHeckeEulerProduct K χ S) s ∧
    logDeriv (partialHeckeEulerProduct K χ S) s =
      ∑ v ∈ S, logDeriv (heckeEulerFactor K χ v) s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hempty : partialHeckeEulerProduct K χ ∅ = fun _ : ℂ => (1 : ℂ) := by
      funext z
      simp [partialHeckeEulerProduct]
    rw [hempty]
    exact ⟨differentiableAt_const 1, by simp [logDeriv]⟩
  | @insert v S hv ih =>
    have hlocal := Round6F.genuineLocalEuler_regular_and_primePower K χ v s hs
    have hfun : partialHeckeEulerProduct K χ (insert v S) =
        fun z => heckeEulerFactor K χ v z * partialHeckeEulerProduct K χ S z := by
      funext z
      simp [partialHeckeEulerProduct, hv]
    rw [hfun]
    refine ⟨hlocal.2.1.mul ih.1, ?_⟩
    rw [logDeriv_mul_at _ _ s hlocal.2.1 ih.1 hlocal.1
      (Round6F.partialHeckeEulerProduct_ne_zero K χ S s hs), ih.2,
      Finset.sum_insert hv]

/-- New round-7 export. Discharges the FINITE signed prime-power identity
needed before the infinite Euler derivative in section 1.4.5. The only
analytic parameter restriction is Re(s)>1; convergence of every series here
is derived. No infinite-place limit or target zero-free region is assumed. -/
theorem genuineFiniteEuler_negative_logDeriv_hasSum
    (χ : UnitaryHeckeCharacter K) (S : Finset (FinitePlace K)) (s : ℂ)
    (hs : 1 < s.re) :
    partialHeckeEulerProduct K χ S s ≠ 0 ∧
    DifferentiableAt ℂ (partialHeckeEulerProduct K χ S) s ∧
    HasSum (fun n : ℕ => ∑ v ∈ S, if IsUnramified K χ v then
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
      ((localCharacter K χ v (localUniformizer K v) : ℂ) *
        (v.asIdeal.absNorm : ℂ) ^ (-s)) ^ (n + 1) else 0)
      (-logDeriv (partialHeckeEulerProduct K χ S) s) := by
  classical
  have hcalc := partialHeckeEulerProduct_differentiable_logDeriv K χ S s hs
  refine ⟨Round6F.partialHeckeEulerProduct_ne_zero K χ S s hs, hcalc.1, ?_⟩
  rw [hcalc.2, ← Finset.sum_neg_distrib]
  clear hcalc
  induction S using Finset.induction_on with
  | empty => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  | @insert v S hv ih =>
    simpa only [Finset.sum_insert hv] using
      (Round6F.genuineLocalEuler_regular_and_primePower K χ v s hs).2.2.add ih

#check partialHeckeEulerProduct_differentiable_logDeriv
#print axioms partialHeckeEulerProduct_differentiable_logDeriv
#check genuineFiniteEuler_negative_logDeriv_hasSum
#print axioms genuineFiniteEuler_negative_logDeriv_hasSum
end MasulloGRH.Round7F


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

namespace MasulloGRH.Round9F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the logarithmic weight in the independent all-prime majorant
needed for the Euler logarithmic-derivative germ in manuscript 1.4.4-5. -/
theorem finitePlace_log_norm_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun v : FinitePlace K =>
      Real.log (v.asIdeal.absNorm : ℝ) * (v.asIdeal.absNorm : ℝ) ^ (-σ)) := by
  let ε := (σ - 1) / 2
  let κ := (σ + 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hκ : 1 < κ := by dsimp [κ]; linarith
  have hm := (finitePlace_norm_summable K κ hκ).mul_left ε⁻¹
  apply hm.of_norm_bounded
  intro v
  have hq := residueNorm_pos K v
  have hq1 : (1 : ℝ) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.log_nonneg hq1.le) (Real.rpow_nonneg hq.le _))]
  calc
    _ ≤ ((v.asIdeal.absNorm : ℝ) ^ ε / ε) *
        (v.asIdeal.absNorm : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hq.le hε)
        (Real.rpow_nonneg hq.le _)
    _ = ε⁻¹ * (v.asIdeal.absNorm : ℝ) ^ (-κ) := by
      rw [div_eq_mul_inv, mul_right_comm, ← Real.rpow_add hq]
      have he : ε + -σ = -κ := by dsimp [ε, κ]; ring
      rw [he, mul_comm]

/-- Discharges a uniform absolute majorant for the GENUINE local logarithmic
 derivatives, for every unitary character and Re(s)>=σ>1. No critical-strip
 exclusion or summability is assumed. Infinite-product differentiation remains
 a separate limit theorem. -/
theorem genuineLocal_logDeriv_uniform_majorant (σ : ℝ) (hσ : 1 < σ) :
    ∃ B : FinitePlace K → ℝ, Summable B ∧
      ∀ (χ : UnitaryHeckeCharacter K) (s : ℂ), σ ≤ s.re →
        ∀ v, ‖logDeriv (heckeEulerFactor K χ v) s‖ ≤ B v := by
  let c : ℝ := (2 : ℝ) ^ (-σ)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨fun v => (Real.log (v.asIdeal.absNorm : ℝ) *
      (v.asIdeal.absNorm : ℝ) ^ (-σ)) * (1 - c)⁻¹,
    (finitePlace_log_norm_summable K σ hσ).mul_right _, ?_⟩
  intro χ s hs v
  have hs1 : 1 < s.re := lt_of_lt_of_le hσ hs
  have hq := residueNorm_pos K v
  have hq2 : (2 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hl : 0 ≤ Real.log (v.asIdeal.absNorm : ℝ) := Real.log_nonneg (by linarith)
  let r : ℂ := (localCharacter K χ v (localUniformizer K v) : ℂ) *
    (v.asIdeal.absNorm : ℂ) ^ (-s)
  have hr : ‖r‖ = (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by
    dsimp [r]
    rw [norm_mul, Circle.norm_coe, one_mul]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hq (-s)
  have hrσ : ‖r‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-σ) := by
    rw [hr]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hrc : ‖r‖ ≤ c := hrσ.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith))
  have hden : 1 - r ≠ 0 := by
    intro he
    have he' : r = 1 := (sub_eq_zero.mp he).symm
    rw [he', norm_one] at hrc
    exact (not_le_of_gt hc1) hrc
  have hd : 1 - c ≤ ‖1 - r‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) r
    rw [norm_one] at hn
    linarith
  by_cases hv : IsUnramified K χ v
  · have he : -logDeriv (heckeEulerFactor K χ v) s =
        (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * r / (1 - r) := by
      have hf : heckeEulerFactor K χ v = fun z =>
          (1 - (localCharacter K χ v (localUniformizer K v) : ℂ) *
            Complex.exp (-z * (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)))⁻¹ := by
        funext z
        simp [heckeEulerFactor, hv, heckePrimeCoefficient, residue_cpow_eq_exp K]
      rw [hf]
      simpa only [r, residue_cpow_eq_exp K] using
        CriticalLineF.negative_logDeriv_localEuler
          (localCharacter K χ v (localUniformizer K v) : ℂ)
          (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) s
          (by simpa only [r, residue_cpow_eq_exp K] using hden)
    have hn := congrArg norm he
    rw [norm_neg, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hl] at hn
    rw [hn]
    change _ ≤ (Real.log (v.asIdeal.absNorm : ℝ) *
      (v.asIdeal.absNorm : ℝ) ^ (-σ)) * (1 - c)⁻¹
    rw [← div_eq_mul_inv]
    exact div_le_div₀ (mul_nonneg hl (Real.rpow_nonneg hq.le _))
      (mul_le_mul_of_nonneg_left hrσ hl) (by linarith) hd
  · have hf : heckeEulerFactor K χ v = fun _ : ℂ => (1 : ℂ) := by
      funext z
      simp [heckeEulerFactor, hv]
    have hb : 0 ≤ (Real.log (v.asIdeal.absNorm : ℝ) *
        (v.asIdeal.absNorm : ℝ) ^ (-σ)) * (1 - c)⁻¹ :=
      mul_nonneg (mul_nonneg hl (Real.rpow_nonneg hq.le _))
        (inv_nonneg.mpr (by linarith))
    simpa [hf, logDeriv] using hb

#check MasulloGRH.finitePlace_norm_summable
#print axioms MasulloGRH.finitePlace_norm_summable
#check finitePlace_log_norm_summable
#print axioms finitePlace_log_norm_summable
#check genuineLocal_logDeriv_uniform_majorant
#print axioms genuineLocal_logDeriv_uniform_majorant
end MasulloGRH.Round9F

namespace MasulloGRH.Round10F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the normal-convergence premise for the local logarithmic
 derivatives in the Euler overlap of manuscript 1.4.4-5. The convergence is
 uniform simultaneously in every actual unitary Hecke character and the
 whole closed half-plane Re(s)>=sigma>1. The limit is not yet identified
 with the logarithmic derivative of the infinite Euler product. -/
theorem genuineEuler_logDeriv_normal_convergence (σ : ℝ) (hσ : 1 < σ) :
    (∀ (χ : UnitaryHeckeCharacter K) (s : ℂ), σ ≤ s.re →
      Summable (fun v : FinitePlace K => logDeriv (heckeEulerFactor K χ v) s)) ∧
    TendstoUniformlyOn
      (fun S (p : UnitaryHeckeCharacter K × ℂ) =>
        logDeriv (partialHeckeEulerProduct K p.1 S) p.2)
      (fun p => ∑' v : FinitePlace K, logDeriv (heckeEulerFactor K p.1 v) p.2)
      Filter.atTop {p | σ ≤ p.2.re} := by
  obtain ⟨B, hB, hbound⟩ := Round9F.genuineLocal_logDeriv_uniform_majorant K σ hσ
  refine ⟨fun χ s hs => hB.of_norm_bounded (hbound χ s hs), ?_⟩
  have hu := tendstoUniformlyOn_tsum hB
    (f := fun v (p : UnitaryHeckeCharacter K × ℂ) =>
      logDeriv (heckeEulerFactor K p.1 v) p.2)
    (s := {p | σ ≤ p.2.re}) (fun v p hp => hbound p.1 p.2 hp v)
  apply hu.congr
  exact Filter.Eventually.of_forall fun S p hp =>
    (Round7F.partialHeckeEulerProduct_differentiable_logDeriv K p.1 S p.2
      (lt_of_lt_of_le hσ hp)).2.symm

#check genuineEuler_logDeriv_normal_convergence
#print axioms genuineEuler_logDeriv_normal_convergence
end MasulloGRH.Round10F

namespace MasulloGRH.Round10F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges holomorphy on each strictly smaller Euler half-plane using
 the derived all-place majorant; no arithmetic continuation is assumed. -/
theorem genuineEuler_logDerivSum_differentiableOn
    (σ : ℝ) (hσ : 1 < σ) (χ : UnitaryHeckeCharacter K) :
    DifferentiableOn ℂ
      (fun s => ∑' v : FinitePlace K, logDeriv (heckeEulerFactor K χ v) s)
      {s : ℂ | σ < s.re} := by
  have hU : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨B, hB, hbound⟩ := Round9F.genuineLocal_logDeriv_uniform_majorant K σ hσ
  apply Complex.differentiableOn_tsum_of_summable_norm hB ?_ hU
    (fun v s hs => hbound χ s hs.le v)
  intro v
  have hf : DifferentiableOn ℂ (heckeEulerFactor K χ v) {s : ℂ | σ < s.re} := by
    intro s hs
    exact (Round6F.genuineLocalEuler_regular_and_primePower K χ v s
      (lt_trans hσ hs)).2.1.differentiableWithinAt
  exact (hf.deriv hU).div hf (fun s hs =>
    (Round6F.genuineLocalEuler_regular_and_primePower K χ v s (lt_trans hσ hs)).1)

/-- Discharges the holomorphic-sum premise in the original Euler overlap
 Re(s)>1 for every actual unitary Hecke character. Identifying this sum with
 L_f'/L_f still requires nonvanishing and differentiation of the infinite
 product. This theorem neither asserts nor assumes any critical-strip fact. -/
theorem genuineEuler_logDerivSum_holomorphic (χ : UnitaryHeckeCharacter K) :
    AnalyticOnNhd ℂ
      (fun s => ∑' v : FinitePlace K, logDeriv (heckeEulerFactor K χ v) s)
      {s : ℂ | 1 < s.re} := by
  have hU : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd ?_ hU
  intro s hs
  change 1 < s.re at hs
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ((genuineEuler_logDerivSum_differentiableOn K σ hσ χ s hsσ).differentiableAt
    (hopen.mem_nhds hsσ)).differentiableWithinAt

#check genuineEuler_logDerivSum_holomorphic
#print axioms genuineEuler_logDerivSum_holomorphic
end MasulloGRH.Round10F

namespace MasulloGRH.Round11F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges absolute Euler-product convergence and inverse control in the
Euler-overlap premise of manuscript 1.4.4-5. The bounds are uniform in ALL
actual unitary characters and Re(s)>=sigma>1, with no summability assumption. -/
theorem genuineEuler_deviation_uniform_majorant (σ : ℝ) (hσ : 1 < σ) :
    ∃ B C : FinitePlace K → ℝ, Summable B ∧ Summable C ∧
      ∀ (χ : UnitaryHeckeCharacter K) (s : ℂ), σ ≤ s.re → ∀ v,
        ‖heckeEulerFactor K χ v s - 1‖ ≤ B v ∧
        ‖(heckeEulerFactor K χ v s)⁻¹ - 1‖ ≤ C v := by
  let c : ℝ := (2 : ℝ) ^ (-σ)
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨fun v => (v.asIdeal.absNorm : ℝ) ^ (-σ) * (1 - c)⁻¹,
    fun v => (v.asIdeal.absNorm : ℝ) ^ (-σ),
    (finitePlace_norm_summable K σ hσ).mul_right _,
    finitePlace_norm_summable K σ hσ, ?_⟩
  intro χ s hs v
  have hq := residueNorm_pos K v
  have hq2 : (2 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  let r : ℂ := heckePrimeCoefficient K χ v * (v.asIdeal.absNorm : ℂ) ^ (-s)
  have hr : ‖r‖ = (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by
    dsimp [r]
    rw [norm_mul, heckePrimeCoefficient_norm, one_mul]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hq (-s)
  have hrσ : ‖r‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-σ) := by
    rw [hr]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hrc : ‖r‖ ≤ c := hrσ.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith))
  have hden : 1 - r ≠ 0 := by
    intro he
    have he' : r = 1 := (sub_eq_zero.mp he).symm
    rw [he', norm_one] at hrc
    exact (not_le_of_gt hc1) hrc
  have hd : 1 - c ≤ ‖1 - r‖ := by
    have hn := norm_sub_norm_le (1 : ℂ) r
    rw [norm_one] at hn
    linarith
  by_cases hv : IsUnramified K χ v
  · have hf : heckeEulerFactor K χ v s = (1 - r)⁻¹ := by
      simp [heckeEulerFactor, hv, r]
    rw [hf]
    constructor
    · have he : (1 - r)⁻¹ - 1 = r / (1 - r) := by
        field_simp [hden]
        ring
      rw [he, norm_div]
      change _ ≤ (v.asIdeal.absNorm : ℝ) ^ (-σ) * (1 - c)⁻¹
      rw [← div_eq_mul_inv]
      exact div_le_div₀ (Real.rpow_nonneg hq.le _) hrσ (by linarith) hd
    · simpa only [inv_inv, sub_sub_cancel_left, norm_neg] using hrσ
  · have hf : heckeEulerFactor K χ v s = 1 := by
      simp [heckeEulerFactor, hv]
    have hb : 0 ≤ (v.asIdeal.absNorm : ℝ) ^ (-σ) * (1 - c)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg hq.le _) (inv_nonneg.mpr (by linarith))
    simpa [hf] using And.intro hb (Real.rpow_nonneg hq.le (-σ))

/-- Discharges pointwise convergence to a NONZERO genuine Euler product in
Re(s)>1, needed before dividing the derivative of that product in 1.4.5.
The inverse product is independently convergent; no zero-free region beyond
the classical Euler overlap is asserted or assumed. -/
theorem genuineEuler_product_converges_nonzero
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun v : FinitePlace K => heckeEulerFactor K χ v s)
      (finiteHeckeL K χ s) ∧ finiteHeckeL K χ s ≠ 0 := by
  obtain ⟨B, C, hB, hC, hbound⟩ :=
    genuineEuler_deviation_uniform_majorant K s.re hs
  have hb : Summable (fun v : FinitePlace K => ‖heckeEulerFactor K χ v s - 1‖) :=
    hB.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => (hbound χ s le_rfl v).1)
  have hc : Summable (fun v : FinitePlace K => ‖(heckeEulerFactor K χ v s)⁻¹ - 1‖) :=
    hC.of_nonneg_of_le (fun _ => norm_nonneg _) (fun v => (hbound χ s le_rfl v).2)
  have hp : Multipliable (fun v : FinitePlace K => heckeEulerFactor K χ v s) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hb
  have hi : Multipliable (fun v : FinitePlace K => (heckeEulerFactor K χ v s)⁻¹) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hc
  refine ⟨hp.hasProd, ?_⟩
  have hmul := hp.hasProd.mul hi.hasProd
  have he : (fun v : FinitePlace K => heckeEulerFactor K χ v s *
      (heckeEulerFactor K χ v s)⁻¹) = fun _ => (1 : ℂ) := by
    funext v
    exact mul_inv_cancel₀ (Round6F.genuineLocalEuler_regular_and_primePower K χ v s hs).1
  rw [he] at hmul
  have hone : (∏' v : FinitePlace K, heckeEulerFactor K χ v s) *
      (∏' v : FinitePlace K, (heckeEulerFactor K χ v s)⁻¹) = 1 :=
    hmul.unique hasProd_one
  intro hz
  change (∏' v : FinitePlace K, heckeEulerFactor K χ v s) = 0 at hz
  rw [hz, zero_mul] at hone
  exact zero_ne_one hone

#check genuineEuler_deviation_uniform_majorant
#print axioms genuineEuler_deviation_uniform_majorant
#check genuineEuler_product_converges_nonzero
#print axioms genuineEuler_product_converges_nonzero
end MasulloGRH.Round11F

namespace MasulloGRH.Round11F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the normal-product limit premise needed to differentiate the
actual Euler product in manuscript 1.4.4-5, on every smaller Euler half-plane. -/
theorem genuineEuler_product_locallyUniform
    (σ : ℝ) (hσ : 1 < σ) (χ : UnitaryHeckeCharacter K) :
    TendstoLocallyUniformlyOn (fun S => partialHeckeEulerProduct K χ S)
      (finiteHeckeL K χ) Filter.atTop {s : ℂ | σ < s.re} := by
  have hU : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  obtain ⟨B, C, hB, hC, hbound⟩ := genuineEuler_deviation_uniform_majorant K σ hσ
  have hu := Summable.hasProdLocallyUniformlyOn_one_add hU hB
    (f := fun v s => heckeEulerFactor K χ v s - 1)
    (Filter.Eventually.of_forall (fun v s hs => (hbound χ s hs.le v).1))
    (fun v s hs =>
      ((Round6F.genuineLocalEuler_regular_and_primePower K χ v s
        (lt_trans hσ hs)).2.1.continuousAt.sub continuousAt_const).continuousWithinAt)
  have hu' : HasProdLocallyUniformlyOn (fun v s => heckeEulerFactor K χ v s)
      (finiteHeckeL K χ) {s : ℂ | σ < s.re} := by
    simpa only [add_sub_cancel, finiteHeckeL] using hu
  exact hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hu'

/-- Discharges holomorphy of the genuine product on each smaller Euler domain. -/
theorem genuineEuler_product_differentiableOn
    (σ : ℝ) (hσ : 1 < σ) (χ : UnitaryHeckeCharacter K) :
    DifferentiableOn ℂ (finiteHeckeL K χ) {s : ℂ | σ < s.re} := by
  apply (genuineEuler_product_locallyUniform K σ hσ χ).differentiableOn
    (Filter.Eventually.of_forall (fun S s hs =>
      (Round7F.partialHeckeEulerProduct_differentiable_logDeriv K χ S s
        (lt_trans hσ hs)).1.differentiableWithinAt))
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Discharges the holomorphic NONZERO arithmetic Euler germ premise in
1.4.5 for every genuine unitary character; no continuation is assumed. -/
theorem genuineEuler_holomorphic_nonzero (χ : UnitaryHeckeCharacter K) :
    AnalyticOnNhd ℂ (finiteHeckeL K χ) {s : ℂ | 1 < s.re} ∧
      ∀ s : ℂ, 1 < s.re → finiteHeckeL K χ s ≠ 0 := by
  refine ⟨?_, fun s hs => (genuineEuler_product_converges_nonzero K χ s hs).2⟩
  have hU : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd ?_ hU
  intro s hs
  change 1 < s.re at hs
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ((genuineEuler_product_differentiableOn K σ hσ χ s hsσ).differentiableAt
    (hopen.mem_nhds hsσ)).differentiableWithinAt

#check genuineEuler_product_locallyUniform
#print axioms genuineEuler_product_locallyUniform
#check genuineEuler_holomorphic_nonzero
#print axioms genuineEuler_holomorphic_nonzero
end MasulloGRH.Round11F


namespace MasulloGRH.Round12F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the derivative-limit premise in manuscript 1.4.4-5 for the
actual Euler product, on each strictly smaller classical Euler half-plane. -/
theorem genuineEuler_derivative_locallyUniform
    (σ : ℝ) (hσ : 1 < σ) (χ : UnitaryHeckeCharacter K) :
    TendstoLocallyUniformlyOn
      (fun S => deriv (partialHeckeEulerProduct K χ S))
      (deriv (finiteHeckeL K χ)) Filter.atTop {s : ℂ | σ < s.re} := by
  exact (Round11F.genuineEuler_product_locallyUniform K σ hσ χ).deriv
    (Filter.Eventually.of_forall (fun S s hs =>
      (Round7F.partialHeckeEulerProduct_differentiable_logDeriv K χ S s
        (lt_trans hσ hs)).1.differentiableWithinAt))
    (isOpen_lt continuous_const Complex.continuous_re)

/-- Discharges the actual infinite-product logarithmic-derivative identity
needed in the Euler overlap of manuscript 1.4.5. Neither summability nor
nonvanishing is assumed; both were derived for the genuine arithmetic factors.
This statement has no critical-strip or analytic-continuation premise. -/
theorem genuineEuler_logDeriv_eq_tsum
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun v : FinitePlace K => logDeriv (heckeEulerFactor K χ v) s) ∧
      logDeriv (finiteHeckeL K χ) s =
        ∑' v : FinitePlace K, logDeriv (heckeEulerFactor K χ v) s := by
  let σ : ℝ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hp := (Round11F.genuineEuler_product_locallyUniform K σ hσ χ).tendsto_at hsσ
  have hd := (genuineEuler_derivative_locallyUniform K σ hσ χ).tendsto_at hsσ
  have hn := (Round11F.genuineEuler_product_converges_nonzero K χ s hs).2
  have hq : Filter.Tendsto
      (fun S : Finset (FinitePlace K) => logDeriv (partialHeckeEulerProduct K χ S) s)
      Filter.atTop (nhds (logDeriv (finiteHeckeL K χ) s)) := by
    simpa only [logDeriv, Pi.div_apply] using hd.div hp hn
  have hsum := Round10F.genuineEuler_logDeriv_normal_convergence K σ hσ
  exact ⟨hsum.1 χ s hsσ.le,
    tendsto_nhds_unique hq (hsum.2.tendsto_at (x := (χ, s)) hsσ.le)⟩

#check genuineEuler_derivative_locallyUniform
#print axioms genuineEuler_derivative_locallyUniform
#check genuineEuler_logDeriv_eq_tsum
#print axioms genuineEuler_logDeriv_eq_tsum
end MasulloGRH.Round12F

namespace MasulloGRH.Round13F
variable (K : Type*) [Field K] [NumberField K]

/-- The actual finite-place prime-power summand, with the original ramification
convention. This is shorthand for the summand already checked in Round6F. -/
noncomputable def genuinePrimePowerTerm (χ : UnitaryHeckeCharacter K)
    (s : ℂ) (p : FinitePlace K × ℕ) : ℂ :=
  if IsUnramified K χ p.1 then
    (Real.log (p.1.asIdeal.absNorm : ℝ) : ℂ) *
      ((localCharacter K χ p.1 (localUniformizer K p.1) : ℂ) *
        (p.1.asIdeal.absNorm : ℂ) ^ (-s)) ^ (p.2 + 1) else 0

/-- Discharges the character-uniform absolute place-by-power majorant required
before interchanging the finite-place sum and cutoff limit in 1.4.4-5.
The bound is derived arithmetically, only on the classical Euler half-plane. -/
theorem genuinePrimePower_uniform_majorant (σ : ℝ) (hσ : 1 < σ) :
    ∃ B : FinitePlace K × ℕ → ℝ, Summable B ∧
      ∀ (χ : UnitaryHeckeCharacter K) (s : ℂ), σ ≤ s.re →
        ∀ p, ‖genuinePrimePowerTerm K χ s p‖ ≤ B p := by
  let c : ℝ := (2 : ℝ) ^ (-σ)
  let A : FinitePlace K → ℝ := fun v =>
    Real.log (v.asIdeal.absNorm : ℝ) * (v.asIdeal.absNorm : ℝ) ^ (-σ)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun n : ℕ => c ^ n) :=
    (hasSum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hc0] using hc1)).summable
  have hA0 : ∀ v, 0 ≤ A v := by
    intro v
    have hq2 : (2 : ℝ) ≤ v.asIdeal.absNorm := by
      exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    exact mul_nonneg (Real.log_nonneg (by linarith))
      (Real.rpow_nonneg (by linarith) _)
  have hB : Summable (fun p : FinitePlace K × ℕ => A p.1 * c ^ p.2) :=
    (Round9F.finitePlace_log_norm_summable K σ hσ).mul_of_nonneg hgeom
      hA0 (fun n => pow_nonneg hc0 n)
  refine ⟨fun p => A p.1 * c ^ p.2, hB, ?_⟩
  intro χ s hs
  rintro ⟨v, n⟩
  have hq := residueNorm_pos K v
  have hq2 : (2 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hl : 0 ≤ Real.log (v.asIdeal.absNorm : ℝ) := Real.log_nonneg (by linarith)
  let r : ℂ := (localCharacter K χ v (localUniformizer K v) : ℂ) *
    (v.asIdeal.absNorm : ℂ) ^ (-s)
  have hr : ‖r‖ = (v.asIdeal.absNorm : ℝ) ^ (-s.re) := by
    dsimp [r]
    rw [norm_mul, Circle.norm_coe, one_mul]
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hq (-s)
  have hrσ : ‖r‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-σ) := by
    rw [hr]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hrc : ‖r‖ ≤ c := hrσ.trans
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hq2 (by linarith))
  by_cases hv : IsUnramified K χ v
  · change ‖(if IsUnramified K χ v then
        (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) * r ^ (n + 1) else 0)‖ ≤ _
    rw [if_pos hv, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hl]
    calc
      _ = (Real.log (v.asIdeal.absNorm : ℝ) * ‖r‖) * ‖r‖ ^ n := by ring
      _ ≤ (Real.log (v.asIdeal.absNorm : ℝ) * ‖r‖) * c ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hrc n)
          (mul_nonneg hl (norm_nonneg r))
      _ ≤ A v * c ^ n := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrσ hl) (pow_nonneg hc0 n)
  · simpa [genuinePrimePowerTerm, hv] using mul_nonneg (hA0 v) (pow_nonneg hc0 n)

/-- Discharges the signed, absolutely convergent FULL prime-power identity
needed on the Euler overlap in 1.4.5. Neither summability nor nonvanishing
is assumed. The arithmetic Euler product is the unchanged source definition. -/
theorem genuineEuler_primePower_absolute_hasSum
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun p : FinitePlace K × ℕ => ‖genuinePrimePowerTerm K χ s p‖) ∧
      HasSum (genuinePrimePowerTerm K χ s) (-logDeriv (finiteHeckeL K χ) s) := by
  obtain ⟨B, hB, hbound⟩ := genuinePrimePower_uniform_majorant K s.re hs
  have habs := hB.of_nonneg_of_le (fun p => norm_nonneg _) (hbound χ s le_rfl)
  have hsum : Summable (genuinePrimePowerTerm K χ s) := habs.of_norm
  have heq := Round12F.genuineEuler_logDeriv_eq_tsum K χ s hs
  have hlocal : ∀ v : FinitePlace K,
      ∑' n : ℕ, genuinePrimePowerTerm K χ s (v, n) =
        -logDeriv (heckeEulerFactor K χ v) s := by
    intro v
    exact (Round6F.genuineLocalEuler_regular_and_primePower K χ v s hs).2.2.tsum_eq
  refine ⟨habs, ?_⟩
  have ht : ∑' p, genuinePrimePowerTerm K χ s p = -logDeriv (finiteHeckeL K χ) s := by
    rw [hsum.tsum_prod]
    simp_rw [hlocal]
    rw [tsum_neg, ← heq.2]
  exact ht ▸ hsum.hasSum

/-- Discharges uniform finite-place AND prime-power truncation on the Euler
 overlap, simultaneously for all genuine unitary characters. It supplies no
critical-strip bound or continuation. -/
theorem genuineEuler_primePower_uniform_limit (σ : ℝ) (hσ : 1 < σ) :
    TendstoUniformlyOn
      (fun S (q : {q : UnitaryHeckeCharacter K × ℂ // σ ≤ q.2.re}) =>
        ∑ p ∈ S, genuinePrimePowerTerm K q.val.1 q.val.2 p)
      (fun q => -logDeriv (finiteHeckeL K q.val.1) q.val.2)
      Filter.atTop Set.univ := by
  obtain ⟨B, hB, hbound⟩ := genuinePrimePower_uniform_majorant K σ hσ
  have hu := tendstoUniformlyOn_tsum hB
    (f := fun p (q : {q : UnitaryHeckeCharacter K × ℂ // σ ≤ q.2.re}) =>
      genuinePrimePowerTerm K q.val.1 q.val.2 p)
    (s := Set.univ) (fun p q _ => hbound q.val.1 q.val.2 q.property p)
  have he : (fun q : {q : UnitaryHeckeCharacter K × ℂ // σ ≤ q.2.re} =>
      ∑' p, genuinePrimePowerTerm K q.val.1 q.val.2 p) =
      (fun q => -logDeriv (finiteHeckeL K q.val.1) q.val.2) := by
    funext q
    exact (genuineEuler_primePower_absolute_hasSum K q.val.1 q.val.2
      (lt_of_lt_of_le hσ q.property)).2.tsum_eq
  rw [he] at hu
  exact hu

#check genuinePrimePower_uniform_majorant
#print axioms genuinePrimePower_uniform_majorant
#check genuineEuler_primePower_absolute_hasSum
#print axioms genuineEuler_primePower_absolute_hasSum
#check genuineEuler_primePower_uniform_limit
#print axioms genuineEuler_primePower_uniform_limit
end MasulloGRH.Round13F

namespace MasulloGRH.Round14F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges exactly the finite-place cutoff/prime-power sum exchange in
sections 1.4.4--1.4.5, on the Euler overlap. The scalar cutoff assumptions
are boundedness and pointwise convergence at genuine prime powers; absolute
summability is derived from Round13F's arithmetic majorant. Attachment to
smooth idelic tests and locally uniform parameter passage are separate. -/
theorem genuineEuler_primePower_cutoff_tendsto
    (χ : UnitaryHeckeCharacter K) (s : ℂ) (hs : 1 < s.re)
    (c : ℕ → FinitePlace K × ℕ → ℂ)
    (hc : ∀ n p, ‖c n p‖ ≤ 1)
    (hlim : ∀ p, Filter.Tendsto (fun n => c n p) Filter.atTop (nhds 1)) :
    (∀ n, Summable (fun p => c n p * Round13F.genuinePrimePowerTerm K χ s p)) ∧
    Filter.Tendsto
      (fun n => ∑' p, c n p * Round13F.genuinePrimePowerTerm K χ s p)
      Filter.atTop (nhds (-logDeriv (finiteHeckeL K χ) s)) := by
  obtain ⟨B, hB, hbound⟩ := Round13F.genuinePrimePower_uniform_majorant K s.re hs
  have hb : ∀ n p, ‖c n p * Round13F.genuinePrimePowerTerm K χ s p‖ ≤ B p := by
    intro n p
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc n p)).trans
      (hbound χ s le_rfl p)
  refine ⟨fun n => hB.of_norm_bounded (hb n), ?_⟩
  have ht := tendsto_tsum_of_dominated_convergence hB
    (fun p => by
      simpa using (hlim p).mul_const (Round13F.genuinePrimePowerTerm K χ s p))
    (Filter.Eventually.of_forall hb)
  rw [(Round13F.genuineEuler_primePower_absolute_hasSum K χ s hs).2.tsum_eq] at ht
  exact ht

#check genuineEuler_primePower_cutoff_tendsto
#print axioms genuineEuler_primePower_cutoff_tendsto
end MasulloGRH.Round14F

namespace MasulloGRH.Round14F
variable (K : Type*) [Field K] [NumberField K]

/-- Discharges the parameter-UNIFORM finite-prime cutoff limit in 1.4.4--5.
The scalar cutoffs are independent of character and spectral parameter.
Their pointwise convergence plus the previously derived arithmetic majorant
produces one vanishing error bound for ALL characters and Re(s)>=sigma>1.
No strip zero-free assertion, trace formula or zero summability is assumed. -/
theorem genuineEuler_primePower_cutoff_uniform
    (σ : ℝ) (hσ : 1 < σ)
    (c : ℕ → FinitePlace K × ℕ → ℂ)
    (hc : ∀ n p, ‖c n p‖ ≤ 1)
    (hlim : ∀ p, Filter.Tendsto (fun n => c n p) Filter.atTop (nhds 1)) :
    TendstoUniformlyOn
      (fun n (q : {q : UnitaryHeckeCharacter K × ℂ // σ ≤ q.2.re}) =>
        ∑' p, c n p * Round13F.genuinePrimePowerTerm K q.val.1 q.val.2 p)
      (fun q => -logDeriv (finiteHeckeL K q.val.1) q.val.2)
      Filter.atTop Set.univ := by
  obtain ⟨B, hB, hbound⟩ := Round13F.genuinePrimePower_uniform_majorant K σ hσ
  have hbn : Summable (fun p => ‖B p‖) := hB.norm
  have htwo : Summable (fun p => (2 : ℝ) * ‖B p‖) := hbn.mul_left 2
  have hc2 : ∀ n p, ‖c n p - 1‖ ≤ 2 := by
    intro n p
    calc
      _ ≤ ‖c n p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hc n p) (by norm_num)
      _ = 2 := by norm_num
  have heb : ∀ n p, ‖‖c n p - 1‖ * ‖B p‖‖ ≤ 2 * ‖B p‖ := by
    intro n p
    simp only [norm_mul, norm_norm]
    exact mul_le_mul_of_nonneg_right (hc2 n p) (norm_nonneg _)
  have hes : ∀ n, Summable (fun p => ‖c n p - 1‖ * ‖B p‖) :=
    fun n => htwo.of_norm_bounded (heb n)
  have het : Filter.Tendsto (fun n => ∑' p, ‖c n p - 1‖ * ‖B p‖)
      Filter.atTop (nhds 0) := by
    have hh := tendsto_tsum_of_dominated_convergence htwo
      (g := fun _ => (0 : ℝ))
      (fun p => by simpa using ((hlim p).sub_const 1).norm.mul_const ‖B p‖)
      (Filter.Eventually.of_forall heb)
    simpa using hh
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Filter.Tendsto.eventually_lt_const hε het] with n hn
  intro q _
  let t := Round13F.genuinePrimePowerTerm K q.val.1 q.val.2
  have hqs : 1 < q.val.2.re := lt_of_lt_of_le hσ q.property
  have ht := (Round13F.genuineEuler_primePower_absolute_hasSum K q.val.1 q.val.2 hqs).2
  have hct := (genuineEuler_primePower_cutoff_tendsto K q.val.1 q.val.2 hqs c hc hlim).1 n
  have hd : ∀ p, ‖(c n p - 1) * t p‖ ≤ ‖c n p - 1‖ * ‖B p‖ := by
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      ((hbound q.val.1 q.val.2 q.property p).trans (by simpa only [Real.norm_eq_abs] using (le_abs_self (B p)))) (norm_nonneg _)
  have hdn : Summable (fun p => ‖(c n p - 1) * t p‖) :=
    (hes n).of_nonneg_of_le (fun p => norm_nonneg _) hd
  have heq : (∑' p, c n p * t p) - (-logDeriv (finiteHeckeL K q.val.1) q.val.2) =
      ∑' p, (c n p - 1) * t p := by
    rw [← ht.tsum_eq, ← hct.tsum_sub ht.summable]
    congr 1
    funext p
    simp only [t, sub_mul, one_mul]
  rw [dist_comm, dist_eq_norm]
  change ‖(∑' p, c n p * t p) - (-logDeriv (finiteHeckeL K q.val.1) q.val.2)‖ < ε
  rw [heq]
  exact ((norm_tsum_le_tsum_norm hdn).trans
    (Summable.tsum_le_tsum hd hdn (hes n))).trans_lt hn

#check genuineEuler_primePower_cutoff_uniform
#print axioms genuineEuler_primePower_cutoff_uniform
end MasulloGRH.Round14F
