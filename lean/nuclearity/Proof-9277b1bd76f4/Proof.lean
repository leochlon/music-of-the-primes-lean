import Mathlib
set_option maxHeartbeats 800000

/-! Actual ideles and local embeddings reused from the exact F r53 checked source.
New work: the finite-place cutoff in manuscript 12.5.1.1, page 520.
This is partial progress, not an operator trace theorem. -/
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

/-- This is the local component of the actual idelic character. -/
noncomputable def localCharacter (χ : UnitaryHeckeCharacter K) (v : FinitePlace K)
    (x : (LocalField K v)ˣ) : Circle := χ.character (localIdele K v x)


/-- The normalized non-Archimedean absolute value uses the actual residue norm. -/
noncomputable def traceLocalAbs (v : FinitePlace K) (x : LocalField K v) : ℝ :=
  (WithZeroMulInt.toNNReal
    (show (v.asIdeal.absNorm : NNReal) ≠ 0 by
      exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v))))
    (Valued.v x) : ℝ)

/-- The local distribution integrand on actual local units for a character component. -/
noncomputable def traceLocalIntegrand (χ : UnitaryHeckeCharacter K)
    (ψ : ℝ → ℂ) (v : FinitePlace K) (x : (LocalField K v)ˣ) : ℂ :=
  (localCharacter K χ v x : ℂ) * ψ (traceLocalAbs K v x) *
    (Real.sqrt (traceLocalAbs K v x) : ℂ) /
    (traceLocalAbs K v (1 - (x : LocalField K v)) : ℂ)

/-- The normalized local value on a nonzero element is an integral power of q_v. -/
theorem traceLocalAbs_eq_zpow (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    traceLocalAbs K v x = (v.asIdeal.absNorm : ℝ) ^ (Valued.v (x : LocalField K v)).log := by
  have hx : Valued.v (x : LocalField K v) ≠ 0 := by
    intro h
    have : (x : LocalField K v) = 0 := (Valuation.zero_iff _).mp h
    exact Units.ne_zero x this
  unfold traceLocalAbs
  conv_lhs => rw [← WithZero.exp_log hx]
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp [WithZero.exp]

/-- The actual finite-place local distribution vanishes beyond the support radius.
The radial support hypothesis is the restriction of |supp φ| ⊂ (1/T,T),
and ψ(1)=0 is the character-component version of φ(C_F^1)=0. -/
theorem traceLocalIntegrand_eq_zero_of_large_residue
    (χ : UnitaryHeckeCharacter K) (ψ : ℝ → ℂ)
    (T : ℝ) (hT : 1 < T) (hψ : ψ 1 = 0)
    (hsupp : ∀ t : ℝ, ψ t ≠ 0 → T⁻¹ < t ∧ t < T)
    (v : FinitePlace K) (hv : T < (v.asIdeal.absNorm : ℝ))
    (x : (LocalField K v)ˣ) : traceLocalIntegrand K χ ψ v x = 0 := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := lt_trans hT hv
  have hq0 : 0 < (v.asIdeal.absNorm : ℝ) := lt_trans zero_lt_one hq
  have hz : ψ (traceLocalAbs K v x) = 0 := by
    rw [traceLocalAbs_eq_zpow]
    let n : ℤ := (Valued.v (x : LocalField K v)).log
    change ψ ((v.asIdeal.absNorm : ℝ) ^ n) = 0
    by_cases hn : n = 0
    · simpa [hn] using hψ
    · by_contra hp
      obtain ⟨hl, hu⟩ := hsupp _ hp
      rcases lt_or_gt_of_ne hn with hn | hn
      · have hb : (v.asIdeal.absNorm : ℝ) ^ n ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
          exact zpow_le_zpow_right₀ (le_of_lt hq) (by omega)
        have hi : (v.asIdeal.absNorm : ℝ)⁻¹ < T⁻¹ := (inv_lt_inv₀ hq0 (show 0 < T by linarith)).mpr hv
        rw [zpow_neg_one] at hb
        linarith
      · have hb : (v.asIdeal.absNorm : ℝ) ≤ (v.asIdeal.absNorm : ℝ) ^ n := by
          simpa using zpow_le_zpow_right₀ (le_of_lt hq) (show (1 : ℤ) ≤ n by omega)
        linarith
  simp [traceLocalIntegrand, hz]

open MeasureTheory in
/-- All cutoffs of this actual local integrand are integrable with zero integral.
This holds for every measure, hence in particular for the required local Haar measure. -/
theorem traceLocalCutoff_integrable_integral_zero
    (χ : UnitaryHeckeCharacter K) (ψ : ℝ → ℂ)
    (T : ℝ) (hT : 1 < T) (hψ : ψ 1 = 0)
    (hsupp : ∀ t : ℝ, ψ t ≠ 0 → T⁻¹ < t ∧ t < T)
    (v : FinitePlace K) (hv : T < (v.asIdeal.absNorm : ℝ))
    [MeasurableSpace (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) (ρ : (LocalField K v)ˣ → ℂ) :
    Integrable (fun x => ρ x * traceLocalIntegrand K χ ψ v x) μ ∧
    (∫ x, ρ x * traceLocalIntegrand K χ ψ v x ∂μ) = 0 := by
  have hz : (fun x => ρ x * traceLocalIntegrand K χ ψ v x) = fun _ => 0 := by
    funext x
    simp [traceLocalIntegrand_eq_zero_of_large_residue K χ ψ T hT hψ hsupp v hv x]
  rw [hz]
  exact ⟨integrable_zero _ _ _, integral_zero _ _⟩

/-- Only finitely many actual finite places can contribute to this local distribution.
The exceptional set is bounded by the actual ideal norm, not a chosen prime sequence. -/
theorem traceLocalIntegrands_finite_support
    (χ : UnitaryHeckeCharacter K) (ψ : ℝ → ℂ)
    (T : ℝ) (hT : 1 < T) (hψ : ψ 1 = 0)
    (hsupp : ∀ t : ℝ, ψ t ≠ 0 → T⁻¹ < t ∧ t < T) :
    ∃ S : Finset (FinitePlace K), ∀ v, v ∉ S →
      ∀ x : (LocalField K v)ˣ, traceLocalIntegrand K χ ψ v x = 0 := by
  classical
  have hf : {v : FinitePlace K | v.asIdeal.absNorm ≤ Nat.ceil T}.Finite :=
    Set.Finite.preimage
      (fun _ _ _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h)
      (Ideal.finite_setOf_absNorm_le (Nat.ceil T))
  refine ⟨hf.toFinset, ?_⟩
  intro v hv x
  apply traceLocalIntegrand_eq_zero_of_large_residue K χ ψ T hT hψ hsupp v _ x
  have hn : ¬ v.asIdeal.absNorm ≤ Nat.ceil T := by simpa using hv
  have hn' : (Nat.ceil T : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast Nat.lt_of_not_ge hn
  exact lt_of_le_of_lt (Nat.le_ceil T) hn'

open MeasureTheory in
/-- The precise non-Archimedean normalization from (12.4.1.3) preserves cutoff vanishing. -/
theorem traceLocalNormalizedCutoff_zero
    (χ : UnitaryHeckeCharacter K) (ψ : ℝ → ℂ)
    (T : ℝ) (hT : 1 < T) (hψ : ψ 1 = 0)
    (hsupp : ∀ t : ℝ, ψ t ≠ 0 → T⁻¹ < t ∧ t < T)
    (v : FinitePlace K) (hv : T < (v.asIdeal.absNorm : ℝ))
    [MeasurableSpace (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) (ρ : (LocalField K v)ˣ → ℂ) :
    (((Real.log (v.asIdeal.absNorm : ℝ)) /
      (μ {x | Valued.v (x : LocalField K v) = 1}).toReal : ℝ) : ℂ) *
      (∫ x, ρ x * traceLocalIntegrand K χ ψ v x ∂μ) = 0 := by
  rw [(traceLocalCutoff_integrable_integral_zero K χ ψ T hT hψ hsupp v hv μ ρ).2,
    mul_zero]

#check traceLocalNormalizedCutoff_zero
#print axioms traceLocalNormalizedCutoff_zero
#check traceLocalIntegrands_finite_support
#print axioms traceLocalIntegrands_finite_support
#check traceLocalCutoff_integrable_integral_zero
#print axioms traceLocalCutoff_integrable_integral_zero
#check traceLocalAbs_eq_zpow
#print axioms traceLocalAbs_eq_zpow
#check traceLocalIntegrand_eq_zero_of_large_residue
#print axioms traceLocalIntegrand_eq_zero_of_large_residue
end MasulloGRH
