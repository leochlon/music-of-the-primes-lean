import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-! Round 54: local geometric-distribution vanishing for the actual finite-place
embeddings into the genuine idele class group. Partial trace work only. -/
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


/-- The actual local point in the genuine idele class group. -/
noncomputable def localClass (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    HeckeIdeleClasses K := QuotientGroup.mk (localIdele K v x)

/-- Normalized nonarchimedean absolute value, with residue cardinality q_v. -/
noncomputable def localAbs (v : FinitePlace K) (x : LocalField K v) : ℝ :=
  if x = 0 then 0 else (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log

/-- The local geometric integrand in (12.5.1.2), before its scalar Haar factor. -/
noncomputable def localGeometricIntegrand (φ : HeckeIdeleClasses K → ℂ)
    (v : FinitePlace K) (x : (LocalField K v)ˣ) : ℂ :=
  φ (localClass K v x) * (Real.sqrt (localAbs K v x) : ℂ) /
    (localAbs K v (1 - (x : LocalField K v)) : ℂ)

/-- Discreteness of a genuine finite-place norm excludes the support annulus
when q_v > T. The two test hypotheses are exactly the local restrictions
needed from φ(C_F^1)=0 and |supp φ| ⊂ (1/T,T). -/
theorem localRestriction_zero_of_large_residue
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (v : FinitePlace K) (hv : T < (v.asIdeal.absNorm : ℝ))
    (hunit : ∀ x : (LocalField K v)ˣ, (Valued.v (x : LocalField K v)).log = 0 →
      φ (localClass K v x) = 0)
    (hsupp : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < localAbs K v x ∧ localAbs K v x < T) :
    ∀ x : (LocalField K v)ˣ, φ (localClass K v x) = 0 := by
  intro x
  by_contra hx
  have hb := hsupp x hx
  have hx0 : (x : LocalField K v) ≠ 0 := Units.ne_zero x
  simp only [localAbs, if_neg hx0] at hb
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := lt_trans hT hv
  have hn : (Valued.v (x : LocalField K v)).log ≠ 0 := fun h => hx (hunit x h)
  rcases lt_or_gt_of_ne hn with hn | hn
  · have hp : (v.asIdeal.absNorm : ℝ) ^ (Valued.v (x : LocalField K v)).log ≤
        (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    have hi : (v.asIdeal.absNorm : ℝ)⁻¹ < T⁻¹ :=
      inv_lt_inv₀ (by linarith) (by linarith) |>.mpr hv
    simp only [zpow_neg_one] at hp
    linarith
  · have hp : (v.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤
        (v.asIdeal.absNorm : ℝ) ^ (Valued.v (x : LocalField K v)).log :=
      zpow_le_zpow_right₀ hq.le (by omega)
    simp only [zpow_one] at hp
    linarith

#check localRestriction_zero_of_large_residue
#print axioms localRestriction_zero_of_large_residue

/-- Outside the support annulus the actual finite-place geometric integrand
is integrable and has zero integral for every measure, hence for every Haar
normalization. No use of a totalized integral of a nonintegrable function occurs. -/
theorem localGeometric_integrable_and_integral_zero
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (v : FinitePlace K) (hv : T < (v.asIdeal.absNorm : ℝ))
    [MeasurableSpace ((LocalField K v)ˣ)]
    (μ : MeasureTheory.Measure ((LocalField K v)ˣ))
    (hunit : ∀ x : (LocalField K v)ˣ, (Valued.v (x : LocalField K v)).log = 0 →
      φ (localClass K v x) = 0)
    (hsupp : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < localAbs K v x ∧ localAbs K v x < T) :
    MeasureTheory.Integrable (localGeometricIntegrand K φ v) μ ∧
      (∫ x, localGeometricIntegrand K φ v x ∂μ) = 0 := by
  have he : localGeometricIntegrand K φ v = fun _ => 0 := by
    funext x
    simp [localGeometricIntegrand,
      localRestriction_zero_of_large_residue K φ T hT v hv hunit hsupp x]
  rw [he]
  exact ⟨MeasureTheory.integrable_zero _ _ _, by simp⟩

#check localGeometric_integrable_and_integral_zero
#print axioms localGeometric_integrable_and_integral_zero

/-- The actual finite places of bounded residue cardinality form a finite set. -/
theorem finitePlaces_bounded_norm (N : ℕ) :
    {v : FinitePlace K | v.asIdeal.absNorm ≤ N}.Finite := by
  have hi : {I : Ideal (𝓞 K) | I.absNorm ≤ N}.Finite :=
    Ideal.finite_setOf_absNorm_le N
  have hinj : Function.Injective (fun v : FinitePlace K => v.asIdeal) := by
    intro v w h
    exact IsDedekindDomain.HeightOneSpectrum.ext h
  exact hi.preimage hinj.injOn

/-- The finite-place geometric integrals have finite support. This justifies
reducing their infinite sum to the finite S of §12.5.1, independently of Haar
normalization. Integrability at places inside S is a separate obligation. -/
theorem finiteGeometricIntegral_finite_support
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    [∀ v : FinitePlace K, MeasurableSpace ((LocalField K v)ˣ)]
    (μ : ∀ v : FinitePlace K, MeasureTheory.Measure ((LocalField K v)ˣ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ)) :
    ∃ S : Finset (FinitePlace K), ∀ v ∉ S,
      MeasureTheory.Integrable (localGeometricIntegrand K φ v) (μ v) ∧
      (∫ x, localGeometricIntegrand K φ v x ∂μ v) = 0 := by
  classical
  refine ⟨(finitePlaces_bounded_norm K N).toFinset, ?_⟩
  intro v hv
  have hlarge : N < v.asIdeal.absNorm := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] using hv
  exact localGeometric_integrable_and_integral_zero K φ N hN v
    (by exact_mod_cast hlarge) (μ v) (hunit v) (hsupp v)

#check finitePlaces_bounded_norm
#print axioms finitePlaces_bounded_norm
#check finiteGeometricIntegral_finite_support
#print axioms finiteGeometricIntegral_finite_support

/-- The finite-place expression with the exact scalar in (12.5.1.2).
For nonzero terms its use as an analytic integral requires integrability. -/
noncomputable def finiteGeometricTerm
    (φ : HeckeIdeleClasses K → ℂ)
    [∀ v : FinitePlace K, MeasurableSpace ((LocalField K v)ˣ)]
    (μ : ∀ v : FinitePlace K, MeasureTheory.Measure ((LocalField K v)ˣ))
    (v : FinitePlace K) : ℂ :=
  (Real.log (v.asIdeal.absNorm : ℝ) /
    (μ v {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = 1}).toReal : ℂ) *
    ∫ x, localGeometricIntegrand K φ v x ∂μ v

/-- Absolute convergence of the genuine finite-place expression, reducing the
remaining integrability obligations to the finitely many small residue norms.
This is a geometric-side convergence statement, not an operator trace theorem. -/
theorem finiteGeometric_absolute_convergence
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    [∀ v : FinitePlace K, MeasurableSpace ((LocalField K v)ˣ)]
    (μ : ∀ v : FinitePlace K, MeasureTheory.Measure ((LocalField K v)ˣ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hsmall : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      MeasureTheory.Integrable (localGeometricIntegrand K φ v) (μ v)) :
    (∀ v, MeasureTheory.Integrable (localGeometricIntegrand K φ v) (μ v)) ∧
    Summable (fun v => ‖finiteGeometricTerm K φ μ v‖) ∧
    ∃ S : Finset (FinitePlace K),
      (∑' v, finiteGeometricTerm K φ μ v) = ∑ v ∈ S, finiteGeometricTerm K φ μ v := by
  classical
  obtain ⟨S, hS⟩ := finiteGeometricIntegral_finite_support K φ N hN μ hunit hsupp
  have hz : ∀ v ∉ S, finiteGeometricTerm K φ μ v = 0 := by
    intro v hv
    simp [finiteGeometricTerm, (hS v hv).2]
  refine ⟨?_, summable_of_ne_finset_zero (s := S) (fun v hv => by rw [hz v hv]; simp),
    S, tsum_eq_sum hz⟩
  intro v
  by_cases hv : v.asIdeal.absNorm ≤ N
  · exact hsmall v hv
  · exact (localGeometric_integrable_and_integral_zero K φ N hN v
      (by exact_mod_cast Nat.lt_of_not_ge hv) (μ v) (hunit v) (hsupp v)).1

#check principalIdele_injective
#print axioms principalIdele_injective
#check finiteGeometric_absolute_convergence
#print axioms finiteGeometric_absolute_convergence

/-- Away from the valuation-unit shell, the actual local denominator is either
one or the absolute value of the argument. This removes the finite-place pole. -/
theorem localDenominator_dichotomy (v : FinitePlace K)
    (x : (LocalField K v)ˣ)
    (hx : (Valued.v (x : LocalField K v)).log ≠ 0) :
    localAbs K v (1 - (x : LocalField K v)) = 1 ∨
    localAbs K v (1 - (x : LocalField K v)) = localAbs K v x := by
  have hv : Valued.v (x : LocalField K v) ≠ 1 := by
    intro h
    exact hx (by rw [h]; exact WithZero.log_one)
  have hx1 : (x : LocalField K v) ≠ 1 := by
    intro h
    exact hv (by rw [h, map_one])
  have hd0 : 1 - (x : LocalField K v) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have htop : Valued.v (1 - (x : LocalField K v)) ≤
      max 1 (Valued.v (x : LocalField K v)) := by
    simpa [sub_eq_add_neg] using (Valued.v.map_add (1 : LocalField K v) (-(x : LocalField K v)))
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · left
    have hback : (1 : WithZero (Multiplicative ℤ)) ≤
        max (Valued.v (1 - (x : LocalField K v))) (Valued.v (x : LocalField K v)) := by
      simpa using (Valued.v.map_add (1 - (x : LocalField K v)) (x : LocalField K v))
    have hd : Valued.v (1 - (x : LocalField K v)) = 1 := by
      apply le_antisymm (htop.trans (max_le le_rfl hlt.le))
      rcases le_max_iff.mp hback with h | h
      · exact h
      · exact False.elim (not_le_of_gt hlt h)
    simp [localAbs, hd0, hd]
  · right
    have hback : Valued.v (x : LocalField K v) ≤
        max (Valued.v (1 - (x : LocalField K v))) 1 := by
      have hh := Valued.v.map_add ((x : LocalField K v) - 1) (1 : LocalField K v)
      simpa [Valuation.map_sub_swap] using hh
    have hd : Valued.v (1 - (x : LocalField K v)) = Valued.v (x : LocalField K v) := by
      apply le_antisymm (htop.trans (max_le hgt.le le_rfl))
      rcases le_max_iff.mp hback with h | h
      · exact h
      · exact False.elim (not_le_of_gt hgt h)
    simp [localAbs, hd0, Units.ne_zero x, hd]

#check localDenominator_dichotomy
#print axioms localDenominator_dichotomy

/-- A support-annulus bound on the actual finite-place geometric integrand.
The constant is deliberately coarse; no zero-divisor or trace data are assumed. -/
theorem localGeometric_norm_bound
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (v : FinitePlace K)
    (hunit : ∀ x : (LocalField K v)ˣ, (Valued.v (x : LocalField K v)).log = 0 →
      φ (localClass K v x) = 0)
    (hsupp : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < localAbs K v x ∧ localAbs K v x < T)
    (x : (LocalField K v)ˣ) :
    ‖localGeometricIntegrand K φ v x‖ ≤
      (Real.sqrt T * T) * ‖φ (localClass K v x)‖ := by
  by_cases hz : φ (localClass K v x) = 0
  · simp [localGeometricIntegrand, hz]
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hTi : 0 < T⁻¹ := inv_pos.mpr hT0
  have hr := hsupp x hz
  have hd : T⁻¹ ≤ localAbs K v (1 - (x : LocalField K v)) := by
    rcases localDenominator_dichotomy K v x (fun h => hz (hunit x h)) with h | h
    · rw [h]
      have : (1 : ℝ) / T ≤ 1 := (div_le_iff₀ hT0).mpr (by linarith)
      simpa using this
    · rw [h]; exact hr.1.le
  have hd0 : 0 < localAbs K v (1 - (x : LocalField K v)) := lt_of_lt_of_le hTi hd
  have hp : 1 ≤ localAbs K v (1 - (x : LocalField K v)) * T :=
    (div_le_iff₀ hT0).mp (by simpa using hd)
  have hs : Real.sqrt (localAbs K v x) ≤ Real.sqrt T := Real.sqrt_le_sqrt hr.2.le
  have hb : Real.sqrt (localAbs K v x) /
      localAbs K v (1 - (x : LocalField K v)) ≤ Real.sqrt T * T := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith [mul_nonneg (Real.sqrt_nonneg T) (sub_nonneg.mpr hp)]
  calc
    ‖localGeometricIntegrand K φ v x‖ = ‖φ (localClass K v x)‖ *
        (Real.sqrt (localAbs K v x) / localAbs K v (1 - (x : LocalField K v))) := by
      simp [localGeometricIntegrand, Complex.norm_real,
        abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hd0, mul_div_assoc]
    _ ≤ ‖φ (localClass K v x)‖ * (Real.sqrt T * T) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_comm _ _

#check localGeometric_norm_bound
#print axioms localGeometric_norm_bound

/-- The finite-place singular factor costs only a bounded multiplier on the
admissible support annulus. Ordinary local test integrability now suffices. -/
theorem localGeometric_integrable_of_test
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (v : FinitePlace K) [MeasurableSpace ((LocalField K v)ˣ)]
    (μ : MeasureTheory.Measure ((LocalField K v)ˣ))
    (hunit : ∀ x : (LocalField K v)ˣ, (Valued.v (x : LocalField K v)).log = 0 →
      φ (localClass K v x) = 0)
    (hsupp : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < localAbs K v x ∧ localAbs K v x < T)
    (hφ : MeasureTheory.Integrable (fun x => φ (localClass K v x)) μ)
    (hm : MeasureTheory.AEStronglyMeasurable (localGeometricIntegrand K φ v) μ) :
    MeasureTheory.Integrable (localGeometricIntegrand K φ v) μ := by
  apply (hφ.norm.const_mul (Real.sqrt T * T)).mono' hm
  exact Filter.Eventually.of_forall (localGeometric_norm_bound K φ T hT v hunit hsupp)

#check localGeometric_integrable_of_test
#print axioms localGeometric_integrable_of_test

/-- Integration into (12.5.1.2): the normalized finite-place expression is
absolutely convergent once ordinary local test integrability and measurability
are supplied at the finitely many small places. No singular-integrand
integrability hypothesis remains. This is still only a geometric-side result. -/
theorem finiteGeometric_convergence_of_localTests
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    [∀ v : FinitePlace K, MeasurableSpace ((LocalField K v)ˣ)]
    (μ : ∀ v : FinitePlace K, MeasureTheory.Measure ((LocalField K v)ˣ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hφ : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      MeasureTheory.Integrable (fun x => φ (localClass K v x)) (μ v))
    (hm : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      MeasureTheory.AEStronglyMeasurable (localGeometricIntegrand K φ v) (μ v)) :
    (∀ v, MeasureTheory.Integrable (localGeometricIntegrand K φ v) (μ v)) ∧
    Summable (fun v => ‖finiteGeometricTerm K φ μ v‖) ∧
    ∃ S : Finset (FinitePlace K),
      (∑' v, finiteGeometricTerm K φ μ v) = ∑ v ∈ S, finiteGeometricTerm K φ μ v := by
  apply finiteGeometric_absolute_convergence K φ N hN μ hunit hsupp
  intro v hv
  exact localGeometric_integrable_of_test K φ N hN v (μ v)
    (hunit v) (hsupp v) (hφ v hv) (hm v hv)

#check finiteGeometric_convergence_of_localTests
#print axioms finiteGeometric_convergence_of_localTests
/-- Local constancy of the actual normalized finite-place absolute value
away from zero. Used below on both factors of the geometric integrand. -/
theorem localAbs_eventually_eq (v : FinitePlace K) (x : LocalField K v)
    (hx : x ≠ 0) : (localAbs K v) =ᶠ[nhds x] (fun _ => localAbs K v x) := by
  have hv : Valued.v x ≠ 0 := (map_ne_zero (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))).mpr hx
  filter_upwards [Valued.loc_const hv] with y hy
  have hy0 : y ≠ 0 := by
    intro h
    apply hv
    simpa [h] using hy.symm
  simp [localAbs, hx, hy0, hy]

#check localAbs_eventually_eq
#print axioms localAbs_eventually_eq

/-- The apparent finite-place singularity is removable for the manuscript's
unit-shell vanishing condition. No measurability of the quotient is assumed. -/
theorem localGeometric_continuous
    (φ : HeckeIdeleClasses K → ℂ) (v : FinitePlace K)
    (hφ : Continuous (fun x : (LocalField K v)ˣ => φ (localClass K v x)))
    (hunit : ∀ x : (LocalField K v)ˣ, (Valued.v (x : LocalField K v)).log = 0 →
      φ (localClass K v x) = 0) :
    Continuous (localGeometricIntegrand K φ v) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : (Valued.v (x : LocalField K v)).log = 0
  · have hv : Valued.v (x : LocalField K v) ≠ 0 :=
      (map_ne_zero (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))).mpr (Units.ne_zero x)
    have hh := Units.continuous_val.continuousAt.preimage_mem_nhds (Valued.loc_const hv)
    have he : localGeometricIntegrand K φ v =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [hh] with y hy
      have hylog : (Valued.v (y : LocalField K v)).log = 0 := by
        change Valued.v (y : LocalField K v) = Valued.v (x : LocalField K v) at hy
        rw [hy]; exact hx
      simp [localGeometricIntegrand, hunit y hylog]
    exact he.continuousAt
  · have hd : 1 - (x : LocalField K v) ≠ 0 := by
      intro h
      have hx1 : (x : LocalField K v) = 1 := (sub_eq_zero.mp h).symm
      apply hx
      simp [hx1]
    have hn := Units.continuous_val.continuousAt.preimage_mem_nhds
      (localAbs_eventually_eq K v (x : LocalField K v) (Units.ne_zero x))
    have hc : Continuous (fun y : (LocalField K v)ˣ => 1 - (y : LocalField K v)) :=
      continuous_const.sub Units.continuous_val
    have hh := hc.continuousAt.preimage_mem_nhds
      (localAbs_eventually_eq K v (1 - (x : LocalField K v)) hd)
    have he : localGeometricIntegrand K φ v =ᶠ[nhds x]
        (fun y => φ (localClass K v y) * (Real.sqrt (localAbs K v x) : ℂ) /
          (localAbs K v (1 - (x : LocalField K v)) : ℂ)) := by
      filter_upwards [hn, hh] with y hy hz
      change localAbs K v (y : LocalField K v) = localAbs K v x at hy
      change localAbs K v (1 - (y : LocalField K v)) =
        localAbs K v (1 - (x : LocalField K v)) at hz
      simp only [localGeometricIntegrand, hy, hz]
    apply ContinuousAt.congr_of_eventuallyEq _ he
    exact (hφ.continuousAt.mul continuousAt_const).div_const _

#check localGeometric_continuous
#print axioms localGeometric_continuous
/-- Direct application to (12.5.1.2): continuous compact local restrictions
supply both ordinary integrability and measurability. The local support and
unit-shell hypotheses still need their global admissible-test bridge. -/
theorem finiteGeometric_convergence_of_compactLocalTests
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    [∀ v : FinitePlace K, MeasurableSpace ((LocalField K v)ˣ)]
    [∀ v : FinitePlace K, OpensMeasurableSpace ((LocalField K v)ˣ)]
    (μ : ∀ v : FinitePlace K, MeasureTheory.Measure ((LocalField K v)ˣ))
    [∀ v : FinitePlace K, MeasureTheory.IsFiniteMeasureOnCompacts (μ v)]
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hc : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      Continuous (fun x : (LocalField K v)ˣ => φ (localClass K v x)))
    (hk : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      HasCompactSupport (fun x : (LocalField K v)ˣ => φ (localClass K v x))) :
    (∀ v, MeasureTheory.Integrable (localGeometricIntegrand K φ v) (μ v)) ∧
    Summable (fun v => ‖finiteGeometricTerm K φ μ v‖) ∧
    ∃ S : Finset (FinitePlace K),
      (∑' v, finiteGeometricTerm K φ μ v) = ∑ v ∈ S, finiteGeometricTerm K φ μ v := by
  apply finiteGeometric_convergence_of_localTests K φ N hN μ hunit hsupp
  · intro v hv
    exact (hc v hv).integrable_of_hasCompactSupport (hk v hv)
  · intro v hv
    exact (localGeometric_continuous K φ v (hc v hv) (hunit v)).aestronglyMeasurable

#check finiteGeometric_convergence_of_compactLocalTests
#print axioms finiteGeometric_convergence_of_compactLocalTests
end MasulloGRH

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

/-- Actual integral-unit inclusion in the multiplicative local field. -/
noncomputable def localUnitInclusion (v : FinitePlace K)
    (x : (v.adicCompletionIntegers K)ˣ) : (LocalField K v)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype x

def localUnitSet (v : FinitePlace K) : Set ((LocalField K v)ˣ) :=
  {x | Valued.v (x : LocalField K v) ≤ 1 ∧ Valued.v (↑(x⁻¹) : LocalField K v) ≤ 1}

theorem localUnitSet_eq_range (v : FinitePlace K) :
    localUnitSet K v = Set.range (localUnitInclusion K v) := by
  ext x
  constructor
  · rintro ⟨hx, hi⟩
    let u : (v.adicCompletionIntegers K)ˣ :=
      { val := ⟨x.val, hx⟩
        inv := ⟨x.inv, hi⟩
        val_inv := Subtype.ext x.val_inv
        inv_val := Subtype.ext x.inv_val }
    exact ⟨u, Units.ext rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u.val.property, u.inv.property⟩

theorem localUnitSet_isCompact (v : FinitePlace K) :
    IsCompact (localUnitSet K v) := by
  letI := localIntegralUnits_compactSpace K v
  rw [localUnitSet_eq_range]
  apply isCompact_range
  apply Units.continuous_iff.mpr
  exact ⟨continuous_subtype_val.comp Units.continuous_val,
    continuous_subtype_val.comp Units.continuous_coe_inv⟩

theorem localUnitSet_isOpen (v : FinitePlace K) : IsOpen (localUnitSet K v) := by
  have ho := (Valued.isClopen_closedBall (LocalField K v)
    (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen
  exact (ho.preimage Units.continuous_val).inter (ho.preimage Units.continuous_coe_inv)

theorem localUnitSet_eq_valuation_one (v : FinitePlace K) :
    localUnitSet K v = {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = 1} := by
  ext x
  constructor
  · rintro ⟨hx, hi⟩
    apply le_antisymm hx
    calc
      1 = Valued.v (x : LocalField K v) * Valued.v (↑(x⁻¹) : LocalField K v) := by
        rw [← map_mul]; simp
      _ ≤ Valued.v (x : LocalField K v) := by
        simpa using mul_le_mul_right hi (Valued.v (x : LocalField K v))
  · intro hx
    change Valued.v (x : LocalField K v) = 1 at hx
    exact ⟨hx.le, by simp only [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one, le_refl]⟩

noncomputable def localUnitsPositiveCompact (v : FinitePlace K) :
    TopologicalSpace.PositiveCompacts ((LocalField K v)ˣ) :=
  ⟨⟨localUnitSet K v, localUnitSet_isCompact K v⟩, by
    rw [(localUnitSet_isOpen K v).interior_eq]
    exact ⟨1, by simp [localUnitSet]⟩⟩

local instance (v : FinitePlace K) : MeasurableSpace ((LocalField K v)ˣ) := borel _
local instance (v : FinitePlace K) : BorelSpace ((LocalField K v)ˣ) := ⟨rfl⟩

noncomputable def normalizedLocalHaar (v : FinitePlace K) :
    MeasureTheory.Measure ((LocalField K v)ˣ) :=
  MeasureTheory.Measure.haarMeasure (localUnitsPositiveCompact K v)

theorem normalizedLocalHaar_isHaar (v : FinitePlace K) :
    MeasureTheory.Measure.IsHaarMeasure (normalizedLocalHaar K v) := by
  unfold normalizedLocalHaar
  infer_instance

theorem normalizedLocalHaar_units (v : FinitePlace K) :
    normalizedLocalHaar K v {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = 1} = 1 := by
  rw [← localUnitSet_eq_valuation_one]
  exact MeasureTheory.Measure.haarMeasure_self

/-- The scalar in (12.5.1.2) now uses a proved nondegenerate local Haar measure. -/
theorem normalizedFiniteGeometricTerm (φ : HeckeIdeleClasses K → ℂ)
    (v : FinitePlace K) :
    finiteGeometricTerm K φ (normalizedLocalHaar K) v =
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
        ∫ x, localGeometricIntegrand K φ v x ∂normalizedLocalHaar K v := by
  simp [finiteGeometricTerm, normalizedLocalHaar_units]

/-- Integration into the geometric side: local Haar hypotheses are discharged. -/
theorem normalizedFiniteGeometric_convergence
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hc : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      Continuous (fun x : (LocalField K v)ˣ => φ (localClass K v x)))
    (hk : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      HasCompactSupport (fun x : (LocalField K v)ˣ => φ (localClass K v x))) :
    (∀ v, MeasureTheory.Integrable (localGeometricIntegrand K φ v) (normalizedLocalHaar K v)) ∧
    Summable (fun v => ‖finiteGeometricTerm K φ (normalizedLocalHaar K) v‖) ∧
    ∃ S : Finset (FinitePlace K),
      (∑' v, finiteGeometricTerm K φ (normalizedLocalHaar K) v) =
        ∑ v ∈ S, finiteGeometricTerm K φ (normalizedLocalHaar K) v := by
  letI (v : FinitePlace K) := normalizedLocalHaar_isHaar K v
  exact finiteGeometric_convergence_of_compactLocalTests K φ N hN
    (normalizedLocalHaar K) hunit hsupp hc hk

#check normalizedLocalHaar_isHaar
#print axioms normalizedLocalHaar_isHaar
#check normalizedLocalHaar_units
#print axioms normalizedLocalHaar_units
#check normalizedFiniteGeometricTerm
#print axioms normalizedFiniteGeometricTerm
#check normalizedFiniteGeometric_convergence
#print axioms normalizedFiniteGeometric_convergence
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Each genuine valuation fiber is a translate of the compact integral units. -/
theorem localValuationFiber_isCompact (v : FinitePlace K)
    (r : WithZero (Multiplicative ℤ)) :
    IsCompact {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = r} := by
  classical
  by_cases h : ∃ a : (LocalField K v)ˣ, Valued.v (a : LocalField K v) = r
  · obtain ⟨a, ha⟩ := h
    have hr : r ≠ 0 := by
      rw [← ha]
      exact (map_ne_zero (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))).mpr (Units.ne_zero a)
    have he : {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = r} =
        (fun u => a * u) '' localUnitSet K v := by
      rw [localUnitSet_eq_valuation_one]
      ext x
      constructor
      · intro hx
        change Valued.v (x : LocalField K v) = r at hx
        refine ⟨a⁻¹ * x, ?_, by simp⟩
        change Valued.v (↑(a⁻¹ * x) : LocalField K v) = 1
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, ha, hx, inv_mul_cancel₀ hr]
      · rintro ⟨u, hu, rfl⟩
        change Valued.v ((a : LocalField K v) * (u : LocalField K v)) = r
        change Valued.v (u : LocalField K v) = 1 at hu
        rw [map_mul, ha, hu, mul_one]
    rw [he]
    exact (localUnitSet_isCompact K v).image (continuous_const.mul continuous_id)
  · have he : {x : (LocalField K v)ˣ | Valued.v (x : LocalField K v) = r} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hx => h ⟨x, hx⟩
    rw [he]
    exact isCompact_empty

/-- An annulus bounds the integer valuation exponents of the actual test. -/
theorem localTest_log_bounded (φ : HeckeIdeleClasses K → ℂ)
    (v : FinitePlace K) (T : ℝ) (hT : 1 < T)
    (hsupp : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < localAbs K v x ∧ localAbs K v x < T) :
    ∃ M : ℤ, ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      -M ≤ (Valued.v (x : LocalField K v)).log ∧
      (Valued.v (x : LocalField K v)).log ≤ M := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hlq : 0 < Real.log (v.asIdeal.absNorm : ℝ) := Real.log_pos hq
  obtain ⟨M, hM⟩ := exists_int_gt (Real.log T / Real.log (v.asIdeal.absNorm : ℝ))
  have hM' : Real.log T < (M : ℝ) * Real.log (v.asIdeal.absNorm : ℝ) :=
    (div_lt_iff₀ hlq).mp hM
  refine ⟨M, ?_⟩
  intro x hx
  have hb := hsupp x hx
  simp only [localAbs, if_neg (Units.ne_zero x)] at hb
  have hq0 : 0 < (v.asIdeal.absNorm : ℝ) := lt_trans zero_lt_one hq
  have hT0 : 0 < T := lt_trans zero_lt_one hT
  have hlo := Real.log_lt_log (inv_pos.mpr hT0) hb.1
  have hhi := Real.log_lt_log (zpow_pos hq0 _) hb.2
  rw [Real.log_inv, Real.log_zpow] at hlo
  rw [Real.log_zpow] at hhi
  constructor
  · have hh : -(M : ℝ) ≤ ((Valued.v (x : LocalField K v)).log : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : ((Valued.v (x : LocalField K v)).log : ℝ) ≤ (M : ℝ) := by nlinarith
    exact_mod_cast hh

/-- The compact-support premise is discharged from the actual norm annulus. -/
theorem localTest_hasCompactSupport_of_annulus (φ : HeckeIdeleClasses K → ℂ)
    (v : FinitePlace K) (T : ℝ) (hT : 1 < T)
    (hsupp : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < localAbs K v x ∧ localAbs K v x < T) :
    HasCompactSupport (fun x : (LocalField K v)ˣ => φ (localClass K v x)) := by
  classical
  obtain ⟨M, hM⟩ := localTest_log_bounded K φ v T hT hsupp
  let C : Set ((LocalField K v)ˣ) := ⋃ n ∈ Set.Icc (-M) M,
    {x | Valued.v (x : LocalField K v) = WithZero.exp n}
  have hC : IsCompact C :=
    (Set.finite_Icc (-M) M).isCompact_biUnion fun n _ =>
      localValuationFiber_isCompact K v (WithZero.exp n)
  apply hC.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hC.isClosed
  intro x hx
  have hn := hM x hx
  apply Set.mem_iUnion.mpr
  refine ⟨(Valued.v (x : LocalField K v)).log, Set.mem_iUnion.mpr ⟨hn, ?_⟩⟩
  exact (WithZero.exp_log ((map_ne_zero (Valued.v : Valuation (LocalField K v) (WithZero (Multiplicative ℤ)))).mpr (Units.ne_zero x))).symm

local instance (v : FinitePlace K) : MeasurableSpace ((LocalField K v)ˣ) := borel _
local instance (v : FinitePlace K) : BorelSpace ((LocalField K v)ˣ) := ⟨rfl⟩

/-- Geometric-side convergence for annular continuous local restrictions, with
no separate compact-support or Haar-normalization premise. -/
theorem normalizedFiniteGeometric_convergence_of_annulus
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hc : ∀ v : FinitePlace K, v.asIdeal.absNorm ≤ N →
      Continuous (fun x : (LocalField K v)ˣ => φ (localClass K v x))) :
    (∀ v, MeasureTheory.Integrable (localGeometricIntegrand K φ v) (normalizedLocalHaar K v)) ∧
    Summable (fun v => ‖finiteGeometricTerm K φ (normalizedLocalHaar K) v‖) ∧
    ∃ S : Finset (FinitePlace K),
      (∑' v, finiteGeometricTerm K φ (normalizedLocalHaar K) v) =
        ∑ v ∈ S, finiteGeometricTerm K φ (normalizedLocalHaar K) v := by
  apply normalizedFiniteGeometric_convergence K φ N hN hunit hsupp hc
  intro v _
  exact localTest_hasCompactSupport_of_annulus K φ v N hN (hsupp v)

#check localValuationFiber_isCompact
#print axioms localValuationFiber_isCompact
#check localTest_log_bounded
#print axioms localTest_log_bounded
#check localTest_hasCompactSupport_of_annulus
#print axioms localTest_hasCompactSupport_of_annulus
#check normalizedFiniteGeometric_convergence_of_annulus
#print axioms normalizedFiniteGeometric_convergence_of_annulus
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Continuity of the genuine one-place adele insertion. -/
theorem localFiniteAdele_continuous (v : FinitePlace K) :
    Continuous (localFiniteAdele K v) := by
  classical
  let S : Set (FinitePlace K) := {v}ᶜ
  let f : LocalField K v → RestrictedProduct (LocalField K)
      (fun w => (w.adicCompletionIntegers K : Set (LocalField K w)))
      (Filter.principal S) := fun x => ⟨Function.update (fun _ => 1) v x, by
        rw [Filter.eventually_principal]
        intro w hw
        have hwv : w ≠ v := by simpa [S] using hw
        simp [Function.update_of_ne hwv]⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    intro w
    by_cases hw : w = v
    · subst w
      simpa [f, Function.comp_def] using
        (continuous_id : Continuous (fun x : LocalField K v => x))
    · simpa [f, Function.comp_def, Function.update_of_ne hw] using
        (continuous_const : Continuous (fun _ : LocalField K v => (1 : LocalField K w)))
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    apply Filter.eventually_cofinite.mpr
    simp
  exact (RestrictedProduct.continuous_inclusion hS).comp hf

/-- Continuity includes both the adele and its inverse, as required for ideles. -/
theorem localIdele_continuous (v : FinitePlace K) :
    Continuous (localIdele K v) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact continuous_const.prodMk ((localFiniteAdele_continuous K v).comp
      Units.continuous_val)
  · exact continuous_const.prodMk ((localFiniteAdele_continuous K v).comp
      Units.continuous_coe_inv)

/-- The actual local insertion into the genuine quotient is continuous. -/
theorem localClass_continuous (v : FinitePlace K) :
    Continuous (localClass K v) :=
  QuotientGroup.continuous_mk.comp (localIdele_continuous K v)

#check localFiniteAdele_continuous
#print axioms localFiniteAdele_continuous
#check localIdele_continuous
#print axioms localIdele_continuous
#check localClass_continuous
#print axioms localClass_continuous
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
local instance (v : FinitePlace K) : MeasurableSpace ((LocalField K v)ˣ) := borel _
local instance (v : FinitePlace K) : BorelSpace ((LocalField K v)ˣ) := ⟨rfl⟩

/-- Finite geometric term of (12.5.1.2) for a globally continuous genuine test.
Local continuity and local compact support are proved, not extra premises. -/
theorem normalizedFiniteGeometric_convergence_of_continuous_test
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hc : Continuous φ) :
    (∀ v, MeasureTheory.Integrable (localGeometricIntegrand K φ v) (normalizedLocalHaar K v)) ∧
    Summable (fun v => ‖finiteGeometricTerm K φ (normalizedLocalHaar K) v‖) ∧
    ∃ S : Finset (FinitePlace K),
      (∑' v, finiteGeometricTerm K φ (normalizedLocalHaar K) v) =
        ∑ v ∈ S, finiteGeometricTerm K φ (normalizedLocalHaar K) v := by
  exact normalizedFiniteGeometric_convergence_of_annulus K φ N hN hunit hsupp
    (fun v _ => hc.comp (localClass_continuous K v))

#check normalizedFiniteGeometric_convergence_of_continuous_test
#print axioms normalizedFiniteGeometric_convergence_of_continuous_test
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
local instance (v : FinitePlace K) : MeasurableSpace ((LocalField K v)ˣ) := borel _
local instance (v : FinitePlace K) : BorelSpace ((LocalField K v)ˣ) := ⟨rfl⟩

/-- Bounded continuous test cutoffs can be removed from the actual finite
geometric expression (12.5.1.2). Convergence is required only where the test
is nonzero, allowing cutoffs that vanish on the norm-one locus. This does
not assert convergence of the manuscript operator cutoffs or spectral sum. -/
theorem normalizedFiniteGeometric_cutoff_limit
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ) (hN : 1 < (N : ℝ))
    (hunit : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → φ (localClass K v x) = 0)
    (hsupp : ∀ (v : FinitePlace K) (x : (LocalField K v)ˣ),
      φ (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ))
    (hc : Continuous φ) (b : ℕ → HeckeIdeleClasses K → ℂ)
    (hbc : ∀ n, Continuous (b n)) (hb : ∀ n g, ‖b n g‖ ≤ 1)
    (hlim : ∀ g, φ g ≠ 0 → Filter.Tendsto (fun n => b n g) Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun n => ∑' v, finiteGeometricTerm K (fun g => b n g * φ g) (normalizedLocalHaar K) v)
      Filter.atTop (nhds (∑' v, finiteGeometricTerm K φ (normalizedLocalHaar K) v)) := by
  classical
  let ψ := fun n g => b n g * φ g
  have hu : ∀ n v (x : (LocalField K v)ˣ),
      (Valued.v (x : LocalField K v)).log = 0 → ψ n (localClass K v x) = 0 := by
    intro n v x hx
    simp [ψ, hunit v x hx]
  have hs : ∀ n v (x : (LocalField K v)ˣ), ψ n (localClass K v x) ≠ 0 →
      (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ) := by
    intro n v x hx
    apply hsupp v x
    intro hz
    exact hx (by simp [ψ, hz])
  have hi := (normalizedFiniteGeometric_convergence_of_continuous_test K φ N hN hunit hsupp hc).1
  have he : ∀ n v (x : (LocalField K v)ˣ),
      localGeometricIntegrand K (ψ n) v x =
        b n (localClass K v x) * localGeometricIntegrand K φ v x := by
    intro n v x
    simp only [localGeometricIntegrand, ψ]
    ring
  have hl : ∀ v, Filter.Tendsto
      (fun n => ∫ x, localGeometricIntegrand K (ψ n) v x ∂normalizedLocalHaar K v)
      Filter.atTop (nhds (∫ x, localGeometricIntegrand K φ v x ∂normalizedLocalHaar K v)) := by
    intro v
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x => ‖localGeometricIntegrand K φ v x‖)
    · intro n
      exact (localGeometric_continuous K (ψ n) v
        (((hbc n).mul hc).comp (localClass_continuous K v)) (hu n v)).aestronglyMeasurable
    · exact (hi v).norm
    · intro n
      apply Filter.Eventually.of_forall
      intro x
      rw [he, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hb n _) (norm_nonneg _)).trans_eq (one_mul _)
    · apply Filter.Eventually.of_forall
      intro x
      by_cases hz : φ (localClass K v x) = 0
      · simp [localGeometricIntegrand, ψ, hz]
      · simp_rw [he]
        simpa only [one_mul] using (hlim _ hz).mul_const (localGeometricIntegrand K φ v x)
  let S := (finitePlaces_bounded_norm K N).toFinset
  have hz : ∀ (f : HeckeIdeleClasses K → ℂ),
      (∀ v (x : (LocalField K v)ˣ), (Valued.v (x : LocalField K v)).log = 0 → f (localClass K v x) = 0) →
      (∀ v (x : (LocalField K v)ˣ), f (localClass K v x) ≠ 0 →
        (N : ℝ)⁻¹ < localAbs K v x ∧ localAbs K v x < (N : ℝ)) →
      (∑' v, finiteGeometricTerm K f (normalizedLocalHaar K) v) =
        ∑ v ∈ S, finiteGeometricTerm K f (normalizedLocalHaar K) v := by
    intro f huf hsf
    apply tsum_eq_sum
    intro v hv
    have hn : N < v.asIdeal.absNorm := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] using hv
    have hv' : (N : ℝ) < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast hn
    simp [finiteGeometricTerm,
      (localGeometric_integrable_and_integral_zero K f N hN v hv'
        (normalizedLocalHaar K v) (huf v) (hsf v)).2]
  change Filter.Tendsto (fun n => ∑' v, finiteGeometricTerm K (ψ n) (normalizedLocalHaar K) v) _ _
  simp_rw [hz φ hunit hsupp, hz (ψ _) (hu _) (hs _)]
  apply tendsto_finset_sum S
  intro v _
  simpa only [normalizedFiniteGeometricTerm] using
    (hl v).const_mul (Real.log (v.asIdeal.absNorm : ℝ) : ℂ)

#check normalizedFiniteGeometric_cutoff_limit
#print axioms normalizedFiniteGeometric_cutoff_limit
end MasulloGRH
