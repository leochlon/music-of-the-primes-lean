import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-! Participant A, round 56: a finite-place support reduction immediately used
in manuscript Theorem 12.5.1.1, PDF page 520. The operator trace identity is
INCOMPLETE. The actual adele/local-idele definitions below are selected from
the preserved round-53 F checked source; no historical proof assertions are
imported. Only Mathlib is imported. -/
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


noncomputable def normalizedLocalNorm (v : FinitePlace K) (x : LocalField K v) : ℝ :=
  if x = 0 then 0 else (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log

noncomputable def localClass (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    HeckeIdeleClasses K := QuotientGroup.mk (localIdele K v x)

/-- The finite-place contribution in (12.5.1.2), before its scalar Haar factor. -/
noncomputable def localGeometricIntegrand (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (x : (LocalField K v)ˣ) : ℂ :=
  φ (localClass K v x) * (Real.sqrt (normalizedLocalNorm K v x) : ℂ) /
    (normalizedLocalNorm K v (1 - (x : LocalField K v)) : ℂ)

/-- Support reduction used for the finite set S on manuscript PDF page 520.
The explicit local support and norm-one hypotheses still have to be deduced
from the global admissible test-function conditions. -/
theorem largePlace_test_vanishes (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hqT : T < (v.asIdeal.absNorm : ℝ))
    (hsupport : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0) :
    ∀ x : (LocalField K v)ˣ, φ (localClass K v x) = 0 := by
  intro x
  by_contra hx
  obtain ⟨hlo, hhi⟩ := hsupport x hx
  have hx0 : (x : LocalField K v) ≠ 0 := Units.ne_zero x
  simp only [normalizedLocalNorm, if_neg hx0] at hlo hhi
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := lt_trans hT hqT
  let n : ℤ := (Valued.v (x : LocalField K v)).log
  by_cases hn : n = 0
  · apply hx
    apply hone x
    simp only [normalizedLocalNorm, if_neg hx0]
    change (v.asIdeal.absNorm : ℝ) ^ n = 1
    rw [hn, zpow_zero]
  · rcases lt_or_gt_of_ne hn with hn | hn
    · have he : n ≤ -1 := by omega
      have hb : (v.asIdeal.absNorm : ℝ) ^ n ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
        exact zpow_le_zpow_right₀ hq.le he
      have hi : (v.asIdeal.absNorm : ℝ)⁻¹ < T⁻¹ := inv_lt_inv₀ (by linarith) (by linarith) |>.2 hqT
      simp only [zpow_neg_one] at hb
      exact (not_lt_of_ge (le_trans hb hi.le)) hlo
    · have he : (1 : ℤ) ≤ n := by omega
      have hb : (v.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤ (v.asIdeal.absNorm : ℝ) ^ n := by
        exact zpow_le_zpow_right₀ hq.le he
      simp only [zpow_one] at hb
      exact (not_lt_of_ge (le_trans hqT.le hb)) hhi

#check largePlace_test_vanishes
#print axioms largePlace_test_vanishes

open MeasureTheory

theorem largePlace_geometric_integrand_zero (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hqT : T < (v.asIdeal.absNorm : ℝ))
    (hsupport : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0) :
    localGeometricIntegrand K v φ = 0 := by
  funext x
  simp [localGeometricIntegrand, largePlace_test_vanishes K v φ T hT hqT hsupport hone x]

theorem largePlace_geometric_integral_zero (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hqT : T < (v.asIdeal.absNorm : ℝ))
    (hsupport : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    [MeasurableSpace (LocalField K v)ˣ] (μ : Measure (LocalField K v)ˣ) :
    Integrable (localGeometricIntegrand K v φ) μ ∧
      (∫ x, localGeometricIntegrand K v φ x ∂μ) = 0 := by
  rw [largePlace_geometric_integrand_zero K v φ T hT hqT hsupport hone]
  exact ⟨integrable_zero _ _ _, by simp⟩

#check largePlace_geometric_integrand_zero
#print axioms largePlace_geometric_integrand_zero
#check largePlace_geometric_integral_zero
#print axioms largePlace_geometric_integral_zero

lemma residueNorm_nnreal_ne_zero (v : FinitePlace K) :
    (v.asIdeal.absNorm : NNReal) ≠ 0 := by
  have h := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  exact_mod_cast (ne_of_gt (lt_trans Nat.zero_lt_one h))

/-- The formula used in the geometric integrand is the actual residue-cardinality
normalization of the completion valuation, including at zero. -/
theorem normalizedLocalNorm_eq_valuation (v : FinitePlace K) (x : LocalField K v) :
    normalizedLocalNorm K v x =
      ((WithZeroMulInt.toNNReal (residueNorm_nnreal_ne_zero K v) (Valued.v x) : NNReal) : ℝ) := by
  by_cases hx : x = 0
  · subst x
    simp [normalizedLocalNorm]
  · have hv : Valued.v x ≠ 0 := by simpa using hx
    simp only [normalizedLocalNorm, if_neg hx]
    conv_rhs => rw [← WithZero.exp_log hv,
      WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    simp

/-- Identical finite-coordinate modulus to the checked round-53 construction. -/
noncomputable def arithmeticFiniteIdeleNorm (a : HeckeIdeles K) : ℝ :=
  ∏ᶠ v : FinitePlace K, ((WithZeroMulInt.toNNReal
    (residueNorm_nnreal_ne_zero K v) (Valued.v (a.val.2 v)) : NNReal) : ℝ)

theorem localIdele_finiteNorm (v : FinitePlace K) (x : (LocalField K v)ˣ) :
    arithmeticFiniteIdeleNorm K (localIdele K v x) = normalizedLocalNorm K v x := by
  classical
  unfold arithmeticFiniteIdeleNorm
  rw [finprod_eq_single _ v]
  · rw [normalizedLocalNorm_eq_valuation]
    congr 2
    change Valued.v (Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑x) v) = Valued.v (x : LocalField K v)
    simp
  · intro w hw
    change ((WithZeroMulInt.toNNReal (residueNorm_nnreal_ne_zero K w)
      (Valued.v (Function.update (fun w : FinitePlace K => (1 : LocalField K w)) v (↑x) w)) : NNReal) : ℝ) = 1
    simp [Function.update_of_ne hw]

#check residueNorm_nnreal_ne_zero
#print axioms residueNorm_nnreal_ne_zero
#check normalizedLocalNorm_eq_valuation
#print axioms normalizedLocalNorm_eq_valuation
#check localIdele_finiteNorm
#print axioms localIdele_finiteNorm

section GeometricSum
variable [∀ v : FinitePlace K, MeasurableSpace (LocalField K v)ˣ]

/-- Precisely the finite-place coefficient in (12.5.1.2), for the given measures.
At contributing places, identifying the ordinary integral with the primed local
distribution remains an analytic obligation. -/
noncomputable def finiteLocalGeometricTerm
    (μ : ∀ v : FinitePlace K, Measure (LocalField K v)ˣ)
    (φ : HeckeIdeleClasses K → ℂ) (v : FinitePlace K) : ℂ :=
  ((Real.log (v.asIdeal.absNorm : ℝ) /
    (μ v {x | normalizedLocalNorm K v (x : LocalField K v) = 1}).toReal : ℝ) : ℂ) *
      ∫ x, localGeometricIntegrand K v φ x ∂(μ v)

/-- Exact finite reduction of the finite-place geometric expression. -/
theorem finite_geometric_sum_reduction
    (μ : ∀ v : FinitePlace K, Measure (LocalField K v)ˣ)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (S : Finset (FinitePlace K))
    (hS : ∀ v ∉ S, T < (v.asIdeal.absNorm : ℝ))
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hintegrable : ∀ v ∈ S, Integrable (localGeometricIntegrand K v φ) (μ v)) :
    (∀ v, Integrable (localGeometricIntegrand K v φ) (μ v)) ∧
    (∑' v, finiteLocalGeometricTerm K μ φ v) =
      ∑ v ∈ S, finiteLocalGeometricTerm K μ φ v := by
  constructor
  · intro v
    by_cases hv : v ∈ S
    · exact hintegrable v hv
    · exact (largePlace_geometric_integral_zero K v φ T hT (hS v hv)
        (hsupport v) (hone v) (μ v)).1
  · apply tsum_eq_sum
    intro v hv
    unfold finiteLocalGeometricTerm
    rw [(largePlace_geometric_integral_zero K v φ T hT (hS v hv)
      (hsupport v) (hone v) (μ v)).2, mul_zero]

#check finite_geometric_sum_reduction
#print axioms finite_geometric_sum_reduction
end GeometricSum

/-- The genuine finite places with bounded residue norm form a finite set,
used to select S in manuscript Theorem 12.5.1.1, page 520. -/
theorem finite_smallNormPlaces (T : ℝ) :
    {v : FinitePlace K | (v.asIdeal.absNorm : ℝ) ≤ T}.Finite := by
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hi : Function.Injective (fun v : FinitePlace K => v.asIdeal) := by
    intro v w h
    exact IsDedekindDomain.HeightOneSpectrum.ext h
  have hf : {v : FinitePlace K | v.asIdeal.absNorm ≤ n}.Finite :=
    Set.Finite.preimage hi.injOn (Ideal.finite_setOf_absNorm_le n)
  apply hf.subset
  intro v hv
  have hb : (v.asIdeal.absNorm : ℝ) ≤ (n : ℝ) := le_trans hv hn.le
  exact_mod_cast hb

noncomputable def smallNormPlaces (T : ℝ) : Finset (FinitePlace K) :=
  (finite_smallNormPlaces K T).toFinset

@[simp] theorem mem_smallNormPlaces (T : ℝ) (v : FinitePlace K) :
    v ∈ smallNormPlaces K T ↔ (v.asIdeal.absNorm : ℝ) ≤ T := by
  simp [smallNormPlaces]

#check finite_smallNormPlaces
#print axioms finite_smallNormPlaces
#check mem_smallNormPlaces
#print axioms mem_smallNormPlaces

section ActualGeometricConvergence
variable [∀ v : FinitePlace K, MeasurableSpace (LocalField K v)ˣ]

/-- Absolute convergence of the finite-place series in (12.5.1.2), with the
exceptional finite set constructed from actual residue norms. The remaining
local hypotheses are explicit; no trace identity is assumed. -/
theorem finite_geometric_absolute_convergence
    (μ : ∀ v : FinitePlace K, Measure (LocalField K v)ˣ)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hintegrable : ∀ v, (v.asIdeal.absNorm : ℝ) ≤ T →
      Integrable (localGeometricIntegrand K v φ) (μ v)) :
    (∀ v, Integrable (localGeometricIntegrand K v φ) (μ v)) ∧
    Summable (fun v => finiteLocalGeometricTerm K μ φ v) ∧
    Summable (fun v => ‖finiteLocalGeometricTerm K μ φ v‖) ∧
    (∑' v, finiteLocalGeometricTerm K μ φ v) =
      ∑ v ∈ smallNormPlaces K T, finiteLocalGeometricTerm K μ φ v := by
  have hS : ∀ v ∉ smallNormPlaces K T, T < (v.asIdeal.absNorm : ℝ) := by
    intro v hv
    exact lt_of_not_ge (by simpa using hv)
  have hz : ∀ v ∉ smallNormPlaces K T, finiteLocalGeometricTerm K μ φ v = 0 := by
    intro v hv
    unfold finiteLocalGeometricTerm
    rw [(largePlace_geometric_integral_zero K v φ T hT (hS v hv)
      (hsupport v) (hone v) (μ v)).2, mul_zero]
  have hr := finite_geometric_sum_reduction K μ φ T hT (smallNormPlaces K T)
    hS hsupport hone (fun v hv => hintegrable v ((mem_smallNormPlaces K T v).1 hv))
  refine ⟨hr.1, ?_, ?_, hr.2⟩
  · exact summable_of_ne_finset_zero hz
  · apply summable_of_ne_finset_zero (s := smallNormPlaces K T)
    intro v hv
    rw [hz v hv, norm_zero]

#check finite_geometric_absolute_convergence
#print axioms finite_geometric_absolute_convergence

/-- The place cutoff in the genuine finite geometric expression stabilizes
exactly once it contains the actual small-norm places. This is a place cutoff,
not the still-unproved operator cutoff in rho and Lambda. -/
theorem finite_geometric_place_cutoffs
    (μ : ∀ v : FinitePlace K, Measure (LocalField K v)ˣ)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hintegrable : ∀ v, (v.asIdeal.absNorm : ℝ) ≤ T →
      Integrable (localGeometricIntegrand K v φ) (μ v)) :
    (∀ S : Finset (FinitePlace K), smallNormPlaces K T ⊆ S →
      (∑ v ∈ S, finiteLocalGeometricTerm K μ φ v) =
        ∑' v, finiteLocalGeometricTerm K μ φ v) ∧
    Filter.Tendsto (fun S : Finset (FinitePlace K) =>
      ∑ v ∈ S, finiteLocalGeometricTerm K μ φ v)
      Filter.atTop (nhds (∑' v, finiteLocalGeometricTerm K μ φ v)) := by
  have hc := finite_geometric_absolute_convergence K μ φ T hT hsupport hone hintegrable
  constructor
  · intro S hS
    have hs : ∀ v ∉ S, T < (v.asIdeal.absNorm : ℝ) := by
      intro v hv
      apply lt_of_not_ge
      intro hn
      exact hv (hS ((mem_smallNormPlaces K T v).2 hn))
    exact (finite_geometric_sum_reduction K μ φ T hT S hs hsupport hone
      (fun v _ => hc.1 v)).2.symm
  · exact hc.2.1.hasSum

#check finite_geometric_place_cutoffs
#print axioms finite_geometric_place_cutoffs
end ActualGeometricConvergence
end MasulloGRH


namespace MasulloGRH
open MeasureTheory Topology Filter
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine local geometric integrand vanishes on an open neighborhood of
identity. This removes the finite-place singularity before taking any trace
or local-distribution limit in manuscript (12.5.1.2). -/
theorem localGeometricIntegrand_zero_near_one (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0) :
    ∀ᶠ x in 𝓝 (1 : (LocalField K v)ˣ), localGeometricIntegrand K v φ x = 0 := by
  have hU : {x : LocalField K v | Valued.v x = 1} ∈ 𝓝 (1 : LocalField K v) :=
    (Valued.isClopen_sphere (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen.mem_nhds (by simp)
  have h := (Units.continuous_val.continuousAt (x := (1 : (LocalField K v)ˣ))).preimage_mem_nhds hU
  filter_upwards [h] with x hx
  have hn : normalizedLocalNorm K v x = 1 := by
    rw [normalizedLocalNorm_eq_valuation]
    change Valued.v (x : LocalField K v) = 1 at hx
    simp [hx]
  simp [localGeometricIntegrand, hone x hn]

#check localGeometricIntegrand_zero_near_one
#print axioms localGeometricIntegrand_zero_near_one

/-- Deleting any set contained in the genuine valuation-one shell leaves the
finite geometric integrand exactly unchanged, including at x=1. -/
theorem localGeometricIntegrand_cutoff_eq (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (U : Set (LocalField K v)ˣ)
    (hU : ∀ x ∈ U, Valued.v (x : LocalField K v) = 1) :
    Uᶜ.indicator (localGeometricIntegrand K v φ) = localGeometricIntegrand K v φ := by
  classical
  funext x
  by_cases hx : x ∈ U
  · have hn : normalizedLocalNorm K v x = 1 := by
      rw [normalizedLocalNorm_eq_valuation]
      simp [hU x hx]
    simp [hx, localGeometricIntegrand, hone x hn]
  · simp [hx]

#check localGeometricIntegrand_cutoff_eq
#print axioms localGeometricIntegrand_cutoff_eq

/-- The local regularized integrals formed by excluding neighborhoods inside
the unit shell already equal the uncut integral. No limit interchange or
integrability assumption is needed for this exact equality. Integrability
of the contributing Haar integrands is still a separate obligation. -/
theorem localGeometricIntegral_cutoff_eq (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (U : Set (LocalField K v)ˣ)
    (hU : ∀ x ∈ U, Valued.v (x : LocalField K v) = 1)
    [MeasurableSpace (LocalField K v)ˣ] (μ : Measure (LocalField K v)ˣ) :
    (∫ x, Uᶜ.indicator (localGeometricIntegrand K v φ) x ∂μ) =
      ∫ x, localGeometricIntegrand K v φ x ∂μ := by
  rw [localGeometricIntegrand_cutoff_eq K v φ hone U hU]

#check localGeometricIntegral_cutoff_eq
#print axioms localGeometricIntegral_cutoff_eq
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The actual nonarchimedean denominator off the norm-one shell. -/
theorem normalizedLocalNorm_one_sub (v : FinitePlace K) (x : LocalField K v)
    (hx : normalizedLocalNorm K v x ≠ 1) :
    normalizedLocalNorm K v (1-x) = max 1 (normalizedLocalNorm K v x) := by
  have hv : Valued.v (1 : LocalField K v) ≠ Valued.v (-x) := by
    intro h
    have hxv : Valued.v x = 1 := by simpa using h.symm
    apply hx
    rw [normalizedLocalNorm_eq_valuation]
    simp [hxv]
  have he := Valuation.map_add_of_distinct_val Valued.v hv
  have hq : (1 : NNReal) < (v.asIdeal.absNorm : NNReal) := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hm : Monotone (WithZeroMulInt.toNNReal (residueNorm_nnreal_ne_zero K v)) :=
    (WithZeroMulInt.toNNReal_strictMono hq).monotone
  rw [normalizedLocalNorm_eq_valuation, normalizedLocalNorm_eq_valuation]
  simp only [sub_eq_add_neg, he, map_one, Valuation.map_neg]
  rw [hm.map_max]
  simp

#check normalizedLocalNorm_one_sub
#print axioms normalizedLocalNorm_one_sub

/-- Domination by the genuine local test pullback. The condition used here is
precisely vanishing on the norm-one shell, not vanishing on an enlarged test
space. This is the estimate needed for local Haar integrability in (12.5.1.2). -/
theorem localGeometricIntegrand_norm_le (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0) (x : (LocalField K v)ˣ) :
    ‖localGeometricIntegrand K v φ x‖ ≤ ‖φ (localClass K v x)‖ := by
  by_cases hx : normalizedLocalNorm K v x = 1
  · simp [localGeometricIntegrand, hone x hx]
  · have hd := normalizedLocalNorm_one_sub K v (x : LocalField K v) hx
    have hdpos : 0 < max 1 (normalizedLocalNorm K v x) :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hs : Real.sqrt (normalizedLocalNorm K v x) ≤ max 1 (normalizedLocalNorm K v x) := by
      by_cases hr : normalizedLocalNorm K v x ≤ 1
      · exact (Real.sqrt_le_one.mpr hr).trans (le_max_left _ _)
      · have hr' : 1 ≤ normalizedLocalNorm K v x := le_of_lt (lt_of_not_ge hr)
        have hsq := Real.sq_sqrt (le_trans zero_le_one hr')
        have hsn := Real.sqrt_nonneg (normalizedLocalNorm K v x)
        have hh : Real.sqrt (normalizedLocalNorm K v x) ≤ normalizedLocalNorm K v x := by
          nlinarith
        exact hh.trans (le_max_right _ _)
    rw [localGeometricIntegrand, norm_div, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), hd, abs_of_pos hdpos]
    apply (div_le_iff₀ hdpos).2
    exact mul_le_mul_of_nonneg_left hs (norm_nonneg _)

#check localGeometricIntegrand_norm_le
#print axioms localGeometricIntegrand_norm_le

/-- Integrated use of the bound: local pullback integrability suffices for
integrability of the genuine geometric kernel, given measurability. -/
theorem localGeometricIntegrand_integrable (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    [MeasurableSpace (LocalField K v)ˣ] (μ : Measure (LocalField K v)ˣ)
    (hφ : Integrable (fun x => φ (localClass K v x)) μ)
    (hm : AEStronglyMeasurable (localGeometricIntegrand K v φ) μ) :
    Integrable (localGeometricIntegrand K v φ) μ := by
  apply hφ.norm.mono' hm
  exact Filter.Eventually.of_forall (localGeometricIntegrand_norm_le K v φ hone)

#check localGeometricIntegrand_integrable
#print axioms localGeometricIntegrand_integrable
end MasulloGRH

namespace MasulloGRH
open MeasureTheory Topology Filter
variable (K : Type*) [Field K] [NumberField K]

/-- Actual residue-normalized modulus on local units. -/
theorem continuous_normalizedLocalNorm_units (v : FinitePlace K) :
    Continuous (fun x : (LocalField K v)ˣ => normalizedLocalNorm K v x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hv : Valued.v (x : LocalField K v) ≠ 0 := by simp
  have hU : {y : LocalField K v | Valued.v y = Valued.v (x : LocalField K v)} ∈
      𝓝 (x : LocalField K v) :=
    (Valued.isClopen_sphere (LocalField K v) hv).isOpen.mem_nhds rfl
  have he := (Units.continuous_val.continuousAt (x := x)).preimage_mem_nhds hU
  apply (show ContinuousAt (fun _ : (LocalField K v)ˣ => normalizedLocalNorm K v x) x from
    continuousAt_const).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  rw [normalizedLocalNorm_eq_valuation, normalizedLocalNorm_eq_valuation]
  change Valued.v (y : LocalField K v) = Valued.v (x : LocalField K v) at hy
  rw [hy]

#check continuous_normalizedLocalNorm_units
#print axioms continuous_normalizedLocalNorm_units

/-- Replace the denominator by a nowhere-zero expression using norm-one vanishing. -/
theorem localGeometricIntegrand_eq_nonsingular (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0) :
    localGeometricIntegrand K v φ = fun x =>
      φ (localClass K v x) * (Real.sqrt (normalizedLocalNorm K v x) : ℂ) /
        ((max 1 (normalizedLocalNorm K v x) : ℝ) : ℂ) := by
  funext x
  by_cases hx : normalizedLocalNorm K v x = 1
  · simp [localGeometricIntegrand, hone x hx]
  · simp only [localGeometricIntegrand, normalizedLocalNorm_one_sub K v _ hx]

#check localGeometricIntegrand_eq_nonsingular
#print axioms localGeometricIntegrand_eq_nonsingular

theorem continuous_localGeometricIntegrand (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hφ : Continuous (fun x => φ (localClass K v x))) :
    Continuous (localGeometricIntegrand K v φ) := by
  rw [localGeometricIntegrand_eq_nonsingular K v φ hone]
  have hn := continuous_normalizedLocalNorm_units K v
  apply (hφ.mul (Complex.continuous_ofReal.comp hn.sqrt)).div
    (Complex.continuous_ofReal.comp (continuous_const.max hn))
  intro x
  have hp : 0 < max 1 (normalizedLocalNorm K v x) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  change ((max 1 (normalizedLocalNorm K v x) : ℝ) : ℂ) ≠ 0
  exact_mod_cast ne_of_gt hp

#check continuous_localGeometricIntegrand
#print axioms continuous_localGeometricIntegrand

/-- Discharges geometric integrability from local compact support and continuity. -/
theorem localGeometricIntegrand_integrable_of_compact (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    [MeasurableSpace (LocalField K v)ˣ] [OpensMeasurableSpace (LocalField K v)ˣ]
    (μ : Measure (LocalField K v)ˣ) [IsFiniteMeasureOnCompacts μ]
    (hφ : Continuous (fun x => φ (localClass K v x)))
    (hc : HasCompactSupport (fun x => φ (localClass K v x))) :
    Integrable (localGeometricIntegrand K v φ) μ := by
  exact localGeometricIntegrand_integrable K v φ hone μ
    (hφ.integrable_of_hasCompactSupport hc)
    (continuous_localGeometricIntegrand K v φ hone hφ).aestronglyMeasurable

#check localGeometricIntegrand_integrable_of_compact
#print axioms localGeometricIntegrand_integrable_of_compact

/-- Direct integration into the actual finite geometric expression (12.5.1.2).
Local hypotheses still need derivation from the global admissible test space;
this is not the operator cutoff or the complete trace theorem. -/
theorem finite_geometric_convergence_of_local_compact
    [∀ v : FinitePlace K, MeasurableSpace (LocalField K v)ˣ]
    [∀ v : FinitePlace K, OpensMeasurableSpace (LocalField K v)ˣ]
    (μ : ∀ v : FinitePlace K, Measure (LocalField K v)ˣ)
    [∀ v : FinitePlace K, IsFiniteMeasureOnCompacts (μ v)]
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hcontinuous : ∀ v, Continuous (fun x => φ (localClass K v x)))
    (hcompact : ∀ v, (v.asIdeal.absNorm : ℝ) ≤ T →
      HasCompactSupport (fun x => φ (localClass K v x))) :
    (∀ v, Integrable (localGeometricIntegrand K v φ) (μ v)) ∧
    Summable (fun v => finiteLocalGeometricTerm K μ φ v) ∧
    Summable (fun v => ‖finiteLocalGeometricTerm K μ φ v‖) ∧
    (∑' v, finiteLocalGeometricTerm K μ φ v) =
      ∑ v ∈ smallNormPlaces K T, finiteLocalGeometricTerm K μ φ v ∧
    Filter.Tendsto (fun S : Finset (FinitePlace K) =>
      ∑ v ∈ S, finiteLocalGeometricTerm K μ φ v)
      Filter.atTop (nhds (∑' v, finiteLocalGeometricTerm K μ φ v)) := by
  have hi : ∀ v, (v.asIdeal.absNorm : ℝ) ≤ T →
      Integrable (localGeometricIntegrand K v φ) (μ v) := by
    intro v hv
    exact localGeometricIntegrand_integrable_of_compact K v φ (hone v) (μ v)
      (hcontinuous v) (hcompact v hv)
  have h := finite_geometric_absolute_convergence K μ φ T hT hsupport hone hi
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
    (finite_geometric_place_cutoffs K μ φ T hT hsupport hone hi).2⟩

#check finite_geometric_convergence_of_local_compact
#print axioms finite_geometric_convergence_of_local_compact
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
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

noncomputable def integralLocalUnit (v : FinitePlace K)
    (u : (v.adicCompletionIntegers K)ˣ) : (LocalField K v)ˣ :=
  Units.map (v.adicCompletionIntegers K).subtype.toMonoidHom u

def geometricLocalUnitSet (v : FinitePlace K) : Set (LocalField K v)ˣ :=
  {x | Valued.v (x : LocalField K v) ≤ 1 ∧
    Valued.v (↑(x⁻¹) : LocalField K v) ≤ 1}

theorem geometricLocalUnitSet_eq_range (v : FinitePlace K) :
    geometricLocalUnitSet K v = Set.range (integralLocalUnit K v) := by
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

 theorem geometricLocalUnitSet_compact (v : FinitePlace K) :
    IsCompact (geometricLocalUnitSet K v) := by
  letI := localIntegralUnits_compactSpace K v
  rw [geometricLocalUnitSet_eq_range]
  apply isCompact_range
  apply Units.continuous_iff.mpr
  exact ⟨continuous_subtype_val.comp Units.continuous_val,
    continuous_subtype_val.comp Units.continuous_coe_inv⟩

theorem geometricLocalUnitSet_open (v : FinitePlace K) :
    IsOpen (geometricLocalUnitSet K v) := by
  have ho := (Valued.isClopen_closedBall (LocalField K v)
    (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen
  exact (ho.preimage Units.continuous_val).inter
    (ho.preimage Units.continuous_coe_inv)

noncomputable def geometricLocalUnitCompact (v : FinitePlace K) :
    TopologicalSpace.PositiveCompacts (LocalField K v)ˣ :=
  ⟨⟨geometricLocalUnitSet K v, geometricLocalUnitSet_compact K v⟩, by
    rw [(geometricLocalUnitSet_open K v).interior_eq]
    exact ⟨1, by simp [geometricLocalUnitSet]⟩⟩

local instance (v : FinitePlace K) : MeasurableSpace (LocalField K v)ˣ := borel _
local instance (v : FinitePlace K) : BorelSpace (LocalField K v)ˣ := ⟨rfl⟩

/-- Multiplicative Haar measure used for the local geometric term (12.5.1.2). -/
noncomputable def geometricLocalHaar (v : FinitePlace K) :
    Measure (LocalField K v)ˣ := Measure.haarMeasure (geometricLocalUnitCompact K v)

theorem geometricLocalHaar_isHaar (v : FinitePlace K) :
    (geometricLocalHaar K v).IsHaarMeasure := by
  unfold geometricLocalHaar
  infer_instance

theorem geometricLocalHaar_units (v : FinitePlace K) :
    geometricLocalHaar K v (geometricLocalUnitSet K v) = 1 :=
  Measure.haarMeasure_self

/-- Immediate use of the constructed Haar measure in the genuine local
geometric integrability obligation of manuscript (12.5.1.2). -/
theorem localGeometricIntegrand_integrable_haar (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hφ : Continuous (fun x => φ (localClass K v x)))
    (hc : HasCompactSupport (fun x => φ (localClass K v x))) :
    Integrable (localGeometricIntegrand K v φ) (geometricLocalHaar K v) := by
  letI := geometricLocalHaar_isHaar K v
  exact localGeometricIntegrand_integrable_of_compact K v φ hone
    (geometricLocalHaar K v) hφ hc

#check geometricLocalUnitSet_eq_range
#print axioms geometricLocalUnitSet_eq_range
#check geometricLocalUnitSet_compact
#print axioms geometricLocalUnitSet_compact
#check geometricLocalUnitSet_open
#print axioms geometricLocalUnitSet_open
#check geometricLocalHaar_isHaar
#print axioms geometricLocalHaar_isHaar
#check geometricLocalHaar_units
#print axioms geometricLocalHaar_units
#check localGeometricIntegrand_integrable_haar
#print axioms localGeometricIntegrand_integrable_haar
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Identifies the norm-one shell in (12.5.1.2) with actual integer units. -/
theorem geometricLocalUnitSet_eq_normOne (v : FinitePlace K) :
    geometricLocalUnitSet K v =
      {x : (LocalField K v)ˣ | normalizedLocalNorm K v x = 1} := by
  have hn : ∀ x : (LocalField K v)ˣ,
      normalizedLocalNorm K v x = 1 ↔ Valued.v (x : LocalField K v) = 1 := by
    intro x
    constructor
    · intro h
      have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
        exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
      have hx0 : (x : LocalField K v) ≠ 0 := Units.ne_zero x
      simp only [normalizedLocalNorm, if_neg hx0] at h
      have hz : (Valued.v (x : LocalField K v)).log = 0 := by
        by_contra hz
        rcases lt_or_gt_of_ne hz with hl | hg
        · have he : (Valued.v (x : LocalField K v)).log ≤ -1 := by omega
          have hb := zpow_le_zpow_right₀ hq.le he
          have hi : (v.asIdeal.absNorm : ℝ)⁻¹ < 1 :=
            (inv_lt_one₀ (lt_trans zero_lt_one hq)).2 hq
          rw [zpow_neg_one, h] at hb
          exact (not_le_of_gt hi) hb
        · have he : (1 : ℤ) ≤ (Valued.v (x : LocalField K v)).log := by omega
          have hb := zpow_le_zpow_right₀ hq.le he
          rw [zpow_one, h] at hb
          exact (not_le_of_gt hq) hb
      have hv0 : Valued.v (x : LocalField K v) ≠ 0 := by simp
      rw [← WithZero.exp_log hv0, hz]
      simp
    · intro h
      rw [normalizedLocalNorm_eq_valuation]
      simp [h]
  ext x
  rw [Set.mem_setOf_eq, hn]
  constructor
  · rintro ⟨hx, hi⟩
    apply le_antisymm hx
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hi
    have hv0 : Valued.v (x : LocalField K v) ≠ 0 := by simp
    have hm := mul_le_mul_right hi (Valued.v (x : LocalField K v))
    simpa [hv0] using hm
  · intro h
    change Valued.v (x : LocalField K v) ≤ 1 ∧
      Valued.v (↑(x⁻¹) : LocalField K v) ≤ 1
    simp [Units.val_inv_eq_inv_val, map_inv₀, h]

local instance (v : FinitePlace K) : MeasurableSpace (LocalField K v)ˣ := borel _
local instance (v : FinitePlace K) : BorelSpace (LocalField K v)ˣ := ⟨rfl⟩

theorem geometricLocalHaar_normOne (v : FinitePlace K) :
    geometricLocalHaar K v {x | normalizedLocalNorm K v (x : LocalField K v) = 1} = 1 := by
  rw [← geometricLocalUnitSet_eq_normOne]
  exact geometricLocalHaar_units K v

/-- The finite coefficient in (12.5.1.2) is exactly log(q_v). -/
theorem finiteLocalGeometricTerm_normalized
    (φ : HeckeIdeleClasses K → ℂ) (v : FinitePlace K) :
    finiteLocalGeometricTerm K (geometricLocalHaar K) φ v =
      (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
        ∫ x, localGeometricIntegrand K v φ x ∂(geometricLocalHaar K v) := by
  simp [finiteLocalGeometricTerm, geometricLocalHaar_normOne]

/-- Integrated normalized Haar version of the finite-place convergence step.
The local test hypotheses still require derivation from the global test space. -/
theorem finite_geometric_haar_convergence
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hcontinuous : ∀ v, Continuous (fun x => φ (localClass K v x)))
    (hcompact : ∀ v, (v.asIdeal.absNorm : ℝ) ≤ T →
      HasCompactSupport (fun x => φ (localClass K v x))) :
    (∀ v, Integrable (localGeometricIntegrand K v φ) (geometricLocalHaar K v)) ∧
    Summable (fun v => finiteLocalGeometricTerm K (geometricLocalHaar K) φ v) ∧
    Summable (fun v => ‖finiteLocalGeometricTerm K (geometricLocalHaar K) φ v‖) ∧
    (∑' v, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v) =
      ∑ v ∈ smallNormPlaces K T, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v ∧
    Filter.Tendsto (fun S : Finset (FinitePlace K) =>
      ∑ v ∈ S, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v)
      Filter.atTop (nhds (∑' v, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v)) := by
  letI : ∀ v : FinitePlace K, (geometricLocalHaar K v).IsHaarMeasure :=
    geometricLocalHaar_isHaar K
  exact finite_geometric_convergence_of_local_compact K (geometricLocalHaar K)
    φ T hT hsupport hone hcontinuous hcompact

#check geometricLocalUnitSet_eq_normOne
#print axioms geometricLocalUnitSet_eq_normOne
#check geometricLocalHaar_normOne
#print axioms geometricLocalHaar_normOne
#check finiteLocalGeometricTerm_normalized
#print axioms finiteLocalGeometricTerm_normalized
#check finite_geometric_haar_convergence
#print axioms finite_geometric_haar_convergence
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Compactness of the actual valuation shells used in (12.5.1.2). -/
theorem localValuationShell_compact (v : FinitePlace K) (n : ℤ) :
    IsCompact {x : (LocalField K v)ˣ | (Valued.v (x : LocalField K v)).log = n} := by
  classical
  let S : Set (LocalField K v)ˣ := {x | (Valued.v (x : LocalField K v)).log = n}
  by_cases hs : S.Nonempty
  · obtain ⟨y, hy⟩ := hs
    have heq : S = (fun u => y * u) '' geometricLocalUnitSet K v := by
      ext x
      constructor
      · intro hx
        have hv : Valued.v (x : LocalField K v) = Valued.v (y : LocalField K v) := by
          rw [← WithZero.exp_log (show Valued.v (x : LocalField K v) ≠ 0 by simp),
            ← WithZero.exp_log (show Valued.v (y : LocalField K v) ≠ 0 by simp)]
          exact congrArg WithZero.exp (hx.trans hy.symm)
        refine ⟨y⁻¹ * x, ?_, by simp⟩
        change Valued.v (↑(y⁻¹ * x) : LocalField K v) ≤ 1 ∧
          Valued.v (↑((y⁻¹ * x)⁻¹) : LocalField K v) ≤ 1
        simp [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv]
      · rintro ⟨u, hu, rfl⟩
        have hu1 : Valued.v (u : LocalField K v) = 1 := by
          apply le_antisymm hu.1
          have hi := hu.2
          rw [Units.val_inv_eq_inv_val, map_inv₀] at hi
          have hm := mul_le_mul_right hi (Valued.v (u : LocalField K v))
          simpa using hm
        change (Valued.v (↑(y * u) : LocalField K v)).log = n
        simpa [Units.val_mul, map_mul, hu1] using hy
    change IsCompact S
    rw [heq]
    exact (geometricLocalUnitSet_compact K v).image (continuous_const.mul continuous_id)
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
    change IsCompact S
    rw [he]
    exact isCompact_empty

/-- Removes compact support from the finite local integrability obligation
when the actual local valuations lie in a finite interval. -/
theorem localPullback_compact_of_valuationBounds (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (a b : ℤ)
    (hb : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      (Valued.v (x : LocalField K v)).log ∈ Set.Icc a b) :
    HasCompactSupport (fun x => φ (localClass K v x)) := by
  apply HasCompactSupport.intro
    ((Set.finite_Icc a b).isCompact_biUnion (fun n _ => localValuationShell_compact K v n))
  intro x hx
  by_contra h
  apply hx
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hb x h, rfl⟩⟩

open MeasureTheory
local instance (v : FinitePlace K) : MeasurableSpace (LocalField K v)ˣ := borel _
local instance (v : FinitePlace K) : BorelSpace (LocalField K v)ˣ := ⟨rfl⟩

theorem localGeometricIntegrand_integrable_valuationBounds (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (a b : ℤ)
    (hb : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      (Valued.v (x : LocalField K v)).log ∈ Set.Icc a b)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hφ : Continuous (fun x => φ (localClass K v x))) :
    Integrable (localGeometricIntegrand K v φ) (geometricLocalHaar K v) := by
  exact localGeometricIntegrand_integrable_haar K v φ hone hφ
    (localPullback_compact_of_valuationBounds K v φ a b hb)

#check localValuationShell_compact
#print axioms localValuationShell_compact
#check localPullback_compact_of_valuationBounds
#print axioms localPullback_compact_of_valuationBounds
#check localGeometricIntegrand_integrable_valuationBounds
#print axioms localGeometricIntegrand_integrable_valuationBounds
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Closes the compact-local-support premise in geometric term (12.5.1.2),
directly from the norm bounds used on manuscript page 520. -/
theorem localPullback_compact_of_normBounds (v : FinitePlace K)
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ x : (LocalField K v)ˣ, φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T) :
    HasCompactSupport (fun x => φ (localClass K v x)) := by
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
  have hlq : 0 < Real.log (v.asIdeal.absNorm : ℝ) := Real.log_pos hq
  obtain ⟨a, ha⟩ := exists_int_lt (Real.log T⁻¹ / Real.log (v.asIdeal.absNorm : ℝ))
  obtain ⟨b, hb⟩ := exists_int_gt (Real.log T / Real.log (v.asIdeal.absNorm : ℝ))
  apply localPullback_compact_of_valuationBounds K v φ a b
  intro x hx
  obtain ⟨hlo, hhi⟩ := hsupport x hx
  have he : normalizedLocalNorm K v x =
      (v.asIdeal.absNorm : ℝ) ^ (Valued.v (x : LocalField K v)).log := by
    simp [normalizedLocalNorm, Units.ne_zero x]
  rw [he] at hlo hhi
  have hloglo := Real.log_lt_log (inv_pos.mpr (lt_trans zero_lt_one hT)) hlo
  have hloghi := Real.log_lt_log (zpow_pos (lt_trans zero_lt_one hq) _) hhi
  rw [Real.log_zpow] at hloglo hloghi
  have ha' : (a : ℝ) < ((Valued.v (x : LocalField K v)).log : ℝ) :=
    lt_trans ha ((div_lt_iff₀ hlq).mpr hloglo)
  have hb' : ((Valued.v (x : LocalField K v)).log : ℝ) < (b : ℝ) :=
    lt_trans ((lt_div_iff₀ hlq).mpr hloghi) hb
  exact ⟨by exact_mod_cast ha'.le, by exact_mod_cast hb'.le⟩

open MeasureTheory
local instance (v : FinitePlace K) : MeasurableSpace (LocalField K v)ˣ := borel _
local instance (v : FinitePlace K) : BorelSpace (LocalField K v)ˣ := ⟨rfl⟩

/-- Finite geometric convergence in Theorem 12.5.1.1 with no independent
compact-local-support premise. The operator/spectral equality remains open. -/
theorem finite_geometric_haar_convergence_normBounds
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hcontinuous : ∀ v, Continuous (fun x => φ (localClass K v x))) :
    (∀ v, Integrable (localGeometricIntegrand K v φ) (geometricLocalHaar K v)) ∧
    Summable (fun v => finiteLocalGeometricTerm K (geometricLocalHaar K) φ v) ∧
    Summable (fun v => ‖finiteLocalGeometricTerm K (geometricLocalHaar K) φ v‖) ∧
    (∑' v, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v) =
      ∑ v ∈ smallNormPlaces K T, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v ∧
    Filter.Tendsto (fun S : Finset (FinitePlace K) =>
      ∑ v ∈ S, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v)
      Filter.atTop (nhds (∑' v, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v)) := by
  apply finite_geometric_haar_convergence K φ T hT hsupport hone hcontinuous
  intro v _
  exact localPullback_compact_of_normBounds K v φ T hT (hsupport v)

#check localPullback_compact_of_normBounds
#print axioms localPullback_compact_of_normBounds
#check finite_geometric_haar_convergence_normBounds
#print axioms finite_geometric_haar_convergence_normBounds
end MasulloGRH

namespace MasulloGRH
open MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
local instance (v : FinitePlace K) : MeasurableSpace (LocalField K v)ˣ := borel _
local instance (v : FinitePlace K) : BorelSpace (LocalField K v)ˣ := ⟨rfl⟩

/-- The two integrals defining Weil's PF0 in manuscript B.4.4.5, with
multiplicative Haar measure normalized to give integer units mass one. -/
noncomputable def finiteLocalWeilPrincipalValue
    (φ : HeckeIdeleClasses K → ℂ) (v : FinitePlace K) : ℂ :=
  let U : Set (LocalField K v)ˣ := {x | normalizedLocalNorm K v x = 1}
  (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
    ((∫ x, Uᶜ.indicator (localGeometricIntegrand K v φ) x ∂(geometricLocalHaar K v)) +
     (∫ x, U.indicator (fun y =>
       (φ (localClass K v y) - φ (localClass K v 1)) *
       (Real.sqrt (normalizedLocalNorm K v y) : ℂ) /
       (normalizedLocalNorm K v (1 - (y : LocalField K v)) : ℂ)) x
       ∂(geometricLocalHaar K v)))

/-- Identifies the normalized geometric term with the explicit PF0 expression
on the norm-one-vanishing tests of Theorem 12.5.1.1. -/
theorem finiteLocalWeilPrincipalValue_eq_geometric
    (φ : HeckeIdeleClasses K → ℂ) (v : FinitePlace K)
    (hone : ∀ x : (LocalField K v)ˣ, normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0) :
    finiteLocalWeilPrincipalValue K φ v =
      finiteLocalGeometricTerm K (geometricLocalHaar K) φ v := by
  classical
  let U : Set (LocalField K v)ˣ := {x | normalizedLocalNorm K v x = 1}
  have hzero : ∀ x ∈ U, localGeometricIntegrand K v φ x = 0 := by
    intro x hx
    simp [localGeometricIntegrand, hone x hx]
  have hout : Uᶜ.indicator (localGeometricIntegrand K v φ) =
      localGeometricIntegrand K v φ := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx, hzero x hx]
    · simp [hx]
  have hin : U.indicator (localGeometricIntegrand K v φ) = 0 := by
    funext x
    by_cases hx : x ∈ U
    · simp [hx, hzero x hx]
    · simp [hx]
  have h1 : φ (localClass K v 1) = 0 := hone 1 (by simp [normalizedLocalNorm])
  rw [finiteLocalGeometricTerm_normalized]
  unfold finiteLocalWeilPrincipalValue
  simp only [h1, sub_zero]
  change (Real.log (v.asIdeal.absNorm : ℝ) : ℂ) *
    ((∫ x, Uᶜ.indicator (localGeometricIntegrand K v φ) x ∂(geometricLocalHaar K v)) +
     (∫ x, U.indicator (localGeometricIntegrand K v φ) x ∂(geometricLocalHaar K v))) = _
  rw [hout, hin]
  simp

#check finiteLocalWeilPrincipalValue_eq_geometric
#print axioms finiteLocalWeilPrincipalValue_eq_geometric
end MasulloGRH

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
local instance (v : FinitePlace K) : MeasurableSpace (LocalField K v)ˣ := borel _

theorem finite_WeilPrincipalValue_convergence
    (φ : HeckeIdeleClasses K → ℂ) (T : ℝ) (hT : 1 < T)
    (hsupport : ∀ v (x : (LocalField K v)ˣ), φ (localClass K v x) ≠ 0 →
      T⁻¹ < normalizedLocalNorm K v x ∧ normalizedLocalNorm K v x < T)
    (hone : ∀ v (x : (LocalField K v)ˣ), normalizedLocalNorm K v x = 1 →
      φ (localClass K v x) = 0)
    (hcontinuous : ∀ v, Continuous (fun x => φ (localClass K v x))) :
    Summable (finiteLocalWeilPrincipalValue K φ) ∧
    (∑' v, finiteLocalWeilPrincipalValue K φ v) =
      ∑ v ∈ smallNormPlaces K T, finiteLocalGeometricTerm K (geometricLocalHaar K) φ v := by
  have h := finite_geometric_haar_convergence_normBounds K φ T hT hsupport hone hcontinuous
  have he : finiteLocalWeilPrincipalValue K φ =
      fun v => finiteLocalGeometricTerm K (geometricLocalHaar K) φ v := by
    funext v
    exact finiteLocalWeilPrincipalValue_eq_geometric K φ v (hone v)
  rw [he]
  exact ⟨h.2.1, h.2.2.2.1⟩

#check finite_WeilPrincipalValue_convergence
#print axioms finite_WeilPrincipalValue_convergence
end MasulloGRH
