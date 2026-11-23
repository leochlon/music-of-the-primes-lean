import Mathlib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

/-! Participant A, round 55: a finite-place support reduction immediately used
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
