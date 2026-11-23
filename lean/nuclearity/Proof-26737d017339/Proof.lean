import Mathlib

/- Reused exact arithmetic definitions; no topology campaign. -/
open scoped NumberField Valued WithZero ENNReal NNReal
open NumberField MeasureTheory
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
noncomputable instance classCommGroup : CommGroup (HeckeIdeleClasses K) := inferInstance
noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem genuineIdeleModulus_principal (a : Kˣ) :
    genuineIdeleModulus K (principalIdele K a) = 1 := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(principalIdele K a).val.1 w‖ = w (a : K) := by
    exact NumberField.InfinitePlace.Completion.norm_coe w
      ((WithAbs.equiv _).symm (a : K))
  have hf (v : NumberField.FinitePlace K) :
      ‖(principalIdele K a).val.2 v.maximalIdeal‖ = v (a : K) := by
    exact NumberField.FinitePlace.norm_embedding_eq v (a : K)
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  exact NumberField.prod_abs_eq_one (K := K) a.ne_zero
/-- Outside finitely many finite places, an actual idele has local norm one. -/
theorem genuineIdele_finite_norm_support (a : HeckeIdeles K) :
    (Function.mulSupport (fun v : NumberField.FinitePlace K =>
      ‖a.val.2 v.maximalIdeal‖)).Finite := by
  have he : ∀ᶠ v in Filter.cofinite, ‖a.val.2 v‖ = 1 := by
    filter_upwards [RestrictedProduct.eventually _ _ a.val.2,
      RestrictedProduct.eventually _ _ (a⁻¹).val.2] with v hv hi
    change Valued.v (a.val.2 v) ≤ 1 at hv
    change Valued.v ((a⁻¹).val.2 v) ≤ 1 at hi
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 := by
      have h := congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
      exact h
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm hv
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right hi _
        _ = Valued.v (a.val.2 v) := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  exact (Filter.eventually_cofinite.mp he).preimage
    NumberField.FinitePlace.maximalIdeal_injective.injOn
theorem genuineIdeleModulus_mul (a b : HeckeIdeles K) :
    genuineIdeleModulus K (a * b) = genuineIdeleModulus K a * genuineIdeleModulus K b := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(a * b).val.1 w‖ ^ w.mult =
        ‖a.val.1 w‖ ^ w.mult * ‖b.val.1 w‖ ^ w.mult := by
    change ‖a.val.1 w * b.val.1 w‖ ^ w.mult = _
    rw [norm_mul, mul_pow]
  have hf (v : NumberField.FinitePlace K) :
      ‖(a * b).val.2 v.maximalIdeal‖ =
        ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ := by
    change ‖a.val.2 v.maximalIdeal * b.val.2 v.maximalIdeal‖ = _
    exact norm_mul _ _
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib
    (genuineIdele_finite_norm_support K a) (genuineIdele_finite_norm_support K b)]
  ring

theorem genuineIdeleModulus_ne_zero (a : HeckeIdeles K) :
    genuineIdeleModulus K a ≠ 0 := by
  have h1 : genuineIdeleModulus K 1 = 1 := by
    simpa only [map_one] using genuineIdeleModulus_principal K 1
  have hp := genuineIdeleModulus_mul K a a⁻¹
  rw [mul_inv_cancel, h1] at hp
  intro hz
  rw [hz, zero_mul] at hp
  exact one_ne_zero hp


open MeasureTheory Topology Filter
open NumberField.InfinitePlace.Completion
open scoped ENNReal NNReal
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)

instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

instance classMeasurableInv : MeasurableInv (HeckeIdeleClasses K) := by
  infer_instance
instance classMeasurableMul : MeasurableMul (HeckeIdeleClasses K) := by
  infer_instance

noncomputable def genuineIdeleLog (a : HeckeIdeles K) : ℂ :=
  (Real.log (genuineIdeleModulus K a) : ℂ)
/-- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]

/-- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
local-norm logarithm. This is not supplied by an abstract replacement norm. -/
noncomputable def genuineLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeles K →* Multiplicative ℂ where
  toFun a := Multiplicative.ofAdd (genuineIdeleLog K a)
  map_one' := by
    change genuineIdeleLog K 1 = 0
    simpa only [map_one] using genuineIdeleLog_principal K 1
  map_mul' a b := hadd a b

noncomputable def genuineClassLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeleClasses K →* Multiplicative ℂ :=
  QuotientGroup.lift (principalIdeles K) (genuineLogHom K hadd) (by
    rintro x ⟨a, rfl⟩
    exact genuineIdeleLog_principal K a)

noncomputable def genuineClassLog
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (x : HeckeIdeleClasses K) : ℂ :=
  Multiplicative.toAdd (genuineClassLogHom K hadd x)

theorem genuineClassLog_mk
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (a : HeckeIdeles K) :
    genuineClassLog K hadd (QuotientGroup.mk a) = genuineIdeleLog K a := rfl

theorem genuineClassLog_translate
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (g x : HeckeIdeleClasses K) :
    genuineClassLog K hadd (g⁻¹ * x) =
      genuineClassLog K hadd x - genuineClassLog K hadd g := by
  unfold genuineClassLog
  rw [map_mul, map_inv]
  change -Multiplicative.toAdd (genuineClassLogHom K hadd g) +
    Multiplicative.toAdd (genuineClassLogHom K hadd x) = _
  abel


noncomputable def genuineRealClassLog (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re

theorem genuineRealClassLog_mul (x y : HeckeIdeleClasses K) :
    genuineRealClassLog K (x*y) = genuineRealClassLog K x + genuineRealClassLog K y := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_mul]
  rfl

theorem genuineRealClassLog_inv (x : HeckeIdeleClasses K) :
    genuineRealClassLog K x⁻¹ = -genuineRealClassLog K x := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_inv]
  rfl

end MasulloGRH


namespace Round112D
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- At least one geometric perturbation retains the full smoothed geometric
norm. This is a lower bound on the actual lifted rank-one vectors. -/
theorem smoothed_lift_two_signs (A : H →L[ℂ] H) (u g : H) :
    ‖A g‖ ≤ max ‖A (u+g)‖ ‖A (u-g)‖ := by
  have hi : A (u+g) - A (u-g) = (2:ℂ) • A g := by
    simp only [map_add, map_sub, two_smul]
    abel
  have hn := norm_sub_le (A (u+g)) (A (u-g))
  rw [hi, norm_smul] at hn
  norm_num at hn
  have h1 := le_max_left ‖A (u+g)‖ ‖A (u-g)‖
  have h2 := le_max_right ‖A (u+g)‖ ‖A (u-g)‖
  simp only [map_add, map_sub] at h1 h2 ⊢
  linarith

/-- A uniform collar and quotient labels alone permit lifts whose individual
smoothed rank-one costs stay bounded away from zero. No nuclearity is assumed. -/
theorem bad_bounded_lifts (F G : Submodule ℂ H)
    (A : H →L[ℂ] H) (u : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 < C) (hu : ∀ i, u i ∈ F)
    (hbound : ∀ i, ‖u i‖ ≤ C) (hdual : ∀ i, eta i (u i) = 1)
    (g : H) (hgF : g ∈ F) (hgG : g ∈ G) :
    ∃ v : ℕ → H,
      (∀ i, v i ∈ F ∧ v i-u i ∈ G ∧ ‖v i‖ ≤ C+‖g‖) ∧
      (∀ i, ‖A g‖ / C ≤ ‖A (v i)‖ * ‖eta i‖) := by
  classical
  let v : ℕ → H := fun i => if ‖A g‖ ≤ ‖A (u i+g)‖ then u i+g else u i-g
  have hvnorm (i : ℕ) : ‖A g‖ ≤ ‖A (v i)‖ := by
    dsimp [v]
    split_ifs with h
    · exact h
    · have hh := smoothed_lift_two_signs A (u i) g
      exact (le_max_iff.mp hh).resolve_left h
  refine ⟨v, ?_, ?_⟩
  · intro i
    dsimp [v]
    split_ifs
    · refine ⟨F.add_mem (hu i) hgF, ?_, ?_⟩
      · simpa using hgG
      · exact (norm_add_le _ _).trans (by linarith [hbound i])
    · refine ⟨F.sub_mem (hu i) hgF, ?_, ?_⟩
      · have hid : u i-g-u i = -g := by abel
        rw [hid]
        exact G.neg_mem hgG
      · exact (norm_sub_le _ _).trans (by linarith [hbound i])
  · intro i
    have he := (eta i).le_opNorm (u i)
    rw [hdual i, norm_one] at he
    have heC : 1 ≤ ‖eta i‖ * C := he.trans
      (mul_le_mul_of_nonneg_left (hbound i) (norm_nonneg _))
    apply (div_le_iff₀ hC).mpr
    calc
      ‖A g‖ ≤ ‖A g‖ * (‖eta i‖ * C) := by nlinarith [norm_nonneg (A g)]
      _ ≤ ‖A (v i)‖ * (‖eta i‖ * C) :=
        mul_le_mul_of_nonneg_right (hvnorm i) (by positivity)
      _ = _ := by ring

/-- For nontrivial convolution on the geometric subspace, bounded quotient
lifts can have a nonsummable nuclear representation cost. This obstructs a
bound uniform over all such lifts; it does not disprove nuclearity of AP. -/
theorem bad_bounded_quotient_lifts_not_summable (F G : Submodule ℂ H)
    (A : H →L[ℂ] H) (u : ℕ → H) (eta : ℕ → H →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 < C) (hu : ∀ i, u i ∈ F)
    (hbound : ∀ i, ‖u i‖ ≤ C) (hdual : ∀ i, eta i (u i) = 1)
    (hann : ∀ i, ∀ z ∈ G, eta i z = 0)
    (g : H) (hgF : g ∈ F) (hgG : g ∈ G) (hag : A g ≠ 0) :
    ∃ v : ℕ → H,
      (∀ i, v i ∈ F ∧ v i-u i ∈ G ∧ ‖v i‖ ≤ C+‖g‖ ∧ eta i (v i) = 1) ∧
      ¬ Summable (fun i => ‖A (v i)‖ * ‖eta i‖) := by
  obtain ⟨v, hv, hb⟩ := bad_bounded_lifts F G A u eta C hC hu hbound hdual g hgF hgG
  refine ⟨v, ?_, ?_⟩
  · intro i
    have he := hann i (v i-u i) (hv i).2.1
    rw [map_sub, hdual i] at he
    exact ⟨(hv i).1, (hv i).2.1, (hv i).2.2, sub_eq_zero.mp he⟩
  · intro hs
    have hc : Summable (fun _ : ℕ => ‖A g‖ / C) :=
      Summable.of_nonneg_of_le (fun _ => by positivity) hb hs
    have hz : ‖A g‖ / C = 0 := tendsto_nhds_unique tendsto_const_nhds hc.tendsto_atTop_zero
    have hp : 0 < ‖A g‖ / C := div_pos (norm_pos_iff.mpr hag) hC
    linarith

#check bad_bounded_quotient_lifts_not_summable
#print axioms bad_bounded_quotient_lifts_not_summable
#check smoothed_lift_two_signs
#print axioms smoothed_lift_two_signs
#check bad_bounded_lifts
#print axioms bad_bounded_lifts
end Round112D

namespace Round112D
open MeasureTheory MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance : MeasurableSpace (HeckeIdeleClasses K) := borel (HeckeIdeleClasses K)
noncomputable def weightedMeasure (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ) :=
  mu.withDensity (fun x => ENNReal.ofReal
    (Real.exp (2*alpha*|genuineRealClassLog K x|) *
      (1+(genuineRealClassLog K x)^2) ^ (s/2)))
noncomputable abbrev WeightedL2 (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ) :=
  Lp ℂ 2 (weightedMeasure K mu alpha s)

/-- Diagnostic on the genuine weighted idele-class space, with literal
convolution action retained as an explicit hypothesis. The geometric
subspaces and nonzero convolution of g must still be instantiated. -/
theorem genuine_convolution_lift_obstruction
    (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ)
    (phi : HeckeIdeleClasses K → ℂ)
    (F G : Submodule ℂ (WeightedL2 K mu alpha s))
    (A : WeightedL2 K mu alpha s →L[ℂ] WeightedL2 K mu alpha s)
    (hA : ∀ f : WeightedL2 K mu alpha s,
      (A f : HeckeIdeleClasses K → ℂ) =ᵐ[weightedMeasure K mu alpha s]
        fun x => ∫ y, phi y * f (y⁻¹*x) ∂mu)
    (u : ℕ → WeightedL2 K mu alpha s)
    (eta : ℕ → WeightedL2 K mu alpha s →L[ℂ] ℂ)
    (C : ℝ) (hC : 0 < C) (hu : ∀ i, u i ∈ F)
    (hbound : ∀ i, ‖u i‖ ≤ C) (hdual : ∀ i, eta i (u i) = 1)
    (hann : ∀ i, ∀ z ∈ G, eta i z = 0)
    (g : WeightedL2 K mu alpha s) (hgF : g ∈ F) (hgG : g ∈ G) (hag : A g ≠ 0) :
    ∃ v : ℕ → WeightedL2 K mu alpha s,
      (∀ i, v i ∈ F ∧ v i-u i ∈ G ∧ ‖v i‖ ≤ C+‖g‖ ∧ eta i (v i) = 1) ∧
      (∀ i, (A (v i) : HeckeIdeleClasses K → ℂ) =ᵐ[weightedMeasure K mu alpha s]
        fun x => ∫ y, phi y * (v i) (y⁻¹*x) ∂mu) ∧
      ¬ Summable (fun i => ‖A (v i)‖ * ‖eta i‖) := by
  obtain ⟨v, hv, hns⟩ := bad_bounded_quotient_lifts_not_summable
    F G A u eta C hC hu hbound hdual hann g hgF hgG hag
  exact ⟨v, hv, fun i => hA (v i), hns⟩

#check genuine_convolution_lift_obstruction
#print axioms genuine_convolution_lift_obstruction
end Round112D

namespace Round111D
open scoped Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Dense geometric corrections produce quotient-exact lifts with an
arbitrarily specified error from the chosen representative. -/
theorem dense_coset_lift (F G : Submodule ℂ H)
    (hdense : ∀ g ∈ G, g ∈ closure (↑(F ⊓ G) : Set H))
    (p u0 : H) (hu0 : u0 ∈ F) (hcoset : u0-p ∈ G)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ u ∈ F, u-p ∈ G ∧ ‖u-p‖ < δ := by
  obtain ⟨v, hv, hdist⟩ := Metric.mem_closure_iff.mp (hdense _ hcoset) δ hδ
  refine ⟨u0-v, F.sub_mem hu0 hv.1, ?_, ?_⟩
  · have hid : u0-v-p = (u0-p)-v := by abel
    rw [hid]
    exact G.sub_mem hcoset hv.2
  · have hid : u0-v-p = (u0-p)-v := by abel
    rw [hid]
    simpa only [dist_eq_norm, norm_sub_rev] using hdist

/-- The error of a near-minimal quotient lift depends on the individual
quotient norm, rather than merely a common collar bound. -/
theorem orthogonal_lift_error (G : Submodule ℂ H) (p u : H)
    (hp : p ∈ Gᗮ) (hu : u-p ∈ G) (ε : ℝ) (hε : 0 ≤ ε)
    (hnear : ‖u‖ ≤ ‖p‖ + ε) :
    ‖u-p‖ ≤ Real.sqrt (ε*(2*‖p‖+ε)) := by
  have ho : inner ℂ p (u-p) = 0 := (Submodule.mem_orthogonal' G p).mp hp _ hu
  have hn := norm_add_sq (𝕜 := ℂ) p (u-p)
  rw [ho] at hn
  have hsum : p+(u-p) = u := by abel
  rw [hsum] at hn
  simp only [map_zero, mul_zero, add_zero] at hn
  apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
  nlinarith [norm_nonneg u, norm_nonneg p]

/-- No summability or lift norm bound is a premise: the lifts are chosen
using geometric density with coefficient-dependent tolerances. This bounds
only the smoothed correction to the prescribed representatives. -/
theorem summable_smoothed_lift_errors (F G : Submodule ℂ H)
    (hdense : ∀ g ∈ G, g ∈ closure (↑(F ⊓ G) : Set H))
    (p u0 : ℕ → H) (hu0 : ∀ i, u0 i ∈ F)
    (hcoset : ∀ i, u0 i-p i ∈ G)
    (A : H →L[ℂ] H) (eta : ℕ → H →L[ℂ] ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : ℕ → H,
      (∀ i, u i ∈ F ∧ u i-p i ∈ G) ∧
      Summable (fun i => ‖A (u i-p i)‖ * ‖eta i‖) ∧
      (∑' i, ‖A (u i-p i)‖ * ‖eta i‖) ≤ 2*ε*‖A‖ := by
  have hex (i : ℕ) := dense_coset_lift F G hdense (p i) (u0 i) (hu0 i)
    (hcoset i) (ε*(1/2:ℝ)^i/(1+‖eta i‖)) (by positivity)
  choose u huF huG huerr using hex
  have hb (i : ℕ) : ‖A (u i-p i)‖ * ‖eta i‖ ≤
      (‖A‖*ε)*(1/2:ℝ)^i := by
    have hd : 0 < 1+‖eta i‖ := by positivity
    have hc : ‖u i-p i‖ * ‖eta i‖ ≤ ε*(1/2:ℝ)^i := by
      have hh := (lt_div_iff₀ hd).mp (huerr i)
      nlinarith [norm_nonneg (u i-p i)]
    calc
      _ ≤ (‖A‖*‖u i-p i‖)*‖eta i‖ :=
        mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖*(‖u i-p i‖*‖eta i‖) := by ring
      _ ≤ ‖A‖*(ε*(1/2:ℝ)^i) := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = _ := by ring
  have hg : Summable (fun i : ℕ => (‖A‖*ε)*(1/2:ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left _
  have hs : Summable (fun i => ‖A (u i-p i)‖ * ‖eta i‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb hg
  refine ⟨u, fun i => ⟨huF i, huG i⟩, hs, (hs.tsum_le_tsum hb hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)]
  ring

#check dense_coset_lift
#print axioms dense_coset_lift
#check orthogonal_lift_error
#print axioms orthogonal_lift_error
#check summable_smoothed_lift_errors
#print axioms summable_smoothed_lift_errors
end Round111D

namespace Round113D
open scoped Topology
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]

omit [CompleteSpace H] in
theorem rankOne_norm_bound (eta : H →L[ℂ] ℂ) (v : H) :
    ‖eta.smulRight v‖ ≤ ‖v‖ * ‖eta‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  simp only [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc
    ‖eta x‖ * ‖v‖ ≤ (‖eta‖ * ‖x‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (eta.le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

/-- Constructs a convergent operator correction to prescribed quotient
representatives, with a derived nuclear representation cost. The leading
operator on those representatives is not bounded by this theorem. -/
theorem constructed_lift_correction (F G : Submodule ℂ H)
    (hdense : ∀ g ∈ G, g ∈ closure (↑(F ⊓ G) : Set H))
    (p u0 : ℕ → H) (hu0 : ∀ i, u0 i ∈ F)
    (hcoset : ∀ i, u0 i-p i ∈ G)
    (A : H →L[ℂ] H) (eta : ℕ → H →L[ℂ] ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : ℕ → H) (R : H →L[ℂ] H),
      (∀ i, u i ∈ F ∧ u i-p i ∈ G) ∧
      Summable (fun i => ‖A (u i-p i)‖ * ‖eta i‖) ∧
      (∑' i, ‖A (u i-p i)‖ * ‖eta i‖) ≤ 2*ε*‖A‖ ∧
      HasSum (fun i => (eta i).smulRight (A (u i-p i))) R ∧
      ‖R‖ ≤ 2*ε*‖A‖ ∧
      (∀ M : H →L[ℂ] H, (∀ x, ‖M x‖ ≤ ‖x‖) →
        Summable (fun i => ‖M (A (u i-p i))‖ * ‖eta i‖) ∧
        (∑' i, ‖M (A (u i-p i))‖ * ‖eta i‖) ≤ 2*ε*‖A‖ ∧
        HasSum (fun i => (eta i).smulRight (M (A (u i-p i)))) (M.comp R)) := by
  obtain ⟨u, hu, hs, hb⟩ := Round111D.summable_smoothed_lift_errors
    F G hdense p u0 hu0 hcoset A eta ε hε
  let T : ℕ → H →L[ℂ] H := fun i => (eta i).smulRight (A (u i-p i))
  have hn : Summable (fun i => ‖T i‖) := Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun i => rankOne_norm_bound _ _) hs
  have ht := hn.of_norm.hasSum
  refine ⟨u, ∑' i, T i, hu, hs, hb, ht, ?_, ?_⟩
  · exact (norm_tsum_le_tsum_norm hn).trans
      ((Summable.tsum_le_tsum (fun i => rankOne_norm_bound _ _) hn hs).trans hb)
  · intro M hM
    have hle (i : ℕ) : ‖M (A (u i-p i))‖ * ‖eta i‖ ≤
        ‖A (u i-p i)‖ * ‖eta i‖ :=
      mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    have hms := Summable.of_nonneg_of_le (fun _ => by positivity) hle hs
    refine ⟨hms, (Summable.tsum_le_tsum hle hms hs).trans hb, ?_⟩
    have hh := ht.map (ContinuousLinearMap.compL ℂ H H H M)
      (ContinuousLinearMap.compL ℂ H H H M).continuous
    change HasSum (fun i => M.comp (T i)) (M.comp (∑' i, T i)) at hh
    have he (i : ℕ) : M.comp (T i) =
        (eta i).smulRight (M (A (u i-p i))) := by
      ext x
      simp [T, ContinuousLinearMap.smulRight_apply]
    simpa only [he] using hh

#check constructed_lift_correction
#print axioms constructed_lift_correction
end Round113D

namespace Round113D
open MeasureTheory MasulloGRH Round112D
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- Actual arithmetic weighted-space specialization. Geometric density,
quotient representatives and the bounded convolution realization remain
explicit unresolved inputs; no leading nuclear bound is asserted. -/
theorem genuine_constructed_lift_correction
    (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ)
    (phi : HeckeIdeleClasses K → ℂ)
    (F G : Submodule ℂ (WeightedL2 K mu alpha s))
    (hdense : ∀ g ∈ G, g ∈ closure (↑(F ⊓ G) : Set (WeightedL2 K mu alpha s)))
    (p u0 : ℕ → WeightedL2 K mu alpha s)
    (hu0 : ∀ i, u0 i ∈ F) (hcoset : ∀ i, u0 i-p i ∈ G)
    (A : WeightedL2 K mu alpha s →L[ℂ] WeightedL2 K mu alpha s)
    (hA : ∀ f : WeightedL2 K mu alpha s,
      (A f : HeckeIdeleClasses K → ℂ) =ᵐ[weightedMeasure K mu alpha s]
        fun x => ∫ y, phi y * f (y⁻¹*x) ∂mu)
    (eta : ℕ → WeightedL2 K mu alpha s →L[ℂ] ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : ℕ → WeightedL2 K mu alpha s)
      (R : WeightedL2 K mu alpha s →L[ℂ] WeightedL2 K mu alpha s),
      (∀ i, u i ∈ F ∧ u i-p i ∈ G) ∧
      (∀ i, (A (u i-p i) : HeckeIdeleClasses K → ℂ) =ᵐ[weightedMeasure K mu alpha s]
        fun x => ∫ y, phi y * ((u i-p i : WeightedL2 K mu alpha s) : HeckeIdeleClasses K → ℂ) (y⁻¹*x) ∂mu) ∧
      Summable (fun i => ‖A (u i-p i)‖ * ‖eta i‖) ∧
      (∑' i, ‖A (u i-p i)‖ * ‖eta i‖) ≤ 2*ε*‖A‖ ∧
      HasSum (fun i => (eta i).smulRight (A (u i-p i))) R ∧
      ‖R‖ ≤ 2*ε*‖A‖ := by
  obtain ⟨u, R, hu, hs, hb, hr, hn, _⟩ := constructed_lift_correction
    F G hdense p u0 hu0 hcoset A eta ε hε
  exact ⟨u, R, hu, fun i => hA (u i-p i), hs, hb, hr, hn⟩

#check genuine_constructed_lift_correction
#print axioms genuine_constructed_lift_correction
end Round113D
