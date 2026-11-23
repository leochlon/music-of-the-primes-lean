import Mathlib
noncomputable section
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

end MasulloGRH
namespace Round142B
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable def theta (f : HeckeAdeles K → ℂ) (g : HeckeIdeles K) : ℂ :=
  ∑' u : Kˣ, f ((principalIdele K u * g).val)

def adelicTranslate (g : HeckeIdeles K) (f : HeckeAdeles K → ℂ)
    (x : HeckeAdeles K) : ℂ := f ((g⁻¹).val * x)
end Round142B
namespace Round157C
open MasulloGRH Round142B
variable (K : Type*) [Field K] [NumberField K]
noncomputable def compensatedSeed (g : HeckeIdeles K)
    (b : HeckeAdeles K → ℂ) (x : HeckeAdeles K) : ℂ :=
  b x - (genuineIdeleModulus K g : ℂ)⁻¹ * adelicTranslate K g b x

end Round157C
namespace Round160C
open MasulloGRH Round142B Round157C
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_compensated_theta_positive_cutoff
    (g : HeckeIdeles K) (b : HeckeAdeles K → ℂ) (C : ℝ)
    (hsupp : ∀ z : HeckeIdeles K, b z.val ≠ 0 → genuineIdeleModulus K z ≤ C)
    (y : HeckeIdeles K)
    (hy : max C (genuineIdeleModulus K g * C) < genuineIdeleModulus K y) :
    theta K (compensatedSeed K g b) y = 0 := by
  have hn : 0 ≤ genuineIdeleModulus K g := by
    unfold genuineIdeleModulus
    exact mul_nonneg (Finset.prod_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _))
      (finprod_nonneg (fun _ => norm_nonneg _))
  unfold theta
  trans ∑' _u : Kˣ, (0 : ℂ)
  · apply tsum_congr
    intro u
    have hb : b (principalIdele K u * y).val = 0 := by
      by_contra h
      have ht := hsupp (principalIdele K u * y) h
      rw [genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul] at ht
      exact (not_le_of_gt (lt_of_le_of_lt (le_max_left _ _) hy)) ht
    have hd : b (g⁻¹ * (principalIdele K u * y)).val = 0 := by
      by_contra h
      have ht := mul_le_mul_of_nonneg_left
        (hsupp (g⁻¹ * (principalIdele K u * y)) h) hn
      rw [← genuineIdeleModulus_mul, mul_inv_cancel_left,
        genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul] at ht
      exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hy)) ht
    change b (principalIdele K u * y).val -
      (genuineIdeleModulus K g : ℂ)⁻¹ * b (g⁻¹ * (principalIdele K u * y)).val = 0
    rw [hb, hd, mul_zero, sub_zero]
  · simp

#check genuine_compensated_theta_positive_cutoff
#print axioms genuine_compensated_theta_positive_cutoff
end Round160C

/- N1_POSITIVE_TAIL_SUPPORT supplies the genuine seed support premise
for the positive tail of the geometric seed moments needed by the actual
leading projected nuclear estimate. No nuclear bound is asserted here. -/
namespace Round161C
open MasulloGRH Round142B Round157C Round160C
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_common_integral_seed_cutoff
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : HeckeAdeles K → ℂ),
      Function.support b ⊆ S →
      (∀ z : HeckeIdeles K, b z.val ≠ 0 →
        ∀ v : FinitePlace K, ‖z.val.2 v.maximalIdeal‖ ≤ 1) →
      ∀ g y : HeckeIdeles K,
        max C (genuineIdeleModulus K g * C) < genuineIdeleModulus K y →
        theta K (compensatedSeed K g b) y = 0 := by
  classical
  let A : HeckeAdeles K → ℝ := fun x => ∏ w : InfinitePlace K, ‖x.1 w‖ ^ w.mult
  have hA : Continuous A := by
    dsimp [A]
    fun_prop
  obtain ⟨B, hB⟩ := hS.bddAbove_image hA.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro b hb hf g y hy
  apply genuine_compensated_theta_positive_cutoff K g b (max 1 B) ?_ y hy
  intro z hz
  have hi : A z.val ≤ max 1 B :=
    (hB ⟨z.val, hb hz, rfl⟩).trans (le_max_right _ _)
  have hfin := genuineIdele_finite_norm_support K z
  have hp : (∏ᶠ v : FinitePlace K, ‖z.val.2 v.maximalIdeal‖) ≤ 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset _
      (s := hfin.toFinset) (by simp)]
    calc
      _ ≤ ∏ _v ∈ hfin.toFinset, (1 : ℝ) :=
        Finset.prod_le_prod (fun v _ => norm_nonneg _) (fun v _ => hf z hz v)
      _ = 1 := by simp
  have hn : 0 ≤ A z.val :=
    Finset.prod_nonneg (fun w _ => pow_nonneg (norm_nonneg _) _)
  calc
    genuineIdeleModulus K z = A z.val *
        (∏ᶠ v : FinitePlace K, ‖z.val.2 v.maximalIdeal‖) := rfl
    _ ≤ A z.val * 1 := mul_le_mul_of_nonneg_left hp hn
    _ = A z.val := mul_one _
    _ ≤ max 1 B := hi

#check genuine_common_integral_seed_cutoff
#print axioms genuine_common_integral_seed_cutoff
end Round161C

/- Exact premise N1_POSITIVE_TAIL_COMPACT_SUPPORT: derive the finite
exceptional set from compactness in the genuine adele topology. -/
namespace Round162C
open MasulloGRH Round142B Round157C Round160C
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_compact_finite_level
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) :
    ∃ T : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      ∀ x ∈ S, ∀ v ∉ T, Valued.v (x.2 v) ≤ 1 := by
  classical
  let U : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) → Set (HeckeAdeles K) :=
    fun T => {x | ∀ v ∉ T, Valued.v (x.2 v) ≤ 1}
  have hU : ∀ T, IsOpen (U T) := by
    intro T
    exact (RestrictedProduct.isOpen_forall_imp_mem
      (fun _ => Valued.isOpen_valuationSubring _)).preimage continuous_snd
  have hcover : S ⊆ ⋃ T, U T := by
    intro x _
    have he := Filter.eventually_cofinite.mp (RestrictedProduct.eventually _ _ x.2)
    refine Set.mem_iUnion.mpr ⟨he.toFinset, ?_⟩
    intro v hv
    by_contra hn
    exact hv (he.mem_toFinset.mpr hn)
  obtain ⟨Ts, hTs⟩ := hS.elim_finite_subcover U hU hcover
  refine ⟨Ts.biUnion id, ?_⟩
  intro x hx v hv
  obtain ⟨T, hT⟩ := Set.mem_iUnion.mp (hTs hx)
  obtain ⟨hTT, hxT⟩ := Set.mem_iUnion.mp hT
  apply hxT v
  intro hvT
  exact hv (Finset.mem_biUnion.mpr ⟨T, hTT, hvT⟩)

theorem genuine_compact_finite_norm_level
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) :
    ∃ T : Finset (FinitePlace K),
      ∀ x ∈ S, ∀ v ∉ T, ‖x.2 v.maximalIdeal‖ ≤ 1 := by
  classical
  obtain ⟨T, hT⟩ := genuine_compact_finite_level K S hS
  have ht := T.finite_toSet.preimage
    NumberField.FinitePlace.maximalIdeal_injective.injOn
  refine ⟨ht.toFinset, ?_⟩
  intro x hx v hv
  have hh : Valued.v (x.2 v.maximalIdeal) ≤ 1 :=
    hT x hx v.maximalIdeal (by simpa using hv)
  change Valued.norm (x.2 v.maximalIdeal) ≤ 1
  rw [Valued.norm_def]
  let valuation : Valuation (v.maximalIdeal.adicCompletion K) (WithZero (Multiplicative ℤ)) := Valued.v
  have hm : Valuation.RankOne.hom valuation (valuation (x.2 v.maximalIdeal)) ≤ 1 := by
    simpa only [map_one] using (Valuation.RankOne.strictMono' (v := valuation)).monotone hh
  exact_mod_cast hm

#check genuine_compact_finite_norm_level
#print axioms genuine_compact_finite_norm_level
#check genuine_compact_finite_level
#print axioms genuine_compact_finite_level

theorem genuine_compact_modulus_bound
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : HeckeIdeles K, z.val ∈ S → genuineIdeleModulus K z ≤ C := by
  classical
  obtain ⟨T, hT⟩ := genuine_compact_finite_norm_level K S hS
  let A : HeckeAdeles K → ℝ := fun x =>
    (∏ w : InfinitePlace K, ‖x.1 w‖ ^ w.mult) *
      ∏ v ∈ T, max 1 ‖x.2 v.maximalIdeal‖
  have heval (v : FinitePlace K) : Continuous (fun x : HeckeAdeles K => x.2 v.maximalIdeal) :=
    (RestrictedProduct.continuous_eval v.maximalIdeal).comp continuous_snd
  have hA : Continuous A := by
    dsimp [A]
    fun_prop
  obtain ⟨B, hB⟩ := hS.bddAbove_image hA.continuousOn
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro z hz
  have hfin := genuineIdele_finite_norm_support K z
  have hp : (∏ᶠ v : FinitePlace K, ‖z.val.2 v.maximalIdeal‖) ≤
      ∏ v ∈ T, max 1 ‖z.val.2 v.maximalIdeal‖ := by
    rw [finprod_eq_prod_of_mulSupport_subset _
      (s := hfin.toFinset ∪ T) (by
        intro v hv
        exact Finset.mem_union_left T (hfin.mem_toFinset.mpr hv))]
    calc
      _ ≤ ∏ v ∈ hfin.toFinset ∪ T, max 1 ‖z.val.2 v.maximalIdeal‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => le_max_right _ _)
      _ = ∏ v ∈ T, max 1 ‖z.val.2 v.maximalIdeal‖ := by
        symm
        apply Finset.prod_subset Finset.subset_union_right
        intro v _ hv
        exact max_eq_left (hT z.val hz v hv)
  have hn : 0 ≤ ∏ w : InfinitePlace K, ‖z.val.1 w‖ ^ w.mult :=
    Finset.prod_nonneg (fun w _ => pow_nonneg (norm_nonneg _) _)
  calc
    genuineIdeleModulus K z ≤ A z.val := mul_le_mul_of_nonneg_left hp hn
    _ ≤ B := hB ⟨z.val, hz, rfl⟩
    _ ≤ max 1 B := le_max_right _ _

theorem genuine_common_compact_seed_cutoff
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) :
    ∃ C : ℝ, 0 < C ∧ ∀ (b : HeckeAdeles K → ℂ),
      Function.support b ⊆ S → ∀ g y : HeckeIdeles K,
      max C (genuineIdeleModulus K g * C) < genuineIdeleModulus K y →
      theta K (compensatedSeed K g b) y = 0 := by
  obtain ⟨C, hC, hbound⟩ := genuine_compact_modulus_bound K S hS
  refine ⟨C, hC, ?_⟩
  intro b hb g y hy
  exact genuine_compensated_theta_positive_cutoff K g b C
    (fun z hz => hbound z (hb hz)) y hy

#check genuine_compact_modulus_bound
#print axioms genuine_compact_modulus_bound
#check genuine_common_compact_seed_cutoff
#print axioms genuine_common_compact_seed_cutoff
end Round162C

/- N1_CENTRAL_ORBIT_COUNT: actual arithmetic discreteness, needed to
bound the number of principal orbit terms on a compact central region. -/
namespace Round163D
open MasulloGRH Round142B Round157C Round162C
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_principal_isolating_neighborhood :
    ∃ U : Set (HeckeAdeles K), IsOpen U ∧ (0 : HeckeAdeles K) ∈ U ∧
      ∀ k : K, algebraMap K (HeckeAdeles K) k ∈ U → k = 0 := by
  classical
  let A : HeckeAdeles K → ℝ := fun x => ∏ w : InfinitePlace K, ‖x.1 w‖ ^ w.mult
  have hA : Continuous A := by
    exact continuous_finset_prod Finset.univ (fun w _ =>
      (((continuous_apply w).comp continuous_fst).norm).pow _)
  let U : Set (HeckeAdeles K) := {x | A x < 1} ∩
    {x | ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Valued.v (x.2 v) ≤ 1}
  have ho : IsOpen U := by
    exact (isOpen_lt hA continuous_const).inter
      ((RestrictedProduct.isOpen_forall_mem
        (fun _ => Valued.isOpen_valuationSubring _)).preimage continuous_snd)
  have hz : (0 : HeckeAdeles K) ∈ U := by
    constructor
    · have hi (w : InfinitePlace K) :
          ‖(0 : HeckeAdeles K).1 w‖ ^ w.mult = 0 := by
        change ‖(0 : _)‖ ^ w.mult = 0
        rw [norm_zero, zero_pow InfinitePlace.mult_ne_zero]
      change (∏ w : InfinitePlace K, ‖(0 : HeckeAdeles K).1 w‖ ^ w.mult) < 1
      simp_rw [hi]
      simp
    · intro v
      change Valued.v (0 : _) ≤ 1
      simp
  refine ⟨U, ho, hz, ?_⟩
  intro k hk
  by_contra hkn
  let z : HeckeIdeles K := principalIdele K (Units.mk0 k hkn)
  have ha : A z.val < 1 := hk.1
  have hf : ∀ v : FinitePlace K, ‖z.val.2 v.maximalIdeal‖ ≤ 1 := by
    intro v
    apply Valued.toNormedField.norm_le_one_iff.mpr
    exact hk.2 v.maximalIdeal
  have hs := genuineIdele_finite_norm_support K z
  have hp : (∏ᶠ v : FinitePlace K, ‖z.val.2 v.maximalIdeal‖) ≤ 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hs.toFinset) (by simp)]
    calc
      _ ≤ ∏ _v ∈ hs.toFinset, (1 : ℝ) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun v _ => hf v)
      _ = 1 := by simp
  have hm : genuineIdeleModulus K z ≤ A z.val := by
    change A z.val * _ ≤ A z.val
    exact (mul_le_mul_of_nonneg_left hp
      (Finset.prod_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _))).trans_eq
        (mul_one _)
  have he : genuineIdeleModulus K z = 1 := genuineIdeleModulus_principal K _
  linarith

#check genuine_principal_isolating_neighborhood
#print axioms genuine_principal_isolating_neighborhood
end Round163D

namespace Round164D
open MasulloGRH Round163D
variable (K : Type*) [Field K] [NumberField K]
/-- The arithmetic finite-intersection input to actual central theta counts. -/
theorem genuine_principal_compact_inter_finite
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) :
    (S ∩ (NumberField.AdeleRing.principalSubgroup (𝓞 K) K : Set (HeckeAdeles K))).Finite := by
  letI : T2Space (NumberField.InfiniteAdeleRing K) := by
    change T2Space (∀ w : InfinitePlace K, w.Completion)
    infer_instance
  letI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    T2Space.of_injective_continuous DFunLike.coe_injective
      RestrictedProduct.continuous_coe
  letI : T2Space (HeckeAdeles K) := by
    change T2Space (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
    infer_instance
  let H := NumberField.AdeleRing.principalSubgroup (𝓞 K) K
  obtain ⟨U, ho, hz, hu⟩ := genuine_principal_isolating_neighborhood K
  have hpre : (fun x : H => (x : HeckeAdeles K)) ⁻¹' U = {0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := x.property
      have hk0 := hu k (by simpa only [hk] using hx)
      have hx0 : x = 0 := by
        apply Subtype.ext
        change (x : HeckeAdeles K) = 0
        rw [← hk, hk0, map_zero]
      exact Set.mem_singleton_iff.mpr hx0
    · intro hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      simpa only [hx0] using hz
  letI : DiscreteTopology H := discreteTopology_iff_isOpen_singleton_zero.mpr
    (hpre ▸ ho.preimage continuous_subtype_val)
  have hc : IsClosed (H : Set (HeckeAdeles K)) := AddSubgroup.isClosed_of_discrete
  have hd : IsDiscrete (H : Set (HeckeAdeles K)) :=
    isDiscrete_iff_discreteTopology.mpr inferInstance
  exact (hS.inter_right hc).finite (hd.mono Set.inter_subset_right)
#check genuine_principal_compact_inter_finite
#print axioms genuine_principal_compact_inter_finite
end Round164D

/- N1_CENTRAL_ORBIT_COUNT: a single finite set of genuine principal
translates controls every supported seed over a compact idele region.
This supplies the central theta moment count; no nuclearity is asserted. -/
namespace Round164D
open MasulloGRH Round142B
open scoped Pointwise
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_uniform_compact_orbit_set
    (S : Set (HeckeAdeles K)) (Y : Set (HeckeIdeles K))
    (hS : IsCompact S) (hY : IsCompact Y) :
    ∃ U : Finset Kˣ, ∀ y ∈ Y, ∀ u : Kˣ,
      (principalIdele K u * y).val ∈ S → u ∈ U := by
  classical
  let C : Set (HeckeAdeles K) :=
    S * ((fun y : HeckeIdeles K => (y⁻¹).val) '' Y)
  have hC : IsCompact C :=
    hS.mul (hY.image (Units.continuous_val.comp continuous_inv))
  have hinj : Function.Injective (fun u : Kˣ => (principalIdele K u).val) := by
    intro u v huv
    apply Units.ext
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K huv
  have hfinite := (genuine_principal_compact_inter_finite K C hC).preimage hinj.injOn
  refine ⟨hfinite.toFinset, ?_⟩
  intro y hy u hu
  apply hfinite.mem_toFinset.mpr
  constructor
  · change (principalIdele K u).val ∈ C
    apply Set.mem_mul.mpr
    refine ⟨(principalIdele K u * y).val, hu, (y⁻¹).val, ⟨y, hy, rfl⟩, ?_⟩
    change (principalIdele K u).val * y.val * (y⁻¹).val = (principalIdele K u).val
    rw [mul_assoc, y.mul_inv, mul_one]
  · exact ⟨(u : K), rfl⟩

#check genuine_uniform_compact_orbit_set
#print axioms genuine_uniform_compact_orbit_set
end Round164D

namespace Round164D
open MasulloGRH Round142B
variable (K : Type*) [Field K] [NumberField K]

/-- The common arithmetic count derives convergence and the central
bound for all supported seeds; no orbit summability is retained. -/
theorem genuine_uniform_central_theta_bound
    (S : Set (HeckeAdeles K)) (Y : Set (HeckeIdeles K))
    (hS : IsCompact S) (hY : IsCompact Y) :
    ∃ U : Finset Kˣ, ∀ b : HeckeAdeles K → ℂ,
      Function.support b ⊆ S → ∀ y ∈ Y,
        Summable (fun u : Kˣ => b (principalIdele K u * y).val) ∧
        theta K b y = ∑ u ∈ U, b (principalIdele K u * y).val ∧
        ∀ B : ℝ, (∀ x, ‖b x‖ ≤ B) → ‖theta K b y‖ ≤ U.card * B := by
  classical
  obtain ⟨U, hU⟩ := genuine_uniform_compact_orbit_set K S Y hS hY
  refine ⟨U, ?_⟩
  intro b hb y hy
  have hz : ∀ u : Kˣ, u ∉ U → b (principalIdele K u * y).val = 0 := by
    intro u hu
    by_contra hn
    exact hu (hU y hy u (hb hn))
  have he : theta K b y = ∑ u ∈ U, b (principalIdele K u * y).val :=
    tsum_eq_sum hz
  refine ⟨summable_of_ne_finset_zero hz, he, ?_⟩
  intro B hB
  rw [he]
  calc
    ‖∑ u ∈ U, b (principalIdele K u * y).val‖ ≤
        ∑ u ∈ U, ‖b (principalIdele K u * y).val‖ := norm_sum_le _ _
    _ ≤ ∑ _u ∈ U, B := Finset.sum_le_sum (fun u _ => hB _)
    _ = U.card * B := by simp

#check genuine_uniform_central_theta_bound
#print axioms genuine_uniform_central_theta_bound
end Round164D

/- N1_NATIVE_CENTRAL_ATTACHMENT: attach the actual arithmetic theta sum
   to the authentic class quotient. Compact-region continuity is proved
   without assuming global idele local compactness or theta summability.
   These are seed-moment prerequisites for the actual leading S1 estimate,
   not a nuclear estimate or an assumed projected-range cost. -/
namespace Round166E
open MasulloGRH Round142B Round164D
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_theta_principal_invariant
    (b : HeckeAdeles K → ℂ) (v : Kˣ) (y : HeckeIdeles K) :
    theta K b (principalIdele K v * y) = theta K b y := by
  unfold theta
  calc
    _ = ∑' u : Kˣ, b (principalIdele K (u * v) * y).val := by
      apply tsum_congr
      intro u
      rw [map_mul, mul_assoc]
    _ = _ := (Equiv.mulRight v).tsum_eq
      (fun u : Kˣ => b (principalIdele K u * y).val)

noncomputable def genuineClassTheta (b : HeckeAdeles K → ℂ) :
    HeckeIdeleClasses K → ℂ :=
  Quotient.lift (theta K b) (by
    intro y z hyz
    have hm : y⁻¹ * z ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound hyz)
    obtain ⟨u, hu⟩ := hm
    have hz : z = principalIdele K u * y := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hz, genuine_theta_principal_invariant])

@[simp] theorem genuineClassTheta_mk (b : HeckeAdeles K → ℂ)
    (y : HeckeIdeles K) :
    genuineClassTheta K b (QuotientGroup.mk y) = theta K b y := rfl

/-- The same arithmetic finite set gives continuity on every compact
idele region for every continuous seed with the fixed support cover. -/
theorem genuine_theta_continuousOn_compact
    (S : Set (HeckeAdeles K)) (Y : Set (HeckeIdeles K))
    (hS : IsCompact S) (hY : IsCompact Y)
    (b : HeckeAdeles K → ℂ) (hb : Function.support b ⊆ S)
    (hbc : Continuous b) : ContinuousOn (theta K b) Y := by
  classical
  obtain ⟨U, hU⟩ := genuine_uniform_central_theta_bound K S Y hS hY
  have hterm (u : Kˣ) : Continuous
      (fun y : HeckeIdeles K => b (principalIdele K u * y).val) :=
    hbc.comp (Units.continuous_val.comp (continuous_const.mul continuous_id))
  apply (continuousOn_finset_sum U
    (fun u _ => (hterm u).continuousOn)).congr
  intro y hy
  exact (hU b hb y hy).2.1

/-- A genuine bound on the class image of a compact idele region.
Neither a finite theta support nor orbit summability is an assumption. -/
theorem genuine_class_theta_central_bound
    (S : Set (HeckeAdeles K)) (Y : Set (HeckeIdeles K))
    (hS : IsCompact S) (hY : IsCompact Y) :
    ∃ U : Finset Kˣ, ∀ b : HeckeAdeles K → ℂ,
      Function.support b ⊆ S → ∀ B : ℝ,
      (∀ x, ‖b x‖ ≤ B) → ∀ c ∈
      (fun y : HeckeIdeles K => (QuotientGroup.mk y : HeckeIdeleClasses K)) '' Y,
      ‖genuineClassTheta K b c‖ ≤ U.card * B := by
  obtain ⟨U, hU⟩ := genuine_uniform_central_theta_bound K S Y hS hY
  refine ⟨U, ?_⟩
  intro b hb B hB c hc
  obtain ⟨y, hy, rfl⟩ := hc
  exact (hU b hb y hy).2.2 B hB

#check genuine_theta_principal_invariant
#print axioms genuine_theta_principal_invariant
#check genuineClassTheta_mk
#print axioms genuineClassTheta_mk
#check genuine_theta_continuousOn_compact
#print axioms genuine_theta_continuousOn_compact
#check genuine_class_theta_central_bound
#print axioms genuine_class_theta_central_bound
end Round166E

/- N1_NATIVE_CENTRAL_ATTACHMENT: actual global theta continuity via
arithmetic local finiteness; no local-finiteness or summability premise. -/
namespace Round167E
open MasulloGRH Round142B Round163D Round164D Round166E
open Topology
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_principal_subset_closed
    (T : Set (HeckeAdeles K))
    (hT : T ⊆ (NumberField.AdeleRing.principalSubgroup (𝓞 K) K : Set (HeckeAdeles K))) :
    IsClosed T := by
  letI : T2Space (NumberField.InfiniteAdeleRing K) := by
    change T2Space (∀ w : InfinitePlace K, w.Completion)
    infer_instance
  letI : T2Space (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    T2Space.of_injective_continuous DFunLike.coe_injective
      RestrictedProduct.continuous_coe
  letI : T2Space (HeckeAdeles K) := by
    change T2Space (NumberField.InfiniteAdeleRing K ×
      IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
    infer_instance
  let H := NumberField.AdeleRing.principalSubgroup (𝓞 K) K
  obtain ⟨U, ho, hz, hu⟩ := genuine_principal_isolating_neighborhood K
  have hpre : (fun x : H => (x : HeckeAdeles K)) ⁻¹' U = {0} := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := x.property
      have hk0 := hu k (by simpa only [hk] using hx)
      have hx0 : x = 0 := by
        apply Subtype.ext
        change (x : HeckeAdeles K) = 0
        rw [← hk, hk0, map_zero]
      exact Set.mem_singleton_iff.mpr hx0
    · intro hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      simpa only [hx0] using hz
  letI : DiscreteTopology H := discreteTopology_iff_isOpen_singleton_zero.mpr
    (hpre ▸ ho.preimage continuous_subtype_val)
  have hc : IsClosed (H : Set (HeckeAdeles K)) := AddSubgroup.isClosed_of_discrete
  have he : (Subtype.val : H → HeckeAdeles K) ''
      ((Subtype.val : H → HeckeAdeles K) ⁻¹' T) = T := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hT hx⟩, hx, rfl⟩
  rw [← he]
  exact hc.isClosedMap_subtype_val _ (isClosed_discrete _)

theorem genuine_local_finite_orbit_set
    (S : Set (HeckeAdeles K)) (hS : IsCompact S) (y0 : HeckeIdeles K) :
    ∃ N : Set (HeckeIdeles K), IsOpen N ∧ y0 ∈ N ∧
      ∃ U : Finset Kˣ, ∀ y ∈ N, ∀ u : Kˣ,
        (principalIdele K u * y).val ∈ S → u ∈ U := by
  classical
  let H := NumberField.AdeleRing.principalSubgroup (𝓞 K) K
  let C : Set (HeckeAdeles K) := (fun x : HeckeAdeles K => x * (y0⁻¹).val) '' S
  have hC : IsCompact C := hS.image (continuous_id.mul continuous_const)
  have hcT : IsClosed ((H : Set (HeckeAdeles K)) \ C) :=
    genuine_principal_subset_closed K _ Set.diff_subset
  let f : HeckeAdeles K × HeckeIdeles K → HeckeAdeles K :=
    fun p => p.1 * (p.2⁻¹).val
  have hf : Continuous f :=
    continuous_fst.mul (Units.continuous_val.comp continuous_snd.inv)
  have hp : S ×ˢ ({y0} : Set (HeckeIdeles K)) ⊆ f ⁻¹' ((H : Set (HeckeAdeles K)) \ C)ᶜ := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hy0 : y = y0 := Set.mem_singleton_iff.mp hy
    subst y
    intro ht
    exact ht.2 ⟨x, hx, rfl⟩
  obtain ⟨V, N, _hV, hN, hSV, hyN, hVN⟩ := generalized_tube_lemma hS
    isCompact_singleton (hcT.isOpen_compl.preimage hf) hp
  have hinj : Function.Injective (fun u : Kˣ => (principalIdele K u).val) := by
    intro u v huv
    apply Units.ext
    exact NumberField.AdeleRing.algebraMap_injective (𝓞 K) K huv
  have hfinite := (genuine_principal_compact_inter_finite K C hC).preimage hinj.injOn
  refine ⟨N, hN, hyN (Set.mem_singleton y0), hfinite.toFinset, ?_⟩
  intro y hy u hu
  apply hfinite.mem_toFinset.mpr
  have hpr : (principalIdele K u).val ∈ (H : Set (HeckeAdeles K)) := ⟨(u : K), rfl⟩
  have hpair : ((principalIdele K u * y).val, y) ∈ V ×ˢ N := ⟨hSV hu, hy⟩
  have hn := hVN hpair
  have he : f ((principalIdele K u * y).val, y) = (principalIdele K u).val := by
    change (principalIdele K u).val * y.val * (y⁻¹).val = _
    rw [mul_assoc, y.mul_inv, mul_one]
  change f ((principalIdele K u * y).val, y) ∉ (H : Set (HeckeAdeles K)) \ C at hn
  rw [he] at hn
  exact ⟨by by_contra h; exact hn ⟨hpr, h⟩, hpr⟩

theorem genuine_theta_continuous
    (S : Set (HeckeAdeles K)) (hS : IsCompact S)
    (b : HeckeAdeles K → ℂ) (hb : Function.support b ⊆ S)
    (hbc : Continuous b) : Continuous (theta K b) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro y0
  obtain ⟨N, hN, hyN, U, hU⟩ := genuine_local_finite_orbit_set K S hS y0
  have hsum : Continuous (fun y : HeckeIdeles K =>
      ∑ u ∈ U, b (principalIdele K u * y).val) := by
    apply continuous_finset_sum
    intro u _
    exact hbc.comp (Units.continuous_val.comp (continuous_const.mul continuous_id))
  apply hsum.continuousAt.congr_of_eventuallyEq
  filter_upwards [hN.mem_nhds hyN] with y hy
  apply tsum_eq_sum
  intro u hu
  by_contra hn
  exact hu (hU y hy u (hb hn))

theorem genuine_class_theta_continuous
    (S : Set (HeckeAdeles K)) (hS : IsCompact S)
    (b : HeckeAdeles K → ℂ) (hb : Function.support b ⊆ S)
    (hbc : Continuous b) : Continuous (genuineClassTheta K b) := by
  apply (QuotientGroup.isQuotientMap_mk (principalIdeles K)).continuous_iff.mpr
  exact genuine_theta_continuous K S hS b hb hbc

#check genuine_principal_subset_closed
#print axioms genuine_principal_subset_closed
#check genuine_local_finite_orbit_set
#print axioms genuine_local_finite_orbit_set
#check genuine_theta_continuous
#print axioms genuine_theta_continuous
#check genuine_class_theta_continuous
#print axioms genuine_class_theta_continuous
end Round167E
