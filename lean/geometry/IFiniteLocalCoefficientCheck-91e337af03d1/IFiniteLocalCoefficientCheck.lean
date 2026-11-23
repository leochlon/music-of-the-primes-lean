import Mathlib

/-! The kernel and diagonal trace of convolution followed by the geometric projection onto a finite admitted family of Mellin jets. -/
attribute [local instance] Classical.propDecidable

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

namespace Masullo.IdeleClassGeometry
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable def classLog : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (fun y => Real.log (genuineIdeleModulus K y)) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    change Real.log (genuineIdeleModulus K x) = Real.log (genuineIdeleModulus K y)
    rw [hy, genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul])

end Masullo.IdeleClassGeometry
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)
instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩
end MasulloGRH

namespace MasulloGRH
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
abbrev FinitePrime := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
abbrev LocalField (v : FinitePrime K) := v.adicCompletion K
noncomputable def integralFiniteAdele (x : ∀ v : FinitePrime K, v.adicCompletionIntegers K) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun v : FinitePrime K => LocalField K v)
    (fun v => (v.adicCompletionIntegers K : Set (LocalField K v))) Filter.cofinite x

theorem integralFiniteSet_open : IsOpen
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} := by
  have hr : {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} =
      Set.range (integralFiniteAdele K) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact fun v => (x v).property
  rw [hr]
  exact (RestrictedProduct.isOpenEmbedding_structureMap (fun v =>
    (Valued.isClopen_closedBall (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen)).isOpen_range

noncomputable def finiteNorm (a : HeckeIdeles K) : ℝ :=
  ∏ᶠ v : NumberField.FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem finiteNorm_mul (a b : HeckeIdeles K) :
    finiteNorm K (a*b) = finiteNorm K a * finiteNorm K b := by
  unfold finiteNorm
  have h (v : NumberField.FinitePlace K) :
      ‖(a*b).val.2 v.maximalIdeal‖ = ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ :=
    norm_mul _ _
  simp_rw [h]
  exact finprod_mul_distrib (genuineIdele_finite_norm_support K a)
    (genuineIdele_finite_norm_support K b)

theorem finiteNorm_one_of_integral (a : HeckeIdeles K)
    (ha : ∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1)
    (hi : ∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1) :
    finiteNorm K a = 1 := by
  have hn (v : FinitePrime K) : ‖a.val.2 v‖ = 1 := by
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm (ha v)
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right (hi v) _
        _ = _ := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  simp [finiteNorm, hn]

theorem finiteNorm_continuous : Continuous (finiteNorm K) := by
  let U : Set (HeckeIdeles K) := {a | (∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1) ∧
    (∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1)}
  have ho : IsOpen U := (integralFiniteSet_open K).preimage
    (continuous_snd.comp Units.continuous_val) |>.inter
      ((integralFiniteSet_open K).preimage (continuous_snd.comp Units.continuous_coe_inv))
  have h1 : (1 : HeckeIdeles K) ∈ U := by
    constructor <;> intro v <;> change Valued.v (1 : LocalField K v) ≤ 1 <;> simp
  rw [continuous_iff_continuousAt]
  intro a
  have hV : ∀ᶠ b in 𝓝 a, a⁻¹*b ∈ U :=
    ((ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1))
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [hV] with b hb
  have h := finiteNorm_one_of_integral K (a⁻¹*b) hb.1 hb.2
  have he := finiteNorm_mul K a (a⁻¹*b)
  simpa [h, mul_assoc] using he

theorem genuineIdeleModulus_continuous : Continuous (genuineIdeleModulus K) := by
  have h : Continuous (fun a : HeckeIdeles K =>
      ∏ w : NumberField.InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) := by fun_prop
  exact h.mul (finiteNorm_continuous K)

end MasulloGRH

namespace Masullo.WeightedIdeleClass
open MasulloGRH Masullo.IdeleClassGeometry MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Arithmetic logarithm on the actual idele-class quotient. -/
theorem classLog_mul (g x : HeckeIdeleClasses K) :
    classLog K (g * x) = classLog K g + classLog K x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  change Real.log (genuineIdeleModulus K (a*b)) = _
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b)]
  rfl

theorem classLog_continuous : Continuous (classLog K) :=
  ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K)).quotient_lift _

end Masullo.WeightedIdeleClass
end


namespace DReview
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
/-- The physical cutoff is on the actual class logarithm. -/
def physicalBand (n : ℕ) : Set (HeckeIdeleClasses K) :=
  {x | |classLog K x| ≤ (n : ℝ)}

theorem physicalBand_measurable (n : ℕ) : MeasurableSet (physicalBand K n) :=
  measurableSet_le (classLog_continuous K).measurable.abs measurable_const

/-- A fixed original-Haar diagonal is exhausted in the physical variable. -/
theorem originalHaar_physical_limit (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun n => ∫ x, (physicalBand K n).indicator d x ∂mu)
      atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · intro n
    exact hd.aestronglyMeasurable.indicator (physicalBand_measurable K n)
  · exact hd.norm
  · intro n
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ physicalBand K n <;> simp [hx])
  · apply Filter.Eventually.of_forall
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hx : x ∈ physicalBand K n := hN.trans (by exact_mod_cast hn)
    simp [hx]

/-- The same actual quotient logarithm reverses sign under inversion. -/
theorem classLog_inv (x : HeckeIdeleClasses K) : classLog K x⁻¹ = -classLog K x := by
  have h1 := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h1
  have hz : classLog K 1 = 0 := by linarith
  have hi := classLog_mul K x x⁻¹
  rw [mul_inv_cancel, hz] at hi
  linarith

/-- Reverse conjugation, retaining complex tests. -/
noncomputable def sharp (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  star (phi x⁻¹)

theorem sharp_log (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) :
    sharp K (fun y => (classLog K y : ℂ) * phi y) x =
      -(classLog K x : ℂ) * sharp K phi x := by
  simp [sharp, classLog_inv, star_mul, mul_comm]

theorem sharp_compact (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi) :
    Continuous (sharp K phi) ∧ HasCompactSupport (sharp K phi) := by
  refine ⟨hh.star.comp continuous_inv, ?_⟩
  exact (hc.comp_homeomorph (Homeomorph.inv (HeckeIdeleClasses K))).comp_left
    (show star (0 : ℂ) = 0 by simp)

/-- Both manuscript kernels meet the same compact-continuity hypotheses. -/
theorem both_sharp_tests_compact (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi) :
    (Continuous (sharp K phi) ∧ HasCompactSupport (sharp K phi)) ∧
    (Continuous (sharp K (fun x => (classLog K x : ℂ) * phi x)) ∧
      HasCompactSupport (sharp K (fun x => (classLog K x : ℂ) * phi x))) := by
  refine ⟨sharp_compact K phi hh hc, ?_⟩
  exact sharp_compact K _
    ((Complex.continuous_ofReal.comp (classLog_continuous K)).mul hh) hc.mul_left

/-- Vanishing on the full norm-one subgroup is preserved by sharp. -/
theorem sharp_vanishes_normOne (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (x : HeckeIdeleClasses K) (hx : classLog K x = 0) : sharp K phi x = 0 := by
  have hi : classLog K x⁻¹ = 0 := by rw [classLog_inv, hx, neg_zero]
  simp [sharp, hphi x⁻¹ hi]


end DReview

namespace LIntegrated
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The two required tests, without changing their complex conjugation convention. -/
def requiredTest (phi : HeckeIdeleClasses K → ℂ) (q : Fin 2) :
    HeckeIdeleClasses K → ℂ :=
  if q = 0 then DReview.sharp K phi
  else DReview.sharp K (fun x => (classLog K x : ℂ) * phi x)

@[simp] theorem requiredTest_zero (phi : HeckeIdeleClasses K → ℂ) :
    requiredTest K phi 0 = DReview.sharp K phi := by simp [requiredTest]

@[simp] theorem requiredTest_one (phi : HeckeIdeleClasses K → ℂ) :
    requiredTest K phi 1 = DReview.sharp K (fun x => (classLog K x : ℂ) * phi x) := by
  simp [requiredTest]

theorem requiredTest_log_sign (phi : HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K) :
    requiredTest K phi 1 x = -(classLog K x : ℂ) * requiredTest K phi 0 x := by
  simpa only [requiredTest_zero, requiredTest_one] using DReview.sharp_log K phi x

theorem requiredTest_compact (phi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous phi) (hc : HasCompactSupport phi) (q : Fin 2) :
    Continuous (requiredTest K phi q) ∧ HasCompactSupport (requiredTest K phi q) := by
  have ht := DReview.both_sharp_tests_compact K phi hh hc
  fin_cases q
  · simpa only [requiredTest_zero] using ht.1
  · simpa only [requiredTest_one] using ht.2

/-- The full norm-one vanishing assumption of 12.5.1.1 is discharged for both tests. -/
theorem requiredTest_vanishes_normOne (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (x : HeckeIdeleClasses K) (hx : classLog K x = 0) :
    requiredTest K phi q x = 0 := by
  fin_cases q
  · exact DReview.sharp_vanishes_normOne K phi hphi x hx
  · change requiredTest K phi 1 x = 0
    rw [requiredTest_log_sign, hx]
    simp

/-- Consequently both free convolution diagonals vanish at the group identity. -/
theorem requiredTest_at_one (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) :
    requiredTest K phi q 1 = 0 := by
  apply requiredTest_vanishes_normOne K phi hphi q
  have h := Masullo.WeightedIdeleClass.classLog_mul K
    (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h
  linarith

/-- The geometric-minus-spectral diagonal sign is pointwise, on a chosen kernel.
This avoids restricting an arbitrary product-a.e. representative to the diagonal. -/
theorem both_kernel_diagonal_sign (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (spectralKernel : Fin 2 → HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (q : Fin 2) (x : HeckeIdeleClasses K) :
    requiredTest K phi q (x * x⁻¹) - spectralKernel q x x = -spectralKernel q x x := by
  rw [mul_inv_cancel, requiredTest_at_one K phi hphi q, zero_sub]


end
end LIntegrated

/- Insert after DReview and LIntegrated.requiredTest. This is the compact
support step of 12.5.1.1 on the actual quotient, not an orbital trace premise. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
open Filter
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem classLog_one : classLog K (1 : HeckeIdeleClasses K) = 0 := by
  have h := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h
  linarith

theorem classLog_pow (g : HeckeIdeleClasses K) (n : ℕ) :
    classLog K (g^n) = (n : ℝ) * classLog K g := by
  induction n with
  | zero => simp [classLog_one]
  | succ n ih =>
    rw [pow_succ, classLog_mul, ih]
    push_cast
    ring

theorem classLog_zpow (g : HeckeIdeleClasses K) (n : ℤ) :
    classLog K (g^n) = (n : ℝ) * classLog K g := by
  cases n with
  | ofNat n => simpa using classLog_pow K g n
  | negSucc n =>
    simp only [zpow_negSucc, DReview.classLog_inv, classLog_pow, Int.cast_negSucc]
    push_cast
    ring

/-- Compact support supplies the actual logarithmic bound used outside S. -/
theorem compact_log_support_bound (h : HeckeIdeleClasses K → ℂ)
    (hc : HasCompactSupport h) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, h x ≠ 0 → |classLog K x| ≤ R := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport h) from hc).exists_bound_of_continuousOn
    (classLog_continuous K).continuousOn
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro x hx
  have hm : x ∈ tsupport h := subset_tsupport h hx
  have hb : |classLog K x| ≤ R := by
    simpa only [Real.norm_eq_abs] using hR x hm
  exact hb.trans (le_max_left _ _)

/-- Every nonzero integer power lies outside support when the logarithmic
step is larger than the support radius; the identity term uses h(1)=0. -/
theorem large_log_step_vanishes
    (h : HeckeIdeleClasses K → ℂ) (R : ℝ)
    (hR : ∀ x, h x ≠ 0 → |classLog K x| ≤ R) (h1 : h 1 = 0)
    (g : HeckeIdeleClasses K) (hg : R < |classLog K g|) (n : ℤ) :
    h (g^n) = 0 := by
  by_cases hn : n = 0
  · simp [hn, h1]
  · by_contra hne
    have hx := hR (g^n) hne
    rw [classLog_zpow, abs_mul] at hx
    have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
      rcases lt_or_gt_of_ne hn with hneg | hpos
      · have hi : n ≤ -1 := by omega
        have hr : (n : ℝ) ≤ -1 := by exact_mod_cast hi
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hi : (1 : ℤ) ≤ n := by omega
        have hr : (1 : ℝ) ≤ n := by exact_mod_cast hi
        exact hr.trans (le_abs_self _)
    have hstep : |classLog K g| ≤ |(n : ℝ)| * |classLog K g| := by
      nlinarith [abs_nonneg (classLog K g)]
    linarith

/-- The proof of large-place vanishing applies to BOTH literal sharp tests
with one support radius. It allows the actual local character/norm factors
as arbitrary coefficients, since every lattice evaluation already vanishes. -/
theorem both_tests_large_log_step
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ q : Fin 2, ∀ g : HeckeIdeleClasses K,
      R < |classLog K g| →
      (∀ n : ℤ, LIntegrated.requiredTest K phi q (g^n) = 0) ∧
      (∀ c : ℤ → ℂ, HasSum
        (fun n : ℤ => c n * LIntegrated.requiredTest K phi q (g^n)) 0) := by
  obtain ⟨R0, hR0, hb0⟩ := compact_log_support_bound K _
    (LIntegrated.requiredTest_compact K phi hh hc 0).2
  obtain ⟨R1, _, hb1⟩ := compact_log_support_bound K _
    (LIntegrated.requiredTest_compact K phi hh hc 1).2
  refine ⟨max R0 R1, hR0.trans (le_max_left _ _), ?_⟩
  intro q g hg
  have hzero : ∀ n : ℤ, LIntegrated.requiredTest K phi q (g^n) = 0 := by
    intro n
    fin_cases q
    · exact large_log_step_vanishes K _ R0 hb0
        (LIntegrated.requiredTest_at_one K phi hphi 0) g
        ((le_max_left R0 R1).trans_lt hg) n
    · exact large_log_step_vanishes K _ R1 hb1
        (LIntegrated.requiredTest_at_one K phi hphi 1) g
        ((le_max_right R0 R1).trans_lt hg) n
  refine ⟨hzero, ?_⟩
  intro c
  simpa only [hzero, mul_zero] using
    (hasSum_zero : HasSum (fun _ : ℤ => (0 : ℂ)) 0)

/-- Sharp inverts the norm direction. Thus the one-sided orbital theorem
requires an actual inversion/splitting application, even for both valid tests. -/
theorem both_tests_support_direction
    (phi : HeckeIdeleClasses K → ℂ)
    (hpos : ∀ x, classLog K x ≤ 0 → phi x = 0)
    (q : Fin 2) (x : HeckeIdeleClasses K) (hx : 0 ≤ classLog K x) :
    LIntegrated.requiredTest K phi q x = 0 := by
  have hi : classLog K x⁻¹ ≤ 0 := by rw [DReview.classLog_inv]; linarith
  have h0 : LIntegrated.requiredTest K phi 0 x = 0 := by
    simp only [LIntegrated.requiredTest_zero, DReview.sharp, hpos x⁻¹ hi, star_zero]
  fin_cases q
  · exact h0
  · change LIntegrated.requiredTest K phi 1 x = 0
    rw [LIntegrated.requiredTest_log_sign, h0, mul_zero]

end
end ReviewI.LocalArithmetic
/- Insert after ILocalFinitenessFragment. The local generator's nonzero norm
must be proved when this is applied to an actual uniformizer class. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Compact logarithmic support makes each nontrivial local norm lattice
finite. Arbitrary local character and norm coefficients do not change this. -/
theorem integer_lattice_support_finite
    (h : HeckeIdeleClasses K → ℂ) (hc : HasCompactSupport h)
    (g : HeckeIdeleClasses K) (hg : classLog K g ≠ 0) :
    Set.Finite (Function.support (fun n : ℤ => h (g^n))) := by
  obtain ⟨R, _, hR⟩ := compact_log_support_bound K h hc
  have hu : 0 < |classLog K g| := abs_pos.mpr hg
  obtain ⟨N, hN⟩ := exists_nat_ge (R / |classLog K g|)
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro n hn
  have hb := hR (g^n) hn
  rw [classLog_zpow, abs_mul] at hb
  have ha : |(n : ℝ)| ≤ (N : ℝ) :=
    ((le_div_iff₀ hu).mpr hb).trans hN
  rcases abs_le.mp ha with ⟨hlo, hhi⟩
  constructor
  · exact_mod_cast hlo
  · exact_mod_cast hhi

/-- Both manuscript test families therefore have finite local lattice sums
at every generator whose norm is not one. -/
theorem both_tests_lattice_summable
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (g : HeckeIdeleClasses K) (hg : classLog K g ≠ 0)
    (q : Fin 2) (c : ℤ → ℂ) :
    Summable (fun n : ℤ => c n * LIntegrated.requiredTest K phi q (g^n)) := by
  have hf := integer_lattice_support_finite K (LIntegrated.requiredTest K phi q)
    (LIntegrated.requiredTest_compact K phi hh hc q).2 g hg
  apply summable_of_ne_finset_zero (s := hf.toFinset)
  intro n hn
  have hz : LIntegrated.requiredTest K phi q (g^n) = 0 := by
    by_contra hne
    exact hn (hf.mem_toFinset.mpr hne)
  simp [hz]
end
end ReviewI.LocalArithmetic

/- Actual finite local embeddings and normalized local expression. The embedding
proofs adapt ALPO GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.
This defines the local endpoint; it does not assert an unproved global trace equality. -/
namespace NLocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField IsDedekindDomain MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

open Classical in
def finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := ⟨Pi.mulSingle v x, by
    have he : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ≠ v :=
      Filter.eventually_cofinite.mpr (by simp)
    filter_upwards [he] with w hw
    rw [Pi.mulSingle_eq_of_ne hw]
    exact one_mem _⟩
  map_one' := Subtype.ext (Pi.mulSingle_one (M := fun w : HeightOneSpectrum (𝓞 K) =>
    w.adicCompletion K) v)
  map_mul' x y := Subtype.ext (Pi.mulSingle_mul v x y)

def finiteEmbedding (v : FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* HeckeIdeles K :=
  Units.map (MonoidHom.prod 1 (finiteAdeleSingle K v.maximalIdeal))

def finiteClass (v : FinitePlace K) :
    (v.maximalIdeal.adicCompletion K)ˣ →* HeckeIdeleClasses K :=
  (QuotientGroup.mk' (principalIdeles K)).comp (finiteEmbedding K v)

theorem finiteEmbedding_modulus (v : FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    genuineIdeleModulus K (finiteEmbedding K v u) =
      ‖(u : v.maximalIdeal.adicCompletion K)‖ := by
  classical
  unfold genuineIdeleModulus
  have hi : (∏ w : InfinitePlace K, ‖(finiteEmbedding K v u).val.1 w‖ ^ w.mult) = 1 := by
    apply Finset.prod_eq_one
    intro w _
    change ‖(1 : w.Completion)‖ ^ w.mult = 1
    simp
  rw [hi, one_mul]
  refine (finprod_eq_single _ v fun w hw => ?_).trans ?_
  · have hn : w.maximalIdeal ≠ v.maximalIdeal :=
      fun h => hw (FinitePlace.maximalIdeal_injective h)
    change ‖Pi.mulSingle v.maximalIdeal (u : v.maximalIdeal.adicCompletion K)
      w.maximalIdeal‖ = 1
    rw [Pi.mulSingle_eq_of_ne hn]
    exact norm_one
  · change ‖Pi.mulSingle v.maximalIdeal (u : v.maximalIdeal.adicCompletion K)
      v.maximalIdeal‖ = _
    rw [Pi.mulSingle_eq_same]

theorem finiteClass_log (v : FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    classLog K (finiteClass K v u) = Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖ := by
  change Real.log (genuineIdeleModulus K (finiteEmbedding K v u)) = _
  rw [finiteEmbedding_modulus]

def finiteUnitGroup (v : FinitePlace K) : Set (v.maximalIdeal.adicCompletion K)ˣ :=
  {u | ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1}

def residueCard (v : FinitePlace K) : ℝ := (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)

def finiteLocalCoefficient (v : FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (mu : Measure (v.maximalIdeal.adicCompletion K)ˣ) : ℝ :=
  Real.log (residueCard K v) / mu.real (finiteUnitGroup K v)

def finiteLocalDensity (v : FinitePlace K) (h : HeckeIdeleClasses K → ℂ)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) : ℂ :=
  h (finiteClass K v u) * (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) /
    (‖1 - (u : v.maximalIdeal.adicCompletion K)‖ : ℂ)

def finiteLocalTerm (v : FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (mu : Measure (v.maximalIdeal.adicCompletion K)ˣ)
    (h : HeckeIdeleClasses K → ℂ) : ℂ :=
  (finiteLocalCoefficient K v mu : ℂ) * ∫ u, finiteLocalDensity K v h u ∂mu

/-- The manuscript's full norm-one vanishing removes the entire finite local
unit group from the density, including the singular point u=1. -/
theorem finiteLocalDensity_unit_zero (v : FinitePlace K)
    (h : HeckeIdeleClasses K → ℂ)
    (hh : ∀ x, classLog K x = 0 → h x = 0)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) (hu : u ∈ finiteUnitGroup K v) :
    finiteLocalDensity K v h u = 0 := by
  have he : classLog K (finiteClass K v u) = 0 := by
    rw [finiteClass_log, show ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1 from hu,
      Real.log_one]
  simp only [finiteLocalDensity, hh _ he, zero_mul, zero_div]

end
end NLocalArithmetic

/- Insert after ILatticeSupportFragment and NLocalArithmeticFragment. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The lattice convergence application uses N's actual local-to-class map. -/
theorem both_tests_finite_local_lattice
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (v : FinitePlace K) (u : (v.maximalIdeal.adicCompletion K)ˣ)
    (hu : ‖(u : v.maximalIdeal.adicCompletion K)‖ ≠ 1)
    (q : Fin 2) (c : ℤ → ℂ) :
    Summable (fun n : ℤ => c n *
      LIntegrated.requiredTest K phi q (NLocalArithmetic.finiteClass K v (u^n))) := by
  have hg : classLog K (NLocalArithmetic.finiteClass K v u) ≠ 0 := by
    rw [NLocalArithmetic.finiteClass_log]
    intro hz
    have he := Real.exp_log (norm_pos_iff.mpr (Units.ne_zero u))
    rw [hz, Real.exp_zero] at he
    exact hu he.symm
  simpa only [map_zpow] using both_tests_lattice_summable K phi hh hc
    (NLocalArithmetic.finiteClass K v u) hg q c

/-- Full norm-one vanishing is applied to both actual finite local densities. -/
theorem both_tests_finite_local_unit_zero
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : FinitePlace K) (u : (v.maximalIdeal.adicCompletion K)ˣ)
    (hu : u ∈ NLocalArithmetic.finiteUnitGroup K v) (q : Fin 2) :
    NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q) u = 0 :=
  NLocalArithmetic.finiteLocalDensity_unit_zero K v _
    (LIntegrated.requiredTest_vanishes_normOne K phi hphi q) u hu

end
end ReviewI.LocalArithmetic
/- Insert after ILocalFinitenessFragment and NLocalArithmeticFragment.
   The adic norm calculation adapts ALPO LocalFieldAtPlace.lean:53--61;
   bounded ideal finiteness is Mathlib's actual number-field theorem. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField MeasureTheory
open scoped BigOperators WithZero
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The norm of each actual finite-local element lies in the residue-cardinality
lattice. No uniformizer norm or local-class logarithm is assumed. -/
theorem finite_norm_eq_zpow (v : NumberField.FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    ‖(u : v.maximalIdeal.adicCompletion K)‖ =
      (NLocalArithmetic.residueCard K v) ^
        WithZero.log (Valued.v (u : v.maximalIdeal.adicCompletion K)) := by
  have hv : Valued.v (u : v.maximalIdeal.adicCompletion K) ≠ 0 :=
    (Valued.v).ne_zero_iff.2 u.ne_zero
  have key : ∀ (y : ℤᵐ⁰) (hy : y ≠ 0),
      Multiplicative.toAdd (WithZero.unzero hy) = WithZero.log y := by
    rintro (_ | a) hy
    · exact absurd rfl hy
    · rfl
  change ((WithZeroMulInt.toNNReal
    (NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero v.maximalIdeal))
      (Valued.v (u : v.maximalIdeal.adicCompletion K)) : ℝ) = _
  rw [WithZeroMulInt.toNNReal_neg_apply _ hv, key]
  simp [NLocalArithmetic.residueCard]

theorem finiteClass_log_lattice (v : NumberField.FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    classLog K (NLocalArithmetic.finiteClass K v u) =
      ((WithZero.log (Valued.v (u : v.maximalIdeal.adicCompletion K)) : ℤ) : ℝ) *
        Real.log (NLocalArithmetic.residueCard K v) := by
  rw [NLocalArithmetic.finiteClass_log, finite_norm_eq_zpow, Real.log_zpow]

theorem residueCard_pos (v : NumberField.FinitePlace K) :
    0 < NLocalArithmetic.residueCard K v := by
  have hz : Ideal.absNorm v.maximalIdeal.asIdeal ≠ 0 :=
    fun h => v.maximalIdeal.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  change (0 : ℝ) < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
  exact_mod_cast Nat.pos_of_ne_zero hz

private theorem one_le_abs_intCast {n : ℤ} (hn : n ≠ 0) :
    (1 : ℝ) ≤ |(n : ℝ)| := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hi : n ≤ -1 := by omega
    have hr : (n : ℝ) ≤ -1 := by exact_mod_cast hi
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have hi : (1 : ℤ) ≤ n := by omega
    have hr : (1 : ℝ) ≤ n := by exact_mod_cast hi
    exact hr.trans (le_abs_self _)

/-- Compact support and full norm-one vanishing force the entire local
density to vanish at every place with logarithmic step exceeding its radius. -/
theorem finite_density_zero_of_large_residueCard
    (h : HeckeIdeleClasses K → ℂ) (R : ℝ) (hR0 : 0 ≤ R)
    (hR : ∀ x, h x ≠ 0 → |classLog K x| ≤ R)
    (hunit : ∀ x, classLog K x = 0 → h x = 0)
    (v : NumberField.FinitePlace K)
    (hv : R < Real.log (NLocalArithmetic.residueCard K v))
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    NLocalArithmetic.finiteLocalDensity K v h u = 0 := by
  have hz : h (NLocalArithmetic.finiteClass K v u) = 0 := by
    let n : ℤ := WithZero.log (Valued.v (u : v.maximalIdeal.adicCompletion K))
    have he : classLog K (NLocalArithmetic.finiteClass K v u) =
        (n : ℝ) * Real.log (NLocalArithmetic.residueCard K v) :=
      finiteClass_log_lattice K v u
    by_cases hn : n = 0
    · apply hunit
      simp [he, hn]
    · by_contra hne
      have hb := hR _ hne
      rw [he, abs_mul, abs_of_pos (hR0.trans_lt hv)] at hb
      have hi := one_le_abs_intCast hn
      have hlog : 0 < Real.log (NLocalArithmetic.residueCard K v) := hR0.trans_lt hv
      nlinarith
  simp only [NLocalArithmetic.finiteLocalDensity, hz, zero_mul, zero_div]

/-- The finite places below a fixed real norm bound form an actual finite set. -/
theorem finite_places_residueCard_le (B : ℝ) :
    Set.Finite {v : NumberField.FinitePlace K | NLocalArithmetic.residueCard K v ≤ B} := by
  obtain ⟨N, hN⟩ := exists_nat_gt B
  have hI : Set.Finite {I : Ideal (𝓞 K) | Ideal.absNorm I < N} := by
    exact (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) N).subset
      (by
        intro I hI
        change Ideal.absNorm I ≤ N
        exact le_of_lt hI)
  have hpre := hI.preimage (f := fun v : NumberField.FinitePlace K => v.maximalIdeal.asIdeal)
    (fun v _ w _ h => NumberField.FinitePlace.maximalIdeal_injective
      (IsDedekindDomain.HeightOneSpectrum.ext h))
  apply hpre.subset
  intro v hv
  change Ideal.absNorm v.maximalIdeal.asIdeal < N
  have hr : (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ) < N := hv.trans_lt hN
  exact_mod_cast hr

/-- One finite set works for BOTH literal manuscript tests, all local elements
and every local Haar normalization. This proves a local-support application,
not the separate equality of a local orbital integral with the global kernel. -/
theorem both_tests_finite_local_support
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) :
    ∃ S : Finset (NumberField.FinitePlace K), ∀ v ∉ S, ∀ q : Fin 2,
      (∀ u : (v.maximalIdeal.adicCompletion K)ˣ,
        NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q) u = 0) ∧
      (∀ (m : MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ)
        (nu : @Measure (v.maximalIdeal.adicCompletion K)ˣ m),
        @NLocalArithmetic.finiteLocalTerm K _ _ v m nu
          (LIntegrated.requiredTest K phi q) = 0) := by
  classical
  obtain ⟨R0, hR0, hb0⟩ := compact_log_support_bound K _
    (LIntegrated.requiredTest_compact K phi hh hc 0).2
  obtain ⟨R1, _, hb1⟩ := compact_log_support_bound K _
    (LIntegrated.requiredTest_compact K phi hh hc 1).2
  let R := max R0 R1
  have hR : 0 ≤ R := hR0.trans (le_max_left _ _)
  let S := (finite_places_residueCard_le K (Real.exp R)).toFinset
  refine ⟨S, ?_⟩
  intro v hv q
  have hexp : Real.exp R < NLocalArithmetic.residueCard K v := by
    have hn : ¬ NLocalArithmetic.residueCard K v ≤ Real.exp R := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hv
    exact lt_of_not_ge hn
  have hlog : R < Real.log (NLocalArithmetic.residueCard K v) :=
    (Real.lt_log_iff_exp_lt (residueCard_pos K v)).mpr hexp
  have hb : ∀ x, LIntegrated.requiredTest K phi q x ≠ 0 → |classLog K x| ≤ R := by
    intro x hx
    fin_cases q
    · exact (hb0 x hx).trans (le_max_left _ _)
    · exact (hb1 x hx).trans (le_max_right _ _)
  have hd : ∀ u : (v.maximalIdeal.adicCompletion K)ˣ,
      NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q) u = 0 :=
    finite_density_zero_of_large_residueCard K _ R hR hb
      (LIntegrated.requiredTest_vanishes_normOne K phi hphi q) v hlog
  refine ⟨hd, ?_⟩
  intro m nu
  simp only [NLocalArithmetic.finiteLocalTerm, hd, integral_zero, mul_zero]

end
end ReviewI.LocalArithmetic

/- Insert after NLocalArithmeticFragment and IFiniteLocalSupportFragment.
   This is the actual nonarchimedean density in manuscript (12.4.1.3),
   with its coefficient and local measure unchanged. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The small-norm branch of the actual local denominator. -/
theorem finite_norm_one_sub_of_lt (v : NumberField.FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ)
    (hu : ‖(u : v.maximalIdeal.adicCompletion K)‖ < 1) :
    ‖1 - (u : v.maximalIdeal.adicCompletion K)‖ = 1 := by
  have hup := IsUltrametricDist.norm_add_le_max
    (1 : v.maximalIdeal.adicCompletion K) (-(u : v.maximalIdeal.adicCompletion K))
  rw [norm_one, norm_neg, max_eq_left hu.le] at hup
  rw [← sub_eq_add_neg] at hup
  refine le_antisymm hup (le_of_not_gt ?_)
  intro hlt
  have hback := IsUltrametricDist.norm_add_le_max
    (1 - (u : v.maximalIdeal.adicCompletion K)) (u : v.maximalIdeal.adicCompletion K)
  rw [sub_add_cancel, norm_one] at hback
  exact (not_lt_of_ge hback) (max_lt hlt hu)

/-- The large-norm branch of the actual local denominator. -/
theorem finite_norm_one_sub_of_gt (v : NumberField.FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ)
    (hu : 1 < ‖(u : v.maximalIdeal.adicCompletion K)‖) :
    ‖1 - (u : v.maximalIdeal.adicCompletion K)‖ =
      ‖(u : v.maximalIdeal.adicCompletion K)‖ := by
  have hup := IsUltrametricDist.norm_add_le_max
    (1 : v.maximalIdeal.adicCompletion K) (-(u : v.maximalIdeal.adicCompletion K))
  rw [norm_one, norm_neg, max_eq_right hu.le] at hup
  rw [← sub_eq_add_neg] at hup
  refine le_antisymm hup (le_of_not_gt ?_)
  intro hlt
  have hback := IsUltrametricDist.norm_add_le_max
    (1 : v.maximalIdeal.adicCompletion K) (-(1 - (u : v.maximalIdeal.adicCompletion K)))
  have he : (1 : v.maximalIdeal.adicCompletion K) + -(1 - (u : v.maximalIdeal.adicCompletion K)) = u := by ring
  rw [he, norm_one, norm_neg] at hback
  exact (not_lt_of_ge hback) (max_lt hu hlt)

/-- The two local weights are sqrt(norm u) and its reciprocal. -/
theorem finiteLocalDensity_of_lt (v : NumberField.FinitePlace K)
    (h : HeckeIdeleClasses K → ℂ) (u : (v.maximalIdeal.adicCompletion K)ˣ)
    (hu : ‖(u : v.maximalIdeal.adicCompletion K)‖ < 1) :
    NLocalArithmetic.finiteLocalDensity K v h u =
      h (NLocalArithmetic.finiteClass K v u) *
        (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) := by
  rw [NLocalArithmetic.finiteLocalDensity, finite_norm_one_sub_of_lt K v u hu,
    Complex.ofReal_one, div_one]

theorem finiteLocalDensity_of_gt (v : NumberField.FinitePlace K)
    (h : HeckeIdeleClasses K → ℂ) (u : (v.maximalIdeal.adicCompletion K)ˣ)
    (hu : 1 < ‖(u : v.maximalIdeal.adicCompletion K)‖) :
    NLocalArithmetic.finiteLocalDensity K v h u =
      h (NLocalArithmetic.finiteClass K v u) /
        (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) := by
  rw [NLocalArithmetic.finiteLocalDensity, finite_norm_one_sub_of_gt K v u hu]
  have he : (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) ^ 2 =
      (‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) := by
    exact_mod_cast Real.sq_sqrt (norm_nonneg (u : v.maximalIdeal.adicCompletion K))
  have hn : (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (norm_pos_iff.2 u.ne_zero)).ne'
  rw [← he, pow_two, mul_div_mul_right _ _ hn]

/-- Full norm-one vanishing supplies the remaining unit branch. -/
theorem finiteLocalDensity_piecewise (v : NumberField.FinitePlace K)
    (h : HeckeIdeleClasses K → ℂ)
    (hh : ∀ x, classLog K x = 0 → h x = 0)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    NLocalArithmetic.finiteLocalDensity K v h u =
      if ‖(u : v.maximalIdeal.adicCompletion K)‖ < 1 then
        h (NLocalArithmetic.finiteClass K v u) *
          (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ)
      else if ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1 then 0
      else h (NLocalArithmetic.finiteClass K v u) /
        (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) := by
  split_ifs with hlt heq
  · exact finiteLocalDensity_of_lt K v h u hlt
  · exact NLocalArithmetic.finiteLocalDensity_unit_zero K v h hh u heq
  · exact finiteLocalDensity_of_gt K v h u (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq))

/-- This evaluates the denominator of the literal local term for BOTH tests;
all local normalizations stay explicit. It does not identify the global trace
with this local expression. -/
theorem both_tests_finiteLocalTerm_piecewise
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (v : NumberField.FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (nu : Measure (v.maximalIdeal.adicCompletion K)ˣ) :
    NLocalArithmetic.finiteLocalTerm K v nu (LIntegrated.requiredTest K phi q) =
      (NLocalArithmetic.finiteLocalCoefficient K v nu : ℂ) *
        ∫ u, (if ‖(u : v.maximalIdeal.adicCompletion K)‖ < 1 then
          LIntegrated.requiredTest K phi q (NLocalArithmetic.finiteClass K v u) *
            (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ)
        else if ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1 then 0
        else LIntegrated.requiredTest K phi q (NLocalArithmetic.finiteClass K v u) /
          (Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ)) ∂nu := by
  unfold NLocalArithmetic.finiteLocalTerm
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => finiteLocalDensity_piecewise K v _
    (LIntegrated.requiredTest_vanishes_normOne K phi hphi q) u

end
end ReviewI.LocalArithmetic

/- Insert immediately after IFiniteDensityFragment. This quantitative bound
   is on N's literal local density, including the removed unit singularity. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem finiteLocalDensity_norm_le (v : NumberField.FinitePlace K)
    (h : HeckeIdeleClasses K → ℂ)
    (hh : ∀ x, classLog K x = 0 → h x = 0)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    ‖NLocalArithmetic.finiteLocalDensity K v h u‖ ≤
      ‖h (NLocalArithmetic.finiteClass K v u)‖ := by
  rcases lt_trichotomy ‖(u : v.maximalIdeal.adicCompletion K)‖ 1 with hlt | heq | hgt
  · rw [finiteLocalDensity_of_lt K v h u hlt, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hlt.le
    exact mul_le_of_le_one_right (norm_nonneg _) hs
  · rw [NLocalArithmetic.finiteLocalDensity_unit_zero K v h hh u heq, norm_zero]
    exact norm_nonneg _
  · rw [finiteLocalDensity_of_gt K v h u hgt, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : 1 ≤ Real.sqrt ‖(u : v.maximalIdeal.adicCompletion K)‖ := by
      simpa using Real.sqrt_le_sqrt hgt.le
    exact div_le_self (norm_nonneg _) hs

theorem both_tests_finiteLocalDensity_norm_le
    (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (v : NumberField.FinitePlace K)
    (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    ‖NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q) u‖ ≤
      ‖LIntegrated.requiredTest K phi q (NLocalArithmetic.finiteClass K v u)‖ :=
  finiteLocalDensity_norm_le K v _
    (LIntegrated.requiredTest_vanishes_normOne K phi hphi q) u

end
end ReviewI.LocalArithmetic

/- Concrete local compactness dependencies, adapted from ALPO GroundTheory/GlobalFields/LocalAtPlace.lean. -/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

namespace NIdelicTopology

section Residue

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem isUnit_iff_valued_eq_one (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  have hv : (Valued.v : Valuation (v.adicCompletion K) _).Integers (v.adicCompletionIntegers K) :=
    ⟨Subtype.coe_injective, fun y => y.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  exact hv.isUnit_iff_valuation_eq_one

theorem denseRange_algebraMap : DenseRange (algebraMap K (v.adicCompletion K)) := by
  exact (UniformSpace.Completion.denseRange_coe (α := WithVal (v.valuation K))).comp
    (WithVal.equiv (v.valuation K)).symm.surjective.denseRange
    (UniformSpace.Completion.continuous_coe _)

theorem algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r ∈
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔ r ∈ v.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_valued_eq_one v, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_of_algebraMap, intValuation_eq_one_iff, not_not]

theorem exists_valuation_sub_lt_one (k : K) (hk : v.valuation K k ≤ 1) :
    ∃ r : R, v.valuation K (k - algebraMap (R) K r) < 1 := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (R)) k
  dsimp only at hab
  subst hab
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hspan : Ideal.span {(b : R)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hb0
  have hfin := Ideal.finite_factors hspan
  have hn : ∀ w : HeightOneSpectrum (R),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) ≤ w.intValuation (b : R) := by
    intro w
    rw [intValuation_def, if_neg hb0]
    exact ⟨_, le_rfl⟩
  choose n hn using hn
  have hdist : ∀ i ∈ insert v hfin.toFinset, ∀ j ∈ insert v hfin.toFinset, i ≠ j →
      (fun w : HeightOneSpectrum (R) => w.asIdeal) i ≠ (fun w => w.asIdeal) j := by
    intro i _ j _ hij h
    exact hij (HeightOneSpectrum.ext h)
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := insert v hfin.toFinset)
    (fun w : HeightOneSpectrum (R) => w.asIdeal)
    (fun w => if w = v then 1 else n w)
    (fun w _ => Ideal.prime_of_isPrime w.ne_bot w.isPrime) hdist
    (fun w => if (w : HeightOneSpectrum (R)) = v then (1 : R) else 0)
  have hcv : c ∉ v.asIdeal := by
    intro hmem
    have h1 := hc v (Finset.mem_insert_self v _)
    simp at h1
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 := v.asIdeal.sub_mem hmem h1
    simpa using h2
  have hcw : ∀ w ∈ hfin.toFinset, w ≠ v → c ∈ w.asIdeal ^ n w := by
    intro w hw hwv
    have h1 := hc w (Finset.mem_insert_of_mem hw)
    simpa [hwv] using h1
  have key : ∀ w : HeightOneSpectrum (R),
      w.valuation K (algebraMap (R) K c * IsLocalization.mk' K a b) ≤ 1 := by
    intro w
    have hvc : w.valuation K (algebraMap (R) K c) = w.intValuation c :=
      valuation_of_algebraMap w c
    rw [map_mul, hvc]
    by_cases hwv : w = v
    · rw [hwv, intValuation_eq_one_iff.mpr hcv, one_mul]
      exact hk
    · rw [valuation_of_mk']
      have hbne : w.intValuation (b : R) ≠ 0 := by
        exact intValuation_ne_zero w _ hb0
      by_cases hwS : w ∈ hfin.toFinset
      · have hc' : w.intValuation c ≤ w.intValuation (b : R) :=
          ((intValuation_le_pow_iff_mem w c (n w)).mpr (hcw w hwS hwv)).trans (hn w)
        rw [div_eq_mul_inv]
        calc w.intValuation c * (w.intValuation a * (w.intValuation (b : R))⁻¹)
            ≤ w.intValuation (b : R) * (1 * (w.intValuation (b : R))⁻¹) := by
              exact mul_le_mul' hc' (mul_le_mul_left (intValuation_le_one w a) _)
          _ = 1 := by rw [one_mul, mul_inv_cancel₀ hbne]
      · have hb1 : w.intValuation (b : R) = 1 := by
          rw [intValuation_eq_one_iff]
          intro hmem
          exact hwS (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr hmem))
        rw [hb1, div_one]
        exact mul_le_one' (intValuation_le_one w c) (intValuation_le_one w a)
  obtain ⟨r', hr'⟩ := RingHom.mem_range.mp (mem_integers_of_valuation_le_one K _ key)
  have hmax : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hcv
  refine ⟨y * r', ?_⟩
  have hi' : i = 1 - y * c := by linear_combination hyi
  have hdiff : IsLocalization.mk' K a b - algebraMap (R) K (y * r') =
      IsLocalization.mk' K a b * algebraMap (R) K i := by
    rw [hi']
    simp only [map_mul, map_sub, map_one, hr']
    ring
  rw [hdiff, map_mul]
  have hvi : v.valuation K (algebraMap (R) K i) < 1 := (valuation_lt_one_iff_mem v i).mpr hi
  calc v.valuation K (IsLocalization.mk' K a b) * v.valuation K (algebraMap (R) K i)
      ≤ 1 * v.valuation K (algebraMap (R) K i) := by
        exact mul_le_mul_left hk _
    _ = v.valuation K (algebraMap (R) K i) := one_mul _
    _ < 1 := hvi


theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) :
    ∃ r : R, x - algebraMap R (v.adicCompletionIntegers K) r ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by

  have hnhds : {y : v.adicCompletion K | Valued.v (y - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by
      exact hy⟩
  obtain ⟨k, hk⟩ := (denseRange_algebraMap (K := K) v).mem_nhds hnhds
  have hk' : Valued.v ((x : v.adicCompletion K) - (k : v.adicCompletion K)) < 1 := by
    rw [Valuation.map_sub_swap]; exact hk

  have hk1 : v.valuation K k ≤ 1 := by
    rw [← valuedAdicCompletion_eq_valuation']
    have : (k : v.adicCompletion K) = (x : v.adicCompletion K) -
        ((x : v.adicCompletion K) - (k : v.adicCompletion K)) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le x.2 hk'.le)
  obtain ⟨r, hr⟩ := exists_valuation_sub_lt_one v k hk1
  refine ⟨r, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_valued_eq_one v]
  refine ne_of_lt ?_
  have hr' : Valued.v (algebraMap K (v.adicCompletion K) (k - algebraMap R K r)) < 1 := by
    have := valuedAdicCompletion_eq_valuation' (R := R) v (k - algebraMap R K r)
    exact this.trans_lt (by simpa using hr)
  have : ((x - algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) :
      v.adicCompletion K) = ((x : v.adicCompletion K) - (k : v.adicCompletion K)) +
        algebraMap K (v.adicCompletion K) (k - algebraMap R K r) := by
    rw [map_sub]
    simp [algebraMap_adicCompletion]
  rw [this]
  exact Valuation.map_add_lt _ hk' hr'

noncomputable def toResidueFieldAdicCompletionIntegers :
    R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (IsLocalRing.residue _).comp (algebraMap R (v.adicCompletionIntegers K))

theorem ker_toResidueFieldAdicCompletionIntegers :
    RingHom.ker (toResidueFieldAdicCompletionIntegers (K := K) v) = v.asIdeal := by
  ext r
  rw [RingHom.mem_ker, toResidueFieldAdicCompletionIntegers, RingHom.comp_apply,
    IsLocalRing.residue_eq_zero_iff, algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff]

theorem toResidueFieldAdicCompletionIntegers_surjective :
    Function.Surjective (toResidueFieldAdicCompletionIntegers (K := K) v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_maximalIdeal v x
  exact ⟨r, (Ideal.Quotient.eq.2 hr).symm⟩

noncomputable def residueFieldEquiv :
    (R ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotEquivOfEq (ker_toResidueFieldAdicCompletionIntegers v).symm).trans
    (RingHom.quotientKerEquivOfSurjective (toResidueFieldAdicCompletionIntegers_surjective v))

@[simp]
theorem residueFieldEquiv_mk (r : R) :
    residueFieldEquiv (K := K) v (Ideal.Quotient.mk v.asIdeal r) =
      IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) :=
  rfl

end Residue

section NumberField

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  Finite.of_equiv _ (residueFieldEquiv v).toEquiv

theorem natCard_residueField_adicCompletionIntegers :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) =
      Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueFieldEquiv v).toEquiv).symm

end NumberField

section Topology

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem isOpen_adicCompletionIntegers :
    IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isOpen_valuationSubring _

theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  (Valued.isClopen_integer (v.adicCompletion K)).isClosed

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have : CompleteSpace (Valued.integer (v.adicCompletion K)) :=
    (isClosed_adicCompletionIntegers v).completeSpace_coe
  have : IsDiscreteValuationRing (Valued.integer (v.adicCompletion K)) :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have : Finite (Valued.ResidueField (v.adicCompletion K)) :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have h : CompactSpace (Valued.integer (v.adicCompletion K)) :=
    Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.2
      ⟨inferInstance, inferInstance, inferInstance⟩
  exact isCompact_iff_compactSpace.2 h

instance : CompactSpace (v.adicCompletionIntegers K) :=
  isCompact_iff_compactSpace.1 (isCompact_adicCompletionIntegers v)

instance : LocallyCompactSpace (v.adicCompletion K) :=
  (isCompact_adicCompletionIntegers v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((isOpen_adicCompletionIntegers v).mem_nhds (v.adicCompletionIntegers K).zero_mem)

instance : CompleteSpace (v.adicCompletionIntegers K) :=
  (isClosed_adicCompletionIntegers v).completeSpace_coe

end Topology

end NIdelicTopology
/- Insert after NIdelicTopologyFragment, IFiniteLocalSupportFragment,
   IFiniteDensityFragment and IFiniteDensityBoundFragment.
   Compactness adapts ALPO IdeleGroups/UnitBound; the continuous embedding
   adapts ALPO IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField MeasureTheory IsDedekindDomain
open scoped WithZero RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem finiteCompletion_properSpace (v : NumberField.FinitePlace K) :
    ProperSpace (v.maximalIdeal.adicCompletion K) := by
  obtain ⟨x, hx⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective
    K v.maximalIdeal (WithZero.exp (1 : ℤ))
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  have hn := finite_norm_eq_zpow K v (Units.mk0 x hx0)
  simp only [Units.val_mk0, hx, WithZero.log_exp, zpow_one] at hn
  have hq : (1 : ℝ) < NLocalArithmetic.residueCard K v := by
    change (1 : ℝ) < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
  letI : NontriviallyNormedField (v.maximalIdeal.adicCompletion K) :=
    { (inferInstance : NormedField (v.maximalIdeal.adicCompletion K)) with
      non_trivial := ⟨x, by rw [hn]; exact hq⟩ }
  exact ProperSpace.of_locallyCompactSpace (v.maximalIdeal.adicCompletion K)

/-- The actual finite local log bands are compact, in the original norm. -/
theorem finite_units_logBand_compact (v : NumberField.FinitePlace K) (R : ℝ) :
    IsCompact {u : (v.maximalIdeal.adicCompletion K)ˣ |
      |Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖| ≤ R} := by
  letI := finiteCompletion_properSpace K v
  have hlog {r : ℝ} (hr : 0 < r) :
      |Real.log r| ≤ R ↔ Real.exp (-R) ≤ r ∧ r ≤ Real.exp R := by
    rw [abs_le, neg_le, ← Real.log_inv, Real.log_le_iff_le_exp (inv_pos.2 hr),
      Real.log_le_iff_le_exp hr, inv_le_comm₀ hr (Real.exp_pos _), Real.exp_neg]
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have he : ((↑) : (v.maximalIdeal.adicCompletion K)ˣ → v.maximalIdeal.adicCompletion K) ''
      {u : (v.maximalIdeal.adicCompletion K)ˣ |
        |Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖| ≤ R} =
      {c : v.maximalIdeal.adicCompletion K |
        Real.exp (-R) ≤ ‖c‖ ∧ ‖c‖ ≤ Real.exp R} := by
    ext c
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hlog (norm_pos_iff.2 u.ne_zero)).1 hu
    · rintro ⟨h1, h2⟩
      have hc : c ≠ 0 := norm_pos_iff.1 ((Real.exp_pos _).trans_le h1)
      exact ⟨Units.mk0 c hc, (hlog (norm_pos_iff.2 hc)).2 ⟨h1, h2⟩, rfl⟩
  rw [he]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · exact (Metric.isBounded_closedBall (x := (0 : v.maximalIdeal.adicCompletion K))
      (r := Real.exp R)).subset fun c hc => by simpa using hc.2

theorem continuous_finiteAdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (NLocalArithmetic.finiteAdeleSingle K v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 K))) := by simp
  let g : v.adicCompletion K → Πʳ w : HeightOneSpectrum (𝓞 K),
      [w.adicCompletion K, w.adicCompletionIntegers K]_[Filter.principal {v}ᶜ] :=
    fun x => ⟨Pi.mulSingle v x, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.mulSingle_eq_of_ne hw x]
      exact one_mem _⟩
  have hg : Continuous g :=
    RestrictedProduct.continuous_rng_of_principal.mpr (continuous_mulSingle v)
  have he : (NLocalArithmetic.finiteAdeleSingle K v :
      v.adicCompletion K → FiniteAdeleRing (𝓞 K) K) =
      RestrictedProduct.inclusion _ _ hS ∘ g := rfl
  rw [he]
  exact (RestrictedProduct.continuous_inclusion hS).comp hg

theorem continuous_finiteClass (v : NumberField.FinitePlace K) :
    Continuous (NLocalArithmetic.finiteClass K v) := by
  have he : Continuous (NLocalArithmetic.finiteEmbedding K v) :=
    Units.continuous_map (continuous_const.prodMk
      (continuous_finiteAdeleSingle K v.maximalIdeal))
  exact QuotientGroup.continuous_mk.comp he

/-- A compact test on the actual idele-class quotient pulls back to a compact
finite-local test. Compactness of the local log band is proved above. -/
theorem finiteClass_test_hasCompactSupport
    (v : NumberField.FinitePlace K) (h : HeckeIdeleClasses K → ℂ)
    (hc : HasCompactSupport h) :
    HasCompactSupport (fun u => h (NLocalArithmetic.finiteClass K v u)) := by
  obtain ⟨R, _, hR⟩ := compact_log_support_bound K h hc
  apply (finite_units_logBand_compact K v R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal
  · intro u hu
    have hb := hR (NLocalArithmetic.finiteClass K v u) hu
    rwa [NLocalArithmetic.finiteClass_log] at hb
  · exact isClosed_le
      (Units.continuous_val.norm.log (fun u => norm_ne_zero_iff.2 u.ne_zero)).abs
      continuous_const

/-- The ordinary finite-local integral is absolutely admitted for each of
BOTH manuscript tests. No local convergence hypothesis is inserted. -/
theorem both_tests_finiteLocalDensity_integrable
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (q : Fin 2) (v : NumberField.FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    [BorelSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (nu : Measure (v.maximalIdeal.adicCompletion K)ˣ) [IsFiniteMeasureOnCompacts nu] :
    Integrable (NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q)) nu := by
  have ht := LIntegrated.requiredTest_compact K phi hh hc q
  have hp := (ht.1.comp (continuous_finiteClass K v)).integrable_of_hasCompactSupport
    (finiteClass_test_hasCompactSupport K v _ ht.2) (μ := nu)
  have hm : Measurable
      (NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q)) := by
    unfold NLocalArithmetic.finiteLocalDensity
    exact ((ht.1.comp (continuous_finiteClass K v)).measurable.mul
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        Units.continuous_val.norm)).measurable).div
      (Complex.continuous_ofReal.comp (continuous_const.sub Units.continuous_val).norm).measurable
  exact hp.norm.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => both_tests_finiteLocalDensity_norm_le K phi hphi q v u)

end
end ReviewI.LocalArithmetic

/- Insert after IFiniteLocalIntegrableFragment. This proves the actual
   log(q_v)/mu_v(O_v^units) normalization is positive and finite. -/
namespace ReviewI.LocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem finiteUnitGroup_isCompact (v : NumberField.FinitePlace K) :
    IsCompact (NLocalArithmetic.finiteUnitGroup K v) := by
  have he : NLocalArithmetic.finiteUnitGroup K v =
      {u : (v.maximalIdeal.adicCompletion K)ˣ |
        |Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖| ≤ 0} := by
    ext u
    constructor
    · intro hu
      change |Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖| ≤ 0
      rw [show ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1 from hu,
        Real.log_one, abs_zero]
    · intro hu
      have hz : Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖ = 0 :=
        abs_nonpos_iff.mp hu
      change ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1
      have hh := congrArg Real.exp hz
      rwa [Real.exp_log (norm_pos_iff.2 u.ne_zero), Real.exp_zero] at hh
  rw [he]
  exact finite_units_logBand_compact K v 0

theorem finiteLocalCoefficient_pos (v : NumberField.FinitePlace K)
    [MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    [BorelSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (nu : Measure (v.maximalIdeal.adicCompletion K)ˣ) [nu.IsHaarMeasure] :
    0 < NLocalArithmetic.finiteLocalCoefficient K v nu := by
  let U : Set (v.maximalIdeal.adicCompletion K)ˣ :=
    {u | ‖1 - (u : v.maximalIdeal.adicCompletion K)‖ < 1}
  have ho : IsOpen U := isOpen_lt
    (continuous_const.sub Units.continuous_val).norm continuous_const
  have hne : U.Nonempty := ⟨1, by simp [U]⟩
  have hsub : U ⊆ NLocalArithmetic.finiteUnitGroup K v := by
    intro u hu
    change ‖(u : v.maximalIdeal.adicCompletion K)‖ = 1
    by_cases hz : 1 - (u : v.maximalIdeal.adicCompletion K) = 0
    · rw [← sub_eq_zero.mp hz, norm_one]
    · have hh := finite_norm_one_sub_of_lt K v
        (Units.mk0 (1 - (u : v.maximalIdeal.adicCompletion K)) hz) hu
      have he : (1 : v.maximalIdeal.adicCompletion K) -
          (1 - (u : v.maximalIdeal.adicCompletion K)) = u := by ring
      simpa only [Units.val_mk0, he] using hh
  have hp : 0 < nu (NLocalArithmetic.finiteUnitGroup K v) :=
    (ho.measure_pos nu hne).trans_le (measure_mono hsub)
  have ht : nu (NLocalArithmetic.finiteUnitGroup K v) < ⊤ :=
    (finiteUnitGroup_isCompact K v).measure_lt_top
  have hv : 0 < nu.real (NLocalArithmetic.finiteUnitGroup K v) :=
    ENNReal.toReal_pos hp.ne' ht.ne
  have hq : (1 : ℝ) < NLocalArithmetic.residueCard K v := by
    change (1 : ℝ) < (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)
    exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.maximalIdeal
  exact div_pos (Real.log_pos hq) hv

/-- One finite S works for both tests; every local density is absolutely
integrable, every coefficient is positive, and the full finite-place sum is
absolutely summable with its exact finite-S value. -/
theorem both_tests_finite_local_admission
    [∀ v : NumberField.FinitePlace K, MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    [∀ v : NumberField.FinitePlace K, BorelSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (nu : (v : NumberField.FinitePlace K) → Measure (v.maximalIdeal.adicCompletion K)ˣ)
    [∀ v, (nu v).IsHaarMeasure]
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) :
    ∃ S : Finset (NumberField.FinitePlace K), ∀ q : Fin 2,
      (∀ v : NumberField.FinitePlace K,
        0 < NLocalArithmetic.finiteLocalCoefficient K v (nu v) ∧
        Integrable (NLocalArithmetic.finiteLocalDensity K v (LIntegrated.requiredTest K phi q)) (nu v)) ∧
      HasSum (fun v => NLocalArithmetic.finiteLocalTerm K v (nu v) (LIntegrated.requiredTest K phi q))
        (∑ v ∈ S, NLocalArithmetic.finiteLocalTerm K v (nu v) (LIntegrated.requiredTest K phi q)) ∧
      Summable (fun v => ‖NLocalArithmetic.finiteLocalTerm K v (nu v)
        (LIntegrated.requiredTest K phi q)‖) := by
  obtain ⟨S, hS⟩ := both_tests_finite_local_support K phi hh hc hphi
  refine ⟨S, fun q => ⟨?_, ?_, ?_⟩⟩
  · intro v
    exact ⟨finiteLocalCoefficient_pos K v (nu v),
      both_tests_finiteLocalDensity_integrable K phi hh hc hphi q v (nu v)⟩
  · exact hasSum_sum_of_ne_finset_zero fun v hv => (hS v hv q).2 _ (nu v)
  · exact summable_of_ne_finset_zero fun v hv => by
      rw [(hS v hv q).2 _ (nu v), norm_zero]

end
end ReviewI.LocalArithmetic
#check ReviewI.LocalArithmetic.both_tests_finite_local_admission
#print axioms ReviewI.LocalArithmetic.both_tests_finite_local_admission
