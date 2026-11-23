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
#print axioms ReviewI.LocalArithmetic.both_tests_finite_local_lattice
#print axioms ReviewI.LocalArithmetic.both_tests_finite_local_unit_zero
/- Insert after NLocalArithmeticFragment. Actual archimedean embeddings and
the complete local endpoint, with the normalized complex modulus (norm squared).
This does not assert the unproved global operator-to-local equality. -/
namespace NLocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField MeasureTheory
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

open Classical in
def infiniteAdeleSingle (w : InfinitePlace K) : w.Completion →* InfiniteAdeleRing K :=
  MonoidHom.mulSingle (fun u : InfinitePlace K => u.Completion) w

def infiniteEmbedding (w : InfinitePlace K) : w.Completionˣ →* HeckeIdeles K :=
  Units.map (MonoidHom.prod (infiniteAdeleSingle K w) 1)

def infiniteClass (w : InfinitePlace K) : w.Completionˣ →* HeckeIdeleClasses K :=
  (QuotientGroup.mk' (principalIdeles K)).comp (infiniteEmbedding K w)

theorem infiniteEmbedding_modulus (w : InfinitePlace K) (u : w.Completionˣ) :
    genuineIdeleModulus K (infiniteEmbedding K w u) = ‖(u : w.Completion)‖ ^ w.mult := by
  classical
  unfold genuineIdeleModulus
  have hf : (∏ᶠ v : FinitePlace K,
      ‖(infiniteEmbedding K w u).val.2 v.maximalIdeal‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => norm_one
  rw [hf, mul_one]
  refine (Fintype.prod_eq_single w fun v hv => ?_).trans ?_
  · change ‖Pi.mulSingle w (u : w.Completion) v‖ ^ v.mult = 1
    rw [Pi.mulSingle_eq_of_ne hv, norm_one, one_pow]
  · change ‖Pi.mulSingle w (u : w.Completion) w‖ ^ w.mult = _
    rw [Pi.mulSingle_eq_same]

theorem infiniteClass_log (w : InfinitePlace K) (u : w.Completionˣ) :
    classLog K (infiniteClass K w u) = Real.log (‖(u : w.Completion)‖ ^ w.mult) := by
  change Real.log (genuineIdeleModulus K (infiniteEmbedding K w u)) = _
  rw [infiniteEmbedding_modulus]

def infiniteLocalCoefficient (w : InfinitePlace K) : ℝ :=
  if w.IsReal then 1/2 else 1/(2*Real.pi)

omit [NumberField K] in
theorem infiniteLocalCoefficient_real (w : InfinitePlace K) (hw : w.IsReal) :
    infiniteLocalCoefficient K w = 1/2 := by simp [infiniteLocalCoefficient, hw]

omit [NumberField K] in
theorem infiniteLocalCoefficient_complex (w : InfinitePlace K) (hw : ¬w.IsReal) :
    infiniteLocalCoefficient K w = 1/(2*Real.pi) := by simp [infiniteLocalCoefficient, hw]

/-- The normalized local absolute value has exponent mult=2 at complex places,
as specified in the manuscript's conventions and Appendix B.4.4.16. -/
def infiniteLocalDensity (w : InfinitePlace K) (h : HeckeIdeleClasses K → ℂ)
    (u : w.Completionˣ) : ℂ :=
  h (infiniteClass K w u) * (Real.sqrt (‖(u : w.Completion)‖ ^ w.mult) : ℂ) /
    (‖1 - (u : w.Completion)‖ ^ w.mult : ℝ)

def infiniteLocalTerm (w : InfinitePlace K) [MeasurableSpace w.Completionˣ]
    (mu : Measure w.Completionˣ) (h : HeckeIdeleClasses K → ℂ) : ℂ :=
  (infiniteLocalCoefficient K w : ℂ) * ∫ u, infiniteLocalDensity K w h u ∂mu

theorem infiniteLocalDensity_unit_zero (w : InfinitePlace K)
    (h : HeckeIdeleClasses K → ℂ)
    (hh : ∀ x, classLog K x = 0 → h x = 0)
    (u : w.Completionˣ) (hu : ‖(u : w.Completion)‖ = 1) :
    infiniteLocalDensity K w h u = 0 := by
  have he : classLog K (infiniteClass K w u) = 0 := by
    rw [infiniteClass_log, hu, one_pow, Real.log_one]
  simp only [infiniteLocalDensity, hh _ he, zero_mul, zero_div]

/-- The actual local endpoint of 12.5.1.1, with each original local Haar
retained. Convergence/principal-value and trace identification are separate proofs. -/
def localExpression
    [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
    [∀ v : FinitePlace K, MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (muInf : (w : InfinitePlace K) → Measure w.Completionˣ)
    (muFin : (v : FinitePlace K) → Measure (v.maximalIdeal.adicCompletion K)ˣ)
    (h : HeckeIdeleClasses K → ℂ) : ℂ :=
  (∑ w : InfinitePlace K, infiniteLocalTerm K w (muInf w) h) +
    ∑' v : FinitePlace K, finiteLocalTerm K v (muFin v) h

/-- The finite-S endpoint used before the outside-S vanishing application. -/
def semilocalExpression
    [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
    [∀ v : FinitePlace K, MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (muInf : (w : InfinitePlace K) → Measure w.Completionˣ)
    (muFin : (v : FinitePlace K) → Measure (v.maximalIdeal.adicCompletion K)ˣ)
    (S : Finset (FinitePlace K)) (h : HeckeIdeleClasses K → ℂ) : ℂ :=
  (∑ w : InfinitePlace K, infiniteLocalTerm K w (muInf w) h) +
    ∑ v ∈ S, finiteLocalTerm K v (muFin v) h

theorem localExpression_eq_semilocal
    [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
    [∀ v : FinitePlace K, MeasurableSpace (v.maximalIdeal.adicCompletion K)ˣ]
    (muInf : (w : InfinitePlace K) → Measure w.Completionˣ)
    (muFin : (v : FinitePlace K) → Measure (v.maximalIdeal.adicCompletion K)ˣ)
    (S : Finset (FinitePlace K)) (h : HeckeIdeleClasses K → ℂ)
    (hz : ∀ v ∉ S, finiteLocalTerm K v (muFin v) h = 0) :
    localExpression K muInf muFin h = semilocalExpression K muInf muFin S h := by
  unfold localExpression semilocalExpression
  rw [tsum_eq_sum hz]

end
end NLocalArithmetic
#check NLocalArithmetic.localExpression
#print axioms NLocalArithmetic.infiniteClass_log
#print axioms NLocalArithmetic.infiniteLocalDensity_unit_zero
#print axioms NLocalArithmetic.localExpression_eq_semilocal
/- Insert after NArchimedeanLocalFragment and LIntegrated.requiredTest. -/
namespace NLocalArithmetic
open MasulloGRH Masullo.IdeleClassGeometry NumberField
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem finiteLocalDensity_log_test (phi : HeckeIdeleClasses K → ℂ)
    (v : FinitePlace K) (u : (v.maximalIdeal.adicCompletion K)ˣ) :
    finiteLocalDensity K v (LIntegrated.requiredTest K phi 1) u =
      -(Real.log ‖(u : v.maximalIdeal.adicCompletion K)‖ : ℂ) *
        finiteLocalDensity K v (LIntegrated.requiredTest K phi 0) u := by
  simp only [finiteLocalDensity, LIntegrated.requiredTest_log_sign, finiteClass_log]
  ring

theorem infiniteLocalDensity_log_test (phi : HeckeIdeleClasses K → ℂ)
    (w : InfinitePlace K) (u : w.Completionˣ) :
    infiniteLocalDensity K w (LIntegrated.requiredTest K phi 1) u =
      -(Real.log (‖(u : w.Completion)‖ ^ w.mult) : ℂ) *
        infiniteLocalDensity K w (LIntegrated.requiredTest K phi 0) u := by
  simp only [infiniteLocalDensity, LIntegrated.requiredTest_log_sign, infiniteClass_log]
  ring

theorem both_tests_local_unit_zero (phi : HeckeIdeleClasses K → ℂ)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0) (q : Fin 2) :
    (∀ (v : FinitePlace K) (u : (v.maximalIdeal.adicCompletion K)ˣ),
      u ∈ finiteUnitGroup K v →
        finiteLocalDensity K v (LIntegrated.requiredTest K phi q) u = 0) ∧
    (∀ (w : InfinitePlace K) (u : w.Completionˣ), ‖(u : w.Completion)‖ = 1 →
      infiniteLocalDensity K w (LIntegrated.requiredTest K phi q) u = 0) := by
  have hh := LIntegrated.requiredTest_vanishes_normOne K phi hphi q
  exact ⟨fun v u hu => finiteLocalDensity_unit_zero K v _ hh u hu,
    fun w u hu => infiniteLocalDensity_unit_zero K w _ hh u hu⟩

end
end NLocalArithmetic
#check NLocalArithmetic.both_tests_local_unit_zero
#print axioms NLocalArithmetic.both_tests_local_unit_zero
#print axioms NLocalArithmetic.infiniteLocalDensity_log_test
#print axioms NLocalArithmetic.finiteLocalDensity_log_test
