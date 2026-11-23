import Mathlib
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
open MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass
variable (K : Type*) [Field K] [NumberField K]
theorem classLog_inv (x : HeckeIdeleClasses K) : classLog K x⁻¹ = -classLog K x := by
  have h1 := classLog_mul K (1 : HeckeIdeleClasses K) 1
  simp only [one_mul] at h1
  have hz : classLog K 1 = 0 := by linarith
  have hi := classLog_mul K x x⁻¹
  rw [mul_inv_cancel, hz] at hi
  linarith

end DReview
/-! F: the actual two-parameter physical regime, beyond a chosen sequence.
Insert after FIntervalPhysical, HSourceTraceFragment, and DResidualKernelFragment. -/
namespace FPhysicalFilter
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology
noncomputable section

/-- Coordinates are (Lambda, delta), with delta = epsilon * Lambda.
The product filter is nontrivial and permits independent rates of approach. -/
def cutoffRegime : Filter (ℝ × ℝ) :=
  (atTop : Filter ℝ) ×ˢ (𝓝[>] (0 : ℝ))

instance cutoffRegime_countablyGenerated : cutoffRegime.IsCountablyGenerated := by
  unfold cutoffRegime
  infer_instance

instance cutoffRegime_neBot : cutoffRegime.NeBot := by
  unfold cutoffRegime
  infer_instance

theorem cutoffRegime_Lambda : Tendsto (fun p : ℝ × ℝ => p.1) cutoffRegime atTop :=
  tendsto_fst

/-- In these coordinates epsilon = delta / Lambda, so the manuscript's
product condition follows without tying the two parameters to a sequence. -/
theorem cutoffRegime_product :
    Tendsto (fun p : ℝ × ℝ => (p.2 / p.1) * p.1) cutoffRegime (𝓝 (0 : ℝ)) := by
  have hd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝 (0 : ℝ)) :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝[>] (0 : ℝ))).mono_right
      nhdsWithin_le_nhds
  apply hd.congr'
  filter_upwards [cutoffRegime_Lambda.eventually (eventually_gt_atTop (0 : ℝ))]
    with p hp
  simp [ne_of_gt hp]

/-- The scalar parameter restrictions from manuscript Definition 9.3.3.1. -/
def ValidCutoff (L e : ℝ) : Prop :=
  0 < L ∧ 0 < e ∧ 0 < L⁻¹-e ∧ L⁻¹-e < L-e

theorem cutoffRegime_admissible :
    ∀ᶠ p : ℝ × ℝ in cutoffRegime, ValidCutoff p.1 (p.2/p.1) := by
  have hd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝 (0 : ℝ)) :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝[>] (0 : ℝ))).mono_right
      nhdsWithin_le_nhds
  have hdpos : ∀ᶠ p : ℝ × ℝ in cutoffRegime, 0 < p.2 :=
    (tendsto_snd : Tendsto (fun p : ℝ × ℝ => p.2) cutoffRegime (𝓝[>] (0 : ℝ))).eventually
      self_mem_nhdsWithin
  filter_upwards [cutoffRegime_Lambda.eventually (eventually_gt_atTop (1 : ℝ)),
    hdpos, hd.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with p hL hd0 hd1
  have hL0 : 0 < p.1 := lt_trans zero_lt_one hL
  have he : p.2/p.1 < p.1⁻¹ := by
    rw [div_lt_iff₀ hL0, inv_mul_cancel₀ (ne_of_gt hL0)]
    exact hd1
  have hi : p.1⁻¹ < p.1 := by
    rw [← one_div, div_lt_iff₀ hL0]
    nlinarith
  exact ⟨hL0, div_pos hd0 hL0, sub_pos.mpr he, sub_lt_sub_right hi _⟩

theorem epsilon_tendsto_zero {ι : Type*} (f : Filter ι) (Lambda epsilon : ι → ℝ)
    (hLambda : Tendsto Lambda f atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) f (𝓝 0)) :
    Tendsto epsilon f (𝓝 0) := by
  have hi : Tendsto (fun n => (Lambda n)⁻¹) f (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hLambda
  have hp := hprod.mul hi
  simp only [mul_zero] at hp
  apply hp.congr'
  filter_upwards [hLambda.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
  field_simp [ne_of_gt hn]

theorem plateau_eventually {ι : Type*} (f : Filter ι) (Lambda epsilon : ι → ℝ)
    (hLambda : Tendsto Lambda f atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) f (𝓝 0))
    (t : ℝ) (ht : 0 < t) :
    ∀ᶠ n in f, (Lambda n)⁻¹ + epsilon n ≤ t ∧ t ≤ Lambda n - epsilon n := by
  have he := epsilon_tendsto_zero f Lambda epsilon hLambda hprod
  have hi : Tendsto (fun n => (Lambda n)⁻¹) f (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hLambda
  have hlo : Tendsto (fun n => (Lambda n)⁻¹ + epsilon n) f (𝓝 (0 : ℝ)) := by
    simpa using hi.add he
  filter_upwards [hlo.eventually (gt_mem_nhds ht),
    he.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hLambda.eventually (eventually_ge_atTop (t+1))] with n hn heps hL
  exact ⟨le_of_lt hn, by linarith⟩

variable (K : Type*) [Field K] [NumberField K]

/-- The filter form of the manuscript's dominated physical passage. The
integrability premise is discharged for the actual source kernel below. -/
theorem manuscript_integral_limit {ι : Type*} (f : Filter ι) [f.IsCountablyGenerated]
    (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu)
    (Lambda epsilon : ι → ℝ) (hLambda : Tendsto Lambda f atTop)
    (hprod : Tendsto (fun n => epsilon n * Lambda n) f (𝓝 0))
    (omega : ι → HeckeIdeleClasses K → ℂ)
    (hm : ∀ᶠ n in f, AEStronglyMeasurable (omega n) mu)
    (hb : ∀ᶠ n in f, ∀ x, ‖omega n x‖ ≤ 1)
    (hp : ∀ᶠ n in f, ∀ x, (Lambda n)⁻¹ + epsilon n ≤ Real.exp (classLog K x) →
      Real.exp (classLog K x) ≤ Lambda n - epsilon n → omega n x = 1) :
    Tendsto (fun n => ∫ x, omega n x * d x ∂mu) f (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖d x‖)
  · exact hm.mono (fun n hn => hn.mul hd.aestronglyMeasurable)
  · exact hb.mono (fun n hn => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hn x)))
  · exact hd.norm
  · exact Eventually.of_forall (fun x => by
      have hx : Tendsto (fun n => omega n x) f (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hp, plateau_eventually f Lambda epsilon hLambda hprod
          (Real.exp (classLog K x)) (Real.exp_pos _)] with n hpn hn
        exact (hpn x hn.1 hn.2).symm
      simpa only [one_mul] using hx.mul (tendsto_const_nhds (x := d x)))


end
end FPhysicalFilter

/-! F continuation: an explicit inversion-symmetric smooth radial cutoff.
Insert after FPhysicalFilter. The scalar construction uses the same smooth
transition argument as Masullo/Analysis/TestFunctions and ALPO ExphOn.shortCut.
No source, kernel, measure, or projection is redefined. -/
namespace FSmoothCutoff
open Set
open scoped ContDiff
noncomputable section

def stepBand (L e t : ℝ) : ℝ :=
  Real.smoothTransition ((Real.exp t - L⁻¹) / e) *
    Real.smoothTransition ((L - Real.exp t) / e)

/-- Smooth union with the inverse image preserves the plateau exactly and
enforces the manuscript's multiplicative symmetry. -/
def logCutoff (L e t : ℝ) : ℝ :=
  1 - (1 - stepBand L e t) * (1 - stepBand L e (-t))

theorem stepBand_bounds (L e t : ℝ) :
    0 ≤ stepBand L e t ∧ stepBand L e t ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem logCutoff_bounds (L e t : ℝ) :
    0 ≤ logCutoff L e t ∧ logCutoff L e t ≤ 1 := by
  obtain ⟨ha0, ha1⟩ := stepBand_bounds L e t
  obtain ⟨hb0, hb1⟩ := stepBand_bounds L e (-t)
  have hp0 : 0 ≤ (1 - stepBand L e t) * (1 - stepBand L e (-t)) :=
    mul_nonneg (by linarith) (by linarith)
  have hp1 : (1 - stepBand L e t) * (1 - stepBand L e (-t)) ≤ 1 :=
    mul_le_one₀ (by linarith) (by linarith) (by linarith)
  unfold logCutoff
  constructor <;> linarith

theorem logCutoff_neg (L e t : ℝ) : logCutoff L e (-t) = logCutoff L e t := by
  simp only [logCutoff, neg_neg]
  ring

theorem stepBand_smooth (L e : ℝ) : ContDiff ℝ ∞ (stepBand L e) := by
  exact (Real.smoothTransition.contDiff.comp
    ((Real.contDiff_exp.sub contDiff_const).div_const e)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub Real.contDiff_exp).div_const e))

theorem logCutoff_smooth (L e : ℝ) : ContDiff ℝ ∞ (logCutoff L e) := by
  exact contDiff_const.sub ((contDiff_const.sub (stepBand_smooth L e)).mul
    (contDiff_const.sub ((stepBand_smooth L e).comp contDiff_id.neg)))

theorem stepBand_eq_one (L e t : ℝ) (he : 0 < e)
    (hl : L⁻¹ + e ≤ Real.exp t) (hr : Real.exp t ≤ L - e) :
    stepBand L e t = 1 := by
  unfold stepBand
  rw [Real.smoothTransition.one_of_one_le ((one_le_div he).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div he).2 (by linarith))]
  exact one_mul 1

theorem logCutoff_eq_one (L e t : ℝ) (he : 0 < e)
    (hl : L⁻¹ + e ≤ Real.exp t) (hr : Real.exp t ≤ L - e) :
    logCutoff L e t = 1 := by
  simp [logCutoff, stepBand_eq_one L e t he hl hr]

theorem stepBand_zero_of_le (L e t : ℝ) (he : 0 < e)
    (ht : Real.exp t ≤ L⁻¹) : stepBand L e t = 0 := by
  unfold stepBand
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) he.le), zero_mul]

theorem stepBand_zero_of_ge (L e t : ℝ) (he : 0 < e)
    (ht : L ≤ Real.exp t) : stepBand L e t = 0 := by
  unfold stepBand
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) he.le), mul_zero]

theorem logCutoff_zero_of_ge (L e t : ℝ) (hL : 0 < L) (he : 0 < e)
    (ht : Real.log L ≤ t) : logCutoff L e t = 0 := by
  have hp : L ≤ Real.exp t := by
    simpa only [Real.exp_log hL] using Real.exp_le_exp.mpr ht
  have hn : Real.exp (-t) ≤ L⁻¹ := by
    calc
      Real.exp (-t) ≤ Real.exp (-Real.log L) := Real.exp_le_exp.mpr (neg_le_neg ht)
      _ = L⁻¹ := by rw [Real.exp_neg, Real.exp_log hL]
  simp [logCutoff, stepBand_zero_of_ge L e t he hp,
    stepBand_zero_of_le L e (-t) he hn]

theorem logCutoff_zero_of_le (L e t : ℝ) (hL : 0 < L) (he : 0 < e)
    (ht : t ≤ -Real.log L) : logCutoff L e t = 0 := by
  rw [← logCutoff_neg]
  exact logCutoff_zero_of_ge L e (-t) hL he (by linarith)

theorem logCutoff_support (L e : ℝ) (hL : 0 < L) (he : 0 < e) :
    Function.support (logCutoff L e) ⊆ Icc (-Real.log L) (Real.log L) := by
  intro t ht
  constructor
  · by_contra h
    exact ht (logCutoff_zero_of_le L e t hL he (le_of_not_ge h))
  · by_contra h
    exact ht (logCutoff_zero_of_ge L e t hL he (le_of_not_ge h))

theorem logCutoff_compact (L e : ℝ) (hL : 0 < L) (he : 0 < e) :
    HasCompactSupport (logCutoff L e) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact closure_minimal (logCutoff_support L e hL he) isClosed_Icc

end
end FSmoothCutoff


/-! F: attach the explicit scalar cutoff to the manuscript's class norm.
Insert after FSmoothCutoff, FPhysicalFilter, and DReview.classLog_inv. -/
namespace FSmoothCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def realMask (L e : ℝ) (x : HeckeIdeleClasses K) : ℝ :=
  logCutoff L e (classLog K x)

def mask (L e : ℝ) (x : HeckeIdeleClasses K) : ℂ :=
  (realMask K L e x : ℂ)

theorem realMask_bounds (L e : ℝ) (x : HeckeIdeleClasses K) :
    0 ≤ realMask K L e x ∧ realMask K L e x ≤ 1 :=
  logCutoff_bounds L e (classLog K x)

theorem realMask_continuous (L e : ℝ) : Continuous (realMask K L e) :=
  (logCutoff_smooth L e).continuous.comp (classLog_continuous K)

theorem mask_continuous (L e : ℝ) : Continuous (mask K L e) :=
  Complex.continuous_ofReal.comp (realMask_continuous K L e)

theorem mask_measurable (mu : Measure (HeckeIdeleClasses K)) (L e : ℝ) :
    AEStronglyMeasurable (mask K L e) mu :=
  (mask_continuous K L e).measurable.aestronglyMeasurable

theorem mask_norm_le (L e : ℝ) (x : HeckeIdeleClasses K) :
    ‖mask K L e x‖ ≤ 1 := by
  simp only [mask, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realMask_bounds K L e x).1]
  exact (realMask_bounds K L e x).2

theorem realMask_inv (L e : ℝ) (x : HeckeIdeleClasses K) :
    realMask K L e x⁻¹ = realMask K L e x := by
  simp only [realMask, DReview.classLog_inv, logCutoff_neg]

theorem mask_inv (L e : ℝ) (x : HeckeIdeleClasses K) :
    mask K L e x⁻¹ = mask K L e x := by
  rw [mask, mask, realMask_inv]

theorem mask_plateau (L e : ℝ) (hv : FPhysicalFilter.ValidCutoff L e)
    (x : HeckeIdeleClasses K)
    (hl : L⁻¹ + e ≤ Real.exp (classLog K x))
    (hr : Real.exp (classLog K x) ≤ L - e) : mask K L e x = 1 := by
  simp only [mask, realMask, logCutoff_eq_one L e (classLog K x) hv.2.1 hl hr,
    Complex.ofReal_one]

theorem mask_support (L e : ℝ) (hv : FPhysicalFilter.ValidCutoff L e) :
    Function.support (mask K L e) ⊆
      {x | L⁻¹ ≤ Real.exp (classLog K x) ∧ Real.exp (classLog K x) ≤ L} := by
  intro x hx
  have hx' : logCutoff L e (classLog K x) ≠ 0 := by
    intro hz
    exact hx (by simp [mask, realMask, hz])
  obtain ⟨hl, hr⟩ := logCutoff_support L e hv.1 hv.2.1 hx'
  constructor
  · have h := Real.exp_le_exp.mpr hl
    simpa only [Real.exp_neg, Real.exp_log hv.1] using h
  · have h := Real.exp_le_exp.mpr hr
    simpa only [Real.exp_log hv.1] using h

/-- Every fixed class eventually lies on the plateau in the actual independent
two-parameter regime, including the identity where the mask attains norm one. -/
theorem mask_eventually_one (x : HeckeIdeleClasses K) :
    ∀ᶠ p : ℝ × ℝ in FPhysicalFilter.cutoffRegime,
      mask K p.1 (p.2 / p.1) x = 1 := by
  filter_upwards [FPhysicalFilter.cutoffRegime_admissible,
    FPhysicalFilter.plateau_eventually FPhysicalFilter.cutoffRegime
      (fun p : ℝ × ℝ => p.1) (fun p : ℝ × ℝ => p.2 / p.1)
      FPhysicalFilter.cutoffRegime_Lambda FPhysicalFilter.cutoffRegime_product
      (Real.exp (classLog K x)) (Real.exp_pos _)] with p hp hx
  exact mask_plateau K p.1 (p.2 / p.1) hp x hx.1 hx.2

/-- All cutoff hypotheses of the original-Haar dominated passage are now
proved for the explicit radial family. Integrability remains the supplied
diagonal theorem's obligation. -/
theorem integral_limit (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun p : ℝ × ℝ => ∫ x, mask K p.1 (p.2 / p.1) x * d x ∂mu)
      FPhysicalFilter.cutoffRegime (𝓝 (∫ x, d x ∂mu)) := by
  exact FPhysicalFilter.manuscript_integral_limit K FPhysicalFilter.cutoffRegime mu d hd
    (fun p : ℝ × ℝ => p.1) (fun p : ℝ × ℝ => p.2 / p.1)
    FPhysicalFilter.cutoffRegime_Lambda FPhysicalFilter.cutoffRegime_product
    (fun p => mask K p.1 (p.2 / p.1))
    (Eventually.of_forall (fun p => mask_measurable K mu p.1 (p.2 / p.1)))
    (Eventually.of_forall (fun p => mask_norm_le K p.1 (p.2 / p.1)))
    (FPhysicalFilter.cutoffRegime_admissible.mono (fun p hp =>
      mask_plateau K p.1 (p.2 / p.1) hp))

end
end FSmoothCutoff


/-! F: convenience properties for K's literal real multiplier.
Insert after FSmoothRadial. K owns the operator specialization. -/
namespace FSmoothCutoff
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem realMask_plateau (L e : ℝ) (hv : FPhysicalFilter.ValidCutoff L e)
    (x : HeckeIdeleClasses K)
    (hl : L⁻¹ + e ≤ Real.exp (classLog K x))
    (hr : Real.exp (classLog K x) ≤ L - e) : realMask K L e x = 1 :=
  logCutoff_eq_one L e (classLog K x) hv.2.1 hl hr

theorem realMask_eventually_one (x : HeckeIdeleClasses K) :
    ∀ᶠ p : ℝ × ℝ in FPhysicalFilter.cutoffRegime,
      realMask K p.1 (p.2 / p.1) x = 1 := by
  simpa only [mask, Complex.ofReal_eq_one] using mask_eventually_one K x

theorem realMask_fibre (L e : ℝ) (x y : HeckeIdeleClasses K)
    (hxy : classLog K x = classLog K y) : realMask K L e x = realMask K L e y := by
  simp only [realMask, hxy]

theorem realMask_normOne_invariant (L e : ℝ) (g x : HeckeIdeleClasses K)
    (hg : classLog K g = 0) : realMask K L e (g*x) = realMask K L e x := by
  apply realMask_fibre
  rw [Masullo.WeightedIdeleClass.classLog_mul, hg, zero_add]

/-- In the eventual admissible regime the uniform bound is attained at the
identity, so it is exactly one, as required by Definition 9.3.3.1. -/
theorem mask_norm_attained :
    ∀ᶠ p : ℝ × ℝ in FPhysicalFilter.cutoffRegime,
      (∀ x, ‖mask K p.1 (p.2/p.1) x‖ ≤ 1) ∧
        ‖mask K p.1 (p.2/p.1) (1 : HeckeIdeleClasses K)‖ = 1 := by
  filter_upwards [mask_eventually_one K (1 : HeckeIdeleClasses K)] with p hp
  exact ⟨mask_norm_le K p.1 (p.2/p.1), by rw [hp, norm_one]⟩

end
end FSmoothCutoff


/-! Insert after FPhysicalFilter. The single smoothing parameter below
satisfies both error regimes of manuscript (12.4.1.28). -/
namespace LCutoffRegime
open Filter
open scoped Topology
noncomputable section

/-- A common smoothing width for independently growing left/right cutoffs. -/
def sharedSmoothing (Lambda Lambda' delta : ℝ) : ℝ := delta / (Lambda+Lambda')

theorem sharedSmoothing_bounds (Lambda Lambda' delta : ℝ)
    (hL : 0 < Lambda) (hL' : 0 < Lambda') (hd : 0 ≤ delta) :
    (0 ≤ sharedSmoothing Lambda Lambda' delta * Lambda ∧
      sharedSmoothing Lambda Lambda' delta * Lambda ≤ delta) ∧
    (0 ≤ sharedSmoothing Lambda Lambda' delta * Lambda' ∧
      sharedSmoothing Lambda Lambda' delta * Lambda' ≤ delta) := by
  have hsum : 0 < Lambda+Lambda' := add_pos hL hL'
  have he : 0 ≤ sharedSmoothing Lambda Lambda' delta := div_nonneg hd hsum.le
  have heq : sharedSmoothing Lambda Lambda' delta * (Lambda+Lambda') = delta := by
    exact div_mul_cancel₀ _ (ne_of_gt hsum)
  constructor
  · refine ⟨mul_nonneg he hL.le, ?_⟩
    calc
      _ ≤ sharedSmoothing Lambda Lambda' delta * (Lambda+Lambda') :=
        mul_le_mul_of_nonneg_left (by linarith) he
      _ = delta := heq
  · refine ⟨mul_nonneg he hL'.le, ?_⟩
    calc
      _ ≤ sharedSmoothing Lambda Lambda' delta * (Lambda+Lambda') :=
        mul_le_mul_of_nonneg_left (by linarith) he
      _ = delta := heq

/-- Both local error conditions hold with one common epsilon and no
comparison between the independent cutoff growth rates. -/
theorem sharedSmoothing_products {ι : Type*} (f : Filter ι)
    (Lambda Lambda' delta : ι → ℝ)
    (hL : Tendsto Lambda f atTop) (hL' : Tendsto Lambda' f atTop)
    (hdnonneg : ∀ᶠ i in f, 0 ≤ delta i) (hd : Tendsto delta f (𝓝 0)) :
    Tendsto (fun i => sharedSmoothing (Lambda i) (Lambda' i) (delta i) * Lambda i)
      f (𝓝 0) ∧
    Tendsto (fun i => sharedSmoothing (Lambda i) (Lambda' i) (delta i) * Lambda' i)
      f (𝓝 0) := by
  have hb := (hL.eventually (eventually_gt_atTop (0 : ℝ))).and
    ((hL'.eventually (eventually_gt_atTop (0 : ℝ))).and hdnonneg)
  have hbound := hb.mono (fun i hi =>
    sharedSmoothing_bounds (Lambda i) (Lambda' i) (delta i) hi.1 hi.2.1 hi.2.2)
  exact ⟨squeeze_zero' (hbound.mono (fun i hi => hi.1.1))
      (hbound.mono (fun i hi => hi.1.2)) hd,
    squeeze_zero' (hbound.mono (fun i hi => hi.2.1))
      (hbound.mono (fun i hi => hi.2.2)) hd⟩

/-- The two cutoffs and their common positive smoothing approach independently. -/
def localRegime : Filter ((ℝ × ℝ) × ℝ) :=
  ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) ×ˢ (𝓝[>] (0 : ℝ))

instance localRegime_neBot : localRegime.NeBot := by
  unfold localRegime
  infer_instance

instance localRegime_countablyGenerated : localRegime.IsCountablyGenerated := by
  unfold localRegime
  infer_instance

theorem localRegime_first :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => p.1.1) localRegime atTop :=
  tendsto_fst.comp tendsto_fst

theorem localRegime_second :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => p.1.2) localRegime atTop :=
  tendsto_snd.comp tendsto_fst

theorem localRegime_delta :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2) localRegime (𝓝 (0 : ℝ)) :=
  (tendsto_snd : Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2) localRegime
    (𝓝[>] (0 : ℝ))).mono_right nhdsWithin_le_nhds

theorem localRegime_delta_pos :
    ∀ᶠ p : (ℝ × ℝ) × ℝ in localRegime, 0 < p.2 :=
  (tendsto_snd : Tendsto (fun p : (ℝ × ℝ) × ℝ => p.2) localRegime
    (𝓝[>] (0 : ℝ))).eventually self_mem_nhdsWithin

/-- Precisely the two o(1) smoothing products printed in (12.4.1.28). -/
theorem localRegime_products :
    Tendsto (fun p : (ℝ × ℝ) × ℝ =>
      sharedSmoothing p.1.1 p.1.2 p.2 * p.1.1) localRegime (𝓝 (0 : ℝ)) ∧
    Tendsto (fun p : (ℝ × ℝ) × ℝ =>
      sharedSmoothing p.1.1 p.1.2 p.2 * p.1.2) localRegime (𝓝 (0 : ℝ)) :=
  sharedSmoothing_products localRegime _ _ _ localRegime_first localRegime_second
    (localRegime_delta_pos.mono (fun _p hp => hp.le)) localRegime_delta

end
end LCutoffRegime

/-! F: the independently supported smooth physical cutoff requested in
footnote 2 to Theorem 12.4.1.1. Insert after FPhysicalFilter and LTwoCutoff.
The independent source radial parameter in the local orbital calculation is
not identified with either physical endpoint. L retains the max-log term. -/
namespace FAsymmetricCutoff
open Set Filter MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open scoped Topology ContDiff
noncomputable section

/-- Upper physical cutoff U, reciprocal lower physical cutoff D, and a
common positive smoothing width. This family has no symmetry constraint. -/
def logCutoff (U D e t : ℝ) : ℝ :=
  Real.smoothTransition ((Real.exp t - D⁻¹) / e) *
    Real.smoothTransition ((U - Real.exp t) / e)

theorem logCutoff_bounds (U D e t : ℝ) :
    0 ≤ logCutoff U D e t ∧ logCutoff U D e t ≤ 1 := by
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
    mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)⟩

theorem logCutoff_smooth (U D e : ℝ) : ContDiff ℝ ∞ (logCutoff U D e) :=
  (Real.smoothTransition.contDiff.comp
    ((Real.contDiff_exp.sub contDiff_const).div_const e)).mul
    (Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub Real.contDiff_exp).div_const e))

theorem logCutoff_plateau (U D e t : ℝ) (he : 0 < e)
    (hl : D⁻¹+e ≤ Real.exp t) (hr : Real.exp t ≤ U-e) :
    logCutoff U D e t = 1 := by
  unfold logCutoff
  rw [Real.smoothTransition.one_of_one_le ((one_le_div he).2 (by linarith)),
    Real.smoothTransition.one_of_one_le ((one_le_div he).2 (by linarith)), one_mul]

theorem logCutoff_zero_lower (U D e t : ℝ) (he : 0 < e)
    (hl : Real.exp t ≤ D⁻¹) : logCutoff U D e t = 0 := by
  unfold logCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hl) he.le), zero_mul]

theorem logCutoff_zero_upper (U D e t : ℝ) (he : 0 < e)
    (hr : U ≤ Real.exp t) : logCutoff U D e t = 0 := by
  unfold logCutoff
  rw [Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) he.le), mul_zero]

theorem logCutoff_support (U D e : ℝ) (hU : 0 < U) (hD : 0 < D) (he : 0 < e) :
    Function.support (logCutoff U D e) ⊆ Icc (-Real.log D) (Real.log U) := by
  intro t ht
  constructor
  · by_contra h
    have hb : Real.exp t ≤ D⁻¹ := by
      have h' := Real.exp_le_exp.mpr (le_of_not_ge h)
      simpa only [Real.exp_neg, Real.exp_log hD] using h'
    exact ht (logCutoff_zero_lower U D e t he hb)
  · by_contra h
    have hb : U ≤ Real.exp t := by
      have h' := Real.exp_le_exp.mpr (le_of_not_ge h)
      simpa only [Real.exp_log hU] using h'
    exact ht (logCutoff_zero_upper U D e t he hb)

theorem logCutoff_compact (U D e : ℝ) (hU : 0 < U) (hD : 0 < D) (he : 0 < e) :
    HasCompactSupport (logCutoff U D e) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact closure_minimal (logCutoff_support U D e hU hD he) isClosed_Icc

theorem plateau_eventually {ι : Type*} (f : Filter ι) (U D e : ι → ℝ)
    (hU : Tendsto U f atTop) (hD : Tendsto D f atTop) (he : Tendsto e f (𝓝 0))
    (t : ℝ) (ht : 0 < t) :
    ∀ᶠ i in f, (D i)⁻¹+e i ≤ t ∧ t ≤ U i-e i := by
  have hd : Tendsto (fun i => (D i)⁻¹) f (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hD
  have hlo : Tendsto (fun i => (D i)⁻¹+e i) f (𝓝 (0 : ℝ)) := by
    simpa using hd.add he
  filter_upwards [hlo.eventually (gt_mem_nhds ht),
    he.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hU.eventually (eventually_ge_atTop (t+1))] with i hi hei hUi
  exact ⟨hi.le, by linarith⟩

variable (K : Type*) [Field K] [NumberField K]

def realMask (U D e : ℝ) (x : HeckeIdeleClasses K) : ℝ :=
  logCutoff U D e (classLog K x)

def mask (U D e : ℝ) (x : HeckeIdeleClasses K) : ℂ :=
  (realMask K U D e x : ℂ)

theorem realMask_bounds (U D e : ℝ) (x : HeckeIdeleClasses K) :
    0 ≤ realMask K U D e x ∧ realMask K U D e x ≤ 1 :=
  logCutoff_bounds U D e (classLog K x)

theorem realMask_continuous (U D e : ℝ) : Continuous (realMask K U D e) :=
  (logCutoff_smooth U D e).continuous.comp (Masullo.WeightedIdeleClass.classLog_continuous K)

theorem mask_continuous (U D e : ℝ) : Continuous (mask K U D e) :=
  Complex.continuous_ofReal.comp (realMask_continuous K U D e)

theorem mask_norm_le (U D e : ℝ) (x : HeckeIdeleClasses K) :
    ‖mask K U D e x‖ ≤ 1 := by
  simp only [mask, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (realMask_bounds K U D e x).1]
  exact (realMask_bounds K U D e x).2

/-- Both endpoints diverge independently; L's common smoothing width has
both required small products and is eventually positive. -/
theorem mask_eventually_one (x : HeckeIdeleClasses K) :
    ∀ᶠ p : (ℝ × ℝ) × ℝ in LCutoffRegime.localRegime,
      mask K p.1.1 p.1.2 (LCutoffRegime.sharedSmoothing p.1.1 p.1.2 p.2) x = 1 := by
  have he := FPhysicalFilter.epsilon_tendsto_zero LCutoffRegime.localRegime
    (fun p : (ℝ × ℝ) × ℝ => p.1.1)
    (fun p => LCutoffRegime.sharedSmoothing p.1.1 p.1.2 p.2)
    LCutoffRegime.localRegime_first LCutoffRegime.localRegime_products.1
  filter_upwards [plateau_eventually LCutoffRegime.localRegime
    (fun p : (ℝ × ℝ) × ℝ => p.1.1) (fun p => p.1.2)
    (fun p => LCutoffRegime.sharedSmoothing p.1.1 p.1.2 p.2)
    LCutoffRegime.localRegime_first LCutoffRegime.localRegime_second he
    (Real.exp (classLog K x)) (Real.exp_pos _),
    LCutoffRegime.localRegime_first.eventually (eventually_gt_atTop (0 : ℝ)),
    LCutoffRegime.localRegime_second.eventually (eventually_gt_atTop (0 : ℝ)),
    LCutoffRegime.localRegime_delta_pos] with p hp hU hD hd
  have hepos : 0 < LCutoffRegime.sharedSmoothing p.1.1 p.1.2 p.2 :=
    div_pos hd (add_pos hU hD)
  simp only [mask, realMask, logCutoff_plateau _ _ _ _ hepos hp.1 hp.2,
    Complex.ofReal_one]

/-- Physical cutoff removal on the original measure for the actual
asymmetric family. The independent local max-log term is unchanged. -/
theorem integral_limit (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun p : (ℝ × ℝ) × ℝ => ∫ x,
      mask K p.1.1 p.1.2 (LCutoffRegime.sharedSmoothing p.1.1 p.1.2 p.2) x * d x ∂mu)
      LCutoffRegime.localRegime (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖d x‖)
  · exact Eventually.of_forall (fun p =>
      (mask_continuous K p.1.1 p.1.2 _).measurable.aestronglyMeasurable.mul
        hd.aestronglyMeasurable)
  · exact Eventually.of_forall (fun p => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (mask_norm_le K _ _ _ x)))
  · exact hd.norm
  · exact Eventually.of_forall (fun x => by
      apply tendsto_const_nhds.congr'
      filter_upwards [mask_eventually_one K x] with p hp
      simp only [hp, one_mul])

end
end FAsymmetricCutoff

#check FAsymmetricCutoff.integral_limit
#print axioms FAsymmetricCutoff.integral_limit
