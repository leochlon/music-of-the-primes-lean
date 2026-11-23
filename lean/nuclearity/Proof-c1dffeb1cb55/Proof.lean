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

namespace Round166F
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

end Round166F
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

namespace Round173D
open MasulloGRH Round166F MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_classLog_continuous : Continuous (classLog K) := by
  exact ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K)).quotient_lift _

/-- The actual compact-test support radius required in the repair of
manuscript (10.3.2.9)--(10.3.2.11). -/
theorem genuine_compact_log_radius (S : Set (HeckeIdeleClasses K))
    (hS : IsCompact S) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ S, |classLog K x| ≤ R := by
  obtain ⟨B, hB⟩ := hS.bddAbove_image (genuine_classLog_continuous K).abs.continuousOn
  exact ⟨max 1 B, le_max_left _ _, fun x hx =>
    (hB ⟨x, hx, rfl⟩).trans (le_max_right _ _)⟩

def mellinMomentIntegrand (h chi : HeckeIdeleClasses K → ℂ)
    (z : ℂ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  h x * chi x * Complex.exp (z * (classLog K x : ℂ)) *
    (classLog K x : ℂ) ^ m

/-- INTERVAL_VARIABLE_ORDER_MELLIN_MAJORANT: a corrected, actual-class
moment estimate. No assertion of spectral summability or nuclearity. -/
theorem genuine_interval_mellin_moment_bound
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h chi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : Continuous chi) (hs : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1)
    (R alpha : ℝ) (_hR : 0 ≤ R) (ha : 0 ≤ alpha)
    (hr : ∀ x, h x ≠ 0 → |classLog K x| ≤ R)
    (z : ℂ) (hz : |z.re| ≤ alpha) (m : ℕ) :
    Integrable (mellinMomentIntegrand K h chi z m) mu ∧
    ‖∫ x, mellinMomentIntegrand K h chi z m x ∂mu‖ ≤
      (Real.exp (alpha * R) * R ^ m) * ∫ x, ‖h x‖ ∂mu := by
  have hL := genuine_classLog_continuous K
  have hcont : Continuous (mellinMomentIntegrand K h chi z m) := by
    unfold mellinMomentIntegrand
    fun_prop
  have hsupp : HasCompactSupport (mellinMomentIntegrand K h chi z m) := by
    apply hs.mono
    intro x hx
    change h x ≠ 0
    intro he
    exact hx (by simp [mellinMomentIntegrand, he])
  have hint : Integrable (mellinMomentIntegrand K h chi z m) mu :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hhint : Integrable h mu := hh.integrable_of_hasCompactSupport hs
  have hb (x : HeckeIdeleClasses K) :
      ‖mellinMomentIntegrand K h chi z m x‖ ≤
        (Real.exp (alpha * R) * R ^ m) * ‖h x‖ := by
    by_cases he : h x = 0
    · simp [mellinMomentIntegrand, he]
    have hlog := hr x he
    have hreal : z.re * classLog K x ≤ alpha * R := by
      calc
        z.re * classLog K x ≤ |z.re * classLog K x| := le_abs_self _
        _ = |z.re| * |classLog K x| := abs_mul _ _
        _ ≤ alpha * R := mul_le_mul hz hlog (abs_nonneg _) ha
    have hp : |classLog K x| ^ m ≤ R ^ m := pow_le_pow_left₀ (abs_nonneg _) hlog m
    have heq : ‖mellinMomentIntegrand K h chi z m x‖ =
        ‖h x‖ * (Real.exp (z.re * classLog K x) * |classLog K x| ^ m) := by
      simp [mellinMomentIntegrand, norm_pow, Complex.norm_exp,
        Complex.mul_re, Complex.norm_real, Real.norm_eq_abs, mul_assoc, hu]
    rw [heq]
    calc
      _ ≤ ‖h x‖ * (Real.exp (alpha * R) * R ^ m) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.exp_le_exp.mpr hreal) hp
            (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) (norm_nonneg _)
      _ = _ := mul_comm _ _
  refine ⟨hint, (norm_integral_le_integral_norm _).trans ?_⟩
  calc
    (∫ x, ‖mellinMomentIntegrand K h chi z m x‖ ∂mu) ≤
        ∫ x, (Real.exp (alpha * R) * R ^ m) * ‖h x‖ ∂mu :=
      integral_mono hint.norm (hhint.norm.const_mul _) hb
    _ = _ := integral_const_mul _ _

/-- The radius is obtained from the actual test, uniformly for every
unitary character, point of the strip and nonnegative jet order. -/
theorem genuine_compact_interval_mellin_bound
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (chi : HeckeIdeleClasses K → ℂ),
      Continuous chi → (∀ x, ‖chi x‖ = 1) →
      ∀ (alpha : ℝ), 0 ≤ alpha → ∀ (z : ℂ), |z.re| ≤ alpha → ∀ (m : ℕ),
      Integrable (mellinMomentIntegrand K h chi z m) mu ∧
      ‖∫ x, mellinMomentIntegrand K h chi z m x ∂mu‖ ≤
        (Real.exp (alpha * R) * R ^ m) * ∫ x, ‖h x‖ ∂mu := by
  obtain ⟨R, hR, hr⟩ := genuine_compact_log_radius K (tsupport h) hs
  refine ⟨R, hR, ?_⟩
  intro chi hc hu alpha ha z hz m
  apply genuine_interval_mellin_moment_bound K mu h chi hh hc hs hu R alpha
    (le_trans zero_le_one hR) ha _ z hz m
  intro x hx
  exact hr x (show x ∈ closure (Function.support h) from subset_closure hx)

#check genuine_compact_log_radius
#print axioms genuine_compact_log_radius
#check genuine_interval_mellin_moment_bound
#print axioms genuine_interval_mellin_moment_bound
#check genuine_compact_interval_mellin_bound
#print axioms genuine_compact_interval_mellin_bound
end Round173D

namespace Round175D
open MasulloGRH Round166F Round173D MeasureTheory
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- Pointwise domination needed for differentiating the actual Mellin integral. -/
theorem moment_pointwise_bound
    (h chi : HeckeIdeleClasses K → ℂ) (hu : ∀ x, ‖chi x‖ = 1)
    (R alpha : ℝ) (ha : 0 ≤ alpha)
    (hr : ∀ x, h x ≠ 0 → |classLog K x| ≤ R)
    (z : ℂ) (hz : |z.re| ≤ alpha) (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖mellinMomentIntegrand K h chi z m x‖ ≤
      (Real.exp (alpha * R) * R ^ m) * ‖h x‖ := by
  by_cases he : h x = 0
  · simp [mellinMomentIntegrand, he]
  have hlog := hr x he
  have hreal : z.re * classLog K x ≤ alpha * R := by
    calc
      z.re * classLog K x ≤ |z.re * classLog K x| := le_abs_self _
      _ = |z.re| * |classLog K x| := abs_mul _ _
      _ ≤ alpha * R := mul_le_mul hz hlog (abs_nonneg _) ha
  have hp : |classLog K x| ^ m ≤ R ^ m := pow_le_pow_left₀ (abs_nonneg _) hlog m
  have heq : ‖mellinMomentIntegrand K h chi z m x‖ =
      ‖h x‖ * (Real.exp (z.re * classLog K x) * |classLog K x| ^ m) := by
    simp [mellinMomentIntegrand, norm_pow, Complex.norm_exp,
      Complex.mul_re, Complex.norm_real, Real.norm_eq_abs, mul_assoc, hu]
  rw [heq]
  calc
    _ ≤ ‖h x‖ * (Real.exp (alpha * R) * R ^ m) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.exp_le_exp.mpr hreal) hp
          (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- INTERVAL_MELLIN_DERIVATIVE_IDENTIFICATION, needed at (10.3.2.8):
the derivative of each actual compact-test Mellin moment is its next moment.
There is no spectral finiteness or nuclearity premise. -/
theorem genuine_mellin_moment_hasDerivAt
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h chi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : Continuous chi) (hs : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1) (m : ℕ) (z0 : ℂ) :
    HasDerivAt (fun z => ∫ x, mellinMomentIntegrand K h chi z m x ∂mu)
      (∫ x, mellinMomentIntegrand K h chi z0 (m+1) x ∂mu) z0 := by
  obtain ⟨R, hR, hr0⟩ := genuine_compact_log_radius K (tsupport h) hs
  have hr : ∀ x, h x ≠ 0 → |classLog K x| ≤ R :=
    fun x hx => hr0 x (subset_closure hx)
  have hL := genuine_classLog_continuous K
  have hcont (z : ℂ) (n : ℕ) : Continuous (mellinMomentIntegrand K h chi z n) := by
    unfold mellinMomentIntegrand
    fun_prop
  have hint (z : ℂ) (n : ℕ) : Integrable (mellinMomentIntegrand K h chi z n) mu :=
    (genuine_interval_mellin_moment_bound K mu h chi hh hc hs hu R |z.re|
      (by linarith) (abs_nonneg _) hr z le_rfl n).1
  have ha : 0 ≤ ‖z0‖ + 1 := by positivity
  have hz (z : ℂ) (hz : z ∈ Metric.ball z0 1) : |z.re| ≤ ‖z0‖ + 1 := by
    have hd : ‖z-z0‖ < 1 := by simpa [dist_eq_norm] using hz
    calc
      |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      _ = ‖z-z0+z0‖ := by rw [sub_add_cancel]
      _ ≤ ‖z-z0‖+‖z0‖ := norm_add_le _ _
      _ ≤ ‖z0‖+1 := by linarith
  have hd (x : HeckeIdeleClasses K) (z : ℂ) :
      HasDerivAt (fun w => mellinMomentIntegrand K h chi w m x)
        (mellinMomentIntegrand K h chi z (m+1) x) z := by
    have hh0 := (((Complex.hasDerivAt_exp (z * (classLog K x : ℂ))).comp z
      ((hasDerivAt_id z).mul_const (classLog K x : ℂ))).const_mul
        (h x * chi x)).mul_const ((classLog K x : ℂ)^m)
    convert hh0 using 1
    simp [mellinMomentIntegrand, pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x => mellinMomentIntegrand K h chi z m x)
    (F' := fun z x => mellinMomentIntegrand K h chi z (m+1) x)
    (bound := fun x => (Real.exp ((‖z0‖+1)*R)*R^(m+1))*‖h x‖)
    (Metric.ball_mem_nhds z0 zero_lt_one)
    (Filter.Eventually.of_forall fun z => (hcont z m).aestronglyMeasurable)
    (hint z0 m) (hcont z0 (m+1)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x z hzz =>
      moment_pointwise_bound K h chi hu R (‖z0‖+1) ha hr z (hz z hzz) (m+1) x)
    ((hh.integrable_of_hasCompactSupport hs).norm.const_mul _)
    (Filter.Eventually.of_forall fun x z _ => hd x z)).2

/-- All holomorphic derivatives used in the interval spectral proof are the
actual logarithmic moments, uniformly in derivative order. -/
theorem genuine_mellin_iteratedDeriv
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h chi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : Continuous chi) (hs : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1) (m : ℕ) :
    iteratedDeriv m (fun z => ∫ x, mellinMomentIntegrand K h chi z 0 x ∂mu) =
      fun z => ∫ x, mellinMomentIntegrand K h chi z m x ∂mu := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (genuine_mellin_moment_hasDerivAt K mu h chi hh hc hs hu m z).deriv

/-- The corrected compact-support bound now applies to actual complex
Mellin derivatives. This is not a height-decay or nuclear estimate. -/
theorem genuine_compact_interval_mellin_derivative_bound
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (chi : HeckeIdeleClasses K → ℂ),
      Continuous chi → (∀ x, ‖chi x‖ = 1) →
      ∀ (alpha : ℝ), 0 ≤ alpha → ∀ (z : ℂ), |z.re| ≤ alpha → ∀ (m : ℕ),
      ‖iteratedDeriv m (fun w => ∫ x, mellinMomentIntegrand K h chi w 0 x ∂mu) z‖ ≤
        (Real.exp (alpha * R) * R ^ m) * ∫ x, ‖h x‖ ∂mu := by
  obtain ⟨R, hR, hb⟩ := genuine_compact_interval_mellin_bound K mu h hh hs
  refine ⟨R, hR, ?_⟩
  intro chi hc hu alpha ha z hz m
  rw [genuine_mellin_iteratedDeriv K mu h chi hh hc hs hu m]
  exact (hb chi hc hu alpha ha z hz m).2

#check moment_pointwise_bound
#print axioms moment_pointwise_bound
#check genuine_compact_interval_mellin_derivative_bound
#print axioms genuine_compact_interval_mellin_derivative_bound
#check genuine_mellin_moment_hasDerivAt
#print axioms genuine_mellin_moment_hasDerivAt
#check genuine_mellin_iteratedDeriv
#print axioms genuine_mellin_iteratedDeriv
end Round175D

namespace Round176H
open MasulloGRH Round166F Round173D Round175D MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The actual adjoint test and POINTWISE logarithmic test. -/
def sharp (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  star (phi x⁻¹)
def logTest (phi : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  (classLog K x : ℂ) * phi x

lemma native_log_inv (x : HeckeIdeleClasses K) : classLog K x⁻¹ = -classLog K x := by
  have hm (g y : HeckeIdeleClasses K) :
      classLog K (g*y) = classLog K g + classLog K y := by
    refine Quotient.inductionOn₂ g y ?_
    intro a b
    change Real.log (genuineIdeleModulus K (a*b)) = _
    rw [genuineIdeleModulus_mul, Real.log_mul
      (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b)]
    rfl
  have h1 : classLog K 1 = 0 := by
    change Real.log (genuineIdeleModulus K 1) = 0
    have he : genuineIdeleModulus K 1 = 1 := by
      simpa only [map_one] using genuineIdeleModulus_principal K (1 : Kˣ)
    rw [he, Real.log_one]
  have he := hm x x⁻¹
  rw [mul_inv_cancel, h1] at he
  linarith

theorem sharp_logTest (phi : HeckeIdeleClasses K → ℂ) :
    sharp K (logTest K phi) = fun x => -(classLog K x : ℂ) * sharp K phi x := by
  funext x
  simp [sharp, logTest, native_log_inv, star_mul, mul_comm]

lemma sharp_compact (phi : HeckeIdeleClasses K → ℂ) (hs : HasCompactSupport phi) :
    HasCompactSupport (sharp K phi) := by
  have he : Function.support (sharp K phi) = Function.support (fun x => phi x⁻¹) := by
    ext x
    simp [Function.mem_support, sharp]
  change IsCompact (closure (Function.support (sharp K phi)))
  rw [he]
  exact hs.comp_homeomorph (Homeomorph.inv (HeckeIdeleClasses K))

/-- BOTH_REQUIRED_TEST_COEFFICIENTS: the second required test is the negative
next Mellin jet of the first. This attaches pointwise ell multiplication to
(10.3.1.12) and (10.3.2.8), without any nuclearity assumption. -/
theorem genuine_required_test_moment_identity
    (mu : Measure (HeckeIdeleClasses K))
    (phi chi : HeckeIdeleClasses K → ℂ) (z : ℂ) (m : ℕ) :
    (∫ x, mellinMomentIntegrand K (sharp K (logTest K phi)) chi z m x ∂mu) =
      -(∫ x, mellinMomentIntegrand K (sharp K phi) chi z (m+1) x ∂mu) := by
  rw [sharp_logTest]
  have he : mellinMomentIntegrand K
      (fun x => -(classLog K x : ℂ) * sharp K phi x) chi z m =
      fun x => -mellinMomentIntegrand K (sharp K phi) chi z (m+1) x := by
    funext x
    simp only [mellinMomentIntegrand, pow_succ]
    ring
  rw [he, integral_neg]

/-- A single support radius controls the actual coefficients for BOTH tests.
The second test has the necessary extra power R; this is not height decay
or a finite total spectral cost. -/
theorem genuine_required_test_moment_bounds
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hs : HasCompactSupport phi) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (chi : HeckeIdeleClasses K → ℂ),
      Continuous chi → (∀ x, ‖chi x‖ = 1) →
      ∀ alpha : ℝ, 0 ≤ alpha → ∀ z : ℂ, |z.re| ≤ alpha → ∀ m : ℕ,
      (‖∫ x, mellinMomentIntegrand K (sharp K phi) chi z m x ∂mu‖ ≤
        (Real.exp (alpha * R) * R^m) * ∫ x, ‖sharp K phi x‖ ∂mu) ∧
      (‖∫ x, mellinMomentIntegrand K (sharp K (logTest K phi)) chi z m x ∂mu‖ ≤
        (Real.exp (alpha * R) * R^(m+1)) * ∫ x, ‖sharp K phi x‖ ∂mu) := by
  have hc : Continuous (sharp K phi) := by unfold sharp; fun_prop
  obtain ⟨R, hR, hb⟩ := genuine_compact_interval_mellin_bound K mu
    (sharp K phi) hc (sharp_compact K phi hs)
  refine ⟨R, hR, ?_⟩
  intro chi hchi hu alpha ha z hz m
  constructor
  · exact (hb chi hchi hu alpha ha z hz m).2
  · rw [genuine_required_test_moment_identity, norm_neg]
    exact (hb chi hchi hu alpha ha z hz (m+1)).2

#check sharp_logTest
#print axioms sharp_logTest
#check genuine_required_test_moment_identity
#print axioms genuine_required_test_moment_identity
#check genuine_required_test_moment_bounds
#print axioms genuine_required_test_moment_bounds
end Round176H

namespace Round176H
open MasulloGRH Round166F Round173D Round175D MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
/-- The actual derivative coefficients entering both manuscript spectral
nuclearity proofs satisfy the required pointwise-logarithm test identity. -/
theorem genuine_required_test_derivative_identity
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (phi chi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi)
    (hs : HasCompactSupport phi) (hc : Continuous chi) (hu : ∀ x, ‖chi x‖ = 1)
    (z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun w => ∫ x,
      mellinMomentIntegrand K (sharp K (logTest K phi)) chi w 0 x ∂mu) z =
    -iteratedDeriv (m+1) (fun w => ∫ x,
      mellinMomentIntegrand K (sharp K phi) chi w 0 x ∂mu) z := by
  have hL := genuine_classLog_continuous K
  have hl : Continuous (logTest K phi) := by unfold logTest; fun_prop
  have hls : HasCompactSupport (logTest K phi) := hs.mul_left
  have hsh : Continuous (sharp K phi) := by unfold sharp; fun_prop
  have hsl : Continuous (sharp K (logTest K phi)) := by unfold sharp; fun_prop
  rw [genuine_mellin_iteratedDeriv K mu _ chi hsl hc
    (sharp_compact K _ hls) hu m,
    genuine_mellin_iteratedDeriv K mu _ chi hsh hc (sharp_compact K _ hs) hu (m+1)]
  exact genuine_required_test_moment_identity K mu phi chi z m
#check genuine_required_test_derivative_identity
#print axioms genuine_required_test_derivative_identity
end Round176H



/-!
Round 173 A. Structural premise of manuscript (10.4.2.5).
The closed geometric image must still be attached to the native number-field
space. No nuclearity or summability assumption is introduced here.
-/
noncomputable section
set_option linter.unusedSectionVars false
namespace Round173A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The genuine normed quotient map, not an arbitrary surrogate. -/
def Q : H →L[ℂ] H ⧸ G :=
  G.mkQ.mkContinuous 1 (by intro x; simpa using Submodule.Quotient.norm_mk_le G x)

/-- Orthogonal representative, included in the ambient space. -/
def Slinear : (H ⧸ G) →ₗ[ℂ] H :=
  G.liftQ Gᗮ.starProjection.toLinearMap (by
    intro x hx
    change Gᗮ.starProjection x = 0
    simpa only [Submodule.starProjection_apply_eq_zero_iff,
      Submodule.orthogonal_orthogonal] using hx)

@[simp] theorem Slinear_mk (x : H) :
    Slinear G (G.mkQ x) = Gᗮ.starProjection x := rfl

/-- The quotient infimum, not the open mapping theorem, gives this bound. -/
theorem Slinear_contract (x : H ⧸ G) : ‖Slinear G x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt x hε
  have hp := Submodule.norm_starProjection_apply_le Gᗮ y
  change ‖Slinear G (Submodule.Quotient.mk y)‖ ≤ ‖y‖ at hp
  rw [hy] at hp
  exact hp.trans (le_of_lt hnorm)

def S : (H ⧸ G) →L[ℂ] H :=
  (Slinear G).mkContinuous 1 (by intro x; simpa using Slinear_contract G x)

@[simp] theorem S_Q (x : H) : S G (Q G x) = Gᗮ.starProjection x := rfl

/-- Construct the induced quotient action from invariance, without assuming
an operator identity or any nuclear estimate. -/
def AbarLinear (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) :
    (H ⧸ G) →ₗ[ℂ] H ⧸ G :=
  G.mapQ G A.toLinearMap hA

@[simp] theorem AbarLinear_Q (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    AbarLinear G A hA (Q G x) = Q G (A x) := rfl

/-- Exact algebraic factorisation with the quotient and genuine projector. -/
theorem quotient_projected_factorisation (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Gᗮ.starProjection (A x) = S G (AbarLinear G A hA (Q G x)) := rfl

theorem Q_S (x : H ⧸ G) : Q G (S G x) = x := by
  refine Submodule.Quotient.induction_on G x ?_
  intro y
  have hm : y - Gᗮ.starProjection y ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal y
  have hz : G.mkQ (y - Gᗮ.starProjection y) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).2 hm
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem S_isometry (x : H ⧸ G) : ‖S G x‖ = ‖x‖ := by
  apply le_antisymm (Slinear_contract G x)
  have hn := Submodule.Quotient.norm_mk_le G (S G x)
  change ‖Q G (S G x)‖ ≤ ‖S G x‖ at hn
  simpa only [Q_S] using hn

def Abar (A : H →L[ℂ] H) : (H ⧸ G) →L[ℂ] H ⧸ G :=
  (Q G).comp (A.comp (S G))

theorem Abar_Q (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Abar G A (Q G x) = Q G (A x) := by
  have hm : x - Gᗮ.starProjection x ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal x
  have hz : G.mkQ (A (x - Gᗮ.starProjection x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).2 (hA _ hm)
  rw [map_sub, map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The bounded-composition factorisation in (10.4.2.5), with its actual
quotient maps and map costs established. Native H/G/A attachment remains. -/
theorem bounded_quotient_factorisation (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    Gᗮ.starProjection.comp A = (S G).comp ((Abar G A).comp (Q G)) ∧
    ‖Q G‖ ≤ 1 ∧ ‖S G‖ ≤ 1 ∧ (∀ x : H ⧸ G, ‖S G x‖ = ‖x‖) := by
  refine ⟨?_, ?_, ?_, S_isometry G⟩
  · ext x
    change Gᗮ.starProjection (A x) = S G (Abar G A (Q G x))
    rw [Abar_Q G A hA, S_Q]
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem S_mem (x : H ⧸ G) : S G x ∈ Gᗮ := by
  refine Submodule.Quotient.induction_on G x ?_
  intro y
  exact Gᗮ.starProjection_apply_mem y

theorem range_S : LinearMap.range (S G).toLinearMap = Gᗮ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact S_mem G x
  · intro hy
    refine ⟨Q G y, ?_⟩
    change S G (Q G y) = y
    rw [S_Q, Submodule.starProjection_eq_self_iff]
    exact hy

/-- The bounded representative formula is the induced quotient operator,
not just some operator on a space isomorphic to the quotient. -/
theorem Abar_eq_induced (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    (Abar G A).toLinearMap = AbarLinear G A hA := by
  ext x
  change Abar G A (Q G x) = AbarLinear G A hA (Q G x)
  rw [Abar_Q G A hA, AbarLinear_Q]

theorem manuscript_quotient_structure (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    Gᗮ.starProjection.comp A = (S G).comp ((Abar G A).comp (Q G)) ∧
    (Abar G A).toLinearMap = AbarLinear G A hA ∧
    LinearMap.range (S G).toLinearMap = Gᗮ ∧
    (∀ x : H ⧸ G, Q G (S G x) = x) ∧
    ‖Q G‖ ≤ 1 ∧ ‖S G‖ ≤ 1 ∧ (∀ x : H ⧸ G, ‖S G x‖ = ‖x‖) := by
  obtain ⟨hf, hq, hs, hi⟩ := bounded_quotient_factorisation G A hA
  exact ⟨hf, Abar_eq_induced G A hA, range_S G, Q_S G, hq, hs, hi⟩

end Round173A
#check Round173A.manuscript_quotient_structure
#print axioms Round173A.manuscript_quotient_structure
#check Round173A.bounded_quotient_factorisation
#print axioms Round173A.bounded_quotient_factorisation
#check Round173A.quotient_projected_factorisation
#print axioms Round173A.quotient_projected_factorisation
#check Round173A.Slinear_contract
#print axioms Round173A.Slinear_contract

/-!
Round 174 A review implication: the rank-one ideal-property step in
manuscript (10.4.2.5), attached to the actual normed quotient and its
constructed orthogonal representative. The source above is retained from
A173. No native arithmetic identification or finite spectral cost is assumed
or concluded. Infinite costs below remain in ENNReal and may equal infinity.
-/
open scoped ENNReal
namespace Round174A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The exact quotient representative transfers each actual rank-one term. -/
theorem quotient_rankOne_identity
    (f : (H ⧸ G) →L[ℂ] ℂ) (v : H ⧸ G) :
    (Round173A.S G).comp ((f.smulRight v).comp (Round173A.Q G)) =
      (f.comp (Round173A.Q G)).smulRight (Round173A.S G v) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    map_smul]

/-- No separately assumed bounds on Q or S: their native quotient norms
were derived in the retained source. -/
theorem quotient_rankOne_cost_le
    (f : (H ⧸ G) →L[ℂ] ℂ) (v : H ⧸ G) :
    ‖f.comp (Round173A.Q G)‖ * ‖Round173A.S G v‖ ≤ ‖f‖ * ‖v‖ := by
  have hQ : ‖Round173A.Q G‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hf : ‖f.comp (Round173A.Q G)‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖f‖ * ‖Round173A.Q G‖ := f.opNorm_comp_le _
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hQ (ContinuousLinearMap.opNorm_nonneg f)
      _ = _ := mul_one _
  rw [Round173A.S_isometry]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg v)

/-- The absolute expansion cost cannot increase under S(-)Q. This theorem
does not assert that either extended-real sum is finite. -/
theorem quotient_expansion_cost_le {ι : Type*}
    (f : ι → (H ⧸ G) →L[ℂ] ℂ) (v : ι → H ⧸ G) :
    (∑' i, ENNReal.ofReal
      (‖(f i).comp (Round173A.Q G)‖ * ‖Round173A.S G (v i)‖)) ≤
      ∑' i, ENNReal.ofReal (‖f i‖ * ‖v i‖) := by
  apply ENNReal.tsum_le_tsum
  intro i
  exact ENNReal.ofReal_le_ofReal (quotient_rankOne_cost_le G (f i) (v i))

/-- Conditional reconstruction only: if a quotient expansion has been
derived, it represents convolution FIRST and genuine projection SECOND.
No nuclear summability or finiteness hypothesis occurs. -/
theorem projected_quotient_series_transfer {ι : Type*}
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G)
    (f : ι → (H ⧸ G) →L[ℂ] ℂ) (v : ι → H ⧸ G)
    (hrep : ∀ q, HasSum (fun i => f i q • v i) (Round173A.Abar G A q)) :
    (∀ x, HasSum
      (fun i => ((f i).comp (Round173A.Q G)) x • Round173A.S G (v i))
      (Gᗮ.starProjection (A x))) ∧
    (∑' i, ENNReal.ofReal
      (‖(f i).comp (Round173A.Q G)‖ * ‖Round173A.S G (v i)‖)) ≤
      ∑' i, ENNReal.ofReal (‖f i‖ * ‖v i‖) := by
  refine ⟨?_, quotient_expansion_cost_le G f v⟩
  intro x
  have ht := (Round173A.S G).hasSum (hrep (Round173A.Q G x))
  simpa only [map_smul, ContinuousLinearMap.comp_apply,
    Round173A.Abar_Q G A hA, Round173A.S_Q] using ht

end Round174A
#check Round174A.quotient_rankOne_identity
#print axioms Round174A.quotient_rankOne_identity
#check Round174A.quotient_rankOne_cost_le
#print axioms Round174A.quotient_rankOne_cost_le
#check Round174A.quotient_expansion_cost_le
#print axioms Round174A.quotient_expansion_cost_le
#check Round174A.projected_quotient_series_transfer
#print axioms Round174A.projected_quotient_series_transfer


/-!
Round 175 A: FINITE_BINOMIAL_QUOTIENT_BLOCK_COST.
This is the finite rank-one estimate needed at manuscript 10.3.1.18--22,
retaining the actual functional/vector norm factors. It does not prove that
the spectral cost summed over all zeros and characters is finite. The arrays
must still be identified with genuine continuous quotient Mellin jets,
Mellin coefficients, and biorthogonal vectors. No such identification is
silently built into these arbitrary arrays.
-/
namespace Round175A
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

def jetAction (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ) (m : ℕ) : E →L[ℂ] ℂ :=
  ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℂ) * c i) • eta (m - i)

def block (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ)
    (psi : ℕ → E) : E →L[ℂ] E :=
  ∑ m ∈ Finset.range n, (jetAction eta c m).smulRight (psi m)

def blockCost (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ)
    (psi : ℕ → E) : ℝ :=
  ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range (m + 1),
    ((m.choose i : ℝ) * ‖c i‖ * ‖eta (m - i)‖) * ‖psi m‖

/-- The binomial jet action retains all derivative orders and norm factors. -/
theorem jetAction_norm_le (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ) (m : ℕ) :
    ‖jetAction eta c m‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖c i‖ * ‖eta (m - i)‖ := by
  unfold jetAction
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        ‖((m.choose i : ℂ) * c i) • eta (m - i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, norm_mul, Complex.norm_natCast]

/-- A finite nuclear representation cost, derived without a uniform
biorthogonal bound or any infinite summability hypothesis. -/
theorem block_representation_cost_le (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ)
    (c : ℕ → ℂ) (psi : ℕ → E) :
    (∑ m ∈ Finset.range n, ‖jetAction eta c m‖ * ‖psi m‖) ≤
      blockCost n eta c psi := by
  unfold blockCost
  apply Finset.sum_le_sum
  intro m hm
  calc
    _ ≤ (∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖c i‖ * ‖eta (m - i)‖) * ‖psi m‖ :=
      mul_le_mul_of_nonneg_right (jetAction_norm_le eta c m) (norm_nonneg _)
    _ = _ := Finset.sum_mul _ _ _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- An explicit finite rank-one certificate on the ambient Hilbert space,
using the genuine quotient Q and orthogonal representative S. -/
theorem projected_block_certificate (n : ℕ)
    (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (c : ℕ → ℂ) (psi : ℕ → H ⧸ G) :
    (Round173A.S G).comp ((block n eta c psi).comp (Round173A.Q G)) =
      ∑ m ∈ Finset.range n,
        ((jetAction eta c m).comp (Round173A.Q G)).smulRight
          (Round173A.S G (psi m)) := by
  ext x
  simp [block, ContinuousLinearMap.sum_apply, map_sum]

/-- This is a finite block bound only, not the full leading nuclear bound.
It supplies the conditioned finite cost required by the manuscript's
spectral proof before infinite summation and native identification. -/
theorem projected_block_nuclear_cost (n : ℕ)
    (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (c : ℕ → ℂ) (psi : ℕ → H ⧸ G) :
    (Round173A.S G).comp ((block n eta c psi).comp (Round173A.Q G)) =
      ∑ m ∈ Finset.range n,
        ((jetAction eta c m).comp (Round173A.Q G)).smulRight
          (Round173A.S G (psi m)) ∧
    (∑ m ∈ Finset.range n,
      ‖(jetAction eta c m).comp (Round173A.Q G)‖ * ‖Round173A.S G (psi m)‖)
      ≤ blockCost n eta c psi ∧
    ENNReal.ofReal (blockCost n eta c psi) < ⊤ := by
  refine ⟨projected_block_certificate G n eta c psi, ?_, ENNReal.ofReal_lt_top⟩
  calc
    _ ≤ ∑ m ∈ Finset.range n, ‖jetAction eta c m‖ * ‖psi m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact Round174A.quotient_rankOne_cost_le G _ _
    _ ≤ _ := block_representation_cost_le n eta c psi

end Round175A
#check Round175A.jetAction_norm_le
#print axioms Round175A.jetAction_norm_le
#check Round175A.block_representation_cost_le
#print axioms Round175A.block_representation_cost_le
#check Round175A.projected_block_certificate
#print axioms Round175A.projected_block_certificate
#check Round175A.projected_block_nuclear_cost
#print axioms Round175A.projected_block_nuclear_cost

/-!
H177: CONDITIONING_RETAINED_TEST_BLOCK_BOUND in (10.3.1.18)--(10.3.1.22).
Attach actual coefficients for both required tests to finite quotient costs.
No claim that the finite windows have a summable or uniformly bounded cost.
-/
namespace Round177H
open MasulloGRH Round173D Round176H Round175A MeasureTheory
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

def windowMajorant (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ) (psi : ℕ → E)
    (R alpha L : ℝ) (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range (m+1),
    ((m.choose i : ℝ) * ((Real.exp (alpha*R) * R^(i+j))*L) *
      ‖eta (m-i)‖) * ‖psi m‖

theorem coefficient_bound_to_block (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ)
    (psi : ℕ → E) (c : ℕ → ℂ) (R alpha L : ℝ) (j : ℕ)
    (hc : ∀ i, ‖c i‖ ≤ (Real.exp (alpha*R)*R^(i+j))*L) :
    blockCost n eta c psi ≤ windowMajorant n eta psi R alpha L j := by
  unfold blockCost windowMajorant
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact mul_le_mul_of_nonneg_left (hc i) (Nat.cast_nonneg _)

theorem log_window_factor (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ) (psi : ℕ → E)
    (R alpha L : ℝ) :
    windowMajorant n eta psi R alpha L 1 =
      R * windowMajorant n eta psi R alpha L 0 := by
  unfold windowMajorant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.add_zero, pow_succ]
  ring

variable (K : Type*) [Field K] [NumberField K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- One support radius gives a finite explicit rank-one cost for each
projected quotient block for BOTH actual tests. The quotient jets and their
vectors must still be attached to the native spectral data, and the cost
summed over zeros/characters must still be derived. -/
theorem genuine_required_projected_block_cost
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hs : HasCompactSupport phi) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (chi : HeckeIdeleClasses K → ℂ),
      Continuous chi → (∀ x, ‖chi x‖ = 1) →
      ∀ alpha : ℝ, 0 ≤ alpha → ∀ z : ℂ, |z.re| ≤ alpha →
      ∀ (n : ℕ) (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (psi : ℕ → H ⧸ G),
      let c₀ := fun i => ∫ x, mellinMomentIntegrand K (sharp K phi) chi z i x ∂mu
      let c₁ := fun i => ∫ x, mellinMomentIntegrand K (sharp K (logTest K phi)) chi z i x ∂mu
      let B := windowMajorant n eta psi R alpha (∫ x, ‖sharp K phi x‖ ∂mu) 0
      (∑ m ∈ Finset.range n,
        ‖(jetAction eta c₀ m).comp (Round173A.Q G)‖ * ‖Round173A.S G (psi m)‖) ≤ B ∧
      (∑ m ∈ Finset.range n,
        ‖(jetAction eta c₁ m).comp (Round173A.Q G)‖ * ‖Round173A.S G (psi m)‖) ≤ R*B ∧
      ENNReal.ofReal B < ⊤ ∧ ENNReal.ofReal (R*B) < ⊤ := by
  obtain ⟨R, hR, hb⟩ := genuine_required_test_moment_bounds K mu phi hh hs
  refine ⟨R, hR, ?_⟩
  intro chi hc hu alpha ha z hz n eta psi
  dsimp only
  refine ⟨?_, ?_, ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  · apply (projected_block_nuclear_cost G n eta _ psi).2.1.trans
    apply coefficient_bound_to_block
    intro i
    simpa only [Nat.add_zero] using (hb chi hc hu alpha ha z hz i).1
  · rw [← log_window_factor]
    apply (projected_block_nuclear_cost G n eta _ psi).2.1.trans
    apply coefficient_bound_to_block
    intro i
    exact (hb chi hc hu alpha ha z hz i).2

end Round177H
#check Round177H.coefficient_bound_to_block
#print axioms Round177H.coefficient_bound_to_block
#check Round177H.log_window_factor
#print axioms Round177H.log_window_factor
#check Round177H.genuine_required_projected_block_cost
#print axioms Round177H.genuine_required_projected_block_cost
