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

/-! Round176A: ACTUAL_BINOMIAL_ADJOINT_JET_ACTION, manuscript
26967--27004. This proves the translated spectral integral on the actual
idele-class group. Native dual membership and identification with the
bounded quotient adjoint remain separate obligations. -/
namespace Round176A
open MasulloGRH Round166F Round173D MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

-- The arithmetic logarithm calculation is reused from B175; no new
-- progress is claimed for this helper.
private theorem log_mul (g x : HeckeIdeleClasses K) :
    classLog K (g * x) = classLog K g + classLog K x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  change Real.log (genuineIdeleModulus K (a*b)) = _
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b)]
  rfl

def spectralJet (chi : HeckeIdeleClasses K →* ℂ) (z : ℂ)
    (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  chi x * Complex.exp (z * (classLog K x : ℂ)) * (classLog K x : ℂ)^m

theorem spectralJet_mul (chi : HeckeIdeleClasses K →* ℂ)
    (z : ℂ) (m : ℕ) (x y : HeckeIdeleClasses K) :
    spectralJet K chi z m (x*y) =
      ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
        spectralJet K chi z i x * spectralJet K chi z (m-i) y := by
  unfold spectralJet
  rw [map_mul, log_mul, Complex.ofReal_add, mul_add, Complex.exp_add, add_pow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The actual integral version of (10.3.1.12), valid at every complex
Mellin parameter, hence for the whole interval strip as well as its line.
All integrability is derived from continuous compact support. -/
theorem genuine_adjoint_spectral_jet_action
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h : HeckeIdeleClasses K → ℂ) (chi : HeckeIdeleClasses K →* ℂ)
    (hh : Continuous h) (hc : Continuous chi) (hs : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1) (z : ℂ) (m : ℕ) (y : HeckeIdeleClasses K) :
    Integrable (fun x => h x * spectralJet K chi z m (x*y)) mu ∧
    (∫ x, h x * spectralJet K chi z m (x*y) ∂mu) =
      ∑ i ∈ Finset.range (m+1),
        ((m.choose i : ℂ) * spectralJet K chi z (m-i) y) *
          iteratedDeriv i
            (fun w => ∫ x, mellinMomentIntegrand K h chi w 0 x ∂mu) z := by
  obtain ⟨R, hR, hb⟩ := genuine_compact_interval_mellin_bound K mu h hh hs
  have hint (i : ℕ) : Integrable (mellinMomentIntegrand K h chi z i) mu :=
    (hb chi hc hu |z.re| (abs_nonneg _) z le_rfl i).1
  have heq : (fun x => h x * spectralJet K chi z m (x*y)) =
      fun x => ∑ i ∈ Finset.range (m+1),
        ((m.choose i : ℂ) * spectralJet K chi z (m-i) y) *
          mellinMomentIntegrand K h chi z i x := by
    funext x
    rw [spectralJet_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold spectralJet mellinMomentIntegrand
    ring
  rw [heq]
  constructor
  · exact integrable_finset_sum _ (fun i hi => (hint i).const_mul _)
  · rw [integral_finset_sum _ (fun i hi => (hint i).const_mul _)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul,
      Round175D.genuine_mellin_iteratedDeriv K mu h chi hh hc hs hu i]

end Round176A
#check Round176A.spectralJet_mul
#print axioms Round176A.spectralJet_mul
#check Round176A.genuine_adjoint_spectral_jet_action
#print axioms Round176A.genuine_adjoint_spectral_jet_action

namespace Round177A
open MasulloGRH Round166F Round173D Round176A MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Actual convolution first, before any spectral projection. -/
def classConvolution (mu : Measure (HeckeIdeleClasses K))
    (h f : HeckeIdeleClasses K → ℂ) (y : HeckeIdeleClasses K) : ℂ :=
  ∫ x, h x * f (x⁻¹*y) ∂mu

end Round177A

namespace Round180A
open MasulloGRH Round166F Round173D Round176A Round177A MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- NONCOMPACT_INPUT_JET_ACTION, the native-input extension of manuscript
(10.3.1.8)--(10.3.1.14). The input f is only measurable and has finitely
many absolute jet moments. No compact support or continuity of f, no
nuclearity, and no spectral summability is assumed. Native weighted-L2
membership must still supply these ordinary finite-order moments. -/
theorem genuine_convolution_jet_pairing_of_moments
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (h f : HeckeIdeleClasses K → ℂ) (chi : HeckeIdeleClasses K →* ℂ)
    (hh : Continuous h) (hf : Measurable f) (hc : Continuous chi)
    (hs : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1) (z : ℂ) (m : ℕ)
    (fm : ∀ j ≤ m, Integrable (fun y => f y * spectralJet K chi z j y) mu) :
    Integrable (fun y => classConvolution K mu h f y * spectralJet K chi z m y) mu ∧
    (∫ y, classConvolution K mu h f y * spectralJet K chi z m y ∂mu) =
      ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
        iteratedDeriv i
          (fun w => ∫ x, mellinMomentIntegrand K h chi w 0 x ∂mu) z *
        (∫ y, f y * spectralJet K chi z (m-i) y ∂mu) := by
  have hL := genuine_classLog_continuous K
  have hj (i : ℕ) : Continuous (spectralJet K chi z i) := by
    unfold spectralJet
    fun_prop
  have hi (g : HeckeIdeleClasses K → ℂ) (hg : Continuous g)
      (gs : HasCompactSupport g) (i : ℕ) :
      Integrable (fun x => g x * spectralJet K chi z i x) mu := by
    have hgs : HasCompactSupport (fun x => g x * spectralJet K chi z i x) := by
      apply gs.mono
      intro x hx
      exact left_ne_zero_of_mul hx
    exact (hg.mul (hj i)).integrable_of_hasCompactSupport hgs
  let F : HeckeIdeleClasses K × HeckeIdeleClasses K → ℂ :=
    fun p => h p.1 * f (p.1⁻¹*p.2) * spectralJet K chi z m p.2
  have hFm : AEStronglyMeasurable F (mu.prod mu) := by
    dsimp [F]
    exact ((hh.measurable.comp measurable_fst).mul
      (hf.comp (measurable_fst.inv.mul measurable_snd))).mul
        ((hj m).measurable.comp measurable_snd) |>.aestronglyMeasurable
  have hFexp : (F ∘ fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => (p.1, p.1*p.2)) =
      fun p => ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
        ((h p.1 * spectralJet K chi z i p.1) *
          (f p.2 * spectralJet K chi z (m-i) p.2)) := by
    funext p
    simp only [Function.comp_apply, F, inv_mul_cancel_left,
      spectralJet_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hFi : Integrable F (mu.prod mu) := by
    apply ((measurePreserving_prod_mul mu mu).integrable_comp hFm).mp
    rw [hFexp]
    exact integrable_finset_sum _ (fun i _ =>
      ((hi h hh hs i).mul_prod (fm (m-i) (Nat.sub_le m i))).const_mul _)
  have hpair : (fun y => ∫ x, F (x,y) ∂mu) =
      fun y => classConvolution K mu h f y * spectralJet K chi z m y := by
    funext y
    simpa only [F, classConvolution] using
      (integral_mul_const (μ := mu) (spectralJet K chi z m y)
        (fun x => h x * f (x⁻¹*y)))
  refine ⟨hpair ▸ hFi.integral_prod_right, ?_⟩
  rw [← hpair]
  rw [← integral_integral_swap hFi]
  have hinner (x : HeckeIdeleClasses K) :
      (∫ y, F (x,y) ∂mu) =
        ∑ i ∈ Finset.range (m+1),
          ((m.choose i : ℂ) * (h x * spectralJet K chi z i x)) *
            (∫ y, f y * spectralJet K chi z (m-i) y ∂mu) := by
    rw [← integral_mul_left_eq_self (fun y => F (x,y)) x]
    have he : (fun y => F (x,x*y)) = fun y =>
        ∑ i ∈ Finset.range (m+1),
          ((m.choose i : ℂ) * (h x * spectralJet K chi z i x)) *
            (f y * spectralJet K chi z (m-i) y) := by
      funext y
      simp only [F, inv_mul_cancel_left, spectralJet_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, integral_finset_sum _ (fun i _ => (fm (m-i) (Nat.sub_le m i)).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [hinner]
  rw [integral_finset_sum _ (fun i _ => ((hi h hh hs i).const_mul _).mul_const _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_mul_const, integral_const_mul,
    Round175D.genuine_mellin_iteratedDeriv K mu h chi hh hc hs hu i]
  simp only [spectralJet, mellinMomentIntegrand, mul_assoc]

end Round180A
#check Round180A.genuine_convolution_jet_pairing_of_moments
#print axioms Round180A.genuine_convolution_jet_pairing_of_moments

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

namespace Round180A
open MasulloGRH Round166F Round173D Round176A Round177A Round176H MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- BOTH_REQUIRED_NONCOMPACT_INPUT_JET_ACTION. These are literal convolution
pairings for BOTH required test families, with the pointwise-log test
identified by the negative next derivative of the sharp test. This is the
operator-identification premise of (10.3.1.12), not a nuclear estimate. -/
theorem genuine_required_test_convolution_pairings
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    [MeasurableMul₂ (HeckeIdeleClasses K)]
    (phi f : HeckeIdeleClasses K → ℂ) (chi : HeckeIdeleClasses K →* ℂ)
    (hh : Continuous phi) (hf : Measurable f) (hc : Continuous chi)
    (hs : HasCompactSupport phi) (hu : ∀ x, ‖chi x‖ = 1)
    (z : ℂ) (m : ℕ)
    (fm : ∀ j ≤ m, Integrable (fun y => f y * spectralJet K chi z j y) mu) :
    (Integrable (fun y => classConvolution K mu (sharp K phi) f y *
      spectralJet K chi z m y) mu ∧
    (∫ y, classConvolution K mu (sharp K phi) f y * spectralJet K chi z m y ∂mu) =
      ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
        iteratedDeriv i
          (fun w => ∫ x, mellinMomentIntegrand K (sharp K phi) chi w 0 x ∂mu) z *
        (∫ y, f y * spectralJet K chi z (m-i) y ∂mu)) ∧
    (Integrable (fun y => classConvolution K mu (sharp K (logTest K phi)) f y *
      spectralJet K chi z m y) mu ∧
    (∫ y, classConvolution K mu (sharp K (logTest K phi)) f y *
      spectralJet K chi z m y ∂mu) =
      -(∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
        iteratedDeriv (i+1)
          (fun w => ∫ x, mellinMomentIntegrand K (sharp K phi) chi w 0 x ∂mu) z *
        (∫ y, f y * spectralJet K chi z (m-i) y ∂mu))) := by
  have hL := genuine_classLog_continuous K
  have hl : Continuous (logTest K phi) := by unfold logTest; fun_prop
  have hls : HasCompactSupport (logTest K phi) := hs.mul_left
  have hsh : Continuous (sharp K phi) := by unfold sharp; fun_prop
  have hsl : Continuous (sharp K (logTest K phi)) := by unfold sharp; fun_prop
  have h0 := genuine_convolution_jet_pairing_of_moments K mu (sharp K phi) f chi
    hsh hf hc (sharp_compact K phi hs) hu z m fm
  have h1 := genuine_convolution_jet_pairing_of_moments K mu
    (sharp K (logTest K phi)) f chi hsl hf hc (sharp_compact K _ hls) hu z m fm
  refine ⟨h0, h1.1, ?_⟩
  rw [h1.2]
  simp only [genuine_required_test_derivative_identity K mu phi chi hh hs hc hu z,
    mul_neg, neg_mul, Finset.sum_neg_distrib]

end Round180A
#check Round180A.genuine_required_test_convolution_pairings
#print axioms Round180A.genuine_required_test_convolution_pairings
