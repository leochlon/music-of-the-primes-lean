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

/- R175G named premise MELLIN_JET_IDENTIFICATION: the actual compact-test
moments in (10.3.2.8) are successive complex derivatives, without assuming
any spectral summability, quotient nuclearity, or finite nuclear cost. -/
namespace Round175G
open MasulloGRH Round166F Round173D MeasureTheory Filter
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_mellin_moment_hasDerivAt
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h chi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : Continuous chi) (hsupp : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1) (z₀ : ℂ) (m : ℕ) :
    HasDerivAt (fun z => ∫ x, mellinMomentIntegrand K h chi z m x ∂mu)
      (∫ x, mellinMomentIntegrand K h chi z₀ (m+1) x ∂mu) z₀ := by
  obtain ⟨R, hR, hr⟩ := genuine_compact_log_radius K (tsupport h) hsupp
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  let a : ℝ := |z₀.re| + 1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  let U : Set ℂ := {z | |z.re| < a}
  have hU : U ∈ 𝓝 z₀ := by
    apply (isOpen_lt Complex.continuous_re.abs continuous_const).mem_nhds
    dsimp [U, a]
    linarith
  have hL := genuine_classLog_continuous K
  have hi (z : ℂ) (j : ℕ) : Integrable (mellinMomentIntegrand K h chi z j) mu := by
    have hcont : Continuous (mellinMomentIntegrand K h chi z j) := by
      unfold mellinMomentIntegrand
      fun_prop
    apply hcont.integrable_of_hasCompactSupport
    apply hsupp.mono
    intro x hx he
    exact hx (by simp [mellinMomentIntegrand, he])
  have hb : ∀ x, ∀ z ∈ U, ‖mellinMomentIntegrand K h chi z (m+1) x‖ ≤
      (Real.exp (a*R) * R^(m+1)) * ‖h x‖ := by
    intro x z hz
    by_cases he : h x = 0
    · simp [mellinMomentIntegrand, he]
    have hl : |classLog K x| ≤ R := hr x (subset_closure he)
    have hz' : |z.re| ≤ a := le_of_lt hz
    have hreal : z.re * classLog K x ≤ a * R :=
      (le_abs_self _).trans ((abs_mul _ _).le.trans
        (mul_le_mul hz' hl (abs_nonneg _) ha))
    have hp := pow_le_pow_left₀ (abs_nonneg (classLog K x)) hl (m+1)
    have heq : ‖mellinMomentIntegrand K h chi z (m+1) x‖ =
        ‖h x‖ * (Real.exp (z.re * classLog K x) * |classLog K x|^(m+1)) := by
      simp [mellinMomentIntegrand, norm_pow, Complex.norm_exp,
        Complex.mul_re, Complex.norm_real, Real.norm_eq_abs, mul_assoc, hu]
    rw [heq]
    calc
      _ ≤ ‖h x‖ * (Real.exp (a*R) * R^(m+1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (Real.exp_le_exp.mpr hreal) hp
            (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hd (x : HeckeIdeleClasses K) (z : ℂ) :
      HasDerivAt (fun w => mellinMomentIntegrand K h chi w m x)
        (mellinMomentIntegrand K h chi z (m+1) x) z := by
    have hd := (((Complex.hasDerivAt_exp (z * (classLog K x : ℂ))).comp z
      ((hasDerivAt_id z).mul_const (classLog K x : ℂ))).const_mul
      (h x * chi x)).mul_const ((classLog K x : ℂ)^m)
    convert hd using 1
    simp [mellinMomentIntegrand, pow_succ]
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Filter.Eventually.of_forall (fun z => (hi z m).aestronglyMeasurable))
    (hi z₀ m) (hi z₀ (m+1)).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
    ((hh.integrable_of_hasCompactSupport hsupp).norm.const_mul _)
    (Filter.Eventually.of_forall (fun x z _ => hd x z))).2

theorem genuine_mellin_iteratedDeriv
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h chi : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : Continuous chi) (hsupp : HasCompactSupport h)
    (hu : ∀ x, ‖chi x‖ = 1) (m : ℕ) :
    ∀ z, iteratedDeriv m (fun w => ∫ x, mellinMomentIntegrand K h chi w 0 x ∂mu) z =
      ∫ x, mellinMomentIntegrand K h chi z m x ∂mu := by
  induction m with
  | zero => intro z; rfl
  | succ m hm =>
    intro z
    rw [iteratedDeriv_succ, funext hm]
    exact (genuine_mellin_moment_hasDerivAt K mu h chi hh hc hsupp hu z m).deriv

/-- Quantitative bound for the actual complex Mellin derivatives, retaining
R^m for unbounded interior multiplicities. No height decay is claimed. -/
theorem genuine_compact_mellin_derivative_bound
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hsupp : HasCompactSupport h) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (chi : HeckeIdeleClasses K → ℂ),
      Continuous chi → (∀ x, ‖chi x‖ = 1) → ∀ alpha : ℝ, 0 ≤ alpha →
      ∀ z : ℂ, |z.re| ≤ alpha → ∀ m : ℕ,
      ‖iteratedDeriv m (fun w => ∫ x, mellinMomentIntegrand K h chi w 0 x ∂mu) z‖ ≤
        (Real.exp (alpha*R) * R^m) * ∫ x, ‖h x‖ ∂mu := by
  obtain ⟨R, hR, hb⟩ := genuine_compact_interval_mellin_bound K mu h hh hsupp
  refine ⟨R, hR, ?_⟩
  intro chi hc hu alpha ha z hz m
  rw [genuine_mellin_iteratedDeriv K mu h chi hh hc hsupp hu m z]
  exact (hb chi hc hu alpha ha z hz m).2

end Round175G
#check Round175G.genuine_mellin_moment_hasDerivAt
#print axioms Round175G.genuine_mellin_moment_hasDerivAt

#check Round175G.genuine_mellin_iteratedDeriv
#print axioms Round175G.genuine_mellin_iteratedDeriv
#check Round175G.genuine_compact_mellin_derivative_bound
#print axioms Round175G.genuine_compact_mellin_derivative_bound
