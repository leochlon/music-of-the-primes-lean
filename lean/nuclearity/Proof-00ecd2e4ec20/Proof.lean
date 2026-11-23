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

namespace Round175B
open MasulloGRH Round166F MeasureTheory
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

/-- The squared-norm weight from (9.2.2.31), I=[-alpha,alpha]. -/
def nativeWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (2 * alpha * |t|) * (1 + t^2) ^ (s/2)

/-- A finite multiplier valid also at the identity, repairing (9.3.1.6). -/
def translationCost (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (2 * (1 + u^2)) ^ (s/2)

theorem nativeWeight_add_le (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (u t : ℝ) :
    nativeWeight alpha s (u+t) ≤
      translationCost alpha s u * nativeWeight alpha s t := by
  have hp : 1 + (u+t)^2 ≤ (2*(1+u^2)) * (1+t^2) := by
    nlinarith [sq_nonneg (u-t), mul_nonneg (sq_nonneg u) (sq_nonneg t)]
  have he : Real.exp (2*alpha*|u+t|) ≤
      Real.exp (2*alpha*|u|) * Real.exp (2*alpha*|t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_add_le u t]
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 1+(u+t)^2) hp
    (by positivity : 0 ≤ s/2)
  rw [Real.mul_rpow (by positivity) (by positivity)] at hr
  unfold nativeWeight translationCost
  calc
    _ ≤ (Real.exp (2*alpha*|u|) * Real.exp (2*alpha*|t|)) *
        ((2*(1+u^2))^(s/2) * (1+t^2)^(s/2)) :=
      mul_le_mul he hr (by positivity) (by positivity)
    _ = _ := by ring

/-- Actual native squared energy; infinite values are permitted in the definition. -/
def nativeEnergy (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ)
    (f : HeckeIdeleClasses K → ℂ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖f x‖^2 * nativeWeight alpha s (classLog K x)) ∂mu

/-- NATIVE_TRANSLATION_ENERGY: the actual-class Haar translation estimate
needed before completing the native translation action in (10.4.2.6).
This is not a nuclear estimate and imposes no spectral summability. -/
theorem genuine_native_translation_energy_le
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ) (hf : Measurable f)
    (g : HeckeIdeleClasses K) :
    nativeEnergy K mu alpha s (fun x => f (g⁻¹*x)) ≤
      ENNReal.ofReal (translationCost alpha s (classLog K g)) *
        nativeEnergy K mu alpha s f := by
  have hL := (classLog_continuous K).measurable
  have hm : Measurable (fun x => ENNReal.ofReal
      (‖f x‖^2 * nativeWeight alpha s (classLog K x))) := by
    unfold nativeWeight
    fun_prop
  have hc : 0 ≤ translationCost alpha s (classLog K g) := by
    unfold translationCost
    positivity
  unfold nativeEnergy
  rw [← lintegral_mul_left_eq_self
    (fun x => ENNReal.ofReal
      (‖f (g⁻¹*x)‖^2 * nativeWeight alpha s (classLog K x))) g]
  simp only [inv_mul_cancel_left]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (translationCost alpha s (classLog K g)) *
        ENNReal.ofReal (‖f x‖^2 * nativeWeight alpha s (classLog K x)) ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      rw [classLog_mul]
      have hb := mul_le_mul_of_nonneg_left
        (nativeWeight_add_le alpha s ha hs (classLog K g) (classLog K x))
        (sq_nonneg ‖f x‖)
      nlinarith only [hb]
    _ = _ := lintegral_const_mul _ hm

/-- In particular translation preserves finite native energy for all alpha,s>=0. -/
theorem genuine_native_translation_energy_finite
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ) (hf : Measurable f)
    (hfin : nativeEnergy K mu alpha s f < ∞) (g : HeckeIdeleClasses K) :
    nativeEnergy K mu alpha s (fun x => f (g⁻¹*x)) < ∞ := by
  apply lt_of_le_of_lt (genuine_native_translation_energy_le K mu alpha s ha hs f hf g)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin


/-- Compact tests give an integrable scalar majorant for the Bochner action.
The native completion/action and its strong continuity remain to be attached. -/
theorem genuine_native_convolution_majorant_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (alpha s : ℝ) (hs : 0 ≤ s) (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun g => ‖h g‖ *
      Real.sqrt (translationCost alpha s (classLog K g))) mu := by
  have hL := classLog_continuous K
  have hs2 : 0 ≤ s/2 := by positivity
  have hcont : Continuous (fun g => ‖h g‖ *
      Real.sqrt (translationCost alpha s (classLog K g))) := by
    unfold translationCost
    fun_prop (disch := positivity)
  apply hcont.integrable_of_hasCompactSupport
  apply hc.mono
  intro g hg
  change h g ≠ 0
  intro he
  exact hg (by simp [he])

end Round175B
#check Round175B.genuine_native_translation_energy_le
#print axioms Round175B.genuine_native_translation_energy_le
#check Round175B.genuine_native_translation_energy_finite
#print axioms Round175B.genuine_native_translation_energy_finite
#check Round175B.classLog_mul
#print axioms Round175B.classLog_mul

#check Round175B.genuine_native_convolution_majorant_integrable
#print axioms Round175B.genuine_native_convolution_majorant_integrable


namespace Round176B
open MasulloGRH Round166F Round175B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The actual-class Bochner integrability premise in (10.4.2.6).
Orbit measurability and the completed native translation bound are explicit
remaining attachment hypotheses; no nuclear summability is assumed. -/
theorem genuine_class_convolution_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (alpha s : ℝ) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (T : HeckeIdeleClasses K → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun g => T g x) mu)
    (hT : ∀ g x, ‖T g x‖ ≤
      Real.sqrt (translationCost alpha s (classLog K g)) * ‖x‖)
    (x : H) : Integrable (fun g => h g • T g x) mu := by
  have hi := (genuine_native_convolution_majorant_integrable K mu alpha s hs h hh hc).mul_const ‖x‖
  apply hi.mono' (hh.aestronglyMeasurable.smul (hm x))
  exact Filter.Eventually.of_forall (fun g => by
    rw [norm_smul]
    calc
      ‖h g‖ * ‖T g x‖ ≤ ‖h g‖ *
          (Real.sqrt (translationCost alpha s (classLog K g)) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hT g x) (norm_nonneg _)
      _ = _ := by ring)

/-- Pointwise logarithmic multiplication preserves the compact-test majorant.
This uses the actual class logarithm, and does not confuse it with convolution. -/
theorem genuine_pointwise_log_majorant_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (alpha s : ℝ) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun g => ‖(classLog K g : ℂ) * h g‖ *
      Real.sqrt (translationCost alpha s (classLog K g))) mu := by
  apply genuine_native_convolution_majorant_integrable K mu alpha s hs
  · have hL := classLog_continuous K
    fun_prop
  · apply hc.mono
    intro g hg
    change h g ≠ 0
    intro he
    exact hg (by simp [he])
end Round176B
#check Round176B.genuine_class_convolution_integrable
#print axioms Round176B.genuine_class_convolution_integrable
#check Round176B.genuine_pointwise_log_majorant_integrable
#print axioms Round176B.genuine_pointwise_log_majorant_integrable


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


/- Named premise of manuscript (10.4.2.5), lines 27711--27728:
   closed geometric translation invariance passes to Bochner convolution.
   No nuclearity, nuclear cost, or spectral summability is assumed here.
   Native adelic attachment remains a separate, explicitly open obligation. -/
open MeasureTheory
open scoped ENNReal
namespace Round173B
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Closed-subspace invariance for the actual order: convolution first. -/
theorem convolution_mem (G : Submodule ℂ H) [CompleteSpace G]
    (μ : Measure X) (T : X → H →L[ℂ] H) (h : X → ℂ)
    (hinv : ∀ t x, x ∈ G → T t x ∈ G)
    (x : H) (hx : x ∈ G)
    (hint : Integrable (fun t => h t • T t x) μ) :
    (∫ t, h t • T t x ∂μ) ∈ G := by
  let P : H →L[ℂ] H := ContinuousLinearMap.id ℂ H -
    G.subtypeL.comp G.orthogonalProjection
  have hp : ∀ v : H, v ∈ G → P v = 0 := by
    intro v hv
    change v - (G.orthogonalProjection v : H) = 0
    have he := Submodule.orthogonalProjection_mem_subspace_eq_self (⟨v, hv⟩ : G)
    rw [he]
    exact sub_self v
  have hz : ∀ t, P (h t • T t x) = 0 := by
    intro t
    exact hp _ (G.smul_mem _ (hinv t x hx))
  have hi : P (∫ t, h t • T t x ∂μ) = 0 := by
    rw [← P.integral_comp_comm hint]
    simp only [hz, integral_zero]
  change (∫ t, h t • T t x ∂μ) -
    (G.orthogonalProjection (∫ t, h t • T t x ∂μ) : H) = 0 at hi
  rw [sub_eq_zero.mp hi]
  exact (G.orthogonalProjection _).property

/-- Construct the quotient action from invariance, rather than assuming it. -/
theorem convolution_quotient_intertwining
    (G : Submodule ℂ H) [CompleteSpace G]
    (μ : Measure X) (T : X → H →L[ℂ] H) (h : X → ℂ)
    (hinv : ∀ t x, x ∈ G → T t x ∈ G)
    (A : H →L[ℂ] H)
    (hA : ∀ x, A x = ∫ t, h t • T t x ∂μ)
    (hint : ∀ x, Integrable (fun t => h t • T t x) μ) :
    ∃ B : (H ⧸ G) →ₗ[ℂ] (H ⧸ G),
      ∀ x, B (G.mkQ x) = G.mkQ (A x) := by
  have hi : G ≤ G.comap A.toLinearMap := by
    intro x hx
    change A x ∈ G
    rw [hA]
    exact convolution_mem G μ T h hinv x hx (hint x)
  exact ⟨G.mapQ G A.toLinearMap hi, fun x => rfl⟩
/-- The genuine complement projector, with codomain the ambient Hilbert space. -/
noncomputable def spectralProjection (G : Submodule ℂ H) [CompleteSpace G] :
    H →L[ℂ] H := ContinuousLinearMap.id ℂ H - G.subtypeL.comp G.orthogonalProjection

/-- Algebraic quotient factorization (10.4.2.5), constructing both quotient maps.
    Boundedness/isometry of S and nuclearity of B are not claimed by this theorem. -/
theorem projected_convolution_factors
    (G : Submodule ℂ H) [CompleteSpace G]
    (μ : Measure X) (T : X → H →L[ℂ] H) (h : X → ℂ)
    (hinv : ∀ t x, x ∈ G → T t x ∈ G)
    (A : H →L[ℂ] H)
    (hA : ∀ x, A x = ∫ t, h t • T t x ∂μ)
    (hint : ∀ x, Integrable (fun t => h t • T t x) μ) :
    ∃ B : (H ⧸ G) →ₗ[ℂ] (H ⧸ G), ∃ S : (H ⧸ G) →ₗ[ℂ] H,
      (∀ x, B (G.mkQ x) = G.mkQ (A x)) ∧
      (∀ x, S (G.mkQ x) = spectralProjection G x) ∧
      (∀ x, spectralProjection G (A x) = S (B (G.mkQ x))) := by
  obtain ⟨B, hB⟩ := convolution_quotient_intertwining G μ T h hinv A hA hint
  have hk : G ≤ (spectralProjection G).toLinearMap.ker := by
    intro v hv
    change v - (G.orthogonalProjection v : H) = 0
    have he := Submodule.orthogonalProjection_mem_subspace_eq_self (⟨v, hv⟩ : G)
    rw [he]
    exact sub_self v
  refine ⟨B, G.liftQ (spectralProjection G).toLinearMap hk, hB, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rw [hB x]
    rfl
end Round173B
#check Round173B.convolution_mem
#print axioms Round173B.convolution_mem
#check Round173B.convolution_quotient_intertwining
#print axioms Round173B.convolution_quotient_intertwining

#check Round173B.projected_convolution_factors
#print axioms Round173B.projected_convolution_factors

namespace Round175H
open Round173A
open scoped ENNReal
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- Pullback by the canonical quotient preserves the actual functional norm. -/
theorem quotient_functional_norm (f : (H ⧸ G) →L[ℂ] ℂ) :
    ‖f.comp (Q G)‖ = ‖f‖ := by
  apply le_antisymm
  · calc
      _ ≤ ‖f‖ * ‖Q G‖ := f.opNorm_comp_le (Q G)
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) (norm_nonneg f)
      _ = _ := mul_one _
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro q
    calc
      ‖f q‖ = ‖(f.comp (Q G)) (S G q)‖ := by
        rw [ContinuousLinearMap.comp_apply, Q_S]
      _ ≤ ‖f.comp (Q G)‖ * ‖S G q‖ := (f.comp (Q G)).le_opNorm _
      _ = ‖f.comp (Q G)‖ * ‖q‖ := by rw [S_isometry]

/-- An extended representation cost; infinity is explicitly allowed. -/
def seriesCost {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℕ → E →L[ℂ] ℂ) (v : ℕ → E) : ℝ≥0∞ :=
  ∑' n, ENNReal.ofReal (‖f n‖ * ‖v n‖)

/-- No loss of rank-one nuclear cost through the actual quotient/section.
This does not assert that the common cost is finite. -/
theorem canonical_quotient_series_cost (f : ℕ → (H ⧸ G) →L[ℂ] ℂ)
    (v : ℕ → H ⧸ G) :
    seriesCost (fun n => (f n).comp (Q G)) (fun n => S G (v n)) =
      seriesCost f v := by
  unfold seriesCost
  apply tsum_congr
  intro n
  rw [quotient_functional_norm, S_isometry]

/-- Pointwise reconstruction in convolution-first order. The expansion
hypothesis supplies an operator identity but no finite nuclear cost. -/
theorem canonical_quotient_projected_series
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G)
    (f : ℕ → (H ⧸ G) →L[ℂ] ℂ) (v : ℕ → H ⧸ G)
    (hrep : ∀ q, HasSum (fun n => f n q • v n) (Abar G A q)) (x : H) :
    HasSum (fun n => ((f n).comp (Q G)) x • S G (v n))
      (Gᗮ.starProjection (A x)) := by
  have hh := (S G).hasSum (hrep (Q G x))
  simpa only [map_smul, Abar_Q G A hA, S_Q, ContinuousLinearMap.comp_apply] using hh

/-- Infimum of explicit countable nuclear representation costs. This extended
quantity is allowed to be infinite; no library trace-norm identification is
asserted here. A finite value must still be derived for the actual operator. -/
def nuclearRepresentationCost {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ⨅ (f : ℕ → E →L[ℂ] ℂ) (v : ℕ → E)
    (_ : ∀ x, HasSum (fun n => f n x • v n) (T x)), seriesCost f v

/-- The abstract bounded-composition cost premise of (10.4.2.5), without
assuming nuclearity, finiteness or any summability of the quotient operator.
The actual native attachment and finite right hand side remain unproved. -/
theorem canonical_projected_nuclear_cost_le
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) :
    nuclearRepresentationCost (Gᗮ.starProjection.comp A) ≤
      nuclearRepresentationCost (Abar G A) := by
  unfold nuclearRepresentationCost
  refine le_iInf fun f => le_iInf fun v => le_iInf fun hrep => ?_
  refine iInf_le_of_le (fun n => (f n).comp (Q G)) ?_
  refine iInf_le_of_le (fun n => S G (v n)) ?_
  refine iInf_le_of_le (canonical_quotient_projected_series G A hA f v hrep) ?_
  exact le_of_eq (canonical_quotient_series_cost G f v)

end Round175H
#check Round175H.quotient_functional_norm
#print axioms Round175H.quotient_functional_norm
#check Round175H.canonical_quotient_series_cost
#print axioms Round175H.canonical_quotient_series_cost

#check Round175H.canonical_quotient_projected_series
#print axioms Round175H.canonical_quotient_projected_series

#check Round175H.canonical_projected_nuclear_cost_le
#print axioms Round175H.canonical_projected_nuclear_cost_le


namespace Round177B
open MasulloGRH Round166F Round175B Round176B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- CONSTRUCTED_CONVOLUTION_AND_INDUCED_ACTION: removes the supplied A and
integrability assumptions from the (10.4.2.5) attachment. The native completed
translation action and its geometric invariance remain explicit hypotheses.
This is an operator-construction premise, not a finite nuclear bound. -/
theorem genuine_class_convolution_quotient
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (alpha s : ℝ) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (T : HeckeIdeleClasses K → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun g => T g x) mu)
    (hT : ∀ g x, ‖T g x‖ ≤
      Real.sqrt (translationCost alpha s (classLog K g)) * ‖x‖)
    (G : Submodule ℂ H) [CompleteSpace G]
    (hinv : ∀ g x, x ∈ G → T g x ∈ G) :
    ∃ A : H →L[ℂ] H,
      (∀ x, A x = ∫ g, h g • T g x ∂mu) ∧
      ‖A‖ ≤ (∫ g, ‖h g‖ * Real.sqrt
        (translationCost alpha s (classLog K g)) ∂mu) ∧
      (∀ x ∈ G, A x ∈ G) ∧
      (∀ x, Round173A.Abar G A (Round173A.Q G x) = Round173A.Q G (A x)) ∧
      Gᗮ.starProjection.comp A = (Round173A.S G).comp
        ((Round173A.Abar G A).comp (Round173A.Q G)) ∧
      Round175H.nuclearRepresentationCost (Gᗮ.starProjection.comp A) ≤
        Round175H.nuclearRepresentationCost (Round173A.Abar G A) := by
  have hi := genuine_class_convolution_integrable K mu alpha s hs h hh hc T hm hT
  let c : HeckeIdeleClasses K → ℝ := fun g =>
    ‖h g‖ * Real.sqrt (translationCost alpha s (classLog K g))
  have hci : Integrable c mu :=
    genuine_native_convolution_majorant_integrable K mu alpha s hs h hh hc
  let C : ℝ := ∫ g, c g ∂mu
  have hC : 0 ≤ C := integral_nonneg (fun g => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  let L : H →ₗ[ℂ] H :=
    { toFun := fun x => ∫ g, h g • T g x ∂mu
      map_add' := by
        intro x y
        simp only [map_add, smul_add]
        exact integral_add (hi x) (hi y)
      map_smul' := by
        intro z x
        simp only [map_smul, smul_comm (h _) z]
        exact integral_smul z (fun g => h g • T g x) }
  have hL (x : H) : ‖L x‖ ≤ C * ‖x‖ := by
    change ‖∫ g, h g • T g x ∂mu‖ ≤ C * ‖x‖
    calc
      _ ≤ ∫ g, ‖h g • T g x‖ ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ g, c g * ‖x‖ ∂mu := by
        apply integral_mono (hi x).norm (hci.mul_const ‖x‖)
        intro g
        dsimp only
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left (hT g x) (norm_nonneg _)).trans_eq
          (by dsimp [c]; ring)
      _ = C * ‖x‖ := integral_mul_const _ _
  let A : H →L[ℂ] H := L.mkContinuous C hL
  have hA (x : H) : A x = ∫ g, h g • T g x ∂mu := rfl
  have hAG : ∀ x ∈ G, A x ∈ G := by
    intro x hx
    rw [hA]
    exact Round173B.convolution_mem G mu T h hinv x hx (hi x)
  refine ⟨A, hA, ?_, hAG, Round173A.Abar_Q G A hAG, ?_, ?_⟩
  · exact LinearMap.mkContinuous_norm_le _ hC hL
  · exact (Round173A.bounded_quotient_factorisation G A hAG).1
  · exact Round175H.canonical_projected_nuclear_cost_le G A hAG
end Round177B
#check Round177B.genuine_class_convolution_quotient
#print axioms Round177B.genuine_class_convolution_quotient

/-! R179B: COMPLETED_QUOTIENT_JET_ACTION, manuscript (10.3.1.8)--(10.3.1.14).
Extend translation jet identities from a dense native test subspace and derive
 the action of the constructed quotient convolution. This is operator
identification, not a nuclear bound. Native continuous jets remain to attach. -/
namespace Round179B
open MasulloGRH Round166F Round175B Round176B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def jetKernel (chi : HeckeIdeleClasses K → ℂ) (z : ℂ) (i : ℕ)
    (g : HeckeIdeleClasses K) : ℂ :=
  chi g * Complex.exp (z * (classLog K g : ℂ)) * (classLog K g : ℂ)^i

/-- The integrated quotient action is DERIVED from identities on a dense
subspace, without assuming an action formula for Abar or any nuclear cost. -/
theorem completed_quotient_jet_action
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (alpha s : ℝ) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (T : HeckeIdeleClasses K → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun g => T g x) mu)
    (hT : ∀ g x, ‖T g x‖ ≤ Real.sqrt (translationCost alpha s (classLog K g)) * ‖x‖)
    (G : Submodule ℂ H) [CompleteSpace G]
    (hinv : ∀ g x, x ∈ G → T g x ∈ G)
    (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ)
    (chi : HeckeIdeleClasses K → ℂ) (hchi : Continuous chi) (z : ℂ)
    (D : Set H) (hD : Dense D)
    (hjet : ∀ g m x, x ∈ D →
      eta m (Round173A.Q G (T g x)) =
        ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) * jetKernel K chi z i g *
          eta (m-i) (Round173A.Q G x)) :
    ∃ A : H →L[ℂ] H,
      (∀ x, A x = ∫ g, h g • T g x ∂mu) ∧
      (∀ x ∈ G, A x ∈ G) ∧
      Gᗮ.starProjection.comp A = (Round173A.S G).comp
        ((Round173A.Abar G A).comp (Round173A.Q G)) ∧
      ∀ q m, eta m (Round173A.Abar G A q) =
        ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
          (∫ g, h g * jetKernel K chi z i g ∂mu) * eta (m-i) q := by
  obtain ⟨A, hA, _, hAG, hAQ, hfac, _⟩ :=
    Round177B.genuine_class_convolution_quotient K mu alpha s hs h hh hc T hm hT G hinv
  have hj (g) (m) (x : H) : eta m (Round173A.Q G (T g x)) =
      ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) * jetKernel K chi z i g *
        eta (m-i) (Round173A.Q G x) := by
    have he := Continuous.ext_on hD
      (show Continuous (fun y : H => eta m (Round173A.Q G (T g y))) by fun_prop)
      (show Continuous (fun y : H => ∑ i ∈ Finset.range (m+1),
        (m.choose i : ℂ) * jetKernel K chi z i g *
          eta (m-i) (Round173A.Q G y)) by fun_prop)
      (fun y hy => hjet g m y hy)
    exact congrFun he x
  have hi := genuine_class_convolution_integrable K mu alpha s hs h hh hc T hm hT
  have hcj (i : ℕ) : Integrable (fun g => h g * jetKernel K chi z i g) mu := by
    have hl := classLog_continuous K
    have hjc : Continuous (jetKernel K chi z i) := by unfold jetKernel; fun_prop
    apply (hh.mul hjc).integrable_of_hasCompactSupport
    apply hc.mono
    intro g hg
    exact left_ne_zero_of_mul hg
  have hp (x : H) (m : ℕ) : eta m (Round173A.Q G (A x)) =
      ∑ i ∈ Finset.range (m+1), (m.choose i : ℂ) *
        (∫ g, h g * jetKernel K chi z i g ∂mu) * eta (m-i) (Round173A.Q G x) := by
    calc
      _ = ∫ g, eta m (Round173A.Q G (h g • T g x)) ∂mu := by
        change ((eta m).comp (Round173A.Q G)) (A x) = _
        rw [hA x, ← ContinuousLinearMap.integral_comp_comm _ (hi x)]
        rfl
      _ = ∫ g, ∑ i ∈ Finset.range (m+1),
          (m.choose i : ℂ) * (h g * jetKernel K chi z i g) *
            eta (m-i) (Round173A.Q G x) ∂mu := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun g => by
          simp only [map_smul, smul_eq_mul, hj, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring)
      _ = _ := by
        rw [integral_finset_sum _ (fun i _ =>
          ((hcj i).const_mul (m.choose i : ℂ)).mul_const _)]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_mul_const, integral_const_mul]
  refine ⟨A, hA, hAG, hfac, ?_⟩
  intro q m
  have hpq := hp (Round173A.S G q) m
  rw [← hAQ (Round173A.S G q), Round173A.Q_S] at hpq
  simpa only [Round173A.Q_S] using hpq

end Round179B
#check Round179B.completed_quotient_jet_action
#print axioms Round179B.completed_quotient_jet_action
