import Mathlib
set_option maxHeartbeats 600000
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

noncomputable section
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
end
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

end Round175B
end
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- Exact character structure from the checked finite-idelic foundation. -/
structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

/-- Descend the actual character; no spectrum or zero set is prescribed. -/
noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K → Circle :=
  Quotient.lift χ.character (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, map_mul, χ.trivial_on_principal, one_mul])

theorem classCharacter_continuous (χ : UnitaryHeckeCharacter K) :
    Continuous (classCharacter K χ) := χ.character.continuous.quotient_lift _

/-- Definition bridge to the same idelic character as the Euler germ. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (x : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk x) = χ.character x := rfl
end MasulloGRH
namespace SpectralRound11B
open MasulloGRH Round166F
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

end SpectralRound11B

namespace ActualMeasuredJetD
open MeasureTheory MasulloGRH Round166F SpectralRound11B
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

theorem classCharacter_mul_actual (chi : UnitaryHeckeCharacter K)
    (g y : HeckeIdeleClasses K) :
    classCharacter K chi (g*y) = classCharacter K chi g * classCharacter K chi y := by
  refine Quotient.inductionOn₂ g y ?_
  intro u v
  change chi.character (u*v) = chi.character u * chi.character v
  exact map_mul chi.character u v

/-- Actual idele-class Mellin jets, with the original character and log norm.
This discharges the pointwise binomial-action premise, not weighted Fubini. -/
theorem actual_jet_translate (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (g y : HeckeIdeleClasses K) :
    genuineMellinJet K chi z a m (g*y) =
      ∑ k ∈ Finset.range (m+1), genuineMellinJet K chi z a k g *
        (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  simp only [genuineMellinJet, classCharacter_mul_actual, Round175B.classLog_mul,
    Complex.ofReal_pow, Complex.ofReal_add, Circle.coe_mul, mul_add, Complex.exp_add]
  rw [add_pow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The SAME measure appears in every term. The native application sets mu
exactly to the original quotient Haar and h to either admitted test family. -/
theorem actual_measured_jet_action (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (m : ℕ)
    (hint : ∀ k ∈ Finset.range (m+1),
      Integrable (fun g => h g * genuineMellinJet K chi z a k g) mu)
    (y : HeckeIdeleClasses K) :
    (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  have hp : (fun g => h g * genuineMellinJet K chi z a m (g*y)) =
      (fun g => ∑ k ∈ Finset.range (m+1),
        (h g * genuineMellinJet K chi z a k g) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ))) := by
    funext g
    rw [actual_jet_translate, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hp, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_mul_const _ _
  · intro k hk
    exact (hint k hk).mul_const _

#print axioms actual_jet_translate
#print axioms actual_measured_jet_action

/-- Continuity is proved for the original arithmetic kernel itself. -/
theorem actual_jet_continuous (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) :
    Continuous (genuineMellinJet K chi z a m) := by
  have hl := Round175B.classLog_continuous K
  have hc := classCharacter_continuous K chi
  unfold genuineMellinJet
  fun_prop

/-- Compact native tests discharge every moment integrability premise. -/
theorem actual_compact_moment_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h)
    (hs : HasCompactSupport h) (m : ℕ) :
    Integrable (fun g => h g * genuineMellinJet K chi z a m g) mu := by
  exact (hh.mul (actual_jet_continuous K chi z a m)).integrable_of_hasCompactSupport
    hs.mul_right

/-- Native compact-kernel translation action with no separate moment premise.
This is the measured transpose kernel; weighted Fubini into A(h) is separate. -/
theorem actual_compact_measured_jet_action
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h)
    (hs : HasCompactSupport h) (m : ℕ) (y : HeckeIdeleClasses K) :
    (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  exact actual_measured_jet_action K mu chi z a h m
    (fun k _ => actual_compact_moment_integrable K mu chi z a h hh hs k) y

/-- Pointwise log multiplication preserves the compact-test hypotheses. -/
theorem actual_logged_compact_moment_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h)
    (hs : HasCompactSupport h) (m : ℕ) :
    Integrable (fun g => ((classLog K g : ℂ) * h g) *
      genuineMellinJet K chi z a m g) mu := by
  apply actual_compact_moment_integrable K mu chi z a
  · exact (Complex.continuous_ofReal.comp (Round175B.classLog_continuous K)).mul hh
  · exact hs.mul_left

#print axioms actual_jet_continuous
#print axioms actual_compact_moment_integrable
#print axioms actual_compact_measured_jet_action
#print axioms actual_logged_compact_moment_integrable

end ActualMeasuredJetD

namespace Round175B
noncomputable def nativeWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (2 * alpha * |t|) * (1 + t^2) ^ (s/2)
end Round175B
namespace SpectralRound9B
open MasulloGRH Round166F
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)


end SpectralRound9B
namespace SpectralRound11B
open MasulloGRH Round166F SpectralRound9B
noncomputable def nativeHalfWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (alpha * |t|) * (1 + t^2) ^ (s/4)

theorem nativeHalfWeight_pos (alpha s t : ℝ) :
    0 < nativeHalfWeight alpha s t := by
  unfold nativeHalfWeight
  positivity

theorem nativeHalfWeight_sq (alpha s t : ℝ) :
    nativeHalfWeight alpha s t ^ 2 = Round175B.nativeWeight alpha s t := by
  have he : Real.exp (alpha * |t|) ^ 2 = Real.exp (2 * alpha * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp : ((1+t^2)^(s/4))^2 = (1+t^2)^(s/2) := by
    rw [pow_two, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
    congr 1
    ring
  unfold nativeHalfWeight Round175B.nativeWeight
  rw [mul_pow, he, hp]

theorem genuineMellinJet_normalization
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    genuineNormalizedMellinJet K chi z a s alpha m x *
      (nativeHalfWeight alpha s (classLog K x) : ℂ) =
      genuineMellinJet K chi z a m x := by
  let t := classLog K x
  have hp : (((1+t^2)^(-s/4) : ℝ) : ℂ) *
      (((1+t^2)^(s/4) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
    simp [show -s/4+s/4 = 0 by ring]
  have he : Complex.exp ((z - (a : ℂ)) * (t : ℂ) -
      ((alpha * |t| : ℝ) : ℂ)) * (Real.exp (alpha * |t|) : ℂ) =
      Complex.exp ((z - (a : ℂ)) * (t : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, sub_add_cancel]
  simp only [Complex.ofReal_mul] at he
  simp only [genuineNormalizedMellinJet, nativeHalfWeight, genuineMellinJet,
    Complex.ofReal_mul]
  change ((classCharacter K chi x : ℂ) *
      Complex.exp ((z-(a:ℂ))*(t:ℂ)-((alpha:ℂ)*((|t|:ℝ):ℂ))) *
      (((t^m:ℝ):ℂ) * (((1+t^2)^(-s/4):ℝ):ℂ))) *
      ((Real.exp (alpha*|t|):ℂ) * (((1+t^2)^(s/4):ℝ):ℂ)) = _
  calc
    _ = ((classCharacter K chi x : ℂ) *
      (Complex.exp ((z-(a:ℂ))*(t:ℂ)-((alpha:ℂ)*((|t|:ℝ):ℂ))) *
        (Real.exp (alpha*|t|):ℂ)) * ((t^m:ℝ):ℂ)) *
      ((((1+t^2)^(-s/4):ℝ):ℂ) * (((1+t^2)^(s/4):ℝ):ℂ)) := by ring
    _ = _ := by rw [he, hp, mul_one]


end SpectralRound11B
namespace SpectralRound12B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound11B
theorem native_pairing_integrable
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun x => genuineMellinJet K chi z a m x * f x) mu := by
  have hi := hg.integrable_mul hF
  change Integrable (fun x => genuineNormalizedMellinJet K chi z a s alpha m x *
    ((nativeHalfWeight alpha s (classLog K x) : ℂ) * f x)) mu at hi
  have he : (fun x => genuineNormalizedMellinJet K chi z a s alpha m x *
      ((nativeHalfWeight alpha s (classLog K x) : ℂ) * f x)) =
      (fun x => genuineMellinJet K chi z a m x * f x) := by
    funext x
    rw [← mul_assoc, genuineMellinJet_normalization]
  rwa [he] at hi


end SpectralRound12B
namespace NativeConvolutionFubiniD
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound11B
open ActualMeasuredJetD SpectralRound12B
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

/-- Absolute integrability of the actual translated jet against a compact kernel
and a native weighted vector. This supplies the previously absent Fubini premise
in the proof of manuscript (10.3.1.8), with the very same quotient measure. -/
theorem native_translated_product_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m (p.1 * p.2) * f p.2) (mu.prod mu) := by
  have he : (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m (p.1 * p.2) * f p.2) =
    (fun p => ∑ k ∈ Finset.range (m+1),
      ((h p.1 * genuineMellinJet K chi z a k p.1) *
        (genuineMellinJet K chi z a (m-k) p.2 * f p.2)) * (m.choose k : ℂ)) := by
    funext p
    rw [actual_jet_translate, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  apply integrable_finset_sum
  intro k hk
  exact ((actual_compact_moment_integrable K mu chi z a h hh hs k).mul_prod
    (native_pairing_integrable K chi mu z a s alpha (m-k)
      (hg (m-k) (Nat.sub_le _ _)) f hf)).mul_const _

theorem native_translated_fubini
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ g, ∫ y, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu) =
      ∫ y, ∫ g, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu := by
  exact integral_integral_swap
    (native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf)

#print axioms native_translated_product_integrable
#print axioms native_translated_fubini

/-- The actual convolution integrand is absolutely integrable, by the
measure-preserving Haar shear, not by an assumed Fubini premise. -/
theorem native_convolution_product_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      genuineMellinJet K chi z a m p.2 * (h p.1 * f (p.1⁻¹*p.2))) (mu.prod mu) := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  have hp : MeasurePreserving
      (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => (p.1, p.1⁻¹*p.2))
      (mu.prod mu) (mu.prod mu) :=
    (MeasurePreserving.id mu).skew_product (measurable_fst.inv.mul measurable_snd)
      (Filter.Eventually.of_forall (fun g =>
        Measure.IsMulLeftInvariant.map_mul_left_eq_self g⁻¹))
  have ht := (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  apply ht.congr
  exact Filter.Eventually.of_forall (fun p => by
    simp only [Function.comp_apply, mul_inv_cancel_left]
    ring)

/-- Original convolution first: its genuine Mellin pairing is the translated
pairing on the same Haar. Joint integrability is proved above for native vectors. -/
theorem native_convolution_pairing
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, genuineMellinJet K chi z a m x * (∫ g, h g * f (g⁻¹*x) ∂mu) ∂mu) =
      ∫ g, ∫ y, genuineMellinJet K chi z a m (g*y) * (h g * f y) ∂mu ∂mu := by
  simp only [← integral_const_mul]
  rw [← integral_integral_swap
    (native_convolution_product_integrable K mu chi z a s alpha m h f hh hs hg hf)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun g => by
    have he := integral_mul_left_eq_self (μ := mu)
      (fun x => genuineMellinJet K chi z a m x * (h g * f (g⁻¹*x))) g
    simpa only [inv_mul_cancel_left] using he.symm)

#print axioms native_convolution_product_integrable
#print axioms native_convolution_pairing
end NativeConvolutionFubiniD

namespace FollowupF633
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound11B
open ActualMeasuredJetD SpectralRound12B NativeConvolutionFubiniD
variable (K : Type*) [Field K] [NumberField K]

/-- Manuscript 10.3.1.8--13 for the actual measured convolution and a native
weighted vector. The finite moment action is derived, not assumed. -/
theorem native_weighted_convolution_moments
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, genuineMellinJet K chi z a m x * (∫ g, h g * f (g⁻¹*x) ∂mu) ∂mu) =
      ∑ k ∈ Finset.range (m+1), (m.choose k : ℂ) *
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
        (∫ y, genuineMellinJet K chi z a (m-k) y * f y ∂mu) := by
  rw [native_convolution_pairing K mu chi z a s alpha m h f hh hs hg hf]
  have he (g : HeckeIdeleClasses K) :
      (fun y => genuineMellinJet K chi z a m (g*y) * (h g * f y)) =
      (fun y => ∑ k ∈ Finset.range (m+1),
        ((m.choose k : ℂ) * (h g * genuineMellinJet K chi z a k g)) *
          (genuineMellinJet K chi z a (m-k) y * f y)) := by
    funext y
    rw [actual_jet_translate, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [he]
  have hi (k : ℕ) : Integrable
      (fun y => genuineMellinJet K chi z a (m-k) y * f y) mu :=
    native_pairing_integrable K chi mu z a s alpha (m-k)
      (hg (m-k) (Nat.sub_le _ _)) f hf
  have hinner (g : HeckeIdeleClasses K) :
      (∫ y, ∑ k ∈ Finset.range (m+1),
        ((m.choose k : ℂ) * (h g * genuineMellinJet K chi z a k g)) *
          (genuineMellinJet K chi z a (m-k) y * f y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        ((m.choose k : ℂ) * (h g * genuineMellinJet K chi z a k g)) *
          (∫ y, genuineMellinJet K chi z a (m-k) y * f y ∂mu) := by
    rw [integral_finset_sum _ (fun k _ => (hi k).const_mul _)]
    simp only [integral_const_mul]
  simp_rw [hinner]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_mul_const, integral_const_mul]
  · intro k hk
    exact ((actual_compact_moment_integrable K mu chi z a h hh hs k).const_mul
      (m.choose k : ℂ)).mul_const _

#print axioms native_weighted_convolution_moments
end FollowupF633
