import Mathlib
attribute [local instance] Classical.propDecidable

/- Exact reused arithmetic quotient/log definitions and continuity from nuclear B177.
No new credit is claimed for this retained component. -/
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

namespace ActualMeasuredActionC6
open MeasureTheory MasulloGRH Round166F Round175B SpectralRound11B
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

theorem actual_classCharacter_mul (chi : UnitaryHeckeCharacter K)
    (g y : HeckeIdeleClasses K) :
    classCharacter K chi (g*y) = classCharacter K chi g * classCharacter K chi y := by
  refine Quotient.inductionOn₂ g y ?_
  intro a b
  exact map_mul chi.character a b

theorem actual_jet_mul (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ)
    (m : ℕ) (g y : HeckeIdeleClasses K) :
    genuineMellinJet K chi z a m (g*y) =
      ∑ k ∈ Finset.range (m+1), genuineMellinJet K chi z a k g *
        genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ) := by
  simp only [genuineMellinJet, actual_classCharacter_mul, classLog_mul,
    Circle.coe_mul, Complex.ofReal_add, Complex.ofReal_pow, mul_add, Complex.exp_add]
  rw [add_pow]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The genuine idele-class Mellin jets satisfy the measured transpose action.
This discharges the algebraic and measured-moment part of the native flag premise.
Fubini with the original weighted convolution remains a separate attachment. -/
theorem actual_measured_jet_action (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a : ℝ)
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
    rw [actual_jet_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hp, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_mul_const _ _
  · intro k hk
    exact (hint k hk).mul_const _

/-- Every actual jet is continuous on the original quotient. -/
theorem actual_jet_continuous (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) :
    Continuous (genuineMellinJet K chi z a m) := by
  have hc : Continuous (fun x => (classCharacter K chi x : ℂ)) :=
    continuous_subtype_val.comp (classCharacter_continuous K chi)
  have hl := classLog_continuous K
  unfold genuineMellinJet
  fun_prop

/-- Compact original test kernels supply ALL measured jet moments on the same
locally finite quotient measure. Applies equally to the logged test kernel. -/
theorem actual_compact_jet_moment (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (z : ℂ) (a : ℝ) (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hsupp : HasCompactSupport h) (m : ℕ) :
    Integrable (fun g => h g * genuineMellinJet K chi z a m g) mu := by
  apply (hh.mul (actual_jet_continuous K chi z a m)).integrable_of_hasCompactSupport
  have hc : HasCompactSupport (fun g => genuineMellinJet K chi z a m g * h g) :=
    hsupp.mul_left
  simpa only [mul_comm] using hc

/-- Actual same-measure binomial action, with moment premises discharged for
continuous compactly supported kernels. No independent spectrum is specified. -/
theorem actual_compact_measured_jet_action (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (z : ℂ) (a : ℝ) (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hsupp : HasCompactSupport h)
    (m : ℕ) (y : HeckeIdeleClasses K) :
    (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  exact actual_measured_jet_action K chi mu z a h m
    (fun k _ => actual_compact_jet_moment K chi mu z a h hh hsupp k) y

/-- Multiplication by the original class logarithm preserves the compact test
hypotheses used by the measured action. This keeps the logged test in scope. -/
theorem actual_log_kernel_compact (h : HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hsupp : HasCompactSupport h) :
    Continuous (fun g => (classLog K g : ℂ) * h g) ∧
      HasCompactSupport (fun g => (classLog K g : ℂ) * h g) := by
  exact ⟨(Complex.continuous_ofReal.comp (classLog_continuous K)).mul hh,
    hsupp.mul_left⟩

#print axioms actual_jet_mul
#print axioms actual_measured_jet_action
#print axioms actual_jet_continuous
#print axioms actual_compact_jet_moment
#print axioms actual_compact_measured_jet_action
#print axioms actual_log_kernel_compact
end ActualMeasuredActionC6

set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace MasulloGRH.SpectralCycle6E
open Round166F SpectralRound11B
open Complex

/-- Differentiate the actual native kernel before justifying integral interchange. -/
theorem genuineMellinJet_hasDerivAt
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) (z : ℂ) :
    HasDerivAt (fun w : ℂ => genuineMellinJet K chi w a m x)
      (genuineMellinJet K chi z a (m+1) x) z := by
  have he := (((hasDerivAt_id z).sub_const (a : ℂ)).mul_const
    (classLog K x : ℂ)).cexp
  have hh := (he.const_mul (classCharacter K chi x : ℂ)).mul_const
    ((classLog K x ^ m : ℝ) : ℂ)
  convert hh using 1 <;> simp only [genuineMellinJet, one_mul, Complex.ofReal_pow, pow_succ, Complex.ofReal_mul, id_eq] <;> ring

/-- Every pointwise spectral derivative equals the next native logarithmic jet. -/
theorem genuineMellinJet_deriv
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    deriv (fun w : ℂ => genuineMellinJet K chi w a m x) =
      fun w => genuineMellinJet K chi w a (m+1) x := by
  funext z
  exact (genuineMellinJet_hasDerivAt K chi a m x z).deriv

theorem genuineMellinJet_iteratedDeriv
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (m n : ℕ) (x : HeckeIdeleClasses K) :
    iteratedDeriv n (fun w : ℂ => genuineMellinJet K chi w a m x) =
      fun w => genuineMellinJet K chi w a (m+n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, genuineMellinJet_deriv]
    simp only [Nat.add_assoc]

#print axioms genuineMellinJet_iteratedDeriv
#print axioms genuineMellinJet_hasDerivAt
#print axioms genuineMellinJet_deriv
end MasulloGRH.SpectralCycle6E

namespace MasulloGRH.SpectralCycle6E
open MeasureTheory Filter Round166F SpectralRound11B
open scoped Topology

theorem genuineMellinJet_norm_le
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (n : ℕ) (x : HeckeIdeleClasses K) (w : ℂ)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hw : ‖w - (a : ℂ)‖ ≤ B) (hx : |classLog K x| ≤ R) :
    ‖genuineMellinJet K chi w a n x‖ ≤ Real.exp (B*R) * R^n := by
  have he : ((w - (a : ℂ)) * (classLog K x : ℂ)).re ≤ B*R := by
    calc
      _ ≤ ‖(w - (a : ℂ)) * (classLog K x : ℂ)‖ := Complex.re_le_norm _
      _ = ‖w - (a : ℂ)‖ * |classLog K x| := by simp
      _ ≤ B*R := mul_le_mul hw hx (abs_nonneg _) hB
  calc
    ‖genuineMellinJet K chi w a n x‖ =
        Real.exp (((w - (a : ℂ)) * (classLog K x : ℂ)).re) * |classLog K x|^n := by
      simp [genuineMellinJet, norm_mul, Complex.norm_exp, norm_pow]
    _ ≤ Real.exp (B*R) * R^n := by gcongr

/-- Differentiation of the actual measured native Mellin transform.
The logarithm is bounded only where h is nonzero. No differentiation,
uniform derivative bound, or integrability of the jet is assumed. -/
theorem measuredMellin_hasDerivAt
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (hell : Measurable (classLog K))
    (hchi : Measurable (fun x => (classCharacter K chi x : ℂ)))
    (h : HeckeIdeleClasses K → ℂ) (hh : Integrable h mu)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ x, h x ≠ 0 → |classLog K x| ≤ R)
    (a : ℝ) (m : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ x, h x * genuineMellinJet K chi w a m x ∂mu)
      (∫ x, h x * genuineMellinJet K chi z a (m+1) x ∂mu) z := by
  let B : ℝ := ‖z - (a : ℂ)‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hmeas (w : ℂ) (n : ℕ) :
      AEStronglyMeasurable (fun x => h x * genuineMellinJet K chi w a n x) mu := by
    apply hh.aestronglyMeasurable.mul
    apply Measurable.aestronglyMeasurable
    unfold genuineMellinJet
    fun_prop
  have hb (w : ℂ) (n : ℕ) (hw : ‖w - (a : ℂ)‖ ≤ B) (x : HeckeIdeleClasses K) :
      ‖h x * genuineMellinJet K chi w a n x‖ ≤ ‖h x‖ * (Real.exp (B*R) * R^n) := by
    by_cases hx : h x = 0
    · simp [hx]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (genuineMellinJet_norm_le K chi a n x w B R hB hR hw (hsupp x hx)) (norm_nonneg _)
  have hz : ‖z - (a : ℂ)‖ ≤ B := by dsimp [B]; linarith
  have hint : Integrable (fun x => h x * genuineMellinJet K chi z a m x) mu :=
    (hh.norm.mul_const _).mono' (hmeas z m) (ae_of_all _ (hb z m hz))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z 1) (F' := fun w x => h x * genuineMellinJet K chi w a (m+1) x)
    (bound := fun x => ‖h x‖ * (Real.exp (B*R) * R^(m+1)))
    (Metric.ball_mem_nhds z (by norm_num))
    (Eventually.of_forall (fun w => hmeas w m)) hint (hmeas z (m+1))
    (ae_of_all _ (fun x w hw => ?_)) (hh.norm.mul_const _)
    (ae_of_all _ (fun x w _ => (genuineMellinJet_hasDerivAt K chi a m x w).const_mul (h x)))).2
  apply hb w (m+1)
  have hw' : ‖w-z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  calc
    ‖w - (a : ℂ)‖ = ‖(w-z) + (z-(a : ℂ))‖ := by congr 1; ring
    _ ≤ ‖w-z‖ + ‖z-(a : ℂ)‖ := norm_add_le _ _
    _ ≤ B := by dsimp [B]; linarith

#print axioms measuredMellin_hasDerivAt
end MasulloGRH.SpectralCycle6E

namespace MasulloGRH.SpectralCycle6E
open MeasureTheory Round166F SpectralRound11B

theorem measuredMellin_iteratedDeriv
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (hell : Measurable (classLog K))
    (hchi : Measurable (fun x => (classCharacter K chi x : ℂ)))
    (h : HeckeIdeleClasses K → ℂ) (hh : Integrable h mu)
    (R : ℝ) (hR : 0 ≤ R) (hsupp : ∀ x, h x ≠ 0 → |classLog K x| ≤ R)
    (a : ℝ) (m : ℕ) :
    iteratedDeriv m (fun w : ℂ => ∫ x, h x * genuineMellinJet K chi w a 0 x ∂mu) =
      (fun w => ∫ x, h x * genuineMellinJet K chi w a m x ∂mu) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (measuredMellin_hasDerivAt K chi mu hell hchi h hh R hR hsupp a m z).deriv
#print axioms measuredMellin_iteratedDeriv
end MasulloGRH.SpectralCycle6E

namespace MasulloGRH.SpectralCycle6E
open MeasureTheory Round166F Round175B SpectralRound11B ActualMeasuredActionC6

theorem actual_compact_measuredMellin_iteratedDeriv
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts mu]
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (a : ℝ) (m : ℕ) :
    iteratedDeriv m (fun w : ℂ => ∫ x, h x * genuineMellinJet K chi w a 0 x ∂mu) =
      (fun w => ∫ x, h x * genuineMellinJet K chi w a m x ∂mu) := by
  obtain ⟨R, hR⟩ := hs.exists_bound_of_continuousOn (classLog_continuous K).continuousOn
  apply measuredMellin_iteratedDeriv K chi mu (classLog_continuous K).measurable
    (continuous_subtype_val.comp (classCharacter_continuous K chi)).measurable
    h (hh.integrable_of_hasCompactSupport hs) (max R 0) (le_max_right _ _) _ a m
  intro x hx
  simpa only [Real.norm_eq_abs] using (hR x (subset_closure hx)).trans (le_max_left R 0)

#print axioms actual_compact_measuredMellin_iteratedDeriv
end MasulloGRH.SpectralCycle6E

/- Reused exact sharp transport from spectral_C, no independent novelty claimed. -/
namespace SpectralC903
open MeasureTheory MasulloGRH Round166F SpectralRound11B
variable (K : Type*) [Field K] [NumberField K]

/-- Exact original reverseTest definition, recorded in nuclear r142/C
leading-test-definitions.txt from the frozen Round129D source. -/
noncomputable def nativeSharp (phi : HeckeIdeleClasses K → ℂ)
    (g : HeckeIdeleClasses K) : ℂ := star (phi g⁻¹)

noncomputable def nativeLogKernel (phi : HeckeIdeleClasses K → ℂ)
    (g : HeckeIdeleClasses K) : ℂ := (classLog K g : ℂ) * phi g

theorem native_classLog_inv (g : HeckeIdeleClasses K) :
    classLog K g⁻¹ = -classLog K g := by
  have h1 := Round175B.classLog_mul K 1 1
  simp only [one_mul] at h1
  have hz : classLog K 1 = 0 := by linarith
  have hi := Round175B.classLog_mul K g g⁻¹
  rw [mul_inv_cancel, hz] at hi
  linarith

/-- The SECOND original leading kernel has a minus sign after reversal.
It is not log(g) times phi#; this discharges the precise # normalization. -/
theorem native_sharp_log (phi : HeckeIdeleClasses K → ℂ) :
    nativeSharp K (nativeLogKernel K phi) =
      fun g => -(classLog K g : ℂ) * nativeSharp K phi g := by
  funext g
  simp [nativeSharp, nativeLogKernel, native_classLog_inv]

theorem native_sharp_compact (phi : HeckeIdeleClasses K → ℂ)
    (hc : Continuous phi) (hs : HasCompactSupport phi) :
    Continuous (nativeSharp K phi) ∧ HasCompactSupport (nativeSharp K phi) := by
  refine ⟨hc.star.comp continuous_inv, ?_⟩
  exact (hs.comp_homeomorph (Homeomorph.inv (HeckeIdeleClasses K))).comp_left
    (show star (0 : ℂ) = 0 by simp)

#print axioms native_sharp_log
#print axioms native_sharp_compact
end SpectralC903

namespace MasulloGRH.SpectralCycle8E
open MeasureTheory Round166F SpectralRound11B SpectralCycle6E
open ActualMeasuredActionC6 SpectralC903
variable (K : Type*) [Field K] [NumberField K]

/-- Actual compact-kernel matrix coefficients in (10.3.1.17), on the same measure.
No differentiated-integral identity or moment assumption is retained. -/
theorem actual_compact_measured_action_derivatives
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    [IsFiniteMeasureOnCompacts mu] (a : ℝ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (m : ℕ) (z : ℂ) (y : HeckeIdeleClasses K) :
    (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        iteratedDeriv k (fun w => ∫ g, h g * genuineMellinJet K chi w a 0 g ∂mu) z *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ)) := by
  rw [actual_compact_measured_jet_action K chi mu z a h hh hs m y]
  apply Finset.sum_congr rfl
  intro k hk
  rw [actual_compact_measuredMellin_iteratedDeriv K chi mu h hh hs a k]

/-- Exact logarithmic leading kernel, including reversal sign and all derivatives.
This is (ell phi)#, not an independently chosen log-multiplied test. -/
theorem actual_sharp_log_mellin_coefficient
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    [IsFiniteMeasureOnCompacts mu] (a : ℝ)
    (phi : HeckeIdeleClasses K → ℂ)
    (hc : Continuous phi) (hs : HasCompactSupport phi) (m : ℕ) (z : ℂ) :
    (∫ g, nativeSharp K (nativeLogKernel K phi) g *
      genuineMellinJet K chi z a m g ∂mu) =
      -iteratedDeriv (m+1) (fun w => ∫ g,
        nativeSharp K phi g * genuineMellinJet K chi w a 0 g ∂mu) z := by
  obtain ⟨hh, hsp⟩ := native_sharp_compact K phi hc hs
  rw [actual_compact_measuredMellin_iteratedDeriv K chi mu
    (nativeSharp K phi) hh hsp a (m+1)]
  rw [native_sharp_log]
  have he : (fun g => -(classLog K g : ℂ) * nativeSharp K phi g *
      genuineMellinJet K chi z a m g) =
      (fun g => -(nativeSharp K phi g * genuineMellinJet K chi z a (m+1) g)) := by
    funext g
    simp only [genuineMellinJet, pow_succ, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [he, integral_neg]

#print axioms actual_compact_measured_action_derivatives
#print axioms actual_sharp_log_mellin_coefficient
end MasulloGRH.SpectralCycle8E
