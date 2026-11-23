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

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

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

namespace Masullo.GenuineMellinJet
open MasulloGRH Masullo.IdeleClassGeometry
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

end Masullo.GenuineMellinJet

namespace Masullo.ClassCharacterMul
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
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
end Masullo.ClassCharacterMul

namespace Masullo.GenuineNormalizedMellinJet
open MasulloGRH Masullo.IdeleClassGeometry
variable (K : Type*) [Field K] [NumberField K]
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)

end Masullo.GenuineNormalizedMellinJet
namespace Masullo.GenuineMellinJet
open MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet
noncomputable def nativeHalfWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (alpha * |t|) * (1 + t^2) ^ (s/4)

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

#check genuineMellinJet_normalization
#print axioms genuineMellinJet_normalization
end Masullo.GenuineMellinJet

namespace Masullo.GenuineMellinJet
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet

end Masullo.GenuineMellinJet
namespace Masullo.NativePairingIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
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

end Masullo.NativePairingIntegrable
namespace Masullo.NativeTranslatedProductIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.NativePairingIntegrable
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
    rw [actual_jet_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  apply integrable_finset_sum
  intro k hk
  exact ((actual_compact_jet_moment K chi mu z a h hh hs k).mul_prod
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
end Masullo.NativeTranslatedProductIntegrable

namespace Masullo.NativeConvolutionProductIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.NativePairingIntegrable Masullo.NativeTranslatedProductIntegrable
variable (K : Type*) [Field K] [NumberField K]

/-- The missing original-convolution Fubini premise, derived from the weighted
native pairing, compact test moments and SAME-Haar shear preservation. -/
theorem native_convolution_product_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m p.2 * f (p.1⁻¹*p.2)) (mu.prod mu) := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  have ht := (measurePreserving_prod_inv_mul mu mu).integrable_comp hi.aestronglyMeasurable
  have hc := ht.mpr hi
  simpa only [Function.comp_def, mul_inv_cancel_left] using hc

/-- Actual left convolution paired against an admitted native jet on the
original weighted function space. The product/Fubini premise is proved above. -/
theorem native_weighted_convolution_pairing
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a m x ∂mu) =
      ∫ y, (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) * f y ∂mu := by
  have hi := native_convolution_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  calc
    _ = ∫ x, ∫ g, h g * genuineMellinJet K chi z a m x * f (g⁻¹*x) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_mul_const]
      congr 1
      funext g
      ring
    _ = ∫ g, ∫ x, h g * genuineMellinJet K chi z a m x * f (g⁻¹*x) ∂mu ∂mu :=
      (integral_integral_swap hi).symm
    _ = ∫ g, ∫ y, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with g
      have he := integral_mul_left_eq_self (μ := mu)
        (fun x => h g * genuineMellinJet K chi z a m x * f (g⁻¹*x)) g
      simpa only [inv_mul_cancel_left] using he.symm
    _ = ∫ y, ∫ g, h g * genuineMellinJet K chi z a m (g*y) * f y ∂mu ∂mu :=
      native_translated_fubini K mu chi z a s alpha m h f hh hs hg hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact integral_mul_const _ _

#print axioms native_convolution_product_integrable
#print axioms native_weighted_convolution_pairing
end Masullo.NativeConvolutionProductIntegrable

namespace Masullo.NativeWeightedConvolutionTriangular
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.NativePairingIntegrable Masullo.NativeConvolutionProductIntegrable
variable (K : Type*) [Field K] [NumberField K]

/-- Measured convolution acts triangularly on the weighted Mellin functionals,
by Haar invariance and Fubini. -/
theorem native_weighted_convolution_triangular
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a m x ∂mu) =
      ∑ k ∈ Finset.range (m+1),
        ((∫ g, h g * genuineMellinJet K chi z a k g ∂mu) * (m.choose k : ℂ)) *
          (∫ y, genuineMellinJet K chi z a (m-k) y * f y ∂mu) := by
  rw [native_weighted_convolution_pairing K mu chi z a s alpha m h f hh hs hg hf]
  have he : (fun y => (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) * f y) =
      (fun y => ∑ k ∈ Finset.range (m+1),
        ((∫ g, h g * genuineMellinJet K chi z a k g ∂mu) * (m.choose k : ℂ)) *
          (genuineMellinJet K chi z a (m-k) y * f y)) := by
    funext y
    rw [actual_compact_measured_jet_action K chi mu z a h hh hs m y, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_const_mul _ _
  · intro k hk
    exact (native_pairing_integrable K chi mu z a s alpha (m-k)
      (hg (m-k) (Nat.sub_le _ _)) f hf).const_mul _

/-- The diagonal coefficient is the genuine character Mellin integral at z-a
on the original quotient Haar, acting on arbitrary native weighted f. -/
theorem native_weighted_convolution_mellin
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha 0) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, (∫ g, h g * f (g⁻¹*x) ∂mu) * genuineMellinJet K chi z a 0 x ∂mu) =
      (∫ g, h g * genuineMellinJet K chi z a 0 g ∂mu) *
        (∫ y, genuineMellinJet K chi z a 0 y * f y ∂mu) := by
  have hzero : ∀ k ≤ 0, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu := by
    intro k hk
    have he : k = 0 := Nat.eq_zero_of_le_zero hk
    simpa only [he] using hg
  simpa using native_weighted_convolution_triangular K mu chi z a s alpha 0 h f hh hs hzero hf

#print axioms native_weighted_convolution_triangular
#print axioms native_weighted_convolution_mellin
end Masullo.NativeWeightedConvolutionTriangular

namespace Masullo.TransposeDiagonalIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeTranslatedProductIntegrable Masullo.NativeConvolutionProductIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

/-- The specific transposed Mellin coefficient paired with a native vector
is integrable. This is a diagonal estimate, not a product-a.e. restriction. -/
theorem actual_transpose_diagonal_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h u : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hu : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * u x) 2 mu) :
    Integrable (fun y => (∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) * u y) mu := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h u hh hs hg hu
  have hj : Integrable (fun y => ∫ g,
      h g * genuineMellinJet K chi z a m (g*y) * u y ∂mu) mu := by
    first | exact hi.integral_prod_left | exact hi.integral_prod_right
  simpa only [integral_mul_const] using hj

/-- This is the actual finite tensor with its functional slot precomposed
with convolution. No projection or convergence identity is assumed. -/
noncomputable def finitePAKernel {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K))
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ :=
  ∑ i ∈ F, u i x * (∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu)

/-- Correct-order finite-kernel action on every admitted native weighted
input. It is P_F A, not A P_F. The passage P_F A → PA remains separate. -/
theorem actual_finite_PA_kernel_action {ι : Type*} (F : Finset ι)
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ i ∈ F, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (hf : MemLp (fun y => (nativeHalfWeight alpha s (classLog K y) : ℂ) * f y) 2 mu)
    (x : HeckeIdeleClasses K) :
    (∑ i ∈ F, u i x * (∫ y, (∫ g, h g * f (g⁻¹*y) ∂mu) *
      genuineMellinJet K (chi i) (z i) a (m i) y ∂mu)) =
      ∫ y, finitePAKernel K F mu chi z a m h u x y * f y ∂mu := by
  unfold finitePAKernel
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [native_weighted_convolution_pairing K mu (chi i) (z i) a s alpha (m i)
      h f hh hs (hg i hi) hf]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => by ring)
  · intro i hi
    have hd := (actual_transpose_diagonal_integrable K mu (chi i) (z i)
      a s alpha (m i) h f hh hs (hg i hi) hf).const_mul (u i x)
    simpa only [mul_assoc] using hd

/-- Actual Haar diagonal integrability for the finite arithmetic tensor;
the native weight and admitted jets supply the estimate. -/
theorem actual_finite_PA_diagonal_integrable {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ i ∈ F, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (hu : ∀ i ∈ F, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * u i x) 2 mu) :
    Integrable (fun x => finitePAKernel K F mu chi z a m h u x x) mu := by
  unfold finitePAKernel
  apply integrable_finset_sum
  intro i hi
  simpa only [mul_comm] using actual_transpose_diagonal_integrable K mu
    (chi i) (z i) a s alpha (m i) h (u i) hh hs (hg i hi) (hu i hi)

#print axioms actual_transpose_diagonal_integrable
#print axioms actual_finite_PA_kernel_action
#print axioms actual_finite_PA_diagonal_integrable
end Masullo.TransposeDiagonalIntegrable

namespace Masullo.TransposeRowContinuous
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ClassCharacterMul Masullo.TransposeDiagonalIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]

theorem actual_transpose_row_continuous
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    Continuous (fun y => ∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) := by
  have he : (fun y => ∫ g, h g * genuineMellinJet K chi z a m (g*y) ∂mu) =
      (fun y => ∑ k ∈ Finset.range (m+1),
        (∫ g, h g * genuineMellinJet K chi z a k g ∂mu) *
          (genuineMellinJet K chi z a (m-k) y * (m.choose k : ℂ))) := by
    funext y
    exact actual_compact_measured_jet_action K chi mu z a h hh hs m y
  rw [he]
  exact continuous_finset_sum _ (fun k hk => continuous_const.mul
    ((actual_jet_continuous K chi z a (m-k)).mul continuous_const))

/-- The product representative is genuinely continuous, so its diagonal is
specified pointwise; no restriction of a product-a.e. equivalence is used. -/
theorem actual_finite_PA_kernel_continuous {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (u : ι → HeckeIdeleClasses K → ℂ)
    (hh : Continuous h) (hs : HasCompactSupport h)
    (hu : ∀ i ∈ F, Continuous (u i)) :
    Continuous (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      finitePAKernel K F mu chi z a m h u p.1 p.2) := by
  unfold finitePAKernel
  exact continuous_finset_sum _ (fun i hi =>
    ((hu i hi).comp continuous_fst).mul
      ((actual_transpose_row_continuous K mu (chi i) (z i) a (m i) h hh hs).comp
        continuous_snd))

noncomputable def actualWeight (alpha s : ℝ) (x : HeckeIdeleClasses K) : ℝ :=
  Real.exp (2 * alpha * |classLog K x|) * (1 + (classLog K x)^2) ^ (s/2)

theorem actualWeight_pos (alpha s : ℝ) (x : HeckeIdeleClasses K) :
    0 < actualWeight K alpha s x := by
  unfold actualWeight
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

theorem actualWeight_continuous (alpha s : ℝ) (hs0 : 0 ≤ s) : Continuous (actualWeight K alpha s) := by
  unfold actualWeight
  have hc := Masullo.WeightedIdeleClass.classLog_continuous K
  fun_prop (disch := positivity)

/-- The original weighted Riesz vector, not a freely chosen continuous column. -/
noncomputable def actualRieszColumn (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a alpha s : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  star (genuineMellinJet K chi z a m x) / (actualWeight K alpha s x : ℂ)

theorem actualRieszColumn_continuous (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a alpha s : ℝ) (m : ℕ) (hs0 : 0 ≤ s) :
    Continuous (actualRieszColumn K chi z a alpha s m) := by
  unfold actualRieszColumn
  exact (actual_jet_continuous K chi z a m).star.div
    (Complex.continuous_ofReal.comp (actualWeight_continuous K alpha s hs0))
    (fun x => Complex.ofReal_ne_zero.mpr (ne_of_gt (actualWeight_pos K alpha s x)))

/-- Finite Gram-inverse combinations of actual Riesz vectors have a continuous
PA kernel. Choosing the coefficients to be the inverse Gram matrix is a
separate finite-dimensional identification, not an assumption hidden here. -/
theorem actual_Gram_PA_kernel_continuous {ι : Type*} (F : Finset ι)
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a alpha s : ℝ) (m : ι → ℕ)
    (c : ι → ι → ℂ) (h : HeckeIdeleClasses K → ℂ) (hs0 : 0 ≤ s)
    (hh : Continuous h) (hs : HasCompactSupport h) :
    Continuous (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      finitePAKernel K F mu chi z a m h
        (fun i x => ∑ j ∈ F, c i j * actualRieszColumn K (chi j) (z j) a alpha s (m j) x)
        p.1 p.2) := by
  apply actual_finite_PA_kernel_continuous K F mu chi z a m h _ hh hs
  intro i hi
  exact continuous_finset_sum _ (fun j hj => continuous_const.mul
    (actualRieszColumn_continuous K (chi j) (z j) a alpha s (m j) hs0))

#print axioms actual_finite_PA_kernel_continuous
#print axioms actualRieszColumn_continuous
#print axioms actual_Gram_PA_kernel_continuous
end Masullo.TransposeRowContinuous

namespace Masullo.ActualRiesz
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine weighted Riesz vector, written using the half-weight already
attached pointwise to the original Mellin jet. -/
noncomputable def actualRiesz (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  star (genuineNormalizedMellinJet K chi z a s alpha m x) /
    (nativeHalfWeight alpha s (classLog K x) : ℂ)

theorem halfWeight_pos (alpha s t : ℝ) : 0 < nativeHalfWeight alpha s t := by
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

/-- Identifies the square of the half-weight with the manuscript weight. -/
theorem halfWeight_sq (alpha s t : ℝ) :
    nativeHalfWeight alpha s t * nativeHalfWeight alpha s t =
      Real.exp (2 * alpha * |t|) * (1+t^2)^(s/2) := by
  unfold nativeHalfWeight
  calc
    _ = (Real.exp (alpha*|t|) * Real.exp (alpha*|t|)) *
      ((1+t^2)^(s/4) * (1+t^2)^(s/4)) := by ring
    _ = _ := by
      rw [← Real.exp_add, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
      congr 2 <;> ring

/-- The weighted column is the conjugate normalized genuine jet pointwise. -/
theorem actualRiesz_weighted (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      actualRiesz K chi z a s alpha m x =
        star (genuineNormalizedMellinJet K chi z a s alpha m x) := by
  have hw : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (halfWeight_pos alpha s _))
  unfold actualRiesz
  field_simp

/-- The original-Haar functional density is the genuine jet, not an
independently postulated coefficient. This equality holds on the diagonal. -/
theorem actualRiesz_density (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ((Real.exp (2*alpha*|classLog K x|) *
      (1+(classLog K x)^2)^(s/2) : ℝ) : ℂ) *
      star (actualRiesz K chi z a s alpha m x) =
        genuineMellinJet K chi z a m x := by
  rw [← halfWeight_sq, Complex.ofReal_mul]
  have he : (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      star (actualRiesz K chi z a s alpha m x) =
      genuineNormalizedMellinJet K chi z a s alpha m x := by
    simpa [mul_comm] using congrArg star (actualRiesz_weighted K chi z a s alpha m x)
  calc
    _ = (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      ((nativeHalfWeight alpha s (classLog K x) : ℂ) *
        star (actualRiesz K chi z a s alpha m x)) := by ring
    _ = (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      genuineNormalizedMellinJet K chi z a s alpha m x := by rw [he]
    _ = _ := by rw [mul_comm, genuineMellinJet_normalization]

/-- Removes the separate native-vector admission premise for actual Riesz
columns. Only the genuine normalized jet admission remains. -/
theorem actualRiesz_memLp (mu : Measure (HeckeIdeleClasses K))
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      actualRiesz K chi z a s alpha m x) 2 mu := by
  simp_rw [actualRiesz_weighted]
  exact hg.star

end Masullo.ActualRiesz

namespace Masullo.ActualGram
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet Masullo.ActualRiesz
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def actualGram
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
    actualRiesz K (chi j) (z j) a s alpha (m j) x ∂mu

noncomputable def actualGramDual
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (i : ι) (x : HeckeIdeleClasses K) : ℂ :=
  ∑ j, (actualGram K mu chi z a s alpha m)⁻¹ j i *
    actualRiesz K (chi j) (z j) a s alpha (m j) x

theorem actual_Gram_density (chi psi : UnitaryHeckeCharacter K) (z v : ℂ)
    (a s alpha : ℝ) (m n : ℕ) (x : HeckeIdeleClasses K) :
    genuineMellinJet K chi z a m x * actualRiesz K psi v a s alpha n x =
      genuineNormalizedMellinJet K chi z a s alpha m x *
        star (genuineNormalizedMellinJet K psi v a s alpha n x) := by
  rw [← genuineMellinJet_normalization K chi z a s alpha m x]
  unfold actualRiesz
  have hw : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (halfWeight_pos alpha s _))
  field_simp

theorem actual_Gram_integrable
    (mu : Measure (HeckeIdeleClasses K)) (chi psi : UnitaryHeckeCharacter K)
    (z v : ℂ) (a s alpha : ℝ) (m n : ℕ)
    (hi : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (hj : MemLp (genuineNormalizedMellinJet K psi v a s alpha n) 2 mu) :
    Integrable (fun x => genuineMellinJet K chi z a m x *
      actualRiesz K psi v a s alpha n x) mu := by
  simp_rw [actual_Gram_density]
  exact hi.integrable_mul hj.star

/-- Concrete original-Haar biorthogonality. The inverse must be indexed j,i;
using i,j here would generally not give the actual orthogonal section. -/
theorem actual_GramDual_pairing
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det) (i k : ι) :
    (∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
      actualGramDual K mu chi z a s alpha m k x ∂mu) = if i = k then 1 else 0 := by
  have hi (j : ι) := actual_Gram_integrable K mu (chi i) (chi j)
    (z i) (z j) a s alpha (m i) (m j) (hg i) (hg j)
  unfold actualGramDual
  simp_rw [Finset.mul_sum, mul_left_comm (genuineMellinJet K (chi i) (z i) a (m i) _)]
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    have hm := congrArg (fun M : Matrix ι ι ℂ => M i k)
      (Matrix.mul_nonsing_inv (actualGram K mu chi z a s alpha m) hdet)
    simpa only [Matrix.mul_apply, actualGram, Matrix.one_apply, mul_comm] using hm
  · intro j hj
    exact (hi j).const_mul _

#print axioms actual_Gram_density
#print axioms actual_Gram_integrable
#print axioms actual_GramDual_pairing
end Masullo.ActualGram

namespace Masullo.GramDualPairingIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.ActualGram Masullo.ClassCharacterMul
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_GramDual_pairing_integrable
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (i k : ι) :
    Integrable (fun x => genuineMellinJet K (chi i) (z i) a (m i) x *
      actualGramDual K mu chi z a s alpha m k x) mu := by
  unfold actualGramDual
  simp_rw [Finset.mul_sum, mul_left_comm (genuineMellinJet K (chi i) (z i) a (m i) _)]
  apply integrable_finset_sum
  intro j hj
  exact (actual_Gram_integrable K mu (chi i) (chi j) (z i) (z j)
    a s alpha (m i) (m j) (hg i) (hg j)).const_mul _

/-- Every genuine lower jet is represented in the finite label family.
This is the concrete finite flag condition, not a spectral action premise. -/
def JetClosed (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ) : Prop :=
  ∀ i k, k ≤ m i → ∃ j, chi j = chi i ∧ z j = z i ∧ m j = k

/-- On the actual inverse-Gram column the diagonal coefficient is the genuine
zero-th Mellin moment, even for a higher jet. All off-diagonal jet terms
vanish by the proved original-Haar duality, not by a trace assertion. -/
theorem actual_GramDual_PA_coefficient
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (i : ι) :
    (∫ y, (∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu) *
      actualGramDual K mu chi z a s alpha m i y ∂mu) =
      ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu := by
  have hi (k : ℕ) : Integrable (fun y =>
      genuineMellinJet K (chi i) (z i) a (m i-k) y *
        actualGramDual K mu chi z a s alpha m i y) mu := by
    obtain ⟨j, hc, hz, hm⟩ := hclosed i (m i-k) (Nat.sub_le _ _)
    simpa only [hc, hz, hm] using
      actual_GramDual_pairing_integrable K mu chi z a s alpha m hg j i
  have hp (k : ℕ) (hk : k ≤ m i) :
      (∫ y, genuineMellinJet K (chi i) (z i) a (m i-k) y *
        actualGramDual K mu chi z a s alpha m i y ∂mu) =
      if k = 0 then 1 else 0 := by
    by_cases hk0 : k = 0
    · subst k
      simpa using actual_GramDual_pairing K mu chi z a s alpha m hg hdet i i
    · obtain ⟨j, hc, hz, hm⟩ := hclosed i (m i-k) (Nat.sub_le _ _)
      have hji : j ≠ i := by
        intro he
        subst j
        omega
      simpa only [hc, hz, hm, if_neg hji, if_neg hk0] using
        actual_GramDual_pairing K mu chi z a s alpha m hg hdet j i
  have he : (fun y => (∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu) *
      actualGramDual K mu chi z a s alpha m i y) =
      (fun y => ∑ k ∈ Finset.range (m i+1),
        ((∫ g, h g * genuineMellinJet K (chi i) (z i) a k g ∂mu) * ((m i).choose k : ℂ)) *
          (genuineMellinJet K (chi i) (z i) a (m i-k) y *
            actualGramDual K mu chi z a s alpha m i y)) := by
    funext y
    rw [actual_compact_measured_jet_action K (chi i) mu (z i) a h hh hs (m i) y,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, integral_finset_sum]
  · simp_rw [integral_const_mul]
    calc
      _ = ∑ k ∈ Finset.range (m i+1),
          ((∫ g, h g * genuineMellinJet K (chi i) (z i) a k g ∂mu) * ((m i).choose k : ℂ)) *
            (if k = 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hp k (by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))]
      _ = _ := by simp
  · intro k hk
    exact (hi k).const_mul _

#print axioms actual_GramDual_pairing_integrable
#print axioms actual_GramDual_PA_coefficient
end Masullo.GramDualPairingIntegrable

namespace Masullo.GramDualNativeMemLp
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.TransposeDiagonalIntegrable Masullo.ActualGram Masullo.GramDualPairingIntegrable
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_GramDual_native_memLp
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (i : ι) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      actualGramDual K mu chi z a s alpha m i x) 2 mu := by
  unfold actualGramDual
  simp_rw [Finset.mul_sum, mul_left_comm (nativeHalfWeight alpha s (classLog K _) : ℂ)]
  exact memLp_finset_sum _ (fun j hj =>
    (actualRiesz_memLp K mu (chi j) (z j) a s alpha (m j) (hg j)).const_mul _)

omit [Fintype ι] [DecidableEq ι] in
theorem closed_family_native_admission
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m) (i : ι) (k : ℕ) (hk : k ≤ m i) :
    MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu := by
  obtain ⟨j, hc, hz, hm⟩ := hclosed i k hk
  simpa only [hc, hz, hm] using hg j

/-- The actual inverse-Gram PA diagonal is integrable with ORIGINAL Haar.
No integrable-diagonal premise and no independent output-column premise. -/
theorem actual_Gram_PA_diagonal_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    Integrable (fun x => finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x) mu := by
  exact actual_finite_PA_diagonal_integrable K Finset.univ mu chi z a s alpha m h
    (actualGramDual K mu chi z a s alpha m) hh hs
    (fun i hi k hk => closed_family_native_admission K mu chi z a s alpha m hg hclosed i k hk)
    (fun i hi => actual_GramDual_native_memLp K mu chi z a s alpha m hg i)

/-- The explicitly chosen genuine PA diagonal integrates to the complete
finite jet-multiplicity sum. This is a direct arithmetic diagonal identity,
not a restriction of a product-a.e. kernel equality. -/
theorem actual_Gram_PA_diagonal_integral
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h) :
    (∫ x, finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x ∂mu) =
      ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu := by
  unfold finitePAKernel
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    simpa only [mul_comm] using actual_GramDual_PA_coefficient K mu chi z a s alpha m
      hg hdet hclosed h hh hs i
  · intro i hi
    simpa only [mul_comm] using actual_transpose_diagonal_integrable K mu (chi i) (z i)
      a s alpha (m i) h (actualGramDual K mu chi z a s alpha m i) hh hs
      (closed_family_native_admission K mu chi z a s alpha m hg hclosed i)
      (actual_GramDual_native_memLp K mu chi z a s alpha m hg i)

#print axioms actual_GramDual_native_memLp
#print axioms actual_Gram_PA_diagonal_integrable
#print axioms actual_Gram_PA_diagonal_integral
end Masullo.GramDualNativeMemLp


/-! Original-measure shell estimates for B35 (35.7)--(35.8).
The measure is never silently replaced by normalized Haar. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace BReview
variable {X E : Type*} [MeasurableSpace X] (mu : Measure X)

theorem mask_integrable (f : X → ℂ) (hf : Integrable f mu)
    (p : X → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) :
    Integrable (fun x => (p x : ℂ) * f x) mu := by
  apply hf.norm.mono'
    (((Complex.continuous_ofReal.measurable.comp hp).aestronglyMeasurable).mul
      hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
  exact (mul_le_mul_of_nonneg_right (hp1 x) (norm_nonneg _)).trans_eq (one_mul _)

theorem finite_shell_contraction (F : Finset E) (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ x, ∑ e ∈ F, p e x ≤ 1)
    (f : X → ℂ) (hf : Integrable f mu) :
    (∑ e ∈ F, ‖∫ x, (p e x : ℂ) * f x ∂mu‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  have hp1 (e : E) (he : e ∈ F) (x : X) : p e x ≤ 1 := by
    exact (Finset.single_le_sum (fun j _ => hp0 j x) he).trans (hpart x)
  have hi (e : E) (he : e ∈ F) :=
    mask_integrable mu f hf (p e) (hp e) (hp0 e) (hp1 e he)
  calc
    _ ≤ ∑ e ∈ F, ∫ x, ‖(p e x : ℂ) * f x‖ ∂mu := by
      apply Finset.sum_le_sum
      intro e he
      exact norm_integral_le_integral_norm _
    _ = ∫ x, ∑ e ∈ F, ‖(p e x : ℂ) * f x‖ ∂mu := by
      symm
      exact integral_finset_sum F (fun e he => (hi e he).norm)
    _ ≤ ∫ x, ‖f x‖ ∂mu := by
      apply integral_mono (integrable_finset_sum F (fun e he => (hi e he).norm)) hf.norm
      intro x
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp0 _ _)]
      rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right (hpart x) (norm_nonneg _)).trans_eq (one_mul _)

theorem all_shell_contraction (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f : X → ℂ) (hf : Integrable f mu) :
    Summable (fun e => ‖∫ x, (p e x : ℂ) * f x ∂mu‖) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) * f x ∂mu‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  have hs : Summable (fun e => ‖∫ x, (p e x : ℂ) * f x ∂mu‖) :=
    summable_of_sum_le (fun e => norm_nonneg _)
      (fun F => finite_shell_contraction mu F p hp hp0 (hpart F) f hf)
  exact ⟨hs, le_of_tendsto hs.hasSum (Eventually.of_forall
    (fun F => finite_shell_contraction mu F p hp hp0 (hpart F) f hf))⟩

theorem shell_difference_bound (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f g : X → ℂ) (hf : Integrable f mu) (hg : Integrable g mu) :
    (∑' e, ‖(∫ x, (p e x : ℂ) * f x ∂mu) -
      (∫ x, (p e x : ℂ) * g x ∂mu)‖) ≤ ∫ x, ‖f x-g x‖ ∂mu := by
  classical
  have hp1 (e : E) (x : X) : p e x ≤ 1 := by
    simpa using hpart {e} x
  have he (e : E) :
      (∫ x, (p e x : ℂ) * (f x-g x) ∂mu) =
      (∫ x, (p e x : ℂ) * f x ∂mu) - (∫ x, (p e x : ℂ) * g x ∂mu) := by
    simp_rw [mul_sub]
    exact integral_sub
      (mask_integrable mu f hf (p e) (hp e) (hp0 e) (hp1 e))
      (mask_integrable mu g hg (p e) (hp e) (hp0 e) (hp1 e))
  simpa only [he] using
    (all_shell_contraction mu p hp hp0 hpart (fun x => f x-g x) (hf.sub hg)).2

theorem all_shell_L1_limit (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f : ℕ → X → ℂ) (g : X → ℂ)
    (hf : ∀ n, Integrable (f n) mu) (hg : Integrable g mu)
    (hlim : Tendsto (fun n => ∫ x, ‖f n x-g x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) * f n x ∂mu) -
      (∫ x, (p e x : ℂ) * g x ∂mu)‖) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => tsum_nonneg (fun e => norm_nonneg _))
    (fun n => shell_difference_bound mu p hp hp0 hpart (f n) g (hf n) hg) hlim

theorem physical_tail_limit (f : X → ℂ) (hf : Integrable f mu)
    (chi : ℕ → X → ℝ) (hm : ∀ n, Measurable (chi n))
    (h0 : ∀ n x, 0 ≤ chi n x) (h1 : ∀ n x, chi n x ≤ 1)
    (hc : ∀ x, Tendsto (fun n => chi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (1-chi n x)*‖f x‖ ∂mu) atTop (𝓝 0) := by
  have hb (n : ℕ) : ∀ᵐ x ∂mu, ‖(1-chi n x)*‖f x‖‖ ≤ ‖f x‖ := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (h1 n x)) (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (by linarith [h0 n x] : 1-chi n x ≤ 1)
      (norm_nonneg _)).trans_eq (one_mul _)
  have hl : ∀ᵐ x ∂mu, Tendsto (fun n => (1-chi n x)*‖f x‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (hc x)).mul_const ‖f x‖
  simpa using tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => ((measurable_const.sub (hm n)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable.norm) hf.norm hb hl

theorem physical_shell_limit (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f : X → ℂ) (hf : Integrable f mu)
    (chi : ℕ → X → ℝ) (hm : ∀ n, Measurable (chi n))
    (h0 : ∀ n x, 0 ≤ chi n x) (h1 : ∀ n x, chi n x ≤ 1)
    (hc : ∀ x, Tendsto (fun n => chi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) * ((chi n x : ℂ)*f x) ∂mu) -
      (∫ x, (p e x : ℂ) * f x ∂mu)‖) atTop (𝓝 0) := by
  apply all_shell_L1_limit mu p hp hp0 hpart
    (fun n x => (chi n x : ℂ)*f x) f
    (fun n => mask_integrable mu f hf (chi n) (hm n) (h0 n) (h1 n)) hf
  have he (n : ℕ) (x : X) :
      ‖(chi n x : ℂ)*f x-f x‖ = (1-chi n x)*‖f x‖ := by
    have heq : (chi n x : ℂ)*f x-f x = -(((1-chi n x : ℝ) : ℂ)*f x) := by
      push_cast
      ring
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (h1 n x))]
  simpa only [he] using physical_tail_limit mu f hf chi hm h0 h1 hc

theorem shell_reconstruction [Countable E] (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ x, HasSum (fun e => p e x) 1)
    (f : X → ℂ) (hf : Integrable f mu) :
    HasSum (fun e => ∫ x, (p e x : ℂ)*f x ∂mu) (∫ x, f x ∂mu) := by
  classical
  have hsub (F : Finset E) (x : X) : ∑ e ∈ F, p e x ≤ 1 := by
    simpa only [(hpart x).tsum_eq] using
      (hpart x).summable.sum_le_tsum F (fun e _ => hp0 e x)
  have hp1 (e : E) (x : X) : p e x ≤ 1 := by simpa using hsub {e} x
  have hi (e : E) := mask_integrable mu f hf (p e) (hp e) (hp0 e) (hp1 e)
  have hb (F : Finset E) :
      (∑ e ∈ F, ∫ x, ‖(p e x : ℂ)*f x‖ ∂mu) ≤ ∫ x, ‖f x‖ ∂mu := by
    rw [← integral_finset_sum F (fun e _ => (hi e).norm)]
    apply integral_mono (integrable_finset_sum F (fun e _ => (hi e).norm)) hf.norm
    intro x
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 _ _)]
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (hsub F x) (norm_nonneg _)).trans_eq (one_mul _)
  have hs : Summable (fun e => ∫ x, ‖(p e x : ℂ)*f x‖ ∂mu) :=
    summable_of_sum_le (fun e => integral_nonneg (fun x => norm_nonneg _)) hb
  have he (x : X) : (∑' e, (p e x : ℂ)*f x) = f x := by
    have ht := ((Complex.ofRealCLM.hasSum (hpart x)).mul_right (f x)).tsum_eq
    simpa using ht
  simpa only [he] using hasSum_integral_of_summable_integral_norm hi hs

end BReview
#print axioms BReview.mask_integrable
#print axioms BReview.finite_shell_contraction



noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace POriginalHaar

/-- The scalar change from normalized quotient Haar ν to μ=Vν.
This is an equality of actual Bochner integrals, including its 1/V. -/
theorem original_haar_integral {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (V : ℝ) (hV : 0 < V) (d : X → ℂ) :
    (∫ x, (V : ℂ)⁻¹ * d x ∂(ENNReal.ofReal V • nu)) = ∫ x, d x ∂nu := by
  rw [integral_smul_measure, integral_const_mul]
  rw [ENNReal.toReal_ofReal hV.le]
  change (V : ℂ) * ((V : ℂ)⁻¹ * ∫ x, d x ∂nu) = _
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hV)), one_mul]

/-- The original-Haar rank-one density of normalized L2 columns.
For F=√w f and G=√w g this is (w/V) f conj(g). -/
theorem rank_one_original_haar {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (V : ℝ) (hV : 0 < V) (F G : Lp ℂ 2 nu) :
    (∫ x, (V : ℂ)⁻¹ * (F x * star (G x))
      ∂(ENNReal.ofReal V • nu)) = inner ℂ G F := by
  rw [original_haar_integral nu V hV, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp [RCLike.inner_apply])

/-- Weight cancellation is pointwise, so it can be used on the specified
rank-one diagonal; it does not restrict a product-a.e. representative. -/
theorem weighted_rank_one_density (r V : ℝ) (f g : ℂ) :
    (V : ℂ)⁻¹ * (((r : ℂ) * f) * star ((r : ℂ) * g)) =
      ((r*r/V : ℝ) : ℂ) * f * star g := by
  have hr : star (r : ℂ) = (r : ℂ) := by simp
  rw [star_mul, hr]
  push_cast
  ring

end POriginalHaar

#print axioms POriginalHaar.original_haar_integral
#print axioms POriginalHaar.rank_one_original_haar
#print axioms POriginalHaar.weighted_rank_one_density

namespace BArithmetic
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped BigOperators Topology

/-- The actual finite arithmetic PA tensor, with original Haar rows, has
simultaneous shell cutoff convergence. The L1-diagonal premise is proved
from the native jet and inverse-Gram construction, not assumed. -/
theorem actual_Gram_PA_shell_limit
    (K : Type*) [Field K] [NumberField K]
    {ι E : Type*} [Fintype ι] [DecidableEq ι] [Countable E]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (p : E → HeckeIdeleClasses K → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpSum : ∀ x, HasSum (fun e => p e x) 1)
    (rho : ℕ → HeckeIdeleClasses K → ℝ) (hr : ∀ n, Measurable (rho n))
    (hr0 : ∀ n x, 0 ≤ rho n x) (hr1 : ∀ n x, rho n x ≤ 1)
    (hrlim : ∀ x, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    let d := fun x => finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x
    ((∫ x, d x ∂mu) = ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu) ∧
    HasSum (fun e => ∫ x, (p e x : ℂ)*d x ∂mu) (∫ x, d x ∂mu) ∧
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ)*((rho n x : ℂ)*d x) ∂mu) -
      (∫ x, (p e x : ℂ)*d x ∂mu)‖) atTop (𝓝 0) := by
  let d := fun x => finitePAKernel K Finset.univ mu chi z a m h
    (actualGramDual K mu chi z a s alpha m) x x
  have hd : Integrable d mu :=
    actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m hg hclosed h hh hs
  have hpart (F : Finset E) (x : HeckeIdeleClasses K) : ∑ e ∈ F, p e x ≤ 1 := by
    simpa only [(hpSum x).tsum_eq] using
      (hpSum x).summable.sum_le_tsum F (fun e _ => hp0 e x)
  exact ⟨actual_Gram_PA_diagonal_integral K mu chi z a s alpha m hg hdet hclosed h hh hs,
    BReview.shell_reconstruction mu p hp hp0 hpSum d hd,
    BReview.physical_shell_limit mu p hp hp0 hpart d hd rho hr hr0 hr1 hrlim⟩

end BArithmetic
#print axioms BArithmetic.actual_Gram_PA_shell_limit

/- B arithmetic independence fragment; insert after common normalized jets. -/
namespace Masullo.RadialExpHom
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet
open scoped BigOperators

noncomputable def radialExpHom (z : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (z * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' t u := by
    change Complex.exp (z * ((Multiplicative.toAdd t + Multiplicative.toAdd u : ℝ) : ℂ)) = _
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem radialExpHom_injective : Function.Injective radialExpHom := by
  intro z w h
  have hall : (fun t : ℝ => Complex.exp (z*(t:ℂ))) =
      (fun t : ℝ => Complex.exp (w*(t:ℂ))) := by
    funext t
    exact congrArg (fun f : Multiplicative ℝ →* ℂ => f (Multiplicative.ofAdd t)) h
  have hz : HasDerivAt (fun t : ℝ => Complex.exp (z*(t:ℂ))) z 0 := by
    convert (((Complex.hasDerivAt_exp (z*(0:ℂ))).comp 0
      ((hasDerivAt_id (0:ℂ)).const_mul z))).comp_ofReal using 1
    simp
  have hw : HasDerivAt (fun t : ℝ => Complex.exp (w*(t:ℂ))) w 0 := by
    convert (((Complex.hasDerivAt_exp (w*(0:ℂ))).comp 0
      ((hasDerivAt_id (0:ℂ)).const_mul w))).comp_ofReal using 1
    simp
  rw [hall] at hz
  exact hz.unique hw

/-- Actual original-weight zeroth kernels at distinct roots in one Hecke
component are finitely independent modulo the SAME quotient Haar null sets.
No independence or separation conclusion is an input. -/
theorem native_zero_finite_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (b : ι → ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0) :
    ∀ i ∈ S, b i = 0 := by
  classical
  let W : HeckeIdeleClasses K → ℂ := fun x =>
    (classCharacter K chi x : ℂ) * Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) *
      (((1 + (classLog K x)^2)^(-s/4) : ℝ):ℂ)
  have hW (x) : W x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
  have hfactor (i) (x) : genuineNormalizedMellinJet K chi (z i) a s alpha 0 x =
      W x * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) := by
    have he : Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ) -
        ((alpha * |classLog K x| : ℝ):ℂ)) =
        Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) *
        Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) := by
      rw [sub_eq_add_neg, Complex.exp_add]
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul, he]
    dsimp [W]
    ring
  have hrad : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) = 0 := by
    filter_upwards [h] with x hx
    have hh : W x * (∑ i ∈ S, b i * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ))) = 0 := by
      rw [Finset.mul_sum]
      convert hx using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfactor]
      ring
    exact (mul_eq_zero.mp hh).resolve_left (hW x)
  have hcont : Continuous (fun t : ℝ => ∑ i ∈ S,
      b i * Complex.exp ((z i-(a:ℂ))*(t:ℂ))) := by fun_prop
  have hm := (ae_map_iff (Masullo.WeightedIdeleClass.classLog_continuous K).measurable.aemeasurable
    (isClosed_eq hcont continuous_const).measurableSet).mpr hrad
  rw [hmap] at hm
  have hm0 : ∀ᵐ t : ℝ ∂volume, ∑ i ∈ S, b i * Complex.exp ((z i-(a:ℂ))*(t:ℂ)) = 0 := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hm0
  have hinj : Function.Injective (fun i => radialExpHom (z i-(a:ℂ))) := by
    intro i j hij
    apply hz
    have he := radialExpHom_injective hij
    linear_combination he
  have hli := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (fun i => radialExpHom (z i-(a:ℂ))) hinj
  apply (linearIndependent_iff'.mp hli) S b
  funext t
  simpa [radialExpHom, Function.comp_def] using congrFun hall (Multiplicative.toAdd t)

#print axioms native_zero_finite_independent
end Masullo.RadialExpHom

namespace Masullo.RadialExpHom
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet
open scoped BigOperators
/-- Independence of the actual conjugated L2 vectors used by native Gram–Schmidt,
for all distinct zeroth roots in one fixed character component. -/
theorem native_zero_L2_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu) :
    LinearIndependent ℂ (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))) := by
  classical
  let J := fun i => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))
  apply linearIndependent_iff'.mpr
  intro S b hsum
  have he (T : Finset ι) :
      (fun x => (∑ i ∈ T, b i • J i) x) =ᵐ[mu]
        (fun x => ∑ i ∈ T, b i * star (genuineNormalizedMellinJet K chi (z i) a s alpha 0 x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (b i • J i) (∑ j ∈ T, b j • J j),
        Lp.coeFn_smul (b i) (J i), (hg i).star.coeFn_toLp, ih] with x hx hs hj ht
      change J i x = star (genuineNormalizedMellinJet K chi (z i) a s alpha 0 x) at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  have hzsum : ∀ᵐ x ∂mu, ∑ i ∈ S,
      star (b i) * genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0 := by
    have hz0 := Lp.coeFn_zero ℂ 2 mu
    have hh := he S
    change (∑ i ∈ S, b i • J i) = 0 at hsum
    rw [hsum] at hh
    filter_upwards [hh, hz0] with x hx hx0
    have hh' := congrArg star (hx.symm.trans hx0)
    simpa only [star_sum, star_mul, star_star, Pi.zero_apply, star_zero, mul_comm] using hh'
  have hb := native_zero_finite_independent K chi mu c hc hmap z hz a s alpha S
    (fun i => star (b i)) hzsum
  intro i hi
  exact star_eq_zero.mp (hb i hi)

#print axioms native_zero_L2_independent
end Masullo.RadialExpHom


/- B integration fragment: insert after BGramKernel and BIndependence.
   The finite label closure is unconditional. The nonsingularity theorem uses
   proved arithmetic zeroth-jet independence and states its Haar hypotheses. -/
namespace BGramApplications
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.ActualGram
open Masullo.GramDualPairingIntegrable
open scoped InnerProductSpace ComplexOrder
variable (K : Type*) [Field K] [NumberField K]

/-- Complete finite multiplicity flags are downward closed, including when
N is the actual boundary-truncated multiplicity. -/
theorem fullJetFamily_closed {J : Type*}
    (chi : J → UnitaryHeckeCharacter K) (z : J → ℂ) (N : J → ℕ) :
    JetClosed K (fun i : Sigma (fun j => Fin (N j)) => chi i.1)
      (fun i => z i.1) (fun i => i.2.val) := by
  intro i k hk
  exact ⟨⟨i.1, ⟨k, lt_of_le_of_lt hk i.2.isLt⟩⟩, rfl, rfl, rfl⟩

/-- The actual original-Haar Gram matrix equals the Hilbert Gram matrix of
the actual normalized Riesz representatives, with no transposition. -/
theorem actualGram_eq_L2_Gram {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K))
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ)
    (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp
      (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu) :
    (fun i j => inner ℂ
      ((hg i).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i))))
      ((hg j).star.toLp
        (star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j))))) =
      actualGram K mu chi z a s alpha m := by
  funext i j
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hg i).star.coeFn_toLp, (hg j).star.coeFn_toLp] with x hx hy
  rw [hx, hy]
  rw [actual_Gram_density]
  simp [RCLike.inner_apply, mul_comm]

/-- Concrete nonsingularity and flag closure for distinct zeroth Mellin
parameters in one genuine Hecke component. Higher jet independence is not
asserted by this declaration. -/
theorem actual_zeroth_Gram_application
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (hg : ∀ i, MemLp
      (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu) :
    IsUnit (actualGram K mu (fun _ => chi) z a s alpha (fun _ => 0)).det ∧
      JetClosed K (fun _ : ι => chi) z (fun _ => 0) := by
  constructor
  · rw [← actualGram_eq_L2_Gram K mu (fun _ => chi) z a s alpha (fun _ => 0) hg]
    exact isUnit_iff_ne_zero.mpr
      (ne_of_gt (Matrix.posDef_gram_of_linearIndependent
        (Masullo.RadialExpHom.native_zero_L2_independent
          K chi mu c hc hmap z hz a s alpha hg)).det_pos)
  · intro i k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    exact ⟨i, rfl, rfl, hk0.symm⟩

end BGramApplications

#print BGramApplications.actual_zeroth_Gram_application
#print axioms BGramApplications.actual_zeroth_Gram_application
#print axioms BGramApplications.fullJetFamily_closed

/- B integration fragment. Insert after the one actual normalized-jet definition.
   Existing constructive source: NativeHigherIndependence.lean, generic polynomial
   isolation and original-Haar polynomial-block proof. Only namespaces are adapted.
   The arithmetic quotient, classLog and normalized jet are REUSED, never redefined. -/
namespace BHigherJetAlgebra

/-- A shifted nilpotent derivative has no kernel at a distinct exponent.
This is the algebraic isolation step for actual exponential-polynomial jets. -/
theorem nilpotent_shift_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (N : ℕ) (x : V) (hn : (D ^ N) x = 0)
    (hx : D x + c • x = 0) : x = 0 := by
  induction N generalizing x with
  | zero => simpa using hn
  | succ N ih =>
    have hDx : D x = -(c • x) := eq_neg_of_add_eq_zero_left hx
    have hn' : (D ^ N) (D x) = 0 := by
      rw [pow_succ] at hn
      exact hn
    have hzero : (D ^ N) x = 0 := by
      rw [hDx, map_neg, map_smul] at hn'
      have hz : c • (D ^ N) x = 0 := neg_eq_zero.mp hn'
      exact (smul_eq_zero.mp hz).resolve_left hc
    exact ih x hzero hx

/-- Distinct exponent shifts preserve nonzero vectors in a nilpotent jet block. -/
theorem nilpotent_shift_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (N : ℕ) (x : V) (hn : (D ^ N) x = 0) (hx : x ≠ 0) :
    D x + c • x ≠ 0 := by
  intro h
  exact hx (nilpotent_shift_kernel D c hc N x hn h)

#print axioms nilpotent_shift_kernel
#print axioms nilpotent_shift_ne_zero
/-- Ordinary derivative on the polynomial block of an actual Mellin jet. -/
noncomputable def polynomialDerivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun := Polynomial.derivative
  map_add' _ _ := Polynomial.derivative_add
  map_smul' c p := Polynomial.derivative_smul c p

/-- The distinct-root isolator is injective on every polynomial, with no
nilpotence assumption left for the native exponential-polynomial application. -/
theorem polynomial_shift_kernel (c : ℂ) (hc : c ≠ 0) (p : Polynomial ℂ)
    (hp : Polynomial.derivative p + c • p = 0) : p = 0 := by
  have hn : (polynomialDerivative ^ (p.natDegree + 1)) p = 0 := by
    rw [Module.End.pow_apply]
    exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)
  exact nilpotent_shift_kernel polynomialDerivative c hc (p.natDegree + 1) p hn hp

theorem polynomial_shift_injective (c : ℂ) (hc : c ≠ 0) :
    Function.Injective (fun p : Polynomial ℂ => Polynomial.derivative p + c • p) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply polynomial_shift_kernel c hc
  calc
    Polynomial.derivative (p-q) + c • (p-q) =
        (Polynomial.derivative p + c • p) - (Polynomial.derivative q + c • q) := by
      simp only [map_sub, smul_sub]
      abel
    _ = 0 := sub_eq_zero.mpr hpq

#print axioms polynomial_shift_kernel
#print axioms polynomial_shift_injective
end BHigherJetAlgebra


namespace BHigherJetIndependence
open MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet MeasureTheory
open scoped BigOperators

theorem polynomial_real_zero (p : Polynomial ℂ)
    (h : ∀ t : ℝ, p.eval (t:ℂ) = 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro x ⟨t, rfl⟩
  exact h t

theorem shifted_relation {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (p : ι → Polynomial ℂ) (w : ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) :
    ∀ t : ℝ, ∑ i ∈ S,
      (Polynomial.derivative (p i) + (z i-w) • p i).eval (t:ℂ) *
        Complex.exp (z i*(t:ℂ)) = 0 := by
  intro t
  have hd : HasDerivAt (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)))
      (∑ i ∈ S, ((Polynomial.derivative (p i)).eval (t:ℂ) +
        z i * (p i).eval (t:ℂ)) * Complex.exp (z i*(t:ℂ))) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hec := (Complex.hasDerivAt_exp (z i*(t:ℂ))).comp (t:ℂ)
      ((hasDerivAt_id (t:ℂ)).const_mul (z i))
    have he : HasDerivAt (fun u : ℝ => Complex.exp (z i*(u:ℂ)))
        (Complex.exp (z i*(t:ℂ)) * z i) t := by
      simpa using hec.comp_ofReal
    have hp := ((p i).hasDerivAt (t:ℂ)).comp_ofReal
    convert hp.mul he using 1
    ring
  have heq : (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ))) = fun _ => 0 := funext h
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (0:ℂ))
  calc
    _ = (∑ i ∈ S, ((Polynomial.derivative (p i)).eval (t:ℂ) +
        z i * (p i).eval (t:ℂ)) * Complex.exp (z i*(t:ℂ))) -
        w * (∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
      ring
    _ = 0 := by rw [hz, h t]; ring

theorem finite_polynomial_exp_independent {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (hz : Function.Injective z) (p : ι → Polynomial ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) :
    ∀ i ∈ S, p i = 0 := by
  classical
  induction S using Finset.induction_on generalizing p with
  | empty => simp
  | @insert k S hk ih =>
    have main : ∀ n (p : ι → Polynomial ℂ),
        (Polynomial.derivative^[n]) (p k) = 0 →
        (∀ t : ℝ, ∑ i ∈ insert k S,
          (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) →
        ∀ i ∈ insert k S, p i = 0 := by
      intro n
      induction n with
      | zero =>
        intro p hn hp
        have hpk : p k = 0 := hn
        have hs : ∀ t : ℝ, ∑ i ∈ S,
            (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0 := by
          intro t
          simpa [Finset.sum_insert hk, hpk] using hp t
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpk
        · exact ih p hs i hi
      | succ n ihn =>
        intro p hn hp
        let q : ι → Polynomial ℂ := fun i =>
          Polynomial.derivative (p i) + (z i-z k) • p i
        have hqk : q k = Polynomial.derivative (p k) := by simp [q]
        have hqn : (Polynomial.derivative^[n]) (q k) = 0 := by
          rw [hqk]
          simpa only [Function.iterate_succ_apply] using hn
        have hq := ihn q hqn (shifted_relation (insert k S) z p (z k) hp)
        have hs : ∀ i ∈ S, p i = 0 := by
          intro i hi
          apply BHigherJetAlgebra.polynomial_shift_kernel (z i-z k)
            (sub_ne_zero.mpr (fun he => hk (hz he ▸ hi)))
          exact hq i (Finset.mem_insert_of_mem hi)
        have hpk : p k = 0 := by
          apply polynomial_real_zero
          intro t
          have hh := hp t
          rw [Finset.sum_insert hk] at hh
          have hsum : ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp [hs i hi]
          rw [hsum, add_zero] at hh
          exact (mul_eq_zero.mp hh).resolve_right (Complex.exp_ne_zero _)
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpk
        · exact hs i hi
    exact main ((p k).natDegree+1) p
      (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)) h

/-- Finite mixed higher-jet blocks in one genuine Hecke component, expressed
by their coefficient polynomials, are independent in the ORIGINAL weighted
realization modulo the SAME quotient measure. No independence is assumed. -/
theorem native_polynomial_blocks_independent {ι : Type*}
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (p : ι → Polynomial ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) *
        genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0) :
    ∀ i ∈ S, p i = 0 := by
  classical
  let W : HeckeIdeleClasses K → ℂ := fun x =>
    (classCharacter K chi x : ℂ) * Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) *
      (((1 + (classLog K x)^2)^(-s/4) : ℝ):ℂ)
  have hW (x) : W x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
  have hf (i) (x) : genuineNormalizedMellinJet K chi (z i) a s alpha 0 x =
      W x * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) := by
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul, sub_eq_add_neg,
      Complex.exp_add]
    dsimp [W]
    ring
  have hr : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) = 0 := by
    filter_upwards [h] with x hx
    apply (mul_eq_zero.mp (show W x * (∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ))) = 0 from ?_)).resolve_left (hW x)
    rw [Finset.mul_sum]
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hf]
    ring
  have hcont : Continuous (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp ((z i-(a:ℂ))*(t:ℂ))) := by fun_prop
  have hm := (ae_map_iff (Masullo.WeightedIdeleClass.classLog_continuous K).measurable.aemeasurable
    (isClosed_eq hcont continuous_const).measurableSet).mpr hr
  rw [hmap] at hm
  have hm0 : ∀ᵐ t : ℝ ∂volume, ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp ((z i-(a:ℂ))*(t:ℂ)) = 0 := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hm0
  have hz' : Function.Injective (fun i => z i-(a:ℂ)) := by
    intro i j he
    apply hz
    linear_combination he
  exact finite_polynomial_exp_independent S (fun i => z i-(a:ℂ)) hz' p (congrFun hall)

#print axioms native_polynomial_blocks_independent
end BHigherJetIndependence

/- B integration fragment. Insert after BGramApplications and BHigherJetIndependence.
   This discharges Gram nonsingularity for full finite multiplicity flags in one
   character component from the supplied actual polynomial-block independence. -/
namespace BGramApplications
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.ActualGram
open Masullo.GramDualPairingIntegrable
open scoped InnerProductSpace ComplexOrder BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem normalized_jet_power (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    (classLog K x : ℂ)^m * genuineNormalizedMellinJet K chi z a s alpha 0 x =
      genuineNormalizedMellinJet K chi z a s alpha m x := by
  simp only [genuineNormalizedMellinJet, pow_zero, one_mul,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- Finite full higher-jet flags are independent on the SAME quotient measure.
The coefficients are isolated by polynomial blocks, including all multiplicities. -/
theorem native_fullJets_ae_independent {J : Type*} [Fintype J]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : J → ℂ) (hz : Function.Injective z) (N : J → ℕ) (a s alpha : ℝ)
    (coeffs : Sigma (fun j => Fin (N j)) → ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i, coeffs i *
      genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val x = 0) :
    ∀ i, coeffs i = 0 := by
  classical
  let p : J → Polynomial ℂ := fun j =>
    ∑ k : Fin (N j), Polynomial.monomial k.val (coeffs ⟨j,k⟩)
  have hp := BHigherJetIndependence.native_polynomial_blocks_independent
    K chi mu c hc hmap z hz a s alpha Finset.univ p (by
      filter_upwards [h] with x hx
      calc
        ∑ j ∈ Finset.univ, (p j).eval (classLog K x : ℂ) *
            genuineNormalizedMellinJet K chi (z j) a s alpha 0 x =
          ∑ j, ∑ k : Fin (N j), coeffs ⟨j,k⟩ *
            genuineNormalizedMellinJet K chi (z j) a s alpha k.val x := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
            Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [mul_assoc, normalized_jet_power]
        _ = 0 := by simpa only [Fintype.sum_sigma] using hx)
  rintro ⟨j,k⟩
  have hcoeff := congrArg (fun q : Polynomial ℂ => q.coeff k.val)
    (hp j (Finset.mem_univ _))
  have he : (p j).coeff k.val = coeffs ⟨j,k⟩ := by
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' hk' hne
      have hne' : k'.val ≠ k.val := fun he => hne (Fin.ext he)
      simp [hne']
    · simp
  simpa only [he, Polynomial.coeff_zero] using hcoeff

/-- Genuine conjugated normalized L2 representatives of every finite full flag
are linearly independent; no determinant or independence premise remains. -/
theorem native_fullJets_L2_independent {J : Type*} [Fintype J]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : J → ℂ) (hz : Function.Injective z) (N : J → ℕ) (a s alpha : ℝ)
    (hg : ∀ i : Sigma (fun j => Fin (N j)), MemLp
      (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val) 2 mu) :
    LinearIndependent ℂ (fun i : Sigma (fun j => Fin (N j)) =>
      (hg i).star.toLp
        (star (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val))) := by
  classical
  let r := fun i : Sigma (fun j => Fin (N j)) => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val))
  apply Fintype.linearIndependent_iff.mpr
  intro coeffs hsum
  have he (T : Finset (Sigma (fun j => Fin (N j)))) :
      (fun x => (∑ i ∈ T, coeffs i • r i) x) =ᵐ[mu]
        (fun x => ∑ i ∈ T, coeffs i *
          star (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (coeffs i • r i) (∑ j ∈ T, coeffs j • r j),
        Lp.coeFn_smul (coeffs i) (r i), (hg i).star.coeFn_toLp, ih] with x hx hs hj ht
      change r i x = star (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val x) at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  have hzsum : ∀ᵐ x ∂mu, ∑ i,
      star (coeffs i) * genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val x = 0 := by
    have hz0 := Lp.coeFn_zero ℂ 2 mu
    have hh := he Finset.univ
    change (∑ i, coeffs i • r i) = 0 at hsum
    rw [hsum] at hh
    filter_upwards [hh, hz0] with x hx hx0
    have hh' := congrArg star (hx.symm.trans hx0)
    simpa only [star_sum, star_mul, star_star, Pi.zero_apply, star_zero, mul_comm] using hh'
  have hb := native_fullJets_ae_independent K mu chi c hc hmap z hz N a s alpha
    (fun i => star (coeffs i)) hzsum
  intro i
  exact star_eq_zero.mp (hb i)

/-- Actual original-Haar Gram nonsingularity and downward closure for arbitrary
finite full multiplicity flags in one genuine Hecke component. The only measure
normalization premise is the displayed nonzero Haar log pushforward. -/
theorem actual_fullJet_Gram_application {J : Type*} [Fintype J] [DecidableEq J]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : J → ℂ) (hz : Function.Injective z) (N : J → ℕ) (a s alpha : ℝ)
    (hg : ∀ i : Sigma (fun j => Fin (N j)), MemLp
      (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val) 2 mu) :
    IsUnit (actualGram K mu (fun _ : Sigma (fun j => Fin (N j)) => chi)
      (fun i => z i.1) a s alpha (fun i => i.2.val)).det ∧
      JetClosed K (fun _ : Sigma (fun j => Fin (N j)) => chi)
        (fun i => z i.1) (fun i => i.2.val) := by
  constructor
  · rw [← actualGram_eq_L2_Gram K mu (fun _ => chi)
      (fun i : Sigma (fun j => Fin (N j)) => z i.1) a s alpha (fun i => i.2.val) hg]
    exact isUnit_iff_ne_zero.mpr
      (ne_of_gt (Matrix.posDef_gram_of_linearIndependent
        (native_fullJets_L2_independent K mu chi c hc hmap z hz N a s alpha hg)).det_pos)
  · exact fullJetFamily_closed K (fun _ => chi) z N

end
end BGramApplications
#print BGramApplications.actual_fullJet_Gram_application
#print axioms BGramApplications.actual_fullJet_Gram_application

-- Insert after RJetFragment.lean; reuses genuineNormalizedMellinJet.
namespace Masullo.BoundaryJetOrders

/-- The finite set of boundary jets satisfying the STRICT numerical condition
in Proposition 9.1.2.5. This is an index set, not a spectrum or an L-function.
The unresolved analytic bridge is that these are exactly the continuous jets
of the actual weighted idele-class quotient. -/
noncomputable def boundaryJetOrders (N : ℕ) (s : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (2 : ℝ) * j + 1 < s)

/-- Discharges the finite counting premise for boundary multiplicities:
at odd integral weight 2*k+1, the strict cutoff retains min(N,k) jets. -/
theorem boundaryJetOrders_odd (N k : ℕ) :
    boundaryJetOrders N (2 * (k : ℝ) + 1) = Finset.range (min N k) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  constructor
  · intro h
    have hj : (j : ℝ) < (k : ℝ) := by linarith [h.2]
    exact ⟨h.1, by exact_mod_cast hj⟩
  · rintro ⟨hN, hk⟩
    have hj : (j : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ⟨hN, by linarith⟩

/-- Conditional finite-block trace reduction for the binomial jet action
printed at (10.3.1.17). Discharges only its finite trace calculation; the
hypothesis must be proved for the genuine quotient operator before use. -/
theorem trace_of_binomial_jet_action (n : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    Matrix.trace M = (n : ℂ) * a 0 := by
  have hd (i : Fin n) : M i i = a 0 := by simp [hM]
  simp [Matrix.trace, Matrix.diag, hd, nsmul_eq_mul]

/-- Combined exact finite-count and conditional finite-trace step toward the
correct spectral multiplicity. No assertion of analytic jet admissibility,
zero identification, completeness, nuclearity, or infinite summability. -/
theorem boundary_jet_trace_at_odd_weight (N k : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card)
      (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k ∧
      Matrix.trace M = ((min N k : ℕ) : ℂ) * a 0 := by
  have hc : (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k := by
    rw [boundaryJetOrders_odd, Finset.card_range]
  refine ⟨hc, ?_⟩
  simpa only [hc] using trace_of_binomial_jet_action _ a M hM

/-- Numerical boundary multiplicity for every real Sobolev parameter.
This discharges counting only; continuous native jet attachment is unresolved. -/
theorem boundaryJetOrders_all_real (N : ℕ) (s : ℝ) :
    boundaryJetOrders N s = Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range,
    Nat.lt_min, Nat.lt_ceil]
  constructor
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩

end Masullo.BoundaryJetOrders

namespace Masullo.RadialJetDensity
open MeasureTheory Set
/-- The actual polynomial part of the radial squared dual norm in
Proposition 9.1.2.5; no spectrum or L-function is defined here. -/
noncomputable def radialJetDensity (m : ℕ) (s : ℝ) (x : ℝ) : ℝ :=
  x ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2)

/-- Power comparison needed for the native boundary-jet continuity premise. -/
theorem radialJetDensity_tail_comparison (m : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (x : ℝ) (hx : 1 < x) :
    radialJetDensity m s x ≤ x ^ ((2 : ℝ) * m - s) ∧
    (2 : ℝ) ^ (-s / 2) * x ^ ((2 : ℝ) * m - s) ≤ radialJetDensity m s x := by
  have hp : 0 < x := by linarith
  have hsq : 0 < x ^ 2 := sq_pos_of_pos hp
  have he : x ^ (2 * m) * (x ^ 2) ^ (-s / 2) =
      x ^ ((2 : ℝ) * m - s) := by
    rw [← Real.rpow_natCast x (2 * m), ← Real.rpow_natCast x 2,
      ← Real.rpow_mul (le_of_lt hp), ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  have hnon : 0 ≤ x ^ (2 * m) := pow_nonneg (le_of_lt hp) _
  have hq : -s / 2 ≤ 0 := by linarith
  constructor
  · unfold radialJetDensity
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hsq (by linarith) hq) hnon
  · have hbase : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have hb := Real.rpow_le_rpow_of_nonpos
      (show 0 < 1 + x ^ 2 by positivity) hbase hq
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hsq)] at hb
    have hh := mul_le_mul_of_nonneg_left hb hnon
    rw [← he]
    unfold radialJetDensity
    nlinarith

/-- Exact positive-tail criterion for the radial native Mellin-jet norm.
Discharges the boundary power-tail integrability premise, not the genuine
idele Haar decomposition or the weighted dual representation. -/
theorem radialJetDensity_integrable_tail_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (radialJetDensity m s) (Ioi 1) ↔ (2 : ℝ) * m + 1 < s := by
  have hm : AEStronglyMeasurable (radialJetDensity m s) (volume.restrict (Ioi 1)) := by
    apply Continuous.aestronglyMeasurable
    unfold radialJetDensity
    exact (continuous_id.pow _).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (by positivity)))
  have hn (x : ℝ) : 0 ≤ radialJetDensity m s x := by
    unfold radialJetDensity
    exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
      (Real.rpow_nonneg (by positivity) _)
  have hpow : IntegrableOn (fun x : ℝ => x ^ ((2 : ℝ) * m - s)) (Ioi 1) ↔
      (2 : ℝ) * m + 1 < s := by
    rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    apply hpow.mp
    apply (h.const_mul ((2 : ℝ) ^ (s / 2))).mono'
      ((measurable_id.pow_const _).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp : 0 < x := by exact lt_trans zero_lt_one hx
    simp only [id_eq]
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
    have hb := mul_le_mul_of_nonneg_left
      (radialJetDensity_tail_comparison m s hs x hx).2
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (s / 2))
    have hc : (2 : ℝ) ^ (s / 2) * 2 ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
    simpa only [← mul_assoc, hc, one_mul] using hb
  · intro h
    apply (hpow.mpr h).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
    exact (radialJetDensity_tail_comparison m s hs x hx).1

end Masullo.RadialJetDensity

namespace Masullo.RadialJetDensity
open MeasureTheory Set
/-- Includes the compact part of the actual radial density, so the only
obstruction on the positive half-line is the strict boundary jet cutoff. -/
theorem radialJetDensity_integrable_halfLine_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (radialJetDensity m s) (Ici 0) ↔ (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    apply (radialJetDensity_integrable_tail_iff m s hs).mp
    exact h.mono_set (by intro x hx; change 1 < x at hx; change 0 ≤ x; linarith)
  · intro h
    have hc : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
      ext x
      simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro hx
        by_cases h1 : x ≤ 1
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
    have hi := (hc.integrableOn_Icc (a := 0) (b := 1)).union
      ((radialJetDensity_integrable_tail_iff m s hs).mpr h)
    rwa [hu] at hi
end Masullo.RadialJetDensity

namespace Masullo.RadialJetDensity
open MeasureTheory Set
/-- At the right boundary b=alpha the exponential weight cancels on x>=0.
This discharges that precise tail of the actual weighted jet dual-norm test. -/
theorem boundaryRadialJet_integrable_halfLine_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x)
      (Ici 0) ↔ (2 : ℝ) * m + 1 < s := by
  have he : EqOn (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x)
      (radialJetDensity m s) (Ici 0) := by
    intro x hx
    change 0 ≤ x at hx
    dsimp only
    rw [abs_of_nonneg hx, sub_self, Real.exp_zero, one_mul]
  constructor
  · intro h
    exact (radialJetDensity_integrable_halfLine_iff m s hs).mp
      (h.congr_fun he measurableSet_Ici)
  · intro h
    exact ((radialJetDensity_integrable_halfLine_iff m s hs).mpr h).congr_fun
      (fun x hx => (he hx).symm) measurableSet_Ici
end Masullo.RadialJetDensity

namespace Masullo.RadialJetDensityEven
open MeasureTheory Set Masullo.RadialJetDensity
/-- Discharges reflection symmetry of the squared radial jet norm, needed
for the negative-tail part of the native boundary multiplicity criterion. -/
theorem radialJetDensity_even (m : ℕ) (s x : ℝ) :
    radialJetDensity m s (-x) = radialJetDensity m s x := by
  simp [radialJetDensity, pow_mul]

theorem radialJetDensity_integrable_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (radialJetDensity m s) ↔ (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    exact (radialJetDensity_integrable_halfLine_iff m s hs).mp h.integrableOn
  · intro h
    have hp := (radialJetDensity_integrable_halfLine_iff m s hs).mpr h
    have hn : IntegrableOn (radialJetDensity m s) (Iic 0) := by
      simpa [radialJetDensity_even] using hp.comp_neg
    have hu : Ici (0 : ℝ) ∪ Iic 0 = univ := by
      ext x
      simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
      exact le_total 0 x
    simpa only [hu, integrableOn_univ] using hp.union hn

/-- Full right-boundary squared radial norm, including the decaying tail.
This discharges the analytic boundary cutoff premise for spectral jet
multiplicities; the genuine Haar and weighted-dual bridges remain separate. -/
theorem rightBoundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    exact (boundaryRadialJet_integrable_halfLine_iff m s alpha hs).mp h.integrableOn
  · intro h
    have hc : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    have hw : Continuous (fun x : ℝ =>
        Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x) :=
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
        (continuous_const.mul continuous_abs))).mul hc
    apply ((radialJetDensity_integrable_iff m s hs).mpr h).mono'
      hw.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ radialJetDensity m s x := by
      unfold radialJetDensity
      exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
        (Real.rpow_nonneg (by positivity) _)
    have he : Real.exp (2 * alpha * x - 2 * alpha * |x|) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [le_abs_self x]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hn)]
    exact (mul_le_mul_of_nonneg_right he hn).trans_eq (one_mul _)

/-- Reflection proves the same sharp cutoff at the other strip boundary. -/
theorem leftBoundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * (-alpha) * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    apply (rightBoundaryRadialJet_integrable_iff m s alpha hs ha).mp
    simpa only [mul_neg, neg_mul, neg_neg, abs_neg, radialJetDensity_even] using h.comp_neg
  · intro h
    have hr := (rightBoundaryRadialJet_integrable_iff m s alpha hs ha).mpr h
    simpa only [mul_neg, neg_mul, neg_neg, abs_neg, radialJetDensity_even] using hr.comp_neg

/-- Uniform statement for either genuine strip edge (including alpha=0).
It does not assume a prescribed zero set or any spectral summability. -/
theorem boundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  rcases le_total 0 beta with h | h
  · have he : beta = alpha := by simpa only [abs_of_nonneg h] using hb
    subst beta
    exact rightBoundaryRadialJet_integrable_iff m s alpha hs ha
  · have he : beta = -alpha := by rw [abs_of_nonpos h] at hb; linarith
    subst beta
    exact leftBoundaryRadialJet_integrable_iff m s alpha hs ha

end Masullo.RadialJetDensityEven

namespace Masullo.RadialJetDensityEven
open MeasureTheory Set Masullo.RadialJetDensity Masullo.BoundaryJetOrders
attribute [local instance] Classical.propDecidable
/-- Converts the proven full-line integrability condition into the exact
number of surviving orders below N. This discharges only analytic counting;
N still has to be identified with a genuine Hecke zero's order. -/
theorem boundary_integrable_orders
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => Integrable (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x)) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  rw [← boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, boundaryJetOrders,
    boundaryRadialJet_integrable_iff m s alpha beta hs ha hb]
end Masullo.RadialJetDensityEven

namespace Masullo.BoundaryDensityIntegrablePullbackIff
open MeasureTheory Masullo.RadialJetDensity Masullo.RadialJetDensityEven

/-- Conditional measure bridge for the actual log-norm map: a nonzero finite
Haar scaling preserves the sharp radial boundary criterion. Discharges the
measure-transport premise, not the genuine idele-class pushforward identity. -/
theorem boundary_density_integrable_pullback_iff
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (hell : AEMeasurable ell mu) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    Integrable (fun x => Real.exp (2 * beta * ell x - 2 * alpha * |ell x|) *
      radialJetDensity m s (ell x)) mu ↔ (2 : ℝ) * m + 1 < s := by
  let d : ℝ → ℝ := fun x =>
    Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x
  have hc : Continuous (radialJetDensity m s) := by
    unfold radialJetDensity
    exact (continuous_id.pow _).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (by positivity)))
  have hd : Continuous d :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hc
  have ht := integrable_map_measure
    (μ := mu) (f := ell) (g := d) hd.aestronglyMeasurable hell
  rw [hmap, integrable_smul_measure hc0 hct] at ht
  exact ht.symm.trans (boundaryRadialJet_integrable_iff m s alpha beta hs ha hb)

/-- The scalar weight-normalized Mellin jet. The phase is any Circle-valued
function, including an actual unitary character times its imaginary norm twist.
This defines no operator, spectrum, or L-function. -/
noncomputable def weightedMellinJet {X : Type*} (ell : X → ℝ)
    (phase : X → Circle) (m : ℕ) (s alpha beta : ℝ) (x : X) : ℂ :=
  (phase x : ℂ) * ((Real.exp (beta * ell x - alpha * |ell x|) *
    (ell x)^m * (1 + (ell x)^2)^(-s / 4) : ℝ) : ℂ)

/-- Discharges the pointwise squared-norm identity for the explicit weighted
jet; no integrability assumption or zero enumeration enters the identity. -/
theorem weightedMellinJet_sq_norm {X : Type*} (ell : X → ℝ)
    (phase : X → Circle) (m : ℕ) (s alpha beta : ℝ) (x : X) :
    ‖weightedMellinJet ell phase m s alpha beta x‖^2 =
      Real.exp (2 * beta * ell x - 2 * alpha * |ell x|) *
        radialJetDensity m s (ell x) := by
  unfold weightedMellinJet radialJetDensity
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, mul_pow, ← Real.exp_nat_mul, ← pow_mul,
    ← Real.rpow_natCast ((1 + (ell x)^2)^(-s / 4)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ 1 + (ell x)^2)]
  ring_nf

/-- Conditional native-membership bridge: for an explicit weighted jet and
an actual log-norm pushforward, square integrability has the sharp boundary
cutoff. Native Haar splitting and weighted-dual representation remain open. -/
theorem boundary_weightedMellinJet_memLp_iff
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : AEMeasurable ell mu)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha)
    (hf : AEStronglyMeasurable (weightedMellinJet ell phase m s alpha beta) mu) :
    MemLp (weightedMellinJet ell phase m s alpha beta) 2 mu ↔
      (2 : ℝ) * m + 1 < s := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  simp only [weightedMellinJet_sq_norm]
  exact boundary_density_integrable_pullback_iff mu ell hell c hc0 hct hmap
    m s alpha beta hs ha hb

end Masullo.BoundaryDensityIntegrablePullbackIff

namespace Masullo.BoundaryDensityIntegrablePullbackIff
open MeasureTheory Masullo.BoundaryJetOrders
attribute [local instance] Classical.propDecidable
/-- Measurability follows from the log norm and unitary phase; discharges
this hypothesis of boundary weighted-jet membership without assuming it. -/
theorem weightedMellinJet_measurable
    {X : Type*} [MeasurableSpace X] (ell : X → ℝ) (phase : X → Circle)
    (hell : Measurable ell) (hphase : Measurable (fun x => (phase x : ℂ)))
    (m : ℕ) (s alpha beta : ℝ) :
    Measurable (weightedMellinJet ell phase m s alpha beta) := by
  unfold weightedMellinJet
  fun_prop

/-- Conditional exact multiplicity truncation for the explicit weighted jets.
The only geometric input is the actual log-norm Haar pushforward; N must
still be identified with the genuine Hecke analytic zero order. -/
theorem boundary_weightedMellinJet_orders
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : Measurable ell) (hphase : Measurable (fun x => (phase x : ℂ)))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (weightedMellinJet ell phase m s alpha beta) 2 mu) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  rw [← boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, boundaryJetOrders,
    boundary_weightedMellinJet_memLp_iff mu ell phase hell.aemeasurable
      c hc0 hct hmap m s alpha beta hs ha hb
      (weightedMellinJet_measurable ell phase hell hphase m s alpha beta).aestronglyMeasurable]

end Masullo.BoundaryDensityIntegrablePullbackIff

namespace Masullo.InteriorDensityLeExpPolynomial
open MeasureTheory Set Masullo.RadialJetDensity Masullo.RadialJetDensityEven Masullo.BoundaryDensityIntegrablePullbackIff

/-- The interior membership premise of (10.2.2.6): the actual squared
radial jet density is dominated by an exponentially damped polynomial.
This is a pointwise analytic bound, not a zero or spectrum definition. -/
theorem interior_density_le_exp_polynomial
    (m : ℕ) (s alpha beta x : ℝ) (hs : 0 ≤ s) :
    Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x ≤
      Real.exp (-(2 * (alpha - |beta|)) * |x|) * x ^ (2 * m) := by
  have hp : 0 ≤ x ^ (2 * m) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) m
  have hw : (1 + x ^ 2) ^ (-s / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)
  have hb : beta * x ≤ |beta| * |x| := by
    simpa only [abs_mul] using (le_abs_self (beta * x))
  have he : Real.exp (2 * beta * x - 2 * alpha * |x|) ≤
      Real.exp (-(2 * (alpha - |beta|)) * |x|) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (2 * beta * x - 2 * alpha * |x|) * x ^ (2 * m) := by
      unfold radialJetDensity
      exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left hw hp)
        (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right he hp

end Masullo.InteriorDensityLeExpPolynomial

namespace Masullo.InteriorDensityLeExpPolynomial
open MeasureTheory Set Masullo.RadialJetDensity Masullo.RadialJetDensityEven Masullo.BoundaryDensityIntegrablePullbackIff
/-- The integrable majorant required by the interior jet bound. -/
theorem exp_abs_even_polynomial_integrable (m : ℕ) (d : ℝ) (hd : 0 < d) :
    Integrable (fun x : ℝ => Real.exp (-d * |x|) * x ^ (2 * m)) := by
  let g : ℝ → ℝ := fun x => Real.exp (-d * |x|) * x ^ (2 * m)
  have hc : Continuous g := by dsimp [g]; fun_prop
  have ht : IntegrableOn (fun x : ℝ => x ^ (2 * m) * Real.exp (-d * x)) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 * m : ℕ)) (p := 1)
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num) hd)
  have hg : IntegrableOn g (Ioi 0) := ht.congr_fun (by
    intro x hx
    dsimp [g]
    rw [abs_of_pos hx, mul_comm]) measurableSet_Ioi
  have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hp : IntegrableOn g (Ici 0) := by
    rw [← hu]
    exact (hc.integrableOn_Icc).union (hg.mono_set (by intro x hx; change (0 : ℝ) < x; change (1 : ℝ) < x at hx; linarith))
  have hn : IntegrableOn g (Iic 0) := by
    simpa [g, pow_mul] using hp.comp_neg
  have hall : Ici (0 : ℝ) ∪ Iic 0 = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 x
  simpa only [hall, integrableOn_univ] using hp.union hn

/-- All finite radial jet orders are integrable strictly inside the strip;
this discharges the analytic all-orders premise of (10.2.2.6). -/
theorem interiorRadialJet_integrable (m : ℕ) (s alpha beta : ℝ)
    (hs : 0 ≤ s) (hb : |beta| < alpha) :
    Integrable (fun x : ℝ => Real.exp (2 * beta * x - 2 * alpha * |x|) *
      radialJetDensity m s x) := by
  have hc : Continuous (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x) := by
    have hr : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hr
  apply (exp_abs_even_polynomial_integrable m (2 * (alpha - |beta|))
    (by linarith)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hn : 0 ≤ radialJetDensity m s x := by
    unfold radialJetDensity
    exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
      (Real.rpow_nonneg (by positivity) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hn)]
  exact interior_density_le_exp_polynomial m s alpha beta x hs

/-- Conditional native measure transport of the full interior membership
criterion. The actual Haar pushforward and native dual realization remain
application obligations; no zero set or spectral operator is prescribed. -/
theorem interior_weightedMellinJet_memLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : Measurable ell)
    (hphase : Measurable (fun x => (phase x : ℂ)))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (hb : |beta| < alpha) :
    MemLp (weightedMellinJet ell phase m s alpha beta) 2 mu := by
  rw [memLp_two_iff_integrable_sq_norm
    (weightedMellinJet_measurable ell phase hell hphase m s alpha beta).aestronglyMeasurable]
  simp only [weightedMellinJet_sq_norm]
  let d : ℝ → ℝ := fun x => Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x
  have hd : Continuous d := by
    dsimp [d]
    have hr : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hr
  have ht := integrable_map_measure (μ := mu) (f := ell) (g := d)
    hd.aestronglyMeasurable hell.aemeasurable
  rw [hmap, integrable_smul_measure hc0 hct] at ht
  exact ht.mp (interiorRadialJet_integrable m s alpha beta hs hb)

end Masullo.InteriorDensityLeExpPolynomial

namespace Masullo.GenuineNormalizedMellinJet
open MasulloGRH Masullo.IdeleClassGeometry Masullo.BoundaryDensityIntegrablePullbackIff MeasureTheory
variable (K : Type*) [Field K] [NumberField K]
/-- Discharges the actual character/complex-parameter attachment premise of
native jet integrability. The imaginary parameter is retained in the function. -/
theorem genuineNormalizedMellinJet_norm (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineNormalizedMellinJet K χ z a s alpha m x‖ =
      ‖weightedMellinJet (classLog K) (classCharacter K χ) m s alpha (z.re-a) x‖ := by
  simp only [genuineNormalizedMellinJet, weightedMellinJet, norm_mul,
    Circle.norm_coe, one_mul, Complex.norm_exp, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- Conditional sharp native boundary criterion for the genuine character and
complex Mellin parameter. Only the actual Haar pushforward is supplied; the
zero order and weighted-dual/common-kernel realization remain separate gaps. -/
theorem genuine_boundary_mellin_memLp_iff (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) :
    MemLp (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu ↔
      (2 : ℝ) * m + 1 < s := by
  have hchi : Measurable (fun x => (classCharacter K χ x : ℂ)) :=
    (continuous_subtype_val.comp (classCharacter_continuous K χ)).measurable
  have hell := (Masullo.WeightedIdeleClass.classLog_continuous K).measurable
  have hg : Measurable (genuineNormalizedMellinJet K χ z a s alpha m) := by
    unfold genuineNormalizedMellinJet
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simp only [genuineNormalizedMellinJet_norm, weightedMellinJet_sq_norm]
  exact boundary_density_integrable_pullback_iff mu (classLog K) hell.aemeasurable
    c hc0 hct hmap m s alpha (z.re-a) hs ha hb

end Masullo.GenuineNormalizedMellinJet

namespace Masullo.GenuineNormalizedMellinJet
open MasulloGRH Masullo.IdeleClassGeometry Masullo.BoundaryDensityIntegrablePullbackIff Masullo.InteriorDensityLeExpPolynomial MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Interior counterpart for the genuine complex Mellin jet; discharges the
all-finite-orders membership premise of (10.2.2.6), conditionally on Haar transport. -/
theorem genuine_interior_mellin_memLp (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (hb : |z.re-a| < alpha) :
    MemLp (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu := by
  have hchi : Measurable (fun x => (classCharacter K χ x : ℂ)) :=
    (continuous_subtype_val.comp (classCharacter_continuous K χ)).measurable
  have hell := (Masullo.WeightedIdeleClass.classLog_continuous K).measurable
  have hg : Measurable (genuineNormalizedMellinJet K χ z a s alpha m) := by
    unfold genuineNormalizedMellinJet
    fun_prop
  have hi := interior_weightedMellinJet_memLp mu (classLog K) (classCharacter K χ)
    hell hchi c hc0 hct hmap m s alpha (z.re-a) hs hb
  rw [memLp_two_iff_integrable_sq_norm
    (weightedMellinJet_measurable (classLog K) (classCharacter K χ) hell hchi
      m s alpha (z.re-a)).aestronglyMeasurable] at hi
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simpa only [genuineNormalizedMellinJet_norm] using hi

/-- Exact boundary truncation after actual-character attachment. N is still
an external finite order; identifying it with analytic Hecke multiplicity is OPEN. -/
theorem genuine_boundary_mellin_orders (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (N : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu) =
      Finset.range (min N (Nat.ceil ((s-1)/2))) := by
  classical
  rw [← Masullo.BoundaryJetOrders.boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, Masullo.BoundaryJetOrders.boundaryJetOrders,
    genuine_boundary_mellin_memLp_iff K χ mu c hc0 hct hmap z a s alpha m hs ha hb]

end Masullo.GenuineNormalizedMellinJet

namespace MasulloGRH.NativeTateConverse
open MeasureTheory Set Topology Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet

/-- Strict admission gives membership on the SAME Haar measure, including the
zero-width case only through its single boundary condition. -/
theorem native_admitted_memLp
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadm : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s)) :
    MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu := by
  rcases hadm with hi | ⟨hb, hm⟩
  · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap z a s alpha m hs hi
  · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap z a s alpha m hs ha hb).mpr hm

end MasulloGRH.NativeTateConverse


/- B application fragment. Insert after BFullJetGramFragment and RBoundaryFragment.
   R owns the analytic admission proof; B applies it to the full finite flags. -/
namespace BGramApplications
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.ActualGram
open Masullo.GramDualPairingIntegrable
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Full multiplicity in the strict interior; R's strict truncation on the boundary.
This count is used below only for parameters in the closed strip. -/
def stripJetCount (z : ℂ) (a s alpha : ℝ) (N : ℕ) : ℕ :=
  if |z.re-a| < alpha then N else min N (Nat.ceil ((s-1)/2))

/-- All labels of the concrete retained flag satisfy R's numerical admission. -/
theorem stripJetCount_admitted (z : ℂ) (a s alpha : ℝ) (N m : ℕ)
    (hstrip : |z.re-a| ≤ alpha) (hm : m < stripJetCount z a s alpha N) :
    |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s) := by
  by_cases hi : |z.re-a| < alpha
  · exact Or.inl hi
  · have hb : |z.re-a| = alpha := le_antisymm hstrip (le_of_not_gt hi)
    have hm' : m < Nat.ceil ((s-1)/2) :=
      (Nat.lt_min.mp (by simpa only [stripJetCount, if_neg hi] using hm)).2
    have hmreal : (m : ℝ) < (s-1)/2 := Nat.lt_ceil.mp hm'
    exact Or.inr ⟨hb, by linarith⟩

/-- Application of the analytic source theorem to every retained actual jet.
The per-vector MemLp premises of the Gram formula are proved here. -/
theorem strip_fullJet_memLp {J : Type*}
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : J → ℂ) (N : J → ℕ) (a s alpha : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ alpha) (hstrip : ∀ j, |(z j).re-a| ≤ alpha) :
    ∀ i : Sigma (fun j => Fin (stripJetCount (z j) a s alpha (N j))),
      MemLp (genuineNormalizedMellinJet K chi (z i.1) a s alpha i.2.val) 2 mu := by
  intro i
  exact MasulloGRH.NativeTateConverse.native_admitted_memLp K chi mu c hc0 hct hmap
    (z i.1) a s alpha i.2.val hs ha
    (stripJetCount_admitted (z i.1) a s alpha (N i.1) i.2.val (hstrip i.1) i.2.isLt)

/-- The manuscript's finite strict-interior/boundary flags have nonsingular
actual Gram and downward closure. No MemLp, independence or determinant premise
is left; original-Haar log transport remains explicitly required. -/
theorem actual_strip_Gram_application {J : Type*} [Fintype J] [DecidableEq J]
    (mu : Measure (HeckeIdeleClasses K)) (chi : UnitaryHeckeCharacter K)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : J → ℂ) (hz : Function.Injective z) (N : J → ℕ) (a s alpha : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ alpha) (hstrip : ∀ j, |(z j).re-a| ≤ alpha) :
    let n := fun j => stripJetCount (z j) a s alpha (N j)
    IsUnit (actualGram K mu (fun _ : Sigma (fun j => Fin (n j)) => chi)
      (fun i => z i.1) a s alpha (fun i => i.2.val)).det ∧
      JetClosed K (fun _ : Sigma (fun j => Fin (n j)) => chi)
        (fun i => z i.1) (fun i => i.2.val) := by
  dsimp only
  exact actual_fullJet_Gram_application K mu chi c hc0 hmap z hz
    (fun j => stripJetCount (z j) a s alpha (N j)) a s alpha
    (strip_fullJet_memLp K mu chi c hc0 hct hmap z N a s alpha hs ha hstrip)

end
end BGramApplications
#print BGramApplications.actual_strip_Gram_application
#print axioms BGramApplications.actual_strip_Gram_application
