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

namespace Masullo.GramPAColumnFormula
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.TransposeDiagonalIntegrable Masullo.ActualGram Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped BigOperators Matrix
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual PA tensor has precisely the inverse-Gram column coefficients.
This identifies two specified pointwise representatives; no product-a.e.
equality is restricted to the diagonal. -/
theorem actual_Gram_PA_column_formula
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (x y : HeckeIdeleClasses K) :
    finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x y =
    ∑ j, ((actualGram K mu chi z a s alpha m)⁻¹ *ᵥ
      (fun i => ∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu)) j *
        actualRiesz K (chi j) (z j) a s alpha (m j) x := by
  simp only [finitePAKernel, actualGramDual, Matrix.mulVec, dotProduct]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The same specified column in the native half-weight realization. It is
exactly the coefficient expression in the genuine orthogonal PA column
calculation after the inspected actual Gram/L2 entry identification. -/
theorem actual_Gram_PA_normalized_column
    (mu : Measure (HeckeIdeleClasses K)) (chi : ι → UnitaryHeckeCharacter K)
    (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (h : HeckeIdeleClasses K → ℂ) (x y : HeckeIdeleClasses K) :
    (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      finitePAKernel K Finset.univ mu chi z a m h
        (actualGramDual K mu chi z a s alpha m) x y =
    ∑ j, ((actualGram K mu chi z a s alpha m)⁻¹ *ᵥ
      (fun i => ∫ g, h g * genuineMellinJet K (chi i) (z i) a (m i) (g*y) ∂mu)) j *
        star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j) x) := by
  rw [actual_Gram_PA_column_formula, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_left_comm, actualRiesz_weighted]

#print axioms actual_Gram_PA_column_formula
#print axioms actual_Gram_PA_normalized_column
end Masullo.GramPAColumnFormula

namespace Masullo.GenuineMellinJet
theorem nativeHalfWeight_pos (alpha s t : ℝ) : 0 < nativeHalfWeight alpha s t := Masullo.ActualRiesz.halfWeight_pos alpha s t
end Masullo.GenuineMellinJet
namespace Masullo.NativeHalfWeightAddLe
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet

/-- The actual half-weight has a finite, explicit translation bound. This is
 the weight estimate needed in the proof of manuscript Lemma 9.3.1.5. -/
theorem nativeHalfWeight_add_le (alpha s u t : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    nativeHalfWeight alpha s (u+t) ≤
      (Real.exp (alpha * |u|) * (2*(1+u^2))^(s/4)) * nativeHalfWeight alpha s t := by
  have hab : alpha * |u+t| ≤ alpha * |u| + alpha * |t| := by
    nlinarith [abs_add_le u t]
  have hex : Real.exp (alpha * |u+t|) ≤
      Real.exp (alpha * |u|) * Real.exp (alpha * |t|) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hab
  have hpoly : 1+(u+t)^2 ≤ (2*(1+u^2))*(1+t^2) := by
    nlinarith [sq_nonneg (u-t), sq_nonneg (u*t)]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1+(u+t)^2) hpoly
    (by positivity : 0 ≤ s/4)
  rw [Real.mul_rpow (by positivity) (by positivity)] at hp
  unfold nativeHalfWeight
  calc
    _ ≤ (Real.exp (alpha * |u|) * Real.exp (alpha * |t|)) *
        ((2*(1+u^2))^(s/4) * (1+t^2)^(s/4)) :=
      mul_le_mul hex hp (by positivity) (by positivity)
    _ = _ := by ring

variable (K : Type*) [Field K] [NumberField K]

theorem actual_halfWeight_continuous (alpha s : ℝ) (hs : 0 ≤ s) :
    Continuous (fun x : HeckeIdeleClasses K =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ)) := by
  have hl := classLog_continuous K
  unfold nativeHalfWeight
  fun_prop (disch := positivity)

/-- Original same-Haar weighted L2 is preserved by actual left translation.
No spectral operator or arbitrary diagonal is supplied as a hypothesis. -/
theorem actual_weighted_translation_memLp
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (g : HeckeIdeleClasses K) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f (g⁻¹*x)) 2 mu := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hw : Continuous w := actual_halfWeight_continuous K alpha s hs
  have hn (x : HeckeIdeleClasses K) : w x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (ne_of_gt (nativeHalfWeight_pos alpha s (classLog K x)))
  have hfm : AEStronglyMeasurable f mu := by
    have hi : Continuous (fun x => (w x)⁻¹) := hw.inv₀ hn
    have hm := hf.aestronglyMeasurable.mul hi.aestronglyMeasurable
    convert hm using 1
    funext x
    change f x = (w x * f x) * (w x)⁻¹
    rw [mul_comm (w x) (f x), mul_assoc, mul_inv_cancel₀ (hn x), mul_one]
  have hmp := measurePreserving_mul_left mu g⁻¹
  have hfshift := hf.comp_measurePreserving hmp
  have hmeas : AEStronglyMeasurable (fun x => w x * f (g⁻¹*x)) mu :=
    hw.aestronglyMeasurable.mul (hfm.comp_measurePreserving hmp)
  apply hfshift.of_le_mul hmeas
    (c := Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4))
  apply Filter.Eventually.of_forall
  intro x
  change ‖w x * f (g⁻¹*x)‖ ≤ _ * ‖w (g⁻¹*x) * f (g⁻¹*x)‖
  have he : classLog K x = classLog K g + classLog K (g⁻¹*x) := by
    rw [← classLog_mul, mul_inv_cancel_left]
  have hb := nativeHalfWeight_add_le alpha s (classLog K g) (classLog K (g⁻¹*x)) ha hs
  rw [← he] at hb
  simp only [norm_mul, w, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (nativeHalfWeight_pos alpha s _)]
  calc
    _ ≤ ((Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) *
      nativeHalfWeight alpha s (classLog K (g⁻¹*x))) * ‖f (g⁻¹*x)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by ring

/-- Quantitative same-Haar bound for the ACTUAL native weighted translation,
not an assumed boundedness constant for a postulated operator. -/
theorem actual_weighted_translation_eLpNorm
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (g : HeckeIdeleClasses K) :
    eLpNorm (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f (g⁻¹*x)) 2 mu ≤
      ENNReal.ofReal (Real.exp (alpha * |classLog K g|) *
        (2*(1+(classLog K g)^2))^(s/4)) *
      eLpNorm (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hb : ∀ x, ‖w x * f (g⁻¹*x)‖ ≤
      (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) *
      ‖w (g⁻¹*x) * f (g⁻¹*x)‖ := by
    intro x
    have he : classLog K x = classLog K g + classLog K (g⁻¹*x) := by
      rw [← classLog_mul, mul_inv_cancel_left]
    have ht := nativeHalfWeight_add_le alpha s (classLog K g) (classLog K (g⁻¹*x)) ha hs
    rw [← he] at ht
    simp only [norm_mul, w, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (nativeHalfWeight_pos alpha s _)]
    calc
      _ ≤ ((Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) *
        nativeHalfWeight alpha s (classLog K (g⁻¹*x))) * ‖f (g⁻¹*x)‖ :=
        mul_le_mul_of_nonneg_right ht (norm_nonneg _)
      _ = _ := by ring
  have H := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := mu) (Filter.Eventually.of_forall hb) 2
  have heq := eLpNorm_comp_measurePreserving hf.aestronglyMeasurable
    (measurePreserving_mul_left mu g⁻¹) (p := 2)
  exact H.trans_eq (congrArg (fun n => ENNReal.ofReal
    (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) * n) heq)

/-- The original weighted Hilbert norm bound, on normalized representatives. -/
theorem actual_weighted_translation_norm
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (g : HeckeIdeleClasses K) :
    ‖(actual_weighted_translation_memLp K mu alpha s ha hs f hf g).toLp _‖ ≤
      (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) * ‖hf.toLp _‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  have h := actual_weighted_translation_eLpNorm K mu alpha s ha hs f hf g
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_lt_top.ne) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    0 ≤ Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4))] using ht

#print axioms nativeHalfWeight_add_le
#print axioms actual_halfWeight_continuous
#print axioms actual_weighted_translation_memLp
#print axioms actual_weighted_translation_eLpNorm
#print axioms actual_weighted_translation_norm
end Masullo.NativeHalfWeightAddLe

noncomputable section
namespace Masullo.NativeRep
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe
variable (K : Type*) [Field K] [NumberField K]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

/-- The actual original weighted representative of a normalized L2 vector. -/
def nativeRep (F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) : ℂ :=
  F x / (nativeHalfWeight alpha s (classLog K x) : ℂ)

omit [mu.IsMulLeftInvariant] in
theorem nativeRep_normalization (F : Lp ℂ 2 mu) (x : HeckeIdeleClasses K) :
    (nativeHalfWeight alpha s (classLog K x) : ℂ) * nativeRep K mu alpha s F x = F x := by
  have hn : (nativeHalfWeight alpha s (classLog K x) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (nativeHalfWeight_pos _ _ _))
  dsimp [nativeRep]
  field_simp

omit [mu.IsMulLeftInvariant] in
theorem nativeRep_memLp (F : Lp ℂ 2 mu) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      nativeRep K mu alpha s F x) 2 mu := by
  simpa only [nativeRep_normalization] using Lp.memLp F

def nativeTranslation (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  (actual_weighted_translation_memLp K mu alpha s ha hs
    (nativeRep K mu alpha s F) (nativeRep_memLp K mu alpha s F) g).toLp _

theorem nativeTranslation_ae (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    (nativeTranslation K mu alpha s ha hs g F : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
      fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        (F (g⁻¹*x) / (nativeHalfWeight alpha s (classLog K (g⁻¹*x)) : ℂ)) :=
  MemLp.coeFn_toLp _

def nativeTranslationLinear (g : HeckeIdeleClasses K) : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun := nativeTranslation K mu alpha s ha hs g
  map_add' F G := by
    apply Lp.ext
    have hadd := (measurePreserving_mul_left mu g⁻¹).quasiMeasurePreserving.ae (Lp.coeFn_add F G)
    filter_upwards [nativeTranslation_ae K mu alpha s ha hs g (F+G),
      nativeTranslation_ae K mu alpha s ha hs g F,
      nativeTranslation_ae K mu alpha s ha hs g G,
      Lp.coeFn_add (nativeTranslation K mu alpha s ha hs g F)
        (nativeTranslation K mu alpha s ha hs g G), hadd] with x h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h4, h2, h3, h5]
    ring
  map_smul' c F := by
    apply Lp.ext
    have hsmul := (measurePreserving_mul_left mu g⁻¹).quasiMeasurePreserving.ae (Lp.coeFn_smul c F)
    filter_upwards [nativeTranslation_ae K mu alpha s ha hs g (c • F),
      nativeTranslation_ae K mu alpha s ha hs g F,
      Lp.coeFn_smul c (nativeTranslation K mu alpha s ha hs g F), hsmul] with x h1 h2 h3 h4
    simp only [Pi.smul_apply, smul_eq_mul] at h3 h4
    change _ = (c • nativeTranslation K mu alpha s ha hs g F) x
    rw [h1, h3, h2, h4]
    ring

theorem nativeTranslation_norm (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    ‖nativeTranslation K mu alpha s ha hs g F‖ ≤
      (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)) * ‖F‖ := by
  have ht := actual_weighted_translation_norm K mu alpha s ha hs
    (nativeRep K mu alpha s F) (nativeRep_memLp K mu alpha s F) g
  have he : (nativeRep_memLp K mu alpha s F).toLp _ = F := by
    apply Lp.ext
    filter_upwards [(nativeRep_memLp K mu alpha s F).coeFn_toLp] with x hx
    simpa only [nativeRep_normalization] using hx
  simpa only [nativeTranslation, he] using ht

/-- Actual bounded left translation on the original weighted Hilbert space,
expressed through the original half-weight isometry, with unchanged Haar. -/
def nativeTranslationCLM (g : HeckeIdeleClasses K) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (nativeTranslationLinear K mu alpha s ha hs g).mkContinuous
    (Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4))
    (nativeTranslation_norm K mu alpha s ha hs g)

theorem nativeTranslationCLM_ae (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    (nativeTranslationCLM K mu alpha s ha hs g F : HeckeIdeleClasses K → ℂ) =ᵐ[mu]
      fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        (F (g⁻¹*x) / (nativeHalfWeight alpha s (classLog K (g⁻¹*x)) : ℂ)) :=
  nativeTranslation_ae K mu alpha s ha hs g F

#print axioms nativeTranslationCLM
#print axioms nativeTranslationCLM_ae
end Masullo.NativeRep
end

namespace Masullo.NativeTranslationWeaklyMeasurable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe Masullo.NativeRep
variable (K : Type*) [Field K] [NumberField K]

/-- The actual same-Haar weighted translation is weakly measurable on every
native Hilbert vector. This supplies the scalar Pettis input in manuscript
Definition 9.3.1.1 without assuming orbit or coefficient measurability. -/
theorem nativeTranslation_weaklyMeasurable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (F V : Lp ℂ 2 mu) :
    StronglyMeasurable (fun g => inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F)) := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hw : Measurable w := (actual_halfWeight_continuous K alpha s hs).measurable
  have hm : Measurable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => p.1⁻¹*p.2) :=
    measurable_fst.inv.mul measurable_snd
  have hk : StronglyMeasurable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      w p.2 * (F (p.1⁻¹*p.2) / w (p.1⁻¹*p.2))) :=
    ((hw.comp measurable_snd).mul
      (((Lp.stronglyMeasurable F).measurable.comp hm).div (hw.comp hm))).stronglyMeasurable
  have hi : StronglyMeasurable (Function.uncurry (fun g x =>
      inner ℂ (V x) (w x * (F (g⁻¹*x) / w (g⁻¹*x))))) :=
    ((Lp.stronglyMeasurable V).comp_measurable measurable_snd).inner hk
  have he : (fun g => inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F)) =
      (fun g => ∫ x, inner ℂ (V x) (w x * (F (g⁻¹*x) / w (g⁻¹*x))) ∂mu) := by
    funext g
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs g F] with x hx
    rw [hx]
  rw [he]
  exact hi.integral_prod_right

#print axioms nativeTranslation_weaklyMeasurable
end Masullo.NativeTranslationWeaklyMeasurable

namespace Masullo.NativeTranslationBound
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.WeightedIdeleClass Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe
variable (K : Type*) [Field K] [NumberField K]

noncomputable def nativeTranslationBound (alpha s : ℝ) (g : HeckeIdeleClasses K) : ℝ :=
  Real.exp (alpha * |classLog K g|) * (2*(1+(classLog K g)^2))^(s/4)

/-- The actual compact test supplies the integrable operator-norm envelope
needed for the Pettis/Bochner convolution in manuscript (9.3.1.2). -/
theorem native_convolution_envelope_integrable
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    (alpha s : ℝ) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h) :
    Integrable (fun g => ‖h g‖ * nativeTranslationBound K alpha s g) mu := by
  have ht : Continuous (nativeTranslationBound K alpha s) := by
    unfold nativeTranslationBound
    have hl := classLog_continuous K
    fun_prop (disch := positivity)
  exact (hh.norm.mul ht).integrable_of_hasCompactSupport (hc.norm.mul_right)

end Masullo.NativeTranslationBound

namespace Masullo.NativeTranslationWeaklyMeasurable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe Masullo.NativeRep Masullo.NativeTranslationBound
variable (K : Type*) [Field K] [NumberField K]

/-- Every Hilbert scalar test of the ACTUAL compact-kernel convolution is
integrable. This is the scalar integrability prerequisite of Pettis integration,
proved from native weak measurability and the reused norm envelope. -/
theorem native_convolution_scalar_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
    [IsLocallyFiniteMeasure mu]
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (F V : Lp ℂ 2 mu) :
    Integrable (fun g => h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F)) mu := by
  have hi := (native_convolution_envelope_integrable K mu alpha s hs h hh hc).mul_const
    (‖F‖ * ‖V‖)
  have hm := hh.stronglyMeasurable.mul (nativeTranslation_weaklyMeasurable K mu alpha s ha hs F V)
  apply hi.mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro g
  have hb : ‖nativeTranslationCLM K mu alpha s ha hs g F‖ ≤
      nativeTranslationBound K alpha s g * ‖F‖ :=
    nativeTranslation_norm K mu alpha s ha hs g F
  simp only [Pi.mul_apply]
  rw [norm_mul]
  calc
    _ ≤ ‖h g‖ * (‖V‖ * ‖nativeTranslationCLM K mu alpha s ha hs g F‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm V _) (norm_nonneg _)
    _ ≤ ‖h g‖ * (‖V‖ * (nativeTranslationBound K alpha s g * ‖F‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
    _ = (‖h g‖ * nativeTranslationBound K alpha s g) * (‖F‖ * ‖V‖) := by ring

#print axioms native_convolution_scalar_integrable
end Masullo.NativeTranslationWeaklyMeasurable

noncomputable section
namespace Masullo.NativePettisLinear
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineMellinJet Masullo.NativeHalfWeightAddLe
open Masullo.NativeRep Masullo.NativeTranslationWeaklyMeasurable Masullo.NativeTranslationBound
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)

/-- The conjugate scalar integral is a genuine linear form on the original
weighted Hilbert space, with the same Haar and actual inverse translations. -/
def nativePettisLinear (F : Lp ℂ 2 mu) : Lp ℂ 2 mu →ₗ[ℂ] ℂ where
  toFun V := star (∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu)
  map_add' V W := by
    simp only [inner_add_left, mul_add]
    rw [integral_add
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc F V)
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc F W), star_add]
  map_smul' c V := by
    simp only [RingHom.id_apply, smul_eq_mul]
    have he : (fun g => h g * inner ℂ (c • V)
        (nativeTranslationCLM K mu alpha s ha hs g F)) =
        (fun g => (starRingEnd ℂ c) * (h g * inner ℂ V
          (nativeTranslationCLM K mu alpha s ha hs g F))) := by
      funext g
      rw [inner_smul_left]
      ring
    rw [he, integral_const_mul, star_mul]
    simp [mul_comm]

theorem nativePettisLinear_bound (F V : Lp ℂ 2 mu) :
    ‖nativePettisLinear K mu alpha s ha hs h hh hc F V‖ ≤
      ((∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu) * ‖F‖) * ‖V‖ := by
  change ‖star (∫ g, h g * inner ℂ V
    (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu)‖ ≤ _
  rw [norm_star]
  have hi := (native_convolution_envelope_integrable K mu alpha s hs h hh hc).mul_const
    (‖F‖ * ‖V‖)
  calc
    _ ≤ ∫ g, (‖h g‖ * nativeTranslationBound K alpha s g) * (‖F‖ * ‖V‖) ∂mu := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with g
      rw [norm_mul]
      have hb : ‖nativeTranslationCLM K mu alpha s ha hs g F‖ ≤
          nativeTranslationBound K alpha s g * ‖F‖ :=
        nativeTranslation_norm K mu alpha s ha hs g F
      calc
        _ ≤ ‖h g‖ * (‖V‖ * ‖nativeTranslationCLM K mu alpha s ha hs g F‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm V _) (norm_nonneg _)
        _ ≤ ‖h g‖ * (‖V‖ * (nativeTranslationBound K alpha s g * ‖F‖)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hb (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [integral_mul_const]; ring

def nativePettisDual (F : Lp ℂ 2 mu) : Lp ℂ 2 mu →L[ℂ] ℂ :=
  (nativePettisLinear K mu alpha s ha hs h hh hc F).mkContinuous
    ((∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu) * ‖F‖)
    (nativePettisLinear_bound K mu alpha s ha hs h hh hc F)

/-- Construct the original Pettis convolution vector; no orbit-integrability
or postulated convolution operator is an input. -/
def nativePettisVector (F : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 mu)).symm
    (nativePettisDual K mu alpha s ha hs h hh hc F)

theorem nativePettisVector_pairing (F V : Lp ℂ 2 mu) :
    inner ℂ V (nativePettisVector K mu alpha s ha hs h hh hc F) =
      ∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu := by
  have ht : inner ℂ (nativePettisVector K mu alpha s ha hs h hh hc F) V =
      star (∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu) :=
    InnerProductSpace.toDual_symm_apply
  have ht' := congrArg (starRingEnd ℂ) ht
  rw [inner_conj_symm] at ht'
  simpa only [starRingEnd_apply, star_star] using ht'

#print axioms nativePettisLinear_bound
#print axioms nativePettisVector_pairing
end Masullo.NativePettisLinear
end

noncomputable section
namespace Masullo.NativePettisVectorBound
open MeasureTheory MasulloGRH Masullo.NativeRep Masullo.NativeTranslationWeaklyMeasurable Masullo.NativePettisLinear Masullo.NativeTranslationBound
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
variable (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)

theorem nativePettisVector_bound (F : Lp ℂ 2 mu) :
    ‖nativePettisVector K mu alpha s ha hs h hh hc F‖ ≤
      (∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu) * ‖F‖ := by
  rw [nativePettisVector, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound
  · apply mul_nonneg _ (norm_nonneg F)
    apply integral_nonneg
    intro g
    unfold nativeTranslationBound
    positivity
  · intro V
    exact nativePettisLinear_bound K mu alpha s ha hs h hh hc F V

def nativeConvolutionLinear : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu where
  toFun := nativePettisVector K mu alpha s ha hs h hh hc
  map_add' F G := by
    apply ext_inner_left ℂ
    intro V
    rw [inner_add_right]
    simp only [nativePettisVector_pairing]
    rw [← integral_add
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc F V)
      (native_convolution_scalar_integrable K mu alpha s ha hs h hh hc G V)]
    apply integral_congr_ae
    filter_upwards [] with g
    rw [map_add, inner_add_right, mul_add]
  map_smul' c F := by
    apply ext_inner_left ℂ
    intro V
    simp only [RingHom.id_apply, inner_smul_right, nativePettisVector_pairing]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with g
    rw [map_smul, inner_smul_right]
    ring

/-- Actual compact-kernel weak convolution on the native completed half-weight
realization. No bounded convolution or orbit-integrability premise is assumed. -/
def nativeConvolutionCLM : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  (nativeConvolutionLinear K mu alpha s ha hs h hh hc).mkContinuous
    (∫ g, ‖h g‖ * nativeTranslationBound K alpha s g ∂mu)
    (nativePettisVector_bound K mu alpha s ha hs h hh hc)

theorem nativeConvolutionCLM_pairing (F V : Lp ℂ 2 mu) :
    inner ℂ V (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∫ g, h g * inner ℂ V (nativeTranslationCLM K mu alpha s ha hs g F) ∂mu :=
  nativePettisVector_pairing K mu alpha s ha hs h hh hc F V

#print axioms nativePettisVector_bound
#print axioms nativeConvolutionCLM
#print axioms nativeConvolutionCLM_pairing
end Masullo.NativePettisVectorBound
end

namespace Masullo.WeightedConvolutionIntegrable
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeTranslatedProductIntegrable
variable (K : Type*) [Field K] [NumberField K]

/-- Attach the proven weighted-vector integrability to the ORIGINAL convolution
integrand by the actual quotient-Haar shear (g,x) ↦ (g,g⁻¹*x). -/
theorem actual_weighted_convolution_integrable
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m p.2 * f (p.1⁻¹*p.2)) (mu.prod mu) := by
  have hi := native_translated_product_integrable K mu chi z a s alpha m h f hh hs hg hf
  have hp : MeasurePreserving
      (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K => (p.1,p.1⁻¹*p.2))
      (mu.prod mu) (mu.prod mu) := by
    exact measurePreserving_prod_inv_mul mu mu
  have hr := (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  simpa only [Function.comp_def, mul_inv_cancel_left] using hr

/-- The actual SAME-Haar convolution paired with an admitted weighted vector.
The product-integrability/Fubini premise is proved, not assumed. -/
theorem actual_weighted_convolution_pairing
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu]
    [SFinite mu] [mu.IsMulLeftInvariant]
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (h f : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hs : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (hf : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    (∫ x, genuineMellinJet K chi z a m x * (∫ g, h g * f (g⁻¹*x) ∂mu) ∂mu) =
      ∫ g, h g * (∫ y, genuineMellinJet K chi z a m (g*y) * f y ∂mu) ∂mu := by
  have hi := actual_weighted_convolution_integrable K mu chi z a s alpha m h f hh hs hg hf
  have he : (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      h p.1 * genuineMellinJet K chi z a m p.2 * f (p.1⁻¹*p.2)) =
    (fun p => genuineMellinJet K chi z a m p.2 * (h p.1 * f (p.1⁻¹*p.2))) := by
    funext p; ring
  rw [he] at hi
  simp only [← integral_const_mul]
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  have hv := integral_mul_left_eq_self (μ := mu)
    (fun x => genuineMellinJet K chi z a m x * (h g * f (g⁻¹*x))) g
  dsimp only
  rw [← hv]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by simp only [inv_mul_cancel_left]; ring)

#print axioms actual_weighted_convolution_integrable
#print axioms actual_weighted_convolution_pairing
end Masullo.WeightedConvolutionIntegrable

namespace Masullo.NativePairingInner
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeRep Masullo.NativePettisVectorBound
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
variable (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant] [SFinite mu]
variable [IsLocallyFiniteMeasure mu]
variable (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)

 omit [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
   [mu.IsMulLeftInvariant] [SFinite mu] [IsLocallyFiniteMeasure mu] in
 theorem native_pairing_inner (j : HeckeIdeleClasses K → ℂ) (hj : MemLp j 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, j x * F x ∂mu) = inner ℂ (hj.star.toLp (star j)) F := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hj.star.coeFn_toLp] with x hx
  rw [hx]
  simp only [RCLike.inner_apply, Pi.star_apply, starRingEnd_apply, star_star]
  ring

 omit [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
   [SFinite mu] [IsLocallyFiniteMeasure mu] in
 theorem native_translation_mellin (chi : UnitaryHeckeCharacter K) (z : ℂ)
    (a : ℝ) (m : ℕ) (g : HeckeIdeleClasses K) (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z a s alpha m x *
      nativeTranslationCLM K mu alpha s ha hs g F x ∂mu) =
      ∫ y, genuineMellinJet K chi z a m (g*y) * nativeRep K mu alpha s F y ∂mu := by
  calc
    _ = ∫ x, genuineMellinJet K chi z a m x * nativeRep K mu alpha s F (g⁻¹*x) ∂mu := by
      apply integral_congr_ae
      filter_upwards [nativeTranslationCLM_ae K mu alpha s ha hs g F] with x hx
      rw [hx, ← mul_assoc, genuineMellinJet_normalization]
      rfl
    _ = _ := by
      have ht := integral_mul_left_eq_self (μ := mu)
        (fun x => genuineMellinJet K chi z a m x * nativeRep K mu alpha s F (g⁻¹*x)) g
      simpa only [inv_mul_cancel_left] using ht.symm

/-- Attach the constructed bounded Pettis convolution to the ACTUAL same-Haar
measured convolution, on every original normalized native Mellin functional.
Neither an operator action nor a scalar pairing identity is assumed. -/
theorem actual_bounded_convolution_mellin
    (chi : UnitaryHeckeCharacter K) (z : ℂ) (a : ℝ) (m : ℕ)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hg : ∀ k ≤ m, MemLp (genuineNormalizedMellinJet K chi z a s alpha k) 2 mu)
    (F : Lp ℂ 2 mu) :
    (∫ x, genuineNormalizedMellinJet K chi z a s alpha m x *
      nativeConvolutionCLM K mu alpha s ha hs h hh hc F x ∂mu) =
      ∫ x, genuineMellinJet K chi z a m x *
        (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu) ∂mu := by
  rw [native_pairing_inner K mu _ (hg m le_rfl), nativeConvolutionCLM_pairing]
  calc
    _ = ∫ g, h g * (∫ y, genuineMellinJet K chi z a m (g*y) *
        nativeRep K mu alpha s F y ∂mu) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [← native_pairing_inner K mu _ (hg m le_rfl),
        native_translation_mellin K mu alpha s ha hs chi z a m g F]
    _ = _ := (Masullo.WeightedConvolutionIntegrable.actual_weighted_convolution_pairing
      K mu chi z a s alpha m h (nativeRep K mu alpha s F) hh hc hg
      (nativeRep_memLp K mu alpha s F)).symm

#print axioms actual_bounded_convolution_mellin
end Masullo.NativePairingInner

namespace Masullo.InverseGramProjection
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.NativeRep Masullo.NativePettisVectorBound Masullo.NativePairingInner
open scoped InnerProductSpace Matrix BigOperators
noncomputable instance finiteSpan_finiteDim
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] (r : ι → H) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range r)) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range r)

/-- Explicit inverse-Gram coefficients determine the genuine orthogonal
projection, with the complex inner product linear in the second argument. -/
theorem inverseGram_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → H)
    (hG : IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j)))) (v : H) :
    (Submodule.span ℂ (Set.range r)).starProjection v =
      ∑ j, (((fun i j => inner ℂ (r i) (r j)) : Matrix ι ι ℂ)⁻¹ *ᵥ
        (fun i => inner ℂ (r i) v)) j • r j := by
  classical
  let E := Submodule.span ℂ (Set.range r)
  let G : Matrix ι ι ℂ := fun i j => inner ℂ (r i) (r j)
  let c := G⁻¹ *ᵥ (fun i => inner ℂ (r i) v)
  let p := ∑ j, c j • r j
  have hp : p ∈ E := by
    apply Submodule.sum_mem
    intro j hj
    exact E.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have heq : G *ᵥ c = (fun i => inner ℂ (r i) v) := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hi : ∀ i, inner ℂ (r i) (v-p) = 0 := by
    intro i
    rw [inner_sub_right]
    apply sub_eq_zero.mpr
    have hh := congrFun heq i
    simpa [p, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, G, mul_comm] using hh.symm
  have ho : ∀ w ∈ E, inner ℂ w (v-p) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨i, rfl⟩ := hw; exact hi i
    | zero => simp
    | add x y hx hy hpx hpy => simp only [inner_add_left, hpx, hpy, add_zero]
    | smul a x hx hpx => simp only [inner_smul_left, hpx, mul_zero]
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp
    (fun w hw => inner_eq_zero_symm.mpr (ho w hw)))

/-- Actual finite PA on every vector of the completed native realization.
The bounded convolution is constructed from the original Haar translations;
its Mellin coefficients are the original convolution integrals. No separate
MemLp hypothesis for the output of that integral is assumed. -/
theorem actual_completed_orthogonal_PA_action
    (K : Type*) [Field K] [NumberField K]
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hg : ∀ i, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hG : IsUnit (Matrix.det (fun i j => inner ℂ
      ((hg i (m i) le_rfl).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i))))
      ((hg j (m j) le_rfl).star.toLp
        (star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j)))))))
    (F : Lp ℂ 2 mu) :
    let r : ι → Lp ℂ 2 mu := fun i => (hg i (m i) le_rfl).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    (Submodule.span ℂ (Set.range r)).starProjection
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∑ j, (((fun i j => inner ℂ (r i) (r j)) : Matrix ι ι ℂ)⁻¹ *ᵥ
        (fun i => ∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
          (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu) ∂mu)) j • r j := by
  dsimp only
  rw [inverseGram_projection _ hG]
  have hi (i : ι) : inner ℂ
      ((hg i (m i) le_rfl).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i))))
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) =
      ∫ x, genuineMellinJet K (chi i) (z i) a (m i) x *
        (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*x) ∂mu) ∂mu := by
    rw [← native_pairing_inner K mu _ (hg i (m i) le_rfl)]
    exact actual_bounded_convolution_mellin K mu alpha s ha hs
      (chi i) (z i) a (m i) h hh hc (hg i) F
  simp_rw [hi]

#print axioms actual_completed_orthogonal_PA_action
end Masullo.InverseGramProjection

namespace Masullo.GramCompletedKernelAction
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.ActualRiesz Masullo.TransposeDiagonalIntegrable Masullo.ActualGram Masullo.GramDualNativeMemLp Masullo.InverseGramProjection
open Masullo.NativeRep Masullo.NativePettisVectorBound
open scoped Matrix BigOperators InnerProductSpace
variable (K : Type*) [Field K] [NumberField K]

/-- The explicit original-Haar kernel acts as genuine finite orthogonal
projection AFTER completed native convolution, on every native input.
No output-admission or kernel-representation hypothesis is assumed. -/
theorem actual_Gram_completed_kernel_action
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hg : ∀ i, ∀ k ≤ m i,
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (hG : IsUnit (actualGram K mu chi z a s alpha m).det)
    (F : Lp ℂ 2 mu) :
    let r : ι → Lp ℂ 2 mu := fun i => (hg i (m i) le_rfl).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    (fun x => ((Submodule.span ℂ (Set.range r)).starProjection
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F)) x) =ᵐ[mu]
    (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
      ∫ y, finitePAKernel K Finset.univ mu chi z a m h
        (actualGramDual K mu chi z a s alpha m) x y * nativeRep K mu alpha s F y ∂mu) := by
  classical
  let r : ι → Lp ℂ 2 mu := fun i => (hg i (m i) le_rfl).star.toLp
    (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
  let v : ι → ℂ := fun i => ∫ y, (∫ g, h g * nativeRep K mu alpha s F (g⁻¹*y) ∂mu) *
    genuineMellinJet K (chi i) (z i) a (m i) y ∂mu
  let c := (actualGram K mu chi z a s alpha m)⁻¹ *ᵥ v
  have hmat : (fun i j => inner ℂ (r i) (r j)) = actualGram K mu chi z a s alpha m := by
    funext i j
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hg i (m i) le_rfl).star.coeFn_toLp,
      (hg j (m j) le_rfl).star.coeFn_toLp] with x hx hy
    change r i x = _ at hx
    change r j x = _ at hy
    rw [hx, hy]
    rw [actual_Gram_density]
    simp [RCLike.inner_apply, mul_comm]
  have hp : (Submodule.span ℂ (Set.range r)).starProjection
      (nativeConvolutionCLM K mu alpha s ha hs h hh hc F) = ∑ j, c j • r j := by
    have hg' : IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j))) := by rwa [hmat]
    have hp := actual_completed_orthogonal_PA_action K mu chi z m a s alpha ha hs
      hg h hh hc hg' F
    change _ = ∑ j, _ • r j at hp
    rw [hmat] at hp
    simpa only [c, v, mul_comm] using hp
  have he (T : Finset ι) :
      (fun x => (∑ j ∈ T, c j • r j) x) =ᵐ[mu]
      (fun x => ∑ j ∈ T, c j * star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j) x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • r i) (∑ j ∈ T, c j • r j),
        Lp.coeFn_smul (c i) (r i), (hg i (m i) le_rfl).star.coeFn_toLp, ih] with x hx hs hj ht
      change r i x = _ at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  change (fun x => ((Submodule.span ℂ (Set.range r)).starProjection
    (nativeConvolutionCLM K mu alpha s ha hs h hh hc F)) x) =ᵐ[mu] _
  rw [hp]
  filter_upwards [he Finset.univ] with x hx
  rw [hx, ← actual_finite_PA_kernel_action K Finset.univ mu chi z a s alpha m h
    (nativeRep K mu alpha s F) (actualGramDual K mu chi z a s alpha m) hh hc
    (fun i _ => hg i) (nativeRep_memLp K mu alpha s F) x]
  change (∑ j, c j * star (genuineNormalizedMellinJet K (chi j) (z j) a s alpha (m j) x)) =
    (nativeHalfWeight alpha s (classLog K x) : ℂ) * ∑ i, actualGramDual K mu chi z a s alpha m i x * v i
  simp only [c, Matrix.mulVec, dotProduct, actualGramDual, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← actualRiesz_weighted K (chi j) (z j) a s alpha (m j) x]
  ring

#print axioms actual_Gram_completed_kernel_action
end Masullo.GramCompletedKernelAction

namespace DReview
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
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

noncomputable section
open Filter
open scoped BigOperators Topology
namespace ReviewMPartition

/-- An indentation averages a positive partition; the resulting masks may overlap. -/
theorem averaged_partition {U I : Type*} (b : U → ℝ) (d : I → U → ℝ)
    (hb : ∀ u, 0 ≤ b u) (hbs : HasSum b 1)
    (hd : ∀ i u, 0 ≤ d i u) (hds : ∀ u, HasSum (fun i => d i u) 1) :
    (∀ i, Summable (fun u => b u * d i u)) ∧
    (∀ i, 0 ≤ ∑' u, b u * d i u) ∧
    HasSum (fun i => ∑' u, b u * d i u) 1 := by
  have hle (i : I) (u : U) : d i u ≤ 1 := by
    simpa only [Finset.sum_singleton, (hds u).tsum_eq] using
      (hds u).summable.sum_le_tsum {i} (fun j _ => hd j u)
  have hs (i : I) : Summable (fun u => b u * d i u) :=
    Summable.of_nonneg_of_le (fun u => mul_nonneg (hb u) (hd i u))
      (fun u => mul_le_of_le_one_right (hb u) (hle i u)) hbs.summable
  have hrow (u : U) : Summable (fun i => b u * d i u) :=
    (hds u).summable.mul_left (b u)
  have hrowval (u : U) : (∑' i, b u * d i u) = b u := by
    rw [tsum_mul_left, (hds u).tsum_eq, mul_one]
  have hall : Summable (fun ui : U × I => b ui.1 * d ui.2 ui.1) := by
    apply (summable_prod_of_nonneg (fun ui => mul_nonneg (hb ui.1) (hd ui.2 ui.1))).2
    exact ⟨hrow, by simpa only [hrowval] using hbs.summable⟩
  have hmass : (∑' i, ∑' u, b u * d i u) = 1 := by
    calc
      _ = ∑' u, ∑' i, b u * d i u := hall.tsum_comm
      _ = 1 := by simpa only [hrowval] using hbs.tsum_eq
  have houter : Summable (fun i => ∑' u, b u * d i u) := by
    exact ((summable_prod_of_nonneg (fun iu : I × U =>
      mul_nonneg (hb iu.2) (hd iu.1 iu.2))).1 hall.prod_symm).2
  exact ⟨hs, fun i => tsum_nonneg (fun u => mul_nonneg (hb u) (hd i u)),
    hmass ▸ houter.hasSum⟩

end ReviewMPartition
#print axioms ReviewMPartition.averaged_partition


/-! Positive descended shells of the original Haar diagonal, M36 (36.1)-(36.3).
No disjointness assumption is used. Arithmetic identification of the density
is deliberately a separate obligation, not a new axiom. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ReviewM

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The masks are the nonnegative descended indentation weights. -/
structure PositivePartition (p : ι → X → ℝ) : Prop where
  measurable : ∀ i, Measurable (p i)
  nonneg : ∀ i x, 0 ≤ p i x
  mass : ∀ x, HasSum (fun i => p i x) 1

theorem partition_partial_le (p : ι → X → ℝ) (hp : PositivePartition p)
    (s : Finset ι) (x : X) : ∑ i ∈ s, p i x ≤ 1 := by
  simpa only [(hp.mass x).tsum_eq] using
    (hp.mass x).summable.sum_le_tsum s (fun i _ => hp.nonneg i x)

theorem partition_le_one (p : ι → X → ℝ) (hp : PositivePartition p)
    (i : ι) (x : X) : p i x ≤ 1 := by
  simpa using partition_partial_le p hp {i} x

/-- Multiplication by any descended shell preserves L1. -/
theorem shell_integrable (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (i : ι) :
    Integrable (fun x => (p i x : ℂ) * d x) μ := by
  apply hd.norm.mono' ((hp.measurable i).complex_ofReal.aestronglyMeasurable.mul
    hd.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p i x : ℂ) * d x‖ ≤ ‖d x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg i x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (partition_le_one p hp i x)

/-- Every finite family of shell integrals is bounded by the SAME L1 mass. -/
theorem finite_shell_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (s : Finset ι) :
    ∑ i ∈ s, ‖∫ x, (p i x : ℂ) * d x ∂μ‖ ≤ ∫ x, ‖d x‖ ∂μ := by
  have hi := fun i => shell_integrable μ p hp d hd i
  calc
    _ ≤ ∑ i ∈ s, ∫ x, ‖(p i x : ℂ) * d x‖ ∂μ :=
      Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ x, ∑ i ∈ s, ‖(p i x : ℂ) * d x‖ ∂μ :=
      (integral_finset_sum s (fun i _ => (hi i).norm)).symm
    _ ≤ ∫ x, ‖d x‖ ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => (hi i).norm)) hd.norm
      intro x
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp.nonneg _ x)]
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp s x)

/-- Countably many shells cost no factor equal to the number of shells. -/
theorem positive_shell_l1 (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) :
    Summable (fun i => ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ∧
    (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ≤ ∫ x, ‖d x‖ ∂μ := by
  have hs := summable_of_sum_le (fun i => norm_nonneg
    (∫ x, (p i x : ℂ) * d x ∂μ)) (finite_shell_bound μ p hp d hd)
  exact ⟨hs, le_of_tendsto hs.hasSum
    (Eventually.of_forall (finite_shell_bound μ p hp d hd))⟩

/-- The same estimate pays the entire shell-vector error. -/
theorem shell_difference_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d e : X → ℂ) (hd : Integrable d μ) (he : Integrable e μ) :
    (∑' i, ‖(∫ x, (p i x : ℂ) * d x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) ≤ ∫ x, ‖d x - e x‖ ∂μ := by
  have h := (positive_shell_l1 μ p hp (fun x => d x - e x) (hd.sub he)).2
  simpa only [mul_sub, integral_sub (shell_integrable μ p hp d hd _)
    (shell_integrable μ p hp e he _)] using h

/-- L1 convergence of the original Haar densities gives simultaneous shell convergence. -/
theorem shell_l1_limit (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : ℕ → X → ℂ) (e : X → ℂ) (hd : ∀ n, Integrable (d n) μ)
    (he : Integrable e μ)
    (hlim : Tendsto (fun n => ∫ x, ‖d n x - e x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, ‖(∫ x, (p i x : ℂ) * d n x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => tsum_nonneg (fun i => norm_nonneg _))
    (fun n => shell_difference_bound μ p hp (d n) e (hd n) he) hlim

/-- Relative to μ=V_K ν the density is w/V_K, not w. -/
def haarRankOneKernel (V : ℝ) (w : X → ℝ) (u v : X → ℂ) (x y : X) : ℂ :=
  ((w y / V : ℝ) : ℂ) * u x * star (v y)

omit [MeasurableSpace X] in
theorem haarRankOne_diagonal (V : ℝ) (w : X → ℝ) (u v : X → ℂ) (x : X) :
    haarRankOneKernel V w u v x x = ((w x / V : ℝ) : ℂ) * u x * star (v x) := rfl

/-- The manuscript's geometric kernel has the negative spectral diagonal. -/
theorem geometric_diagonal {G : Type*} [Group G] (h : G → ℂ)
    (k : G → G → ℂ) (hunit : h 1 = 0) (x : G) :
    h (x * x⁻¹) - k x x = -k x x := by simp [hunit]

/-- The finite narrow source compensator has the plus sign. -/
theorem finite_source_compensator (wide narrow sandwich regularized : ℂ) :
    wide - narrow - (sandwich - regularized) + (narrow - regularized) =
      wide - sandwich := by ring

/-- Neither the endpoint term nor the omitted-zero remainder disappears. -/
theorem retained_remainder (trace orbital boundary omitted : ℂ)
    (h : trace = orbital + boundary - omitted) :
    orbital = trace - boundary + omitted := by rw [h]; ring

end ReviewM
#print axioms ReviewM.positive_shell_l1
#print axioms ReviewM.shell_l1_limit

namespace ReviewM
variable {X ι U : Type*} [MeasurableSpace X]

/-- Apply the checked orbit-average normalization at every quotient point.
Measurability is stated for the descended functions, as required for Haar integration. -/
theorem averaged_positivePartition
    (b : X → U → ℝ) (d : ι → X → U → ℝ)
    (hb : ∀ x u, 0 ≤ b x u) (hbs : ∀ x, HasSum (b x) 1)
    (hd : ∀ i x u, 0 ≤ d i x u)
    (hds : ∀ x u, HasSum (fun i => d i x u) 1)
    (hm : ∀ i, Measurable (fun x => ∑' u, b x u * d i x u)) :
    PositivePartition (fun i x => ∑' u, b x u * d i x u) := by
  refine ⟨hm, ?_, ?_⟩
  · intro i x
    exact (ReviewMPartition.averaged_partition (b x) (fun i => d i x)
      (hb x) (hbs x) (fun i => hd i x) (hds x)).2.1 i
  · intro x
    exact (ReviewMPartition.averaged_partition (b x) (fun i => d i x)
      (hb x) (hbs x) (fun i => hd i x) (hds x)).2.2

/-- The positive descended shells reconstruct the ORIGINAL-measure diagonal.
This is B's checked reconstruction argument, using the common partition structure. -/
theorem shell_reconstruction [Countable ι] (μ : Measure X)
    (p : ι → X → ℝ) (hp : PositivePartition p)
    (f : X → ℂ) (hf : Integrable f μ) :
    HasSum (fun i => ∫ x, (p i x : ℂ) * f x ∂μ) (∫ x, f x ∂μ) := by
  classical
  have hi (i : ι) := shell_integrable μ p hp f hf i
  have hb (F : Finset ι) :
      (∑ i ∈ F, ∫ x, ‖(p i x : ℂ) * f x‖ ∂μ) ≤ ∫ x, ‖f x‖ ∂μ := by
    rw [← integral_finset_sum F (fun i _ => (hi i).norm)]
    apply integral_mono (integrable_finset_sum F (fun i _ => (hi i).norm)) hf.norm
    intro x
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hp.nonneg _ _)]
    rw [← Finset.sum_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp F x)
  have hs : Summable (fun i => ∫ x, ‖(p i x : ℂ) * f x‖ ∂μ) :=
    summable_of_sum_le (fun i => integral_nonneg (fun x => norm_nonneg _)) hb
  have he (x : X) : (∑' i, (p i x : ℂ) * f x) = f x := by
    have ht := ((Complex.ofRealCLM.hasSum (hp.mass x)).mul_right (f x)).tsum_eq
    simpa using ht
  simpa only [he] using hasSum_integral_of_summable_integral_norm hi hs

end ReviewM
#print ReviewM.shell_reconstruction
#print axioms ReviewM.shell_reconstruction

/- Append after ReviewMPartition.averaged_partition and the seed arithmetic definitions. -/
noncomputable section
open scoped BigOperators
namespace NDivisorialShells
open MasulloGRH NumberField
variable (K : Type*) [Field K] [NumberField K]

/-- The manuscript's nested finite-place unit strata live on ideles. -/
def stratum (v : ℕ → FinitePlace K) (n : ℕ) : Set (HeckeIdeles K) :=
  {x | ∀ k < n, ‖x.val.2 (v k).maximalIdeal‖ = 1}

/-- `none` is the residual S-part; `some n` is the first nonunit place. -/
def shellIndex (v : ℕ → FinitePlace K) (x : HeckeIdeles K) : Option ℕ :=
  if hx : ∃ n, ‖x.val.2 (v n).maximalIdeal‖ ≠ 1 then some (Nat.find hx) else none

def upstairsMask (v : ℕ → FinitePlace K) (e : Option ℕ) (x : HeckeIdeles K) : ℝ :=
  if shellIndex K v x = e then 1 else 0

theorem stratum_antitone (v : ℕ → FinitePlace K) : Antitone (stratum K v) := by
  intro n m hnm x hx k hk
  exact hx k (lt_of_lt_of_le hk hnm)

theorem first_nonunit_shell (v : ℕ → FinitePlace K) (x : HeckeIdeles K)
    (hx : ∃ n, ‖x.val.2 (v n).maximalIdeal‖ ≠ 1) :
    shellIndex K v x = some (Nat.find hx) ∧
      x ∈ stratum K v (Nat.find hx) ∧ x ∉ stratum K v (Nat.find hx + 1) := by
  refine ⟨by simp [shellIndex, hx], ?_, ?_⟩
  · intro k hk
    exact not_not.mp (Nat.find_min hx hk)
  · intro hu
    exact Nat.find_spec hx (hu _ (Nat.lt_succ_self _))

theorem residual_shell (v : ℕ → FinitePlace K) (x : HeckeIdeles K)
    (hx : ∀ n, ‖x.val.2 (v n).maximalIdeal‖ = 1) : shellIndex K v x = none := by
  simp [shellIndex, hx]

theorem upstairs_nonneg (v : ℕ → FinitePlace K) (e : Option ℕ) (x : HeckeIdeles K) :
    0 ≤ upstairsMask K v e x := by
  unfold upstairsMask
  split <;> norm_num

theorem upstairs_mass (v : ℕ → FinitePlace K) (x : HeckeIdeles K) :
    HasSum (fun e => upstairsMask K v e x) 1 := by
  classical
  simpa only [upstairsMask, eq_comm] using
    (hasSum_ite_eq (shellIndex K v x) (1 : ℝ))

/-- Orbit averaging by the fixed manuscript indentation. -/
def orbitMask (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (x : HeckeIdeles K) : ℝ :=
  ∑' q : Kˣ, b (principalIdele K q * x) * upstairsMask K v e (principalIdele K q * x)

theorem orbitMask_principal (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (q : Kˣ) (x : HeckeIdeles K) :
    orbitMask K v b e (principalIdele K q * x) = orbitMask K v b e x := by
  have ht := (Equiv.mulRight q).tsum_eq (fun u : Kˣ =>
    b (principalIdele K u * x) * upstairsMask K v e (principalIdele K u * x))
  change (∑' u : Kˣ, b (principalIdele K (u*q) * x) *
    upstairsMask K v e (principalIdele K (u*q) * x)) = _ at ht
  simpa only [orbitMask, map_mul, mul_assoc] using ht

/-- Actual quotient descent; no representative selector or invariance premise. -/
def descendedMask (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (orbitMask K v b e) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K := QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, orbitMask_principal])

theorem descendedMask_mk (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (x : HeckeIdeles K) :
    descendedMask K v b e (QuotientGroup.mk x) = orbitMask K v b e x := rfl

/-- Positivity and total mass are proved for these actual arithmetic masks.
The indentation normalization is displayed, not claimed to be constructed here. -/
theorem descended_partition_mass (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (x : HeckeIdeleClasses K) :
    (∀ e, 0 ≤ descendedMask K v b e x) ∧
      HasSum (fun e => descendedMask K v b e x) 1 := by
  refine Quotient.inductionOn x ?_
  intro y
  have ht := ReviewMPartition.averaged_partition
    (fun q : Kˣ => b (principalIdele K q * y))
    (fun e q => upstairsMask K v e (principalIdele K q * y))
    (fun q => hb _) (hbs y)
    (fun e q => upstairs_nonneg K v e _) (fun q => upstairs_mass K v _)
  exact ⟨ht.2.1, ht.2.2⟩

/-- The two repairs use the same actual idelic shell and the same quotient mask.
The incoming point is x*t⁻¹ because convolution acts before projection. -/
theorem actual_shell_boundary_split (v : ℕ → FinitePlace K) (b : HeckeIdeles K → ℝ)
    (e : Option ℕ) (y : HeckeIdeles K) (t : HeckeIdeleClasses K) (amp : ℂ) :
    let x : HeckeIdeleClasses K := QuotientGroup.mk y
    ((upstairsMask K v e y : ℂ) - (descendedMask K v b e (x*t⁻¹) : ℂ)) * amp =
      ((upstairsMask K v e y : ℂ) - (descendedMask K v b e x : ℂ)) * amp +
      ((descendedMask K v b e x : ℂ) - (descendedMask K v b e (x*t⁻¹) : ℂ)) * amp := by
  dsimp
  ring

/-- The corrected finite regularizer retains the narrow compensator with PLUS sign. -/
theorem regularizer_plus {X : Type*} (wide narrow sandwich regNarrow : X → ℂ) :
    (fun x => wide x - narrow x - (sandwich x - regNarrow x) +
      (narrow x - regNarrow x)) = (fun x => wide x - sandwich x) := by
  funext x
  ring
end NDivisorialShells
end
#print NDivisorialShells.descended_partition_mass
#print axioms NDivisorialShells.descended_partition_mass
#print axioms NDivisorialShells.actual_shell_boundary_split
#print axioms NDivisorialShells.regularizer_plus

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

/- Append after NShellFragment, MPartitionFragment, the I arithmetic core,
   and the seed DReview block. No alternative kernel or sharp is defined. -/
namespace NArithmeticIntegration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Physical exhaustion of an actual original-Haar diagonal in L1. -/
theorem physical_diagonal_L1 (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun n => ∫ x, ‖(DReview.physicalBand K n).indicator d x - d x‖ ∂mu)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫ x, ‖(DReview.physicalBand K n).indicator d x-d x‖ ∂mu)
      atTop (𝓝 (∫ _ : HeckeIdeleClasses K, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
    · intro n
      exact ((hd.aestronglyMeasurable.indicator (DReview.physicalBand_measurable K n)).sub
        hd.aestronglyMeasurable).norm
    · exact hd.norm
    · intro n
      filter_upwards [] with x
      by_cases hx : x ∈ DReview.physicalBand K n <;> simp [hx]
    · filter_upwards [] with x
      obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ DReview.physicalBand K n := hN.trans (by exact_mod_cast hn)
      simp [hx]
  simpa only [integral_zero] using ht

/-- Actual arithmetic shell partition. The displayed measurable-descent and
indentation normalization obligations remain visible to the caller. -/
theorem descended_positivePartition (v : ℕ → NumberField.FinitePlace K)
    (b : HeckeIdeles K → ℝ) (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (hm : ∀ e, Measurable (NDivisorialShells.descendedMask K v b e)) :
    ReviewM.PositivePartition (NDivisorialShells.descendedMask K v b) := by
  refine ⟨hm, ?_, ?_⟩
  · intro e x
    exact (NDivisorialShells.descended_partition_mass K v b hb hbs x).1 e
  · intro x
    exact (NDivisorialShells.descended_partition_mass K v b hb hbs x).2

/-- Finite complementary-kernel shells, with the negative spectral sign.
This is not an identification of the finite jet span with the full theta source. -/
theorem finite_complement_shells
    {ι J : Type*} [Fintype ι] [DecidableEq ι] [Countable J]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (h1 : h 1 = 0)
    (p : J → HeckeIdeleClasses K → ℝ) (hp : ReviewM.PositivePartition p) :
    let ker := finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m)
    let d := fun x => h (x*x⁻¹) - ker x x
    HasSum (fun j => ∫ x, (p j x : ℂ) * d x ∂mu)
      (-(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu)) ∧
    Summable (fun j => ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ∧
    (∑' j, ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' j, ‖(∫ x, (p j x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p j x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let ker := finitePAKernel K Finset.univ mu chi z a m h
    (actualGramDual K mu chi z a s alpha m)
  let d := fun x => h (x*x⁻¹) - ker x x
  have hd0 := actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m
    hg hclosed h hh hc
  have he := actual_Gram_PA_diagonal_integral K mu chi z a s alpha m
    hg hdet hclosed h hh hc
  have hneg : d = (fun x => -ker x x) := by
    funext x
    simp only [d, mul_inv_cancel, h1, zero_sub]
  have hd : Integrable d mu := by rw [hneg]; exact hd0.neg
  have hge : (∫ x, d x ∂mu) =
      -(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu) := by
    rw [hneg, integral_neg]
    exact congrArg Neg.neg he
  have hsum := ReviewM.shell_reconstruction mu p hp d hd
  rw [hge] at hsum
  have hbound := ReviewM.positive_shell_l1 mu p hp d hd
  refine ⟨hsum, hbound.1, hbound.2, ?_⟩
  exact ReviewM.shell_l1_limit mu p hp (fun n => (DReview.physicalBand K n).indicator d) d
    (fun n => hd.indicator (DReview.physicalBand_measurable K n)) hd
    (physical_diagonal_L1 K mu d hd)

/-- Both literal manuscript tests on the concrete descended divisorial masks. -/
theorem both_sharp_arithmetic_shells
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q*x)) 1)
    (hm : ∀ e, Measurable (NDivisorialShells.descendedMask K v b e)) :
    ∀ h ∈ ({DReview.sharp K phi,
      DReview.sharp K (fun x => (classLog K x : ℂ)*phi x)} :
        Set (HeckeIdeleClasses K → ℂ)),
    let p := NDivisorialShells.descendedMask K v b
    let ker := finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m)
    let d := fun x => h (x*x⁻¹) - ker x x
    HasSum (fun j => ∫ x, (p j x : ℂ) * d x ∂mu)
      (-(∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu)) ∧
    Summable (fun j => ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ∧
    (∑' j, ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' j, ‖(∫ x, (p j x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p j x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  have hz : classLog K (1 : HeckeIdeleClasses K) = 0 := by
    have ht := Masullo.WeightedIdeleClass.classLog_mul K (1 : HeckeIdeleClasses K) 1
    simp only [one_mul] at ht
    linarith
  have hp := descended_positivePartition K v b hb hbs hm
  have ht := DReview.both_sharp_tests_compact K phi hh hc
  intro h hmemb
  rcases Set.mem_insert_iff.mp hmemb with he | hmemb
  · subst h
    exact finite_complement_shells K mu chi z m a s alpha hg hdet hclosed _
      ht.1.1 ht.1.2 (DReview.sharp_vanishes_normOne K phi hphi 1 hz) _ hp
  · have he := Set.mem_singleton_iff.mp hmemb
    subst h
    exact finite_complement_shells K mu chi z m a s alpha hg hdet hclosed _
      ht.2.1 ht.2.2 (DReview.sharp_vanishes_normOne K _
        (fun x hx => by simp [hx]) 1 hz) _ hp
end
end NArithmeticIntegration
#print NArithmeticIntegration.both_sharp_arithmetic_shells
#print axioms NArithmeticIntegration.both_sharp_arithmetic_shells

/- Insert after B/D's completed projection, L's required tests, and
   NArithmeticShellFragment. The same finite operator and kernel are used. -/
namespace ReviewI.Integration
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineMellinJet Masullo.GenuineNormalizedMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open Masullo.NativeRep Masullo.NativePettisVectorBound
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- One finite operator-to-shell statement on the actual arithmetic kernel.
The orthogonal projection acts after the constructed completed convolution.
Both test families and the original-Haar negative complement diagonal use
this very kernel. Global theta-source exhaustion/local unfolding remain separate. -/
theorem both_tests_completed_kernel_shells
    [MeasurableMul₂ (HeckeIdeleClasses K)] [MeasurableInv (HeckeIdeleClasses K)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    [mu.IsMulLeftInvariant]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (m : ι → ℕ)
    (a s alpha : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hdet : IsUnit (actualGram K mu chi z a s alpha m).det)
    (hclosed : JetClosed K chi z m)
    (phi : HeckeIdeleClasses K → ℂ) (hh : Continuous phi) (hc : HasCompactSupport phi)
    (hphi : ∀ x, classLog K x = 0 → phi x = 0)
    (v : ℕ → NumberField.FinitePlace K) (b : HeckeIdeles K → ℝ)
    (hb : ∀ x, 0 ≤ b x)
    (hbs : ∀ x, HasSum (fun q : Kˣ => b (principalIdele K q * x)) 1)
    (hmeas : ∀ e, Measurable (NDivisorialShells.descendedMask K v b e))
    (q : Fin 2) :
    let h := LIntegrated.requiredTest K phi q
    let ht := LIntegrated.requiredTest_compact K phi hh hc q
    let r : ι → Lp ℂ 2 mu := fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    let ker := finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m)
    let d := fun x => h (x*x⁻¹) - ker x x
    let p := NDivisorialShells.descendedMask K v b
    let spectral := ∑ i, ∫ g, h g * genuineMellinJet K (chi i) (z i) a 0 g ∂mu
    (∀ F : Lp ℂ 2 mu,
      (fun x => ((Submodule.span ℂ (Set.range r)).starProjection
        (nativeConvolutionCLM K mu alpha s ha hs h ht.1 ht.2 F)) x) =ᵐ[mu]
      (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) *
        ∫ y, ker x y * nativeRep K mu alpha s F y ∂mu)) ∧
    Integrable (fun x => ker x x) mu ∧
    (∫ x, ker x x ∂mu) = spectral ∧
    HasSum (fun e => ∫ x, (p e x : ℂ) * d x ∂mu) (-spectral) ∧
    Summable (fun e => ‖∫ x, (p e x : ℂ) * d x ∂mu‖) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu ∧
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) *
      (DReview.physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p e x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  dsimp only
  let h := LIntegrated.requiredTest K phi q
  have ht := LIntegrated.requiredTest_compact K phi hh hc q
  have hlow : ∀ i k, k ≤ m i →
      MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha k) 2 mu :=
    fun i k hk => closed_family_native_admission K mu chi z a s alpha m hg hclosed i k hk
  have hp := NArithmeticIntegration.descended_positivePartition K v b hb hbs hmeas
  have hn := NArithmeticIntegration.finite_complement_shells K mu chi z m a s alpha
    hg hdet hclosed h ht.1 ht.2 (LIntegrated.requiredTest_at_one K phi hphi q) _ hp
  refine ⟨?_, actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m
    hg hclosed h ht.1 ht.2, actual_Gram_PA_diagonal_integral K mu chi z a s alpha m
      hg hdet hclosed h ht.1 ht.2, hn⟩
  intro F
  exact Masullo.GramCompletedKernelAction.actual_Gram_completed_kernel_action K mu chi z m
    a s alpha ha hs hlow h ht.1 ht.2 hdet F

end
end ReviewI.Integration
#check ReviewI.Integration.both_tests_completed_kernel_shells
#print axioms ReviewI.Integration.both_tests_completed_kernel_shells
#print ReviewI.Integration.both_tests_completed_kernel_shells
