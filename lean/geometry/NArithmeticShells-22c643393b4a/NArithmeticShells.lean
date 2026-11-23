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

/- Reviewed peer M: measured positive-shell contraction. -/

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


end ReviewM


open MeasureTheory Filter
open scoped BigOperators Topology

namespace NMeasuredShells

variable {X E : Type*} [MeasurableSpace X]

/-- Shell pairing always uses the original quotient Haar measure `mu`. -/
noncomputable def shell (mu : Measure X) (p : X → ℝ) (f : X → ℂ) : ℂ :=
  ∫ x, (p x : ℂ) * f x ∂mu

/-- Bounded measurable shell masks need no separate integrability assumption. -/
theorem masked_integrable (mu : Measure X) (p : X → ℝ) (f : X → ℂ)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => (p x : ℂ) * f x) mu := by
  apply hf.norm.mono'
    ((Complex.continuous_ofReal.measurable.comp hp).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
  simpa using mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg (f x))

/-- A finite set of positive descended masks may overlap. -/
theorem finite_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ)
    (hf : Integrable f mu)
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1)
    (hi : ∀ e ∈ F, Integrable (fun x => (p e x : ℂ) * f x) mu) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  calc
    _ ≤ ∑ e ∈ F, ∫ x, ‖(p e x : ℂ) * f x‖ ∂mu := by
      exact Finset.sum_le_sum (fun e he => norm_integral_le_integral_norm _)
    _ = ∫ x, ∑ e ∈ F, ‖(p e x : ℂ) * f x‖ ∂mu := by
      symm
      exact integral_finset_sum F (fun e he => (hi e he).norm)
    _ ≤ ∫ x, ‖f x‖ ∂mu := by
      apply integral_mono
        (integrable_finset_sum F (fun e he => (hi e he).norm)) hf.norm
      intro x
      calc
        (∑ e ∈ F, ‖(p e x : ℂ) * f x‖) = (∑ e ∈ F, p e x) * ‖f x‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e he
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp e he x)]
        _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hs x) (norm_nonneg _)
        _ = ‖f x‖ := one_mul _

/-- Discharges mask integrability for the positive overlapping partition. -/
theorem measurable_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ) (hf : Integrable f mu)
    (hm : ∀ e ∈ F, Measurable (p e))
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  apply finite_shell_contraction mu F p f hf hp hs
  intro e he
  apply masked_integrable mu (p e) f (hm e he) (hp e he) _ hf
  intro x
  exact (Finset.single_le_sum (fun j hj => hp j hj x) he).trans (hs x)

omit [MeasurableSpace X] in
/-- Exact finite regularizer: the narrow remainder has a PLUS sign. -/
theorem regularizer_plus (wide narrow sandwich regNarrow : X → ℂ) :
    (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) = (fun x => wide x - sandwich x) := by
  funext x
  ring

/-- The correction identity holds under every mask before any limit. -/
theorem regularized_shell_eq (mu : Measure X) (p : X → ℝ)
    (wide narrow sandwich regNarrow : X → ℂ) :
    shell mu p (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) =
      shell mu p (fun x => wide x - sandwich x) := by
  rw [regularizer_plus]

/-- A trace-zero transport has a retained masked boundary contribution. -/
theorem shell_sub (mu : Measure X) (p : X → ℝ) (f g : X → ℂ)
    (hf : Integrable (fun x => (p x : ℂ) * f x) mu)
    (hg : Integrable (fun x => (p x : ℂ) * g x) mu) :
    shell mu p (fun x => f x - g x) = shell mu p f - shell mu p g := by
  simp only [shell, mul_sub]
  exact integral_sub hf hg

/-- Original representative and incoming-mask boundaries telescope before integration. -/
theorem boundary_repairs (indicator outgoing incoming : ℂ) :
    indicator - incoming = (indicator - outgoing) + (outgoing - incoming) := by ring

/-- The omitted residue is bounded by every paid finite shell enclosure. -/
theorem finite_residue_certificate [Fintype E]
    (v w : E → ℂ) (m : ℕ) (err : ℝ)
    (hm : ∑ e, v e = (m : ℂ))
    (he : (∑ e, ‖v e - w e‖) ≤ err) :
    ‖(m : ℂ) - ∑ e, w e‖ ≤ err := by
  rw [← hm, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans he

end NMeasuredShells

#print axioms NMeasuredShells.finite_shell_contraction
#print axioms NMeasuredShells.regularizer_plus
#print axioms NMeasuredShells.boundary_repairs
#print axioms NMeasuredShells.finite_residue_certificate

namespace NArithmeticShells
open MeasureTheory MasulloGRH Masullo.IdeleClassGeometry
open Masullo.GenuineNormalizedMellinJet Masullo.GenuineMellinJet
open Masullo.TransposeDiagonalIntegrable Masullo.ActualGram
open Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped BigOperators Topology

/-- The requested logged partner in the original class-group coordinates. -/
def logged (K : Type*) [Field K] [NumberField K]
    (h : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  -(classLog K x : ℂ) * h x

theorem logged_continuous (K : Type*) [Field K] [NumberField K]
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) :
    Continuous (logged K h) := by
  exact (Complex.continuous_ofReal.comp
    (Masullo.WeightedIdeleClass.classLog_continuous K)).neg.mul hh

theorem logged_compact (K : Type*) [Field K] [NumberField K]
    (h : HeckeIdeleClasses K → ℂ) (hc : HasCompactSupport h) :
    HasCompactSupport (logged K h) := by
  exact hc.mul_left

/-- The arithmetic finite inverse-Gram diagonal pays all descended shells.
The original Haar integral and the actual character/jet parameters are retained.
Native admission and exhaustion into the full spectral projection are distinct. -/
theorem native_gram_shell_l1
    (K : Type*) [Field K] [NumberField K]
    {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (p : J → HeckeIdeleClasses K → ℝ) (hp : ReviewM.PositivePartition p) :
    let d := fun x => finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x
    Summable (fun j => ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ∧
      (∑' j, ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu := by
  exact ReviewM.positive_shell_l1 mu p hp _
    (actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m hg hclosed h hh hc)

/-- Both requested tests have the same arithmetic diagonal/shell interface;
the logged partner's analytic support hypotheses are proved here. -/
theorem both_native_gram_shell_l1
    (K : Type*) [Field K] [NumberField K]
    {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m)
    (h0 : HeckeIdeleClasses K → ℂ) (hh : Continuous h0) (hc : HasCompactSupport h0)
    (p : J → HeckeIdeleClasses K → ℝ) (hp : ReviewM.PositivePartition p) :
    ∀ h ∈ ({h0, logged K h0} : Set (HeckeIdeleClasses K → ℂ)),
      let d := fun x => finitePAKernel K Finset.univ mu chi z a m h
        (actualGramDual K mu chi z a s alpha m) x x
      Summable (fun j => ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ∧
        (∑' j, ‖∫ x, (p j x : ℂ) * d x ∂mu‖) ≤ ∫ x, ‖d x‖ ∂mu := by
  intro h ht
  rcases Set.mem_insert_iff.mp ht with he | ht
  · rw [he]
    exact native_gram_shell_l1 K mu chi z a s alpha m hg hclosed h0 hh hc p hp
  · have he : h = logged K h0 := Set.mem_singleton_iff.mp ht
    rw [he]
    exact native_gram_shell_l1 K mu chi z a s alpha m hg hclosed (logged K h0)
      (logged_continuous K h0 hh) (logged_compact K h0 hc) p hp

end NArithmeticShells

#print axioms NArithmeticShells.both_native_gram_shell_l1

/- Reviewed and adapted from D/DFiniteCutoffExtension.lean. -/
namespace NPhysicalShells
open MeasureTheory Filter MasulloGRH Masullo.IdeleClassGeometry
open Masullo.WeightedIdeleClass Masullo.GenuineMellinJet
open Masullo.GenuineNormalizedMellinJet Masullo.TransposeDiagonalIntegrable
open Masullo.ActualGram Masullo.GramDualPairingIntegrable Masullo.GramDualNativeMemLp
open scoped Topology BigOperators
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

/-- The physical tail vanishes in L1, so every descended shell is controlled. -/
theorem originalHaar_physical_L1 (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) :
    Tendsto (fun n => ∫ x, ‖(physicalBand K n).indicator d x - d x‖ ∂mu)
      atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫ x, ‖(physicalBand K n).indicator d x-d x‖ ∂mu)
      atTop (𝓝 (∫ _ : HeckeIdeleClasses K, (0 : ℝ) ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
    · intro n
      exact ((hd.aestronglyMeasurable.indicator (physicalBand_measurable K n)).sub
        hd.aestronglyMeasurable).norm
    · exact hd.norm
    · intro n
      filter_upwards [] with x
      by_cases hx : x ∈ physicalBand K n <;> simp [hx]
    · filter_upwards [] with x
      obtain ⟨N, hN⟩ := exists_nat_ge |classLog K x|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hx : x ∈ physicalBand K n := hN.trans (by exact_mod_cast hn)
      simp [hx]
  simpa only [integral_zero] using ht

/-- Actual finite arithmetic kernels admit simultaneous shell cutoff removal. -/
theorem native_gram_physical_shell_limit
    {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (mu : Measure (HeckeIdeleClasses K)) [IsLocallyFiniteMeasure mu] [SFinite mu]
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ) (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu)
    (hclosed : JetClosed K chi z m)
    (h : HeckeIdeleClasses K → ℂ) (hh : Continuous h) (hc : HasCompactSupport h)
    (p : J → HeckeIdeleClasses K → ℝ) (hp : ReviewM.PositivePartition p) :
    let d := fun x => finitePAKernel K Finset.univ mu chi z a m h
      (actualGramDual K mu chi z a s alpha m) x x
    Tendsto (fun n => ∑' j, ‖(∫ x, (p j x : ℂ) * (physicalBand K n).indicator d x ∂mu) -
      (∫ x, (p j x : ℂ) * d x ∂mu)‖) atTop (𝓝 0) := by
  let d := fun x => finitePAKernel K Finset.univ mu chi z a m h
    (actualGramDual K mu chi z a s alpha m) x x
  have hd : Integrable d mu :=
    actual_Gram_PA_diagonal_integrable K mu chi z a s alpha m hg hclosed h hh hc
  exact ReviewM.shell_l1_limit mu p hp (fun n => (physicalBand K n).indicator d) d
    (fun n => hd.indicator (physicalBand_measurable K n)) hd
    (originalHaar_physical_L1 K mu d hd)

end NPhysicalShells

#print axioms NPhysicalShells.sharp_log
#print axioms NPhysicalShells.both_sharp_tests_compact
#print axioms NPhysicalShells.native_gram_physical_shell_limit

/- Reviewed original orthogonal-projection order. -/

namespace Masullo.CoreInvarianceExtends
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 theorem core_invariance_extends (T : H →L[ℂ] H) (C : Submodule ℂ H)
    (hC : ∀ x ∈ C, T x ∈ C) :
    ∀ x ∈ C.topologicalClosure, T x ∈ C.topologicalClosure := by
  intro x hx
  exact map_mem_closure T.continuous hx hC

/-- With G the ACTUAL geometric closure, its orthogonal complement projector
is P=1-Q. Invariance of G gives a one-sided triangular block, not commutation. -/
 theorem projection_order_defect (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    T (P x) - P (T x) = Q (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

 theorem convolution_first_compression (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let P := ContinuousLinearMap.id ℂ H - G.starProjection
    P (T x) = P (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

/-- Both complementary printed-to-convolution-first changes have opposite
signs, for the SAME cutoff. Neither individual defect is set to zero. -/
 theorem paired_cutoff_order_defects (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T M : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    (M (T (P x)) - M (P (T x)) = M (Q (T (P x)))) ∧
    (M (T (Q x)) - M (Q (T x)) = -M (Q (T (P x)))) := by
  dsimp only
  have hh := congrArg M (projection_order_defect G T hG x)
  simp only [map_sub] at hh
  constructor
  · exact hh
  · have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
      Submodule.starProjection_eq_self_iff.mpr
        (hG _ (Submodule.starProjection_apply_mem G x))
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
    abel

#print axioms core_invariance_extends
#print axioms projection_order_defect
#print axioms convolution_first_compression
#print axioms paired_cutoff_order_defects
end Masullo.CoreInvarianceExtends

/- Reviewed I: measured finite compensator and omitted edge. -/

/-! I35 (35.7)-(35.9): the finite source term and narrow compensator are
retained under the SAME original-Haar mask. No arithmetic density identity
or nuclearity is asserted by this analytic lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ReviewI
variable {X : Type*} [MeasurableSpace X]

def masked (mu : Measure X) (w f : X → ℂ) : ℂ := ∫ x, w x * f x ∂mu

theorem masked_integrable (mu : Measure X) (w f : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => w x * f x) mu := by
  apply hf.norm.mono' (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖w x * f x‖ ≤ ‖f x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

theorem masked_sub (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    masked mu w (fun x => f x-g x) = masked mu w f-masked mu w g := by
  simp only [masked, mul_sub]
  exact integral_sub (masked_integrable mu w f hw hb hf)
    (masked_integrable mu w g hw hb hg)

theorem masked_error_le (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    ‖masked mu w f-masked mu w g‖ ≤ ∫ x, ‖f x-g x‖ ∂mu := by
  rw [← masked_sub mu w f g hw hb hf hg]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (masked_integrable mu w _ hw hb (hf.sub hg)).norm (hf.sub hg).norm
  filter_upwards [hb] with x hx
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- `wide=d_beta(T_beta)`, `narrow=d_alpha(T_alpha)`,
`sandwich=d_beta(S_e T_beta S_e)`, `regularized=d_alpha(R_e T_alpha R_e)`.
The source transport is `sandwich-regularized`. -/
theorem finite_source_compensator_integral
    (mu : Measure X) (w wide narrow sandwich regularized : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hsand : Integrable sandwich mu) (hreg : Integrable regularized mu) :
    masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich x-regularized x)
      +masked mu w (fun x => narrow x-regularized x) =
    masked mu w (fun x => wide x-sandwich x) := by
  rw [masked_sub mu w sandwich regularized hw hb hsand hreg,
    masked_sub mu w narrow regularized hw hb hnarrow hreg,
    masked_sub mu w wide sandwich hw hb hwide hsand]
  ring

/-- The low-energy cutoff converges to the full-input LEFT correction under
any bounded physical/shell mask. The source identity is not replaced by
its total trace; the regularization compensator is present at every n. -/
theorem regularized_source_shell_limit
    (mu : Measure X) (w wide narrow full : X → ℂ)
    (sandwich regularized : ℕ → X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hfull : Integrable full mu)
    (hsand : ∀ n, Integrable (sandwich n) mu)
    (hreg : ∀ n, Integrable (regularized n) mu)
    (hlim : Tendsto (fun n => ∫ x, ‖sandwich n x-full x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) atTop
      (𝓝 (masked mu w (fun x => wide x-full x))) := by
  have ht : Tendsto (fun n => masked mu w (sandwich n)) atTop
      (𝓝 (masked mu w full)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => masked_error_le mu w (sandwich n) full hw hb (hsand n) hfull) hlim
  have he : (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) =
      (fun n => masked mu w wide-masked mu w (sandwich n)) := by
    funext n
    rw [finite_source_compensator_integral mu w wide narrow (sandwich n)
      (regularized n) hw hb hwide hnarrow (hsand n) (hreg n),
      masked_sub mu w wide (sandwich n) hw hb hwide (hsand n)]
  rw [he, masked_sub mu w wide full hw hb hwide hfull]
  exact tendsto_const_nhds.sub ht

/-- Physical exhaustion is justified from an actual integrable Haar density. -/
theorem physical_cutoff_limit (mu : Measure X) (d : X → ℂ) (w : ℕ → X → ℂ)
    (hd : Integrable d mu) (hw : ∀ n, AEStronglyMeasurable (w n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖w n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => w n x) atTop (𝓝 1)) :
    Tendsto (fun n => masked mu (w n) d) atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · intro n
    exact (hw n).mul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    filter_upwards [hb n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa using hx.mul (tendsto_const_nhds (x := d x))

/-- The physical tail is retained as an integral before taking a limit. -/
theorem physical_tail_identity (mu : Measure X) (w d : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hd : Integrable d mu) :
    (∫ x, d x ∂mu)-masked mu w d = ∫ x, (1-w x)*d x ∂mu := by
  simp only [sub_mul, one_mul, masked]
  exact (integral_sub hd (masked_integrable mu w d hw hb hd)).symm

/-- If the full explicit formula is pole - all zeros, and the native trace
is interior + admitted edge, the correction is omitted - admitted edge. -/
theorem omitted_edge_remainder (pole geometric interior edge omitted spectral : ℂ)
    (hfull : geometric = pole-(interior+omitted))
    (hspec : spectral = interior+edge) :
    pole-geometric-spectral = omitted-edge := by
  rw [hfull, hspec]
  ring

end ReviewI
#print axioms ReviewI.regularized_source_shell_limit
#print axioms ReviewI.omitted_edge_remainder
