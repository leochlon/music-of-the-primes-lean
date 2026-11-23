import Mathlib
/- Exact checked arithmetic definitions extracted without rebuilding topology. -/
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
#check genuineIdele_finite_norm_support
#print axioms genuineIdele_finite_norm_support
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


open MeasureTheory Topology Filter
open NumberField.InfinitePlace.Completion
open scoped ENNReal NNReal
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)

instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

instance classMeasurableInv : MeasurableInv (HeckeIdeleClasses K) := by
  infer_instance
instance classMeasurableMul : MeasurableMul (HeckeIdeleClasses K) := by
  infer_instance

noncomputable def genuineIdeleLog (a : HeckeIdeles K) : ℂ :=
  (Real.log (genuineIdeleModulus K a) : ℂ)
/-- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
#check genuineIdeleModulus_principal
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]
#check genuineIdeleModulus_mul
#print axioms genuineIdeleModulus_mul
#check genuineIdeleModulus_ne_zero
#print axioms genuineIdeleModulus_ne_zero
#check genuineIdeleLog_add
#print axioms genuineIdeleLog_add

/-- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
local-norm logarithm. This is not supplied by an abstract replacement norm. -/
noncomputable def genuineLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeles K →* Multiplicative ℂ where
  toFun a := Multiplicative.ofAdd (genuineIdeleLog K a)
  map_one' := by
    change genuineIdeleLog K 1 = 0
    simpa only [map_one] using genuineIdeleLog_principal K 1
  map_mul' a b := hadd a b

noncomputable def genuineClassLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeleClasses K →* Multiplicative ℂ :=
  QuotientGroup.lift (principalIdeles K) (genuineLogHom K hadd) (by
    rintro x ⟨a, rfl⟩
    exact genuineIdeleLog_principal K a)

noncomputable def genuineClassLog
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (x : HeckeIdeleClasses K) : ℂ :=
  Multiplicative.toAdd (genuineClassLogHom K hadd x)

theorem genuineClassLog_mk
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (a : HeckeIdeles K) :
    genuineClassLog K hadd (QuotientGroup.mk a) = genuineIdeleLog K a := rfl

theorem genuineClassLog_translate
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (g x : HeckeIdeleClasses K) :
    genuineClassLog K hadd (g⁻¹ * x) =
      genuineClassLog K hadd x - genuineClassLog K hadd g := by
  unfold genuineClassLog
  rw [map_mul, map_inv]
  change -Multiplicative.toAdd (genuineClassLogHom K hadd g) +
    Multiplicative.toAdd (genuineClassLogHom K hadd x) = _
  abel


noncomputable def genuineRealClassLog (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re

theorem genuineRealClassLog_mul (x y : HeckeIdeleClasses K) :
    genuineRealClassLog K (x*y) = genuineRealClassLog K x + genuineRealClassLog K y := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_mul]
  rfl

theorem genuineRealClassLog_inv (x : HeckeIdeleClasses K) :
    genuineRealClassLog K x⁻¹ = -genuineRealClassLog K x := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_inv]
  rfl

end MasulloGRH
namespace Round93G
noncomputable section
open MeasureTheory MasulloGRH
def stripWeight (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (1 + u ^ 2) ^ (s / 2)

/-- A corrected translation estimate, valid for every nonnegative strip width
    and real Sobolev parameter; unlike (9.3.1.6), it does not vanish at identity. -/
theorem stripWeight_translate_bound (alpha s u v : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    stripWeight alpha s (u + v) ≤
      (Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)) *
        stripWeight alpha s v := by
  have hp : 1 + (u + v) ^ 2 ≤ (2 * (1 + u ^ 2)) * (1 + v ^ 2) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u * v)]
  have he : Real.exp (2 * alpha * |u + v|) ≤
      Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_add_le u v]
  have hw : (1 + (u + v) ^ 2) ^ (s / 2) ≤
      (2 * (1 + u ^ 2)) ^ (s / 2) * (1 + v ^ 2) ^ (s / 2) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * (1 + u ^ 2))
      (by positivity : 0 ≤ 1 + v ^ 2)]
    exact Real.rpow_le_rpow (by positivity) hp (by positivity)
  unfold stripWeight
  calc
    _ ≤ (Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|)) *
        ((2 * (1 + u ^ 2)) ^ (s / 2) * (1 + v ^ 2) ^ (s / 2)) :=
      mul_le_mul he hw (by positivity) (by positivity)
    _ = _ := by ring


variable (K : Type*) [Field K] [NumberField K]

def translationCost (α s t : ℝ) : ℝ :=
  Real.exp (2 * α * |t|) * (2 * (1+t^2)) ^ (s/2)

/-- The relative weight bound uses only the genuine displacement, not output radius. -/
theorem genuine_relative_weight_bound (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (x y : HeckeIdeleClasses K) :
    stripWeight α s (genuineRealClassLog K x) /
        stripWeight α s (genuineRealClassLog K y) ≤
      translationCost α s (genuineRealClassLog K (x*y⁻¹)) := by
  have hy : 0 < stripWeight α s (genuineRealClassLog K y) := by
    unfold stripWeight
    positivity
  apply (div_le_iff₀ hy).mpr
  have h := stripWeight_translate_bound α s
    (genuineRealClassLog K (x*y⁻¹)) (genuineRealClassLog K y) hα hs
  have he : genuineRealClassLog K (x*y⁻¹) + genuineRealClassLog K y =
      genuineRealClassLog K x := by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv]
    ring
  rw [he] at h
  exact h

/-- Actual transported cutoff kernel: same genuine Haar convolution and actual weight. -/
def genuineCutoffKernel (α s : ℝ) (ρ φ : HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ :=
  ρ x * φ (x*y⁻¹) * (Real.sqrt
    (stripWeight α s (genuineRealClassLog K x) /
      stripWeight α s (genuineRealClassLog K y)) : ℂ)

theorem genuineCutoffKernel_norm_sq (α s : ℝ)
    (ρ φ : HeckeIdeleClasses K → ℂ) (x y : HeckeIdeleClasses K) :
    ‖genuineCutoffKernel K α s ρ φ x y‖^2 =
      ‖ρ x‖^2 * ‖φ (x*y⁻¹)‖^2 *
        (stripWeight α s (genuineRealClassLog K x) /
          stripWeight α s (genuineRealClassLog K y)) := by
  have hp (z : HeckeIdeleClasses K) : 0 ≤ stripWeight α s (genuineRealClassLog K z) := by
    unfold stripWeight
    positivity
  simp only [genuineCutoffKernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (div_nonneg (hp x) (hp y))]

/-- Improved authentic squared-kernel bound: cutoff mass is UNWEIGHTED.
No assumed lift estimate, summability or nuclearity. Haar invariance is explicit.
This is a direct HS-energy component and does not claim an S1 realization. -/
theorem genuine_cutoff_kernel_relative_energy_bound
    (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ρ φ : HeckeIdeleClasses K → ℂ)
    (hρ : Measurable (fun x => ENNReal.ofReal (‖ρ x‖^2)))
    (hφ : Measurable (fun g => ENNReal.ofReal
      (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖genuineCutoffKernel K α s ρ φ x y‖^2) ∂μ ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (‖ρ x‖^2) ∂μ) *
      (∫⁻ g, ENNReal.ofReal
        (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g)) ∂μ) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖ρ x‖^2) *
        (∫⁻ g, ENNReal.ofReal
          (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g)) ∂μ) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (‖ρ x‖^2) * ENNReal.ofReal
            (‖φ (x*y⁻¹)‖^2 * translationCost α s (genuineRealClassLog K (x*y⁻¹))) ∂μ := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (sq_nonneg ‖ρ x‖)]
          apply ENNReal.ofReal_le_ofReal
          rw [genuineCutoffKernel_norm_sq, ← mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (genuine_relative_weight_bound K α s hα hs x y) (by positivity)
        _ = _ := by
          have hm : Measurable (fun y : HeckeIdeleClasses K =>
              ENNReal.ofReal (‖φ (x*y⁻¹)‖^2 *
                translationCost α s (genuineRealClassLog K (x*y⁻¹)))) :=
            hφ.comp (hpres x).measurable
          rw [lintegral_const_mul _ hm, (hpres x).lintegral_comp hφ]
    _ = _ := lintegral_mul_const _ hρ

#check genuine_relative_weight_bound
#print axioms genuine_relative_weight_bound
#check genuineCutoffKernel_norm_sq
#print axioms genuineCutoffKernel_norm_sq
#check genuine_cutoff_kernel_relative_energy_bound
#print axioms genuine_cutoff_kernel_relative_energy_bound

/-- Product-measure version of the same actual kernel estimate. -/
theorem genuine_cutoff_kernel_relative_product_bound
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ρ φ : HeckeIdeleClasses K → ℂ)
    (hρ : Measurable (fun x => ENNReal.ofReal (‖ρ x‖^2)))
    (hφ : Measurable (fun g => ENNReal.ofReal
      (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ)
    (hk : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖genuineCutoffKernel K α s ρ φ z.1 z.2‖^2)) (μ.prod μ)) :
    (∫⁻ z : HeckeIdeleClasses K × HeckeIdeleClasses K,
      ENNReal.ofReal (‖genuineCutoffKernel K α s ρ φ z.1 z.2‖^2) ∂μ.prod μ) ≤
      (∫⁻ x, ENNReal.ofReal (‖ρ x‖^2) ∂μ) *
      (∫⁻ g, ENNReal.ofReal
        (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g)) ∂μ) := by
  rw [lintegral_prod _ hk]
  exact genuine_cutoff_kernel_relative_energy_bound K μ α s hα hs ρ φ hρ hφ hpres

/-- Finiteness of actual kernel energy from the two finite scalar masses. -/
theorem genuine_cutoff_kernel_relative_energy_finite
    (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ρ φ : HeckeIdeleClasses K → ℂ)
    (hρ : Measurable (fun x => ENNReal.ofReal (‖ρ x‖^2)))
    (hφ : Measurable (fun g => ENNReal.ofReal
      (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ)
    (hρfin : (∫⁻ x, ENNReal.ofReal (‖ρ x‖^2) ∂μ) ≠ ⊤)
    (hφfin : (∫⁻ g, ENNReal.ofReal
      (‖φ g‖^2 * translationCost α s (genuineRealClassLog K g)) ∂μ) ≠ ⊤) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖genuineCutoffKernel K α s ρ φ x y‖^2) ∂μ ∂μ) < ⊤ := by
  exact lt_of_le_of_lt
    (genuine_cutoff_kernel_relative_energy_bound K μ α s hα hs ρ φ hρ hφ hpres)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hρfin hφfin))

#check genuine_cutoff_kernel_relative_energy_finite
#print axioms genuine_cutoff_kernel_relative_energy_finite
#check genuine_cutoff_kernel_relative_product_bound
#print axioms genuine_cutoff_kernel_relative_product_bound
end
end Round93G

namespace Round95D
noncomputable section
open MeasureTheory MasulloGRH Round93G
variable (K : Type*) [Field K] [NumberField K]

def logQuadratic (x : HeckeIdeleClasses K) : ℝ :=
  1 + (genuineRealClassLog K x)^2

theorem logQuadratic_pos (x : HeckeIdeleClasses K) : 0 < logQuadratic K x := by
  unfold logQuadratic
  positivity

/-- Combined kernel of M_(1/p) A(psi) M_(sqrt p). The unbounded middle
multiplier is not separately asserted to define a bounded operator. -/
def correctionKernel (α s : ℝ) (ψ : HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ :=
  genuineCutoffKernel K α s (fun z => (((logQuadratic K z)⁻¹ : ℝ) : ℂ)) ψ x y *
    (Real.sqrt (logQuadratic K y) : ℂ)

theorem logQuadratic_displacement (x y : HeckeIdeleClasses K) :
    logQuadratic K y ≤ 2 * logQuadratic K x * logQuadratic K (x*y⁻¹) := by
  have hid : genuineRealClassLog K y =
      genuineRealClassLog K x - genuineRealClassLog K (x*y⁻¹) := by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv]
    ring
  unfold logQuadratic
  conv_lhs => rw [hid]
  nlinarith [sq_nonneg (genuineRealClassLog K x + genuineRealClassLog K (x*y⁻¹)),
    sq_nonneg (genuineRealClassLog K x * genuineRealClassLog K (x*y⁻¹))]

/-- Pointwise energy majorant for the genuine noncompact correction factor. -/
theorem genuine_correction_kernel_bound (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (ψ : HeckeIdeleClasses K → ℂ) (x y : HeckeIdeleClasses K) :
    ‖correctionKernel K α s ψ x y‖^2 ≤
      (2 * (logQuadratic K x)⁻¹) *
      (‖ψ (x*y⁻¹)‖^2 * logQuadratic K (x*y⁻¹) *
        translationCost α s (genuineRealClassLog K (x*y⁻¹))) := by
  have hx := logQuadratic_pos K x
  have hy := logQuadratic_pos K y
  have hg := logQuadratic_pos K (x*y⁻¹)
  have hc : ((logQuadratic K x)⁻¹)^2 * logQuadratic K y ≤
      2 * (logQuadratic K x)⁻¹ * logQuadratic K (x*y⁻¹) := by
    calc
      _ ≤ ((logQuadratic K x)⁻¹)^2 *
          (2 * logQuadratic K x * logQuadratic K (x*y⁻¹)) :=
        mul_le_mul_of_nonneg_left (logQuadratic_displacement K x y) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt hx]
  have hw (z : HeckeIdeleClasses K) :
      0 ≤ stripWeight α s (genuineRealClassLog K z) := by
    unfold stripWeight
    positivity
  have hn : ‖correctionKernel K α s ψ x y‖^2 =
      (((logQuadratic K x)⁻¹)^2 * ‖ψ (x*y⁻¹)‖^2 *
        (stripWeight α s (genuineRealClassLog K x) /
          stripWeight α s (genuineRealClassLog K y))) * logQuadratic K y := by
    unfold correctionKernel
    rw [norm_mul, mul_pow, genuineCutoffKernel_norm_sq]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hy.le,
      abs_of_nonneg (inv_nonneg.mpr hx.le)]
  rw [hn]
  calc
    _ = (‖ψ (x*y⁻¹)‖^2 * (((logQuadratic K x)⁻¹)^2 * logQuadratic K y)) *
        (stripWeight α s (genuineRealClassLog K x) /
          stripWeight α s (genuineRealClassLog K y)) := by ring
    _ ≤ (‖ψ (x*y⁻¹)‖^2 *
        (2 * (logQuadratic K x)⁻¹ * logQuadratic K (x*y⁻¹))) *
        translationCost α s (genuineRealClassLog K (x*y⁻¹)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc (sq_nonneg _))
        (genuine_relative_weight_bound K α s hα hs x y)
        (div_nonneg (hw x) (hw y)) (by positivity)
    _ = _ := by ring

/-- First-factor energy with no expanding output-cutoff mass. -/
theorem genuine_correction_kernel_energy_bound
    (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ψ : HeckeIdeleClasses K → ℂ)
    (hb : Measurable (fun x => ENNReal.ofReal (2 * (logQuadratic K x)⁻¹)))
    (hψ : Measurable (fun g => ENNReal.ofReal
      (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖correctionKernel K α s ψ x y‖^2) ∂μ ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) ∂μ) *
      (∫⁻ g, ENNReal.ofReal
        (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g)) ∂μ) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) *
        (∫⁻ g, ENNReal.ofReal
          (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g)) ∂μ) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) *
            ENNReal.ofReal (‖ψ (x*y⁻¹)‖^2 * logQuadratic K (x*y⁻¹) *
              translationCost α s (genuineRealClassLog K (x*y⁻¹))) ∂μ := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (inv_nonneg.mpr (logQuadratic_pos K x).le))]
          exact ENNReal.ofReal_le_ofReal (genuine_correction_kernel_bound K α s hα hs ψ x y)
        _ = _ := by
          have hm : Measurable (fun y : HeckeIdeleClasses K =>
              ENNReal.ofReal (‖ψ (x*y⁻¹)‖^2 * logQuadratic K (x*y⁻¹) *
                translationCost α s (genuineRealClassLog K (x*y⁻¹)))) :=
            hψ.comp (hpres x).measurable
          rw [lintegral_const_mul _ hm, (hpres x).lintegral_comp hψ]
    _ = _ := lintegral_mul_const _ hb

#check genuine_correction_kernel_bound
#print axioms genuine_correction_kernel_bound
#check genuine_correction_kernel_energy_bound
#print axioms genuine_correction_kernel_energy_bound
end
end Round95D

/- Reused exact checked G95 raw-kernel composition component. -/
namespace Round96D
noncomputable section
open MeasureTheory MasulloGRH Round93G
variable (K : Type*) [Field K] [NumberField K]

def genuineHaarConvolution (μ : Measure (HeckeIdeleClasses K))
    (ψ θ : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ g, ψ g * θ (g⁻¹*x) ∂μ

/-- Exact integral composition with the intermediate cutoff in its correct place.
This identifies raw kernels, not yet bounded operators or their S1 norms. -/
theorem genuine_kernel_composition_integral
    (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (ρ ψ σ θ : HeckeIdeleClasses K → ℂ)
    (hpres : ∀ x, MeasurePreserving (fun z : HeckeIdeleClasses K => x*z⁻¹) μ μ)
    (hemb : ∀ x, MeasurableEmbedding (fun z : HeckeIdeleClasses K => x*z⁻¹))
    (hσ : ∀ x z, ρ x ≠ 0 → ψ (x*z⁻¹) ≠ 0 → σ z = 1)
    (x y : HeckeIdeleClasses K) :
    (∫ z, genuineCutoffKernel K α s ρ ψ x z *
      genuineCutoffKernel K α s σ θ z y ∂μ) =
    genuineCutoffKernel K α s ρ (genuineHaarConvolution K μ ψ θ) x y := by
  let w := fun z : HeckeIdeleClasses K => stripWeight α s (genuineRealClassLog K z)
  have hw (z : HeckeIdeleClasses K) : 0 < w z := by
    dsimp [w, stripWeight]
    positivity
  have htel (z : HeckeIdeleClasses K) :
      (Real.sqrt (w x / w z) : ℂ) * (Real.sqrt (w z / w y) : ℂ) =
        (Real.sqrt (w x / w y) : ℂ) := by
    have hr : Real.sqrt (w x / w z) * Real.sqrt (w z / w y) = Real.sqrt (w x / w y) := by
      rw [← Real.sqrt_mul (div_nonneg (hw x).le (hw z).le)]
      congr 1
      field_simp [ne_of_gt (hw z), ne_of_gt (hw y)]
    exact_mod_cast hr
  have hid : (∫ z, genuineCutoffKernel K α s ρ ψ x z *
      genuineCutoffKernel K α s σ θ z y ∂μ) =
      (ρ x * (Real.sqrt (w x / w y) : ℂ)) *
        (∫ z, ψ (x*z⁻¹) * θ (z*y⁻¹) ∂μ) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    unfold genuineCutoffKernel
    by_cases hρx : ρ x = 0
    · simp [hρx]
    by_cases hψz : ψ (x*z⁻¹) = 0
    · simp [hψz]
    rw [hσ x z hρx hψz]
    change (ρ x * ψ (x*z⁻¹) * (Real.sqrt (w x / w z) : ℂ)) *
      (1 * θ (z*y⁻¹) * (Real.sqrt (w z / w y) : ℂ)) = _
    calc
      _ = (ρ x * ψ (x*z⁻¹) * θ (z*y⁻¹)) *
          ((Real.sqrt (w x / w z) : ℂ) * (Real.sqrt (w z / w y) : ℂ)) := by ring
      _ = _ := by rw [htel]; ring
  have hgroup (z : HeckeIdeleClasses K) : (x*z⁻¹)⁻¹*(x*y⁻¹) = z*y⁻¹ := by group
  have hc := (hpres x).integral_comp (hemb x)
    (fun g => ψ g * θ (g⁻¹*(x*y⁻¹)))
  simp only [hgroup] at hc
  rw [hid, hc]
  unfold genuineCutoffKernel genuineHaarConvolution
  dsimp only [w]
  ring

#check genuine_kernel_composition_integral
#print axioms genuine_kernel_composition_integral
end
end Round96D

namespace Round96D
noncomputable section
open MeasureTheory MasulloGRH Round93G Round95D
variable (K : Type*) [Field K] [NumberField K]

def companionCutoff (z : HeckeIdeleClasses K) : ℂ :=
  (((Real.sqrt (logQuadratic K z))⁻¹ : ℝ) : ℂ)

def companionKernel (α s : ℝ) (θ : HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ :=
  genuineCutoffKernel K α s (companionCutoff K) θ x y

theorem companionCutoff_norm_sq (z : HeckeIdeleClasses K) :
    ‖companionCutoff K z‖^2 = (logQuadratic K z)⁻¹ := by
  unfold companionCutoff
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [inv_pow, Real.sq_sqrt (logQuadratic_pos K z).le]

/-- Actual companion energy, with a fixed Cauchy output mass. -/
theorem genuine_companion_kernel_energy_bound
    (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (θ : HeckeIdeleClasses K → ℂ)
    (hb : Measurable (fun x => ENNReal.ofReal ((logQuadratic K x)⁻¹)))
    (hθ : Measurable (fun g => ENNReal.ofReal
      (‖θ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖companionKernel K α s θ x y‖^2) ∂μ ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal ((logQuadratic K x)⁻¹) ∂μ) *
      (∫⁻ g, ENNReal.ofReal
        (‖θ g‖^2 * translationCost α s (genuineRealClassLog K g)) ∂μ) := by
  have hm : Measurable (fun x => ENNReal.ofReal (‖companionCutoff K x‖^2)) := by
    simpa only [companionCutoff_norm_sq] using hb
  simpa only [companionKernel, companionCutoff_norm_sq] using
    genuine_cutoff_kernel_relative_energy_bound K μ α s hα hs
      (companionCutoff K) θ hm hθ hpres

/-- Exact noncompact correction factorization at the genuine raw-kernel level.
No intermediate support cutoff and no separately bounded sqrt(p) multiplier. -/
theorem genuine_correction_companion_composition
    (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (ψ θ : HeckeIdeleClasses K → ℂ)
    (hpres : ∀ x, MeasurePreserving (fun z : HeckeIdeleClasses K => x*z⁻¹) μ μ)
    (hemb : ∀ x, MeasurableEmbedding (fun z : HeckeIdeleClasses K => x*z⁻¹))
    (x y : HeckeIdeleClasses K) :
    (∫ z, correctionKernel K α s ψ x z * companionKernel K α s θ z y ∂μ) =
      genuineCutoffKernel K α s
        (fun z => (((logQuadratic K z)⁻¹ : ℝ) : ℂ))
        (genuineHaarConvolution K μ ψ θ) x y := by
  have he (z : HeckeIdeleClasses K) :
      correctionKernel K α s ψ x z * companionKernel K α s θ z y =
      genuineCutoffKernel K α s (fun z => (((logQuadratic K z)⁻¹ : ℝ) : ℂ)) ψ x z *
        genuineCutoffKernel K α s (fun _ => 1) θ z y := by
    have hp : (Real.sqrt (logQuadratic K z) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (logQuadratic_pos K z)))
    unfold correctionKernel companionKernel companionCutoff genuineCutoffKernel
    push_cast
    field_simp
  simp_rw [he]
  exact genuine_kernel_composition_integral K μ α s
    (fun z => (((logQuadratic K z)⁻¹ : ℝ) : ℂ)) ψ (fun _ => 1) θ
    hpres hemb (by intros; rfl) x y

#check genuine_companion_kernel_energy_bound
#print axioms genuine_companion_kernel_energy_bound
#check genuine_correction_companion_composition
#print axioms genuine_correction_companion_composition
end
end Round96D

namespace Round96D
noncomputable section
open MeasureTheory MasulloGRH Round93G Round95D
open scoped ENNReal
variable (K : Type*) [Field K] [NumberField K]

/-- Continuous rank-one cost of the two genuine decaying kernels. -/
def correctionCompositionCost (μ : Measure (HeckeIdeleClasses K)) (α s : ℝ)
    (ψ θ : HeckeIdeleClasses K → ℂ) : ℝ≥0∞ :=
  ∫⁻ z, (∫⁻ x, ENNReal.ofReal (‖correctionKernel K α s ψ x z‖^2) ∂μ) ^ (1/2 : ℝ) *
    (∫⁻ y, ENNReal.ofReal (‖companionKernel K α s θ z y‖^2) ∂μ) ^ (1/2 : ℝ) ∂μ

/-- A direct bound on actual rank-one kernel costs, with no cutoff radius.
No nuclearity or summability is assumed. Operator realization is not claimed. -/
theorem genuine_correction_rankOneCost_bound
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ψ θ : HeckeIdeleClasses K → ℂ)
    (hb₂ : Measurable (fun x => ENNReal.ofReal (2 * (logQuadratic K x)⁻¹)))
    (hb₁ : Measurable (fun x => ENNReal.ofReal ((logQuadratic K x)⁻¹)))
    (hψ : Measurable (fun g => ENNReal.ofReal
      (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g))))
    (hθ : Measurable (fun g => ENNReal.ofReal
      (‖θ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ)
    (hk₁ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖correctionKernel K α s ψ z.1 z.2‖^2)) (μ.prod μ))
    (hk₂ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖companionKernel K α s θ z.1 z.2‖^2)) (μ.prod μ)) :
    correctionCompositionCost K μ α s ψ θ ≤
      ((∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) ∂μ) *
        (∫⁻ g, ENNReal.ofReal (‖ψ g‖^2 * logQuadratic K g *
          translationCost α s (genuineRealClassLog K g)) ∂μ)) ^ (1/2 : ℝ) *
      ((∫⁻ x, ENNReal.ofReal ((logQuadratic K x)⁻¹) ∂μ) *
        (∫⁻ g, ENNReal.ofReal (‖θ g‖^2 *
          translationCost α s (genuineRealClassLog K g)) ∂μ)) ^ (1/2 : ℝ) := by
  let a : HeckeIdeleClasses K → ℝ≥0∞ := fun z =>
    ∫⁻ x, ENNReal.ofReal (‖correctionKernel K α s ψ x z‖^2) ∂μ
  let b : HeckeIdeleClasses K → ℝ≥0∞ := fun z =>
    ∫⁻ y, ENNReal.ofReal (‖companionKernel K α s θ z y‖^2) ∂μ
  have ha : AEMeasurable a μ := hk₁.lintegral_prod_left
  have hb : AEMeasurable b μ := hk₂.lintegral_prod_right
  have hhalf₁ : AEMeasurable (fun z => a z ^ (1/2 : ℝ)) μ := by fun_prop
  have hhalf₂ : AEMeasurable (fun z => b z ^ (1/2 : ℝ)) μ := by fun_prop
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two hhalf₁ hhalf₂
  have hpow (t : ℝ≥0∞) : (t ^ (1/2 : ℝ)) ^ (2 : ℝ) = t := by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, hpow] at hholder
  have hea : (∫⁻ z, a z ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) ∂μ) *
        (∫⁻ g, ENNReal.ofReal (‖ψ g‖^2 * logQuadratic K g *
          translationCost α s (genuineRealClassLog K g)) ∂μ) := by
    dsimp only [a]
    rw [← lintegral_lintegral_swap hk₁]
    exact genuine_correction_kernel_energy_bound K μ α s hα hs ψ hb₂ hψ hpres
  have heb := genuine_companion_kernel_energy_bound K μ α s hα hs θ hb₁ hθ hpres
  exact hholder.trans (mul_le_mul'
    (ENNReal.rpow_le_rpow hea (by norm_num))
    (ENNReal.rpow_le_rpow heb (by norm_num)))

#check genuine_correction_rankOneCost_bound
#print axioms genuine_correction_rankOneCost_bound
end
end Round96D

namespace Round96D
noncomputable section
open MeasureTheory MasulloGRH Round93G Round95D
open scoped ENNReal
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_correction_rankOneCost_finite
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] (α s : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (ψ θ : HeckeIdeleClasses K → ℂ)
    (hb₂ : Measurable (fun x => ENNReal.ofReal (2 * (logQuadratic K x)⁻¹)))
    (hb₁ : Measurable (fun x => ENNReal.ofReal ((logQuadratic K x)⁻¹)))
    (hψ : Measurable (fun g => ENNReal.ofReal
      (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g))))
    (hθ : Measurable (fun g => ENNReal.ofReal
      (‖θ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ)
    (hk₁ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖correctionKernel K α s ψ z.1 z.2‖^2)) (μ.prod μ))
    (hk₂ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖companionKernel K α s θ z.1 z.2‖^2)) (μ.prod μ))
    (hM₂ : (∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) ∂μ) ≠ ⊤)
    (hM₁ : (∫⁻ x, ENNReal.ofReal ((logQuadratic K x)⁻¹) ∂μ) ≠ ⊤)
    (hD₁ : (∫⁻ g, ENNReal.ofReal (‖ψ g‖^2 * logQuadratic K g *
      translationCost α s (genuineRealClassLog K g)) ∂μ) ≠ ⊤)
    (hD₀ : (∫⁻ g, ENNReal.ofReal (‖θ g‖^2 *
      translationCost α s (genuineRealClassLog K g)) ∂μ) ≠ ⊤) :
    correctionCompositionCost K μ α s ψ θ < ⊤ := by
  exact lt_of_le_of_lt
    (genuine_correction_rankOneCost_bound K μ α s hα hs ψ θ hb₂ hb₁ hψ hθ hpres hk₁ hk₂)
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hM₂ hD₁))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hM₁ hD₀)))

#check genuine_correction_rankOneCost_finite
#print axioms genuine_correction_rankOneCost_finite
end
end Round96D

namespace Round97D
noncomputable section
open MeasureTheory MasulloGRH Round93G Round95D Round96D
open scoped ENNReal
variable (K : Type*) [Field K] [NumberField K]

/-- Explicit support cost; this radius belongs to the fixed test, not the
expanding output cutoff. -/
def testSupportCost (α s R q : ℝ) : ℝ :=
  (1 + R^2)^q * (Real.exp (2*α*R) * (2*(1+R^2))^(s/2))

theorem translationCost_on_log_ball (α s R t : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R) (ht : |t| ≤ R) :
    translationCost α s t ≤ Real.exp (2*α*R) * (2*(1+R^2))^(s/2) := by
  have hsq : t^2 ≤ R^2 := by
    have h := mul_nonneg (sub_nonneg.mpr ht) (add_nonneg hR (abs_nonneg t))
    nlinarith [sq_abs t]
  unfold translationCost
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  · exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  · positivity
  · positivity

/-- Weighted test masses in the genuine correction estimate are controlled
by ordinary L2 energy and fixed logarithmic support, for every real q>=0. -/
theorem genuine_logSupported_weighted_energy_bound
    (μ : Measure (HeckeIdeleClasses K)) (α s R q : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (φ : HeckeIdeleClasses K → ℂ)
    (hsupport : ∀ g, φ g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hφ : Measurable (fun g => ENNReal.ofReal (‖φ g‖^2))) :
    (∫⁻ g, ENNReal.ofReal (‖φ g‖^2 * (logQuadratic K g)^q *
      translationCost α s (genuineRealClassLog K g)) ∂μ) ≤
    ENNReal.ofReal (testSupportCost α s R q) *
      (∫⁻ g, ENNReal.ofReal (‖φ g‖^2) ∂μ) := by
  have hpoint (g : HeckeIdeleClasses K) :
      ‖φ g‖^2 * (logQuadratic K g)^q *
        translationCost α s (genuineRealClassLog K g) ≤
      testSupportCost α s R q * ‖φ g‖^2 := by
    by_cases hz : φ g = 0
    · simp [hz]
    have ht := hsupport g hz
    have hsq : (genuineRealClassLog K g)^2 ≤ R^2 := by
      have h := mul_nonneg (sub_nonneg.mpr ht)
        (add_nonneg hR (abs_nonneg (genuineRealClassLog K g)))
      nlinarith [sq_abs (genuineRealClassLog K g)]
    have hp : (logQuadratic K g)^q ≤ (1+R^2)^q :=
      Real.rpow_le_rpow (logQuadratic_pos K g).le
        (by unfold logQuadratic; linarith) hq
    have hc := translationCost_on_log_ball α s R (genuineRealClassLog K g)
      hα hs hR ht
    have hh := mul_le_mul hp hc
      (by unfold translationCost; positivity) (by positivity : 0 ≤ (1+R^2)^q)
    have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖φ g‖)
    unfold testSupportCost
    nlinarith only [hh']
  calc
    _ ≤ ∫⁻ g, ENNReal.ofReal (testSupportCost α s R q) *
        ENNReal.ofReal (‖φ g‖^2) ∂μ := by
      apply lintegral_mono
      intro g
      dsimp only
      rw [← ENNReal.ofReal_mul (by unfold testSupportCost; positivity)]
      exact ENNReal.ofReal_le_ofReal (hpoint g)
    _ = _ := lintegral_const_mul _ hφ

/-- Removes the weighted-energy finiteness premise from the genuine kernel
cost route; ordinary test L2 energy remains an explicit input. -/
theorem genuine_logSupported_weighted_energy_finite
    (μ : Measure (HeckeIdeleClasses K)) (α s R q : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R) (hq : 0 ≤ q)
    (φ : HeckeIdeleClasses K → ℂ)
    (hsupport : ∀ g, φ g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hφ : Measurable (fun g => ENNReal.ofReal (‖φ g‖^2)))
    (hE : (∫⁻ g, ENNReal.ofReal (‖φ g‖^2) ∂μ) ≠ ⊤) :
    (∫⁻ g, ENNReal.ofReal (‖φ g‖^2 * (logQuadratic K g)^q *
      translationCost α s (genuineRealClassLog K g)) ∂μ) < ⊤ := by
  exact lt_of_le_of_lt
    (genuine_logSupported_weighted_energy_bound K μ α s R q hα hs hR hq φ hsupport hφ)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE))

#check genuine_logSupported_weighted_energy_bound
#print axioms genuine_logSupported_weighted_energy_bound
#check genuine_logSupported_weighted_energy_finite
#print axioms genuine_logSupported_weighted_energy_finite
end
end Round97D

namespace Round97D
noncomputable section
open MeasureTheory MasulloGRH Round93G Round95D Round96D
open scoped ENNReal
variable (K : Type*) [Field K] [NumberField K]

/-- Specializes the checked logarithmic Haar formula to the fixed mass in
the actual correction factorization. The pushforward is explicit here. -/
theorem genuine_correction_cauchy_integrable
    (μ : Measure (HeckeIdeleClasses K)) (V : ℝ≥0)
    (hlog : Measurable (genuineRealClassLog K))
    (hpush : Measure.map (genuineRealClassLog K) μ = (V : ℝ≥0∞) • volume) :
    Integrable (fun x => (logQuadratic K x)⁻¹) μ := by
  have hg : Continuous (fun t : ℝ => (1+t^2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t; positivity
  have hi : Integrable (fun t : ℝ => (1+t^2)⁻¹)
      (Measure.map (genuineRealClassLog K) μ) := by
    rw [hpush]
    exact integrable_inv_one_add_sq.smul_measure (by simp)
  exact (integrable_map_measure hg.aestronglyMeasurable hlog.aemeasurable).mp hi

/-- Finite continuous rank-one cost for the actual decaying convolution
kernels, now using ordinary test L2 energy rather than weighted energies. -/
theorem genuine_correction_rankOneCost_finite_of_logSupport
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] (α s R : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (ψ θ : HeckeIdeleClasses K → ℂ)
    (hb₁ : Measurable (fun x => ENNReal.ofReal ((logQuadratic K x)⁻¹)))
    (hψ : Measurable (fun g => ENNReal.ofReal
      (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g))))
    (hθ : Measurable (fun g => ENNReal.ofReal
      (‖θ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hψ₀ : Measurable (fun g => ENNReal.ofReal (‖ψ g‖^2)))
    (hθ₀ : Measurable (fun g => ENNReal.ofReal (‖θ g‖^2)))
    (hψsupport : ∀ g, ψ g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hθsupport : ∀ g, θ g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ)
    (hk₁ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖correctionKernel K α s ψ z.1 z.2‖^2)) (μ.prod μ))
    (hk₂ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖companionKernel K α s θ z.1 z.2‖^2)) (μ.prod μ))
    (hM : (∫⁻ x, ENNReal.ofReal ((logQuadratic K x)⁻¹) ∂μ) ≠ ⊤)
    (hEψ : (∫⁻ g, ENNReal.ofReal (‖ψ g‖^2) ∂μ) ≠ ⊤)
    (hEθ : (∫⁻ g, ENNReal.ofReal (‖θ g‖^2) ∂μ) ≠ ⊤) :
    correctionCompositionCost K μ α s ψ θ < ⊤ := by
  have hb₂ : Measurable (fun x => ENNReal.ofReal (2 * (logQuadratic K x)⁻¹)) := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact measurable_const.mul hb₁
  have hM₂ : (∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) ∂μ) ≠ ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul _ hb₁]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  have hD₁ := genuine_logSupported_weighted_energy_finite K μ α s R 1
    hα hs hR (by norm_num) ψ hψsupport hψ₀ hEψ
  have hD₀ := genuine_logSupported_weighted_energy_finite K μ α s R 0
    hα hs hR (by norm_num) θ hθsupport hθ₀ hEθ
  simp only [Real.rpow_one] at hD₁
  simp only [Real.rpow_zero, mul_one] at hD₀
  exact genuine_correction_rankOneCost_finite K μ α s hα hs ψ θ
    hb₂ hb₁ hψ hθ hpres hk₁ hk₂ hM₂ hM (ne_of_lt hD₁) (ne_of_lt hD₀)

#check genuine_correction_cauchy_integrable
#print axioms genuine_correction_cauchy_integrable
#check genuine_correction_rankOneCost_finite_of_logSupport
#print axioms genuine_correction_rankOneCost_finite_of_logSupport
end
end Round97D

namespace Round97D
noncomputable section
open MeasureTheory MasulloGRH Round93G Round95D Round96D
open scoped ENNReal
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_correction_cauchy_mass_finite
    (μ : Measure (HeckeIdeleClasses K)) (V : ℝ≥0)
    (hlog : Measurable (genuineRealClassLog K))
    (hpush : Measure.map (genuineRealClassLog K) μ = (V : ℝ≥0∞) • volume) :
    (∫⁻ x, ENNReal.ofReal ((logQuadratic K x)⁻¹) ∂μ) < ⊤ := by
  exact (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun x => inv_nonneg.mpr (logQuadratic_pos K x).le))).mp
      (genuine_correction_cauchy_integrable K μ V hlog hpush).hasFiniteIntegral

theorem genuine_correction_rankOneCost_finite_of_logHaar
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] (α s R : ℝ)
    (hα : 0 ≤ α) (hs : 0 ≤ s) (hR : 0 ≤ R)
    (ψ θ : HeckeIdeleClasses K → ℂ)
    (hb₁ : Measurable (fun x => ENNReal.ofReal ((logQuadratic K x)⁻¹)))
    (hψ : Measurable (fun g => ENNReal.ofReal
      (‖ψ g‖^2 * logQuadratic K g * translationCost α s (genuineRealClassLog K g))))
    (hθ : Measurable (fun g => ENNReal.ofReal
      (‖θ g‖^2 * translationCost α s (genuineRealClassLog K g))))
    (hψ₀ : Measurable (fun g => ENNReal.ofReal (‖ψ g‖^2)))
    (hθ₀ : Measurable (fun g => ENNReal.ofReal (‖θ g‖^2)))
    (hψsupport : ∀ g, ψ g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hθsupport : ∀ g, θ g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hpres : ∀ x, MeasurePreserving (fun y : HeckeIdeleClasses K => x*y⁻¹) μ μ)
    (hk₁ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖correctionKernel K α s ψ z.1 z.2‖^2)) (μ.prod μ))
    (hk₂ : AEMeasurable (fun z : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      ENNReal.ofReal (‖companionKernel K α s θ z.1 z.2‖^2)) (μ.prod μ))
    (V : ℝ≥0) (hlog : Measurable (genuineRealClassLog K))
    (hpush : Measure.map (genuineRealClassLog K) μ = (V : ℝ≥0∞) • volume)
    (hEψ : (∫⁻ g, ENNReal.ofReal (‖ψ g‖^2) ∂μ) ≠ ⊤)
    (hEθ : (∫⁻ g, ENNReal.ofReal (‖θ g‖^2) ∂μ) ≠ ⊤) :
    correctionCompositionCost K μ α s ψ θ < ⊤ := by
  have hM := ne_of_lt (genuine_correction_cauchy_mass_finite K μ V hlog hpush)
  have hb₂ : Measurable (fun x => ENNReal.ofReal (2 * (logQuadratic K x)⁻¹)) := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact measurable_const.mul hb₁
  have hM₂ : (∫⁻ x, ENNReal.ofReal (2 * (logQuadratic K x)⁻¹) ∂μ) ≠ ⊤ := by
    simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [lintegral_const_mul _ hb₁]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM
  have hD₁ := genuine_logSupported_weighted_energy_finite K μ α s R 1
    hα hs hR (by norm_num) ψ hψsupport hψ₀ hEψ
  have hD₀ := genuine_logSupported_weighted_energy_finite K μ α s R 0
    hα hs hR (by norm_num) θ hθsupport hθ₀ hEθ
  simp only [Real.rpow_one] at hD₁
  simp only [Real.rpow_zero, mul_one] at hD₀
  exact genuine_correction_rankOneCost_finite K μ α s hα hs ψ θ
    hb₂ hb₁ hψ hθ hpres hk₁ hk₂ hM₂ hM (ne_of_lt hD₁) (ne_of_lt hD₀)

#check genuine_correction_cauchy_mass_finite
#print axioms genuine_correction_cauchy_mass_finite
#check genuine_correction_rankOneCost_finite_of_logHaar
#print axioms genuine_correction_rankOneCost_finite_of_logHaar
end
end Round97D
