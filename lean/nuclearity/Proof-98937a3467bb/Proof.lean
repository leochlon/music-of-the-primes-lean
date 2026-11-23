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
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]

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


namespace Round123D
open MeasureTheory MasulloGRH
noncomputable section
def stripWeight (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (1 + u ^ 2) ^ (s / 2)
variable (K : Type*) [Field K] [NumberField K]
abbrev C := HeckeIdeleClasses K
abbrev ell := genuineRealClassLog K
noncomputable def W (alpha s : ℝ) (x : C K) := stripWeight alpha s (ell K x)
end
end Round123D
namespace Round127D
open MeasureTheory MasulloGRH Round123D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
def adjointRow (alpha s : ℝ) (h : C K → ℂ) (g x : C K) : ℂ :=
  h (g⁻¹*x) * (W K alpha s (g⁻¹*x) : ℂ) / (W K alpha s x : ℂ)
def actualAdjoint (mu : Measure (C K)) (alpha s : ℝ) (phi h : C K → ℂ) (x : C K) : ℂ :=
  ∫ g, star (phi g⁻¹) * adjointRow K alpha s h g x ∂mu
end
end Round127D
namespace Round129D
open MeasureTheory MasulloGRH Round123D Round127D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def reverseTest (phi : C K → ℂ) (g : C K) : ℂ := star (phi g⁻¹)
def logMoment (n : ℕ) (phi : C K → ℂ) (g : C K) : ℂ :=
  (ell K g : ℂ)^n * phi g
def genuineConvolution (mu : Measure (C K)) (phi h : C K → ℂ) (x : C K) : ℂ :=
  ∫ g, phi g * h (g⁻¹*x) ∂mu

theorem genuine_quadratic_weight (x : C K) :
    W K 0 2 x = 1 + ell K x ^ 2 := by
  norm_num [W, stripWeight]

/-- Literal weighted-adjoint integral identity at alpha=0,s=2. -/
theorem genuine_one_step_adjoint_expansion
    (mu : Measure (C K)) (phi h : C K → ℂ) (x : C K)
    (hi : ∀ n : ℕ, n ≤ 2 → Integrable
      (fun g => logMoment K n phi g * h (g⁻¹*x)) mu) :
    actualAdjoint K mu 0 2 (reverseTest K phi) h x =
      genuineConvolution K mu phi h x -
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)) *
        genuineConvolution K mu (logMoment K 1 phi) h x +
      (1 / (1 + (ell K x : ℂ)^2)) *
        genuineConvolution K mu (logMoment K 2 phi) h x := by
  have hq : (1 + (ell K x : ℂ)^2) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 1 + ell K x ^ 2))
  have he (g : C K) :
      star (reverseTest K phi g⁻¹) * adjointRow K 0 2 h g x =
      phi g * h (g⁻¹*x) -
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)) *
        (logMoment K 1 phi g * h (g⁻¹*x)) +
      (1 / (1 + (ell K x : ℂ)^2)) *
        (logMoment K 2 phi g * h (g⁻¹*x)) := by
    simp only [reverseTest, inv_inv, star_star, adjointRow, genuine_quadratic_weight,
      logMoment, ell, genuineRealClassLog_mul, genuineRealClassLog_inv,
      Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_pow]
    dsimp only [ell] at hq
    field_simp
    ring
  unfold actualAdjoint
  simp_rw [he]
  have h0 : Integrable (fun g => phi g * h (g⁻¹*x)) mu := by
    simpa only [logMoment, pow_zero, one_mul] using hi 0 (by omega)
  have h1 := (hi 1 (by omega)).const_mul
    (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2))
  have h2 := (hi 2 (by omega)).const_mul
    (1 / (1 + (ell K x : ℂ)^2))
  have hadd := integral_add (h0.sub h1) h2
  have hsub := integral_sub h0 h1
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_const_mul]
  rfl

#check genuine_one_step_adjoint_expansion
#print axioms genuine_one_step_adjoint_expansion
end
end Round129D

namespace Round129D
open MeasureTheory MasulloGRH Round123D Round127D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Two exact adjoint terms leave corrections damped by (1+ell^2)^-1.
No spectral projector or assumed nuclear bound is used in this identity. -/
theorem genuine_two_step_adjoint_expansion
    (mu : Measure (C K)) (phi h : C K → ℂ) (x : C K)
    (hi : ∀ n : ℕ, n ≤ 3 → Integrable
      (fun g => logMoment K n phi g * h (g⁻¹*x)) mu) :
    genuineConvolution K mu phi h x =
      actualAdjoint K mu 0 2 (reverseTest K phi) h x +
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)) *
        actualAdjoint K mu 0 2 (reverseTest K (logMoment K 1 phi)) h x +
      ((3 * (ell K x : ℂ)^2 - 1) / (1 + (ell K x : ℂ)^2)^2) *
        genuineConvolution K mu (logMoment K 2 phi) h x -
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)^2) *
        genuineConvolution K mu (logMoment K 3 phi) h x := by
  have hq : (1 + (ell K x : ℂ)^2) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 1 + ell K x ^ 2))
  have hi1 : ∀ n : ℕ, n ≤ 2 → Integrable
      (fun g => logMoment K n (logMoment K 1 phi) g * h (g⁻¹*x)) mu := by
    intro n hn
    simpa only [logMoment, pow_add, mul_assoc] using hi (n+1) (by omega)
  have h2 : logMoment K 1 (logMoment K 1 phi) = logMoment K 2 phi := by
    funext g
    simp [logMoment]
    ring
  have h3 : logMoment K 2 (logMoment K 1 phi) = logMoment K 3 phi := by
    funext g
    simp [logMoment]
    ring
  have h0 := genuine_one_step_adjoint_expansion K mu phi h x (fun n hn => hi n (by omega))
  have h1 := genuine_one_step_adjoint_expansion K mu (logMoment K 1 phi) h x hi1
  rw [h2, h3] at h1
  rw [h0, h1]
  field_simp
  ring

/-- Explicit correction multipliers: both are bounded by an integrable
reciprocal quadratic profile after genuine log pushforward. -/
theorem genuine_two_step_multiplier_bounds (x : C K) :
    |2 * ell K x / (1 + ell K x ^ 2)| ≤ 1 ∧
    |(3 * ell K x ^ 2 - 1) / (1 + ell K x ^ 2)^2| ≤
      3 / (1 + ell K x ^ 2) ∧
    |2 * ell K x / (1 + ell K x ^ 2)^2| ≤
      1 / (1 + ell K x ^ 2) := by
  have hq : (0 : ℝ) < 1 + ell K x ^ 2 := by positivity
  have ha : |2 * ell K x| ≤ 1 + ell K x ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ell K x - 1), sq_nonneg (ell K x + 1)]
  have hb : |3 * ell K x ^ 2 - 1| ≤ 3 * (1 + ell K x ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ell K x)]
  simp only [abs_div, abs_of_pos hq, abs_pow]
  constructor
  · exact (div_le_one hq).mpr ha
  constructor
  · apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    field_simp
    nlinarith
  · apply (div_le_iff₀ (sq_pos_of_pos hq)).mpr
    field_simp
    nlinarith

#check genuine_two_step_adjoint_expansion
#print axioms genuine_two_step_adjoint_expansion
#check genuine_two_step_multiplier_bounds
#print axioms genuine_two_step_multiplier_bounds
end
end Round129D

namespace Round129D
open MeasureTheory MasulloGRH Round123D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Direct pointwise norm control of the literal correction in the checked
expansion; this is not an integrated nuclear norm estimate. -/
theorem genuine_correction_norm_bound
    (mu : Measure (C K)) (phi h : C K → ℂ) (x : C K) :
    ‖(((3 * ell K x ^ 2 - 1) / (1 + ell K x ^ 2)^2 : ℝ) : ℂ) *
        genuineConvolution K mu (logMoment K 2 phi) h x -
      ((2 * ell K x / (1 + ell K x ^ 2)^2 : ℝ) : ℂ) *
        genuineConvolution K mu (logMoment K 3 phi) h x‖ ≤
      (3 * ‖genuineConvolution K mu (logMoment K 2 phi) h x‖ +
        ‖genuineConvolution K mu (logMoment K 3 phi) h x‖) /
        (1 + ell K x ^ 2) := by
  have hb := (genuine_two_step_multiplier_bounds K x).2.1
  have hc := (genuine_two_step_multiplier_bounds K x).2.2
  calc
    _ ≤ ‖(((3 * ell K x ^ 2 - 1) / (1 + ell K x ^ 2)^2 : ℝ) : ℂ) *
        genuineConvolution K mu (logMoment K 2 phi) h x‖ +
      ‖((2 * ell K x / (1 + ell K x ^ 2)^2 : ℝ) : ℂ) *
        genuineConvolution K mu (logMoment K 3 phi) h x‖ := norm_sub_le _ _
    _ ≤ (3 / (1 + ell K x ^ 2)) *
        ‖genuineConvolution K mu (logMoment K 2 phi) h x‖ +
      (1 / (1 + ell K x ^ 2)) *
        ‖genuineConvolution K mu (logMoment K 3 phi) h x‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    _ = _ := by ring

#check genuine_correction_norm_bound
#print axioms genuine_correction_norm_bound
end
end Round129D

namespace Round130D
open MeasureTheory MasulloGRH Round123D Round127D Round129D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Membership in the genuine quadratic-weight domain implies ordinary L2.
This is a domain attachment for the actual convolution expansion. -/
theorem genuine_weighted_domain_memLp
    (mu : Measure (C K)) (h : C K → ℂ)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun x => ‖h x‖^2 * (1 + ell K x ^ 2)) mu) :
    MemLp h 2 mu := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply he.mono' (hm.norm.pow 2)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖h x‖^2 ≤ ‖h x‖^2 * (1 + ell K x^2)
  nlinarith [mul_nonneg (sq_nonneg ‖h x‖) (sq_nonneg (ell K x))]

/-- All genuine convolution rows are integrable for a square-integrable
admissible test and an input in the actual quadratic weighted domain. -/
theorem genuine_convolution_row_integrable_weighted
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (hp : MemLp phi 2 mu) (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    Integrable (fun g => phi g * h (g⁻¹*x)) mu := by
  have hh := genuine_weighted_domain_memLp K mu h hm he
  have ht : MeasurePreserving (fun g : C K => g⁻¹*x) mu mu := by
    simpa only [Function.comp_def, mul_comm] using
      (measurePreserving_mul_left mu x).comp (mu.measurePreserving_inv)
  exact hp.integrable_mul (hh.comp_measurePreserving ht)

/-- The two-step identity now follows on the actual weighted domain, with
no separately assumed translated row integrabilities. -/
theorem genuine_two_step_expansion_weighted_domain
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (hp : ∀ n : ℕ, n ≤ 3 → MemLp (logMoment K n phi) 2 mu)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    genuineConvolution K mu phi h x =
      actualAdjoint K mu 0 2 (reverseTest K phi) h x +
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)) *
        actualAdjoint K mu 0 2 (reverseTest K (logMoment K 1 phi)) h x +
      ((3 * (ell K x : ℂ)^2 - 1) / (1 + (ell K x : ℂ)^2)^2) *
        genuineConvolution K mu (logMoment K 2 phi) h x -
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)^2) *
        genuineConvolution K mu (logMoment K 3 phi) h x := by
  apply genuine_two_step_adjoint_expansion K mu phi h x
  intro n hn
  exact genuine_convolution_row_integrable_weighted K mu
    (logMoment K n phi) h x (hp n hn) hm he

#check genuine_weighted_domain_memLp
#print axioms genuine_weighted_domain_memLp
#check genuine_convolution_row_integrable_weighted
#print axioms genuine_convolution_row_integrable_weighted
#check genuine_two_step_expansion_weighted_domain
#print axioms genuine_two_step_expansion_weighted_domain
end
end Round130D

namespace Round130D
open MeasureTheory MasulloGRH Round123D Round129D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Compact logarithmic support supplies every test moment with the explicit
R^n cost; no spectral-label uniformity is asserted. -/
theorem genuine_logMoment_memLp
    (mu : Measure (C K)) (phi : C K → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hlog : Measurable (ell K)) (hp : MemLp phi 2 mu)
    (hs : ∀ g, phi g ≠ 0 → |ell K g| ≤ R) (n : ℕ) :
    MemLp (logMoment K n phi) 2 mu := by
  have hm : AEStronglyMeasurable (logMoment K n phi) mu := by
    exact ((Complex.measurable_ofReal.comp hlog).aestronglyMeasurable.pow n).mul
      hp.aestronglyMeasurable
  apply (hp.const_mul ((R : ℂ)^n)).of_le hm
  filter_upwards [] with g
  by_cases hg : phi g = 0
  · simp [logMoment, hg]
  · simp only [logMoment, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR]
    exact mul_le_mul_of_nonneg_right (by gcongr; exact hs g hg) (norm_nonneg _)

#check genuine_logMoment_memLp
#print axioms genuine_logMoment_memLp
end
end Round130D

namespace Round130D
open MeasureTheory MasulloGRH Round123D Round127D Round129D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_two_step_expansion_compact_log
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (R : ℝ) (hR : 0 ≤ R) (hlog : Measurable (ell K))
    (hp : MemLp phi 2 mu) (hs : ∀ g, phi g ≠ 0 → |ell K g| ≤ R)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    genuineConvolution K mu phi h x =
      actualAdjoint K mu 0 2 (reverseTest K phi) h x +
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)) *
        actualAdjoint K mu 0 2 (reverseTest K (logMoment K 1 phi)) h x +
      ((3 * (ell K x : ℂ)^2 - 1) / (1 + (ell K x : ℂ)^2)^2) *
        genuineConvolution K mu (logMoment K 2 phi) h x -
      (2 * (ell K x : ℂ) / (1 + (ell K x : ℂ)^2)^2) *
        genuineConvolution K mu (logMoment K 3 phi) h x := by
  apply genuine_two_step_expansion_weighted_domain K mu phi h x
  · intro n _
    exact genuine_logMoment_memLp K mu phi R hR hlog hp hs n
  · exact hm
  · exact he

#check genuine_two_step_expansion_compact_log
#print axioms genuine_two_step_expansion_compact_log
end
end Round130D

namespace Round130D
open MeasureTheory MasulloGRH Round123D Round129D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- A quantitative estimate on each actual smoothed lift. It has no spectral
label decay and alone does not prove nuclear summability. -/
theorem genuine_smoothed_lift_pointwise_bound
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (hp : MemLp phi 2 mu) (hh : MemLp h 2 mu) :
    ‖genuineConvolution K mu phi h x‖ ≤
      (∫ g, ‖phi g‖^2 ∂mu) ^ (1 / 2 : ℝ) *
      (∫ y, ‖h y‖^2 ∂mu) ^ (1 / 2 : ℝ) := by
  have ht : MeasurePreserving (fun g : C K => g⁻¹*x) mu mu := by
    simpa only [Function.comp_def, mul_comm] using
      (measurePreserving_mul_left mu x).comp (mu.measurePreserving_inv)
  let e : C K ≃ᵐ C K :=
    { toEquiv :=
        { toFun := fun g => g⁻¹*x
          invFun := fun g => g⁻¹*x
          left_inv := by intro g; simp [mul_comm]
          right_inv := by intro g; simp [mul_comm] }
      measurable_toFun := measurable_inv.mul_const x
      measurable_invFun := measurable_inv.mul_const x }
  have heq : (∫ g, ‖h (g⁻¹*x)‖^2 ∂mu) = ∫ y, ‖h y‖^2 ∂mu :=
    ht.integral_comp e.measurableEmbedding (fun y => ‖h y‖^2)
  have hp' : MemLp phi (ENNReal.ofReal 2) mu := by simpa using hp
  have hh' : MemLp (fun g => h (g⁻¹*x)) (ENNReal.ofReal 2) mu := by
    simpa only [ENNReal.ofReal_ofNat, Function.comp_def] using
      hh.comp_measurePreserving ht
  have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hp' hh'
  simp only [Real.rpow_two] at hc
  rw [heq] at hc
  calc
    _ ≤ ∫ g, ‖phi g * h (g⁻¹*x)‖ ∂mu := norm_integral_le_integral_norm _
    _ = ∫ g, ‖phi g‖ * ‖h (g⁻¹*x)‖ ∂mu := by simp only [norm_mul]
    _ ≤ _ := hc

#check genuine_smoothed_lift_pointwise_bound
#print axioms genuine_smoothed_lift_pointwise_bound
end
end Round130D

namespace Round131D
open MeasureTheory MasulloGRH Round123D Round129D Round130D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine weighted input controls its first logarithmic moment. -/
theorem genuine_weighted_log_input_memLp
    (mu : Measure (C K)) (h : C K → ℂ)
    (hlog : Measurable (ell K)) (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    MemLp (logMoment K 1 h) 2 mu := by
  have hme : AEStronglyMeasurable (logMoment K 1 h) mu := by
    change AEStronglyMeasurable (fun y => (ell K y : ℂ)^1 * h y) mu
    simpa only [pow_one] using
      ((Complex.measurable_ofReal.comp hlog).aestronglyMeasurable.mul hm :
        AEStronglyMeasurable (fun y => (ell K y : ℂ) * h y) mu)
  apply (memLp_two_iff_integrable_sq_norm hme).mpr
  apply he.mono' (hme.norm.pow 2)
  filter_upwards [] with y
  change ‖‖logMoment K 1 h y‖^2‖ ≤ ‖h y‖^2 * (1 + ell K y^2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [logMoment, pow_one, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [sq_nonneg ‖h y‖]

/-- Native logarithmic commutator for the actual arithmetic convolution.
The row integrabilities are derived from the weighted input domain. -/
theorem genuine_convolution_log_commutator
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (hlog : Measurable (ell K)) (hp : MemLp phi 2 mu)
    (hp1 : MemLp (logMoment K 1 phi) 2 mu)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    (ell K x : ℂ) * genuineConvolution K mu phi h x =
      genuineConvolution K mu phi (logMoment K 1 h) x +
      genuineConvolution K mu (logMoment K 1 phi) h x := by
  have hh := genuine_weighted_domain_memLp K mu h hm he
  have hh1 := genuine_weighted_log_input_memLp K mu h hlog hm he
  have ht : MeasurePreserving (fun g : C K => g⁻¹*x) mu mu := by
    simpa only [Function.comp_def, mul_comm] using
      (measurePreserving_mul_left mu x).comp (mu.measurePreserving_inv)
  have hi1 := hp.integrable_mul (hh1.comp_measurePreserving ht)
  have hi2 := hp1.integrable_mul (hh.comp_measurePreserving ht)
  have hid (g : C K) :
      (ell K x : ℂ) * (phi g * h (g⁻¹*x)) =
        phi g * logMoment K 1 h (g⁻¹*x) +
          logMoment K 1 phi g * h (g⁻¹*x) := by
    simp only [logMoment, pow_one, ell, genuineRealClassLog_mul,
      genuineRealClassLog_inv, Complex.ofReal_add, Complex.ofReal_neg]
    ring
  unfold genuineConvolution
  rw [← integral_const_mul]
  simp_rw [hid]
  exact integral_add hi1 hi2

/-- A derived weighted pointwise estimate for each actual smoothed lift.
It retains its input energies and does not assert nuclear summability. -/
theorem genuine_smoothed_lift_weighted_pointwise_bound
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (hlog : Measurable (ell K)) (hp : MemLp phi 2 mu)
    (hp1 : MemLp (logMoment K 1 phi) 2 mu)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    ‖genuineConvolution K mu phi h x‖ ^ 2 * (1 + ell K x ^ 2) ≤
      ((∫ g, ‖phi g‖^2 ∂mu) ^ (1/2 : ℝ) *
        (∫ y, ‖h y‖^2 ∂mu) ^ (1/2 : ℝ)) ^ 2 +
      ((∫ g, ‖phi g‖^2 ∂mu) ^ (1/2 : ℝ) *
          (∫ y, ‖logMoment K 1 h y‖^2 ∂mu) ^ (1/2 : ℝ) +
        (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu) ^ (1/2 : ℝ) *
          (∫ y, ‖h y‖^2 ∂mu) ^ (1/2 : ℝ)) ^ 2 := by
  have hh := genuine_weighted_domain_memLp K mu h hm he
  have hh1 := genuine_weighted_log_input_memLp K mu h hlog hm he
  have h0 := genuine_smoothed_lift_pointwise_bound K mu phi h x hp hh
  have h1 := genuine_smoothed_lift_pointwise_bound K mu phi
    (logMoment K 1 h) x hp hh1
  have h2 := genuine_smoothed_lift_pointwise_bound K mu
    (logMoment K 1 phi) h x hp1 hh
  have hid := genuine_convolution_log_commutator K mu phi h x hlog hp hp1 hm he
  have ht := norm_add_le (genuineConvolution K mu phi (logMoment K 1 h) x)
    (genuineConvolution K mu (logMoment K 1 phi) h x)
  rw [← hid, norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
  have hsum := ht.trans (add_le_add h1 h2)
  have hs0 := mul_self_le_mul_self (norm_nonneg _) h0
  have hs1 := mul_self_le_mul_self
    (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hsum
  nlinarith [sq_abs (ell K x)]

#check genuine_weighted_log_input_memLp
#print axioms genuine_weighted_log_input_memLp
#check genuine_convolution_log_commutator
#print axioms genuine_convolution_log_commutator
#check genuine_smoothed_lift_weighted_pointwise_bound
#print axioms genuine_smoothed_lift_weighted_pointwise_bound
end
end Round131D

namespace Round132D
open MeasureTheory MasulloGRH Round123D Round129D Round130D Round131D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def liftCost (mu : Measure (C K)) (phi h : C K → ℂ) : ℝ :=
  ((∫ g, ‖phi g‖^2 ∂mu) ^ (1/2 : ℝ) *
    (∫ y, ‖h y‖^2 ∂mu) ^ (1/2 : ℝ)) ^ 2 +
  ((∫ g, ‖phi g‖^2 ∂mu) ^ (1/2 : ℝ) *
      (∫ y, ‖logMoment K 1 h y‖^2 ∂mu) ^ (1/2 : ℝ) +
    (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu) ^ (1/2 : ℝ) *
      (∫ y, ‖h y‖^2 ∂mu) ^ (1/2 : ℝ)) ^ 2

def secondCorrection (mu : Measure (C K)) (phi h : C K → ℂ) (x : C K) : ℂ :=
  (((3 * ell K x ^ 2 - 1) / (1 + ell K x ^ 2)^2 : ℝ) : ℂ) *
    genuineConvolution K mu phi h x

/-- An actual corrected smoothed lift has a reciprocal-quartic weighted
energy envelope. Its input lift energies remain explicit. -/
theorem genuine_second_correction_pointwise
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (x : C K)
    (hlog : Measurable (ell K)) (hp : MemLp phi 2 mu)
    (hp1 : MemLp (logMoment K 1 phi) 2 mu)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    ‖secondCorrection K mu phi h x‖^2 * (1 + ell K x^2) ≤
      (9 * liftCost K mu phi h) * (1 / (1 + ell K x^2)^2) := by
  have hq : (0 : ℝ) < 1 + ell K x^2 := by positivity
  have hb := (genuine_two_step_multiplier_bounds K x).2.1
  have hv := genuine_smoothed_lift_weighted_pointwise_bound K mu phi h x
    hlog hp hp1 hm he
  change ‖genuineConvolution K mu phi h x‖^2 * (1 + ell K x^2) ≤
    liftCost K mu phi h at hv
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simp only [secondCorrection, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  calc
    _ ≤ (3 / (1 + ell K x^2))^2 * ‖genuineConvolution K mu phi h x‖^2 *
        (1 + ell K x^2) := by gcongr
    _ = (9 / (1 + ell K x^2)^2) *
        (‖genuineConvolution K mu phi h x‖^2 * (1 + ell K x^2)) := by field_simp; ring
    _ ≤ (9 / (1 + ell K x^2)^2) * liftCost K mu phi h :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ = _ := by ring

/-- Finiteness is derived from genuine-log Haar normalization, not assumed. -/
theorem genuine_quartic_profile_finite
    (mu : Measure (C K)) (hlog : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume) :
    (∫⁻ x, ENNReal.ofReal (1/(1+ell K x^2)^2) ∂mu) < ⊤ := by
  have hg : Continuous (fun t : ℝ => (1+t^2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t; positivity
  have hi : Integrable (fun t : ℝ => (1+t^2)⁻¹) (Measure.map (ell K) mu) := by
    rw [hpush]
    exact integrable_inv_one_add_sq.smul_measure (by simp)
  have hj : Integrable (fun x => (1+ell K x^2)⁻¹) mu :=
    (integrable_map_measure hg.aestronglyMeasurable hlog.aemeasurable).mp hi
  have hn : 0 ≤ᵐ[mu] (fun x => (1+ell K x^2)⁻¹) := by
    filter_upwards with x
    positivity
  have hf : (∫⁻ x, ENNReal.ofReal ((1+ell K x^2)⁻¹) ∂mu) < ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hj hn]
    exact ENNReal.ofReal_lt_top
  apply lt_of_le_of_lt _ hf
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith [sq_nonneg (ell K x), sq_nonneg (ell K x^2)]

/-- Quantitative native weighted energy, including a bound on every LEFT
physical tail set. This is a single actual vector, not a nuclear series. -/
theorem genuine_second_correction_tail_energy
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (S : Set (C K))
    (hlog : Measurable (ell K)) (hp : MemLp phi 2 mu)
    (hp1 : MemLp (logMoment K 1 phi) 2 mu)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    (∫⁻ x in S, ENNReal.ofReal
      (‖secondCorrection K mu phi h x‖^2 * (1 + ell K x^2)) ∂mu) ≤
      ENNReal.ofReal (9 * liftCost K mu phi h) *
        ∫⁻ x in S, ENNReal.ofReal (1/(1+ell K x^2)^2) ∂mu := by
  have hq : Measurable (fun x : C K => ENNReal.ofReal (1/(1+ell K x^2)^2)) := by
    fun_prop
  rw [← lintegral_const_mul _ hq]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul (by dsimp [liftCost]; positivity :
    0 ≤ 9 * liftCost K mu phi h)]
  exact ENNReal.ofReal_le_ofReal
    (genuine_second_correction_pointwise K mu phi h x hlog hp hp1 hm he)

#check genuine_second_correction_pointwise
#print axioms genuine_second_correction_pointwise
#check genuine_quartic_profile_finite
#print axioms genuine_quartic_profile_finite
#check genuine_second_correction_tail_energy
#print axioms genuine_second_correction_tail_energy
end
end Round132D

namespace Round133D
open MeasureTheory MasulloGRH Round123D Round129D Round130D Round132D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Actual corrected lift in the genuine quadratic-weight L2 domain. -/
theorem genuine_second_correction_memLp
    (mu : Measure (C K)) [MeasurableMul₂ (C K)] [SFinite mu] [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (hphi : Measurable phi) (hh : Measurable h)
    (hlog : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume)
    (hp : MemLp phi 2 mu) (hp1 : MemLp (logMoment K 1 phi) 2 mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y ^ 2)) mu) :
    MemLp (secondCorrection K mu phi h) 2
      (mu.withDensity (fun x => ENNReal.ofReal (1 + ell K x^2))) := by
  have hmrow : Measurable (fun p : C K × C K => phi p.2 * h (p.2⁻¹*p.1)) :=
    (hphi.comp measurable_snd).mul
      (hh.comp ((measurable_inv.comp measurable_snd).mul measurable_fst))
  have hmconv : StronglyMeasurable (genuineConvolution K mu phi h) :=
    hmrow.stronglyMeasurable.integral_prod_right
  have hm : Measurable (secondCorrection K mu phi h) := by
    unfold secondCorrection
    exact (Complex.measurable_ofReal.comp (by fun_prop)).mul hmconv.measurable
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  refine ⟨(hm.stronglyMeasurable.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [norm_pow, norm_norm]
  have hq : Measurable (fun x : C K => ENNReal.ofReal (1 + ell K x^2)) := by
    fun_prop
  have hd := lintegral_withDensity_eq_lintegral_mul mu hq
    (ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2))
  change (∫⁻ x, ENNReal.ofReal (‖secondCorrection K mu phi h x‖^2)
    ∂mu.withDensity (fun x => ENNReal.ofReal (1 + ell K x^2))) = _ at hd
  rw [hd]
  have heq : (fun x : C K => ENNReal.ofReal (1 + ell K x^2) *
      ENNReal.ofReal (‖secondCorrection K mu phi h x‖^2)) =
    (fun x => ENNReal.ofReal
      (‖secondCorrection K mu phi h x‖^2 * (1 + ell K x^2))) := by
    funext x
    rw [mul_comm, ← ENNReal.ofReal_mul (sq_nonneg _)]
  change (∫⁻ x, ENNReal.ofReal (1 + ell K x^2) *
    ENNReal.ofReal (‖secondCorrection K mu phi h x‖^2) ∂mu) < ⊤
  rw [heq]
  have hb := genuine_second_correction_tail_energy K mu phi h Set.univ hlog hp hp1
    hh.aestronglyMeasurable he
  simp only [Measure.restrict_univ] at hb
  exact lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (genuine_quartic_profile_finite K mu hlog V hpush))

#check genuine_second_correction_memLp
#print axioms genuine_second_correction_memLp
end
end Round133D

namespace Round133D
open MeasureTheory MasulloGRH Round123D Round129D Round130D Round131D Round132D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Uniform input dependence of the actual smoothed-lift cost, with the test
moments explicit. This does not assert spectral decay or family summability. -/
theorem genuine_liftCost_uniform_input
    (mu : Measure (C K)) (phi h : C K → ℂ)
    (hlog : Measurable (ell K)) (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y^2)) mu) :
    liftCost K mu phi h ≤
      (2 * (∫ g, ‖phi g‖^2 ∂mu) + (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu)) *
        (∫ y, ‖h y‖^2 * (1 + ell K y^2) ∂mu) := by
  have hh0 := genuine_weighted_domain_memLp K mu h hm he
  have hh1 := genuine_weighted_log_input_memLp K mu h hlog hm he
  have hi0 := (memLp_two_iff_integrable_sq_norm hh0.aestronglyMeasurable).mp hh0
  have hi1 := (memLp_two_iff_integrable_sq_norm hh1.aestronglyMeasurable).mp hh1
  have hn (y : C K) : ‖logMoment K 1 h y‖^2 = ell K y^2 * ‖h y‖^2 := by
    simp only [logMoment, pow_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
  have heq : (∫ y, ‖h y‖^2 * (1 + ell K y^2) ∂mu) =
      (∫ y, ‖h y‖^2 ∂mu) + (∫ y, ‖logMoment K 1 h y‖^2 ∂mu) := by
    rw [← integral_add hi0 hi1]
    congr 1
    funext y
    rw [hn]
    ring
  have ha : (Real.sqrt (∫ g, ‖phi g‖^2 ∂mu))^2 = (∫ g, ‖phi g‖^2 ∂mu) :=
    Real.sq_sqrt (integral_nonneg (fun g => sq_nonneg _))
  have hb : (Real.sqrt (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu))^2 =
      (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu) :=
    Real.sq_sqrt (integral_nonneg (fun g => sq_nonneg _))
  have hu : (Real.sqrt (∫ y, ‖h y‖^2 ∂mu))^2 = (∫ y, ‖h y‖^2 ∂mu) :=
    Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg _))
  have hv : (Real.sqrt (∫ y, ‖logMoment K 1 h y‖^2 ∂mu))^2 =
      (∫ y, ‖logMoment K 1 h y‖^2 ∂mu) :=
    Real.sq_sqrt (integral_nonneg (fun y => sq_nonneg _))
  have halg (a b u v : ℝ) :
      (a*u)^2 + (a*v+b*u)^2 ≤ (2*a^2+b^2)*(u^2+v^2) := by
    nlinarith [sq_nonneg (a*u-b*v), sq_nonneg (a*v)]
  have hx := halg (Real.sqrt (∫ g, ‖phi g‖^2 ∂mu))
    (Real.sqrt (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu))
    (Real.sqrt (∫ y, ‖h y‖^2 ∂mu))
    (Real.sqrt (∫ y, ‖logMoment K 1 h y‖^2 ∂mu))
  rw [ha, hb, hu, hv] at hx
  simpa only [liftCost, ← Real.sqrt_eq_rpow, heq] using hx

#check genuine_liftCost_uniform_input
#print axioms genuine_liftCost_uniform_input
end
end Round133D

namespace Round133D
open MeasureTheory MasulloGRH Round123D Round129D Round130D Round131D Round132D
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- A derived bound uniform over the input unit ball for the literal
second correction, with the LEFT physical tail retained explicitly. -/
theorem genuine_second_correction_uniform_tail_energy
    (mu : Measure (C K)) [mu.IsMulLeftInvariant] [mu.IsInvInvariant]
    (phi h : C K → ℂ) (S : Set (C K))
    (hlog : Measurable (ell K)) (hp : MemLp phi 2 mu)
    (hp1 : MemLp (logMoment K 1 phi) 2 mu)
    (hm : AEStronglyMeasurable h mu)
    (he : Integrable (fun y => ‖h y‖^2 * (1 + ell K y^2)) mu) :
    (∫⁻ x in S, ENNReal.ofReal
      (‖secondCorrection K mu phi h x‖^2 * (1 + ell K x^2)) ∂mu) ≤
      ENNReal.ofReal
        (9 * (2 * (∫ g, ‖phi g‖^2 ∂mu) + (∫ g, ‖logMoment K 1 phi g‖^2 ∂mu)) *
          (∫ y, ‖h y‖^2 * (1 + ell K y^2) ∂mu)) *
        ∫⁻ x in S, ENNReal.ofReal (1/(1+ell K x^2)^2) ∂mu := by
  apply (genuine_second_correction_tail_energy K mu phi h S hlog hp hp1 hm he).trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have hb := genuine_liftCost_uniform_input K mu phi h hlog hm he
  nlinarith

#check genuine_second_correction_uniform_tail_energy
#print axioms genuine_second_correction_uniform_tail_energy
end
end Round133D
