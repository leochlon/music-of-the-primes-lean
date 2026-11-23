import Mathlib

open scoped NumberField NNReal ENNReal
open MeasureTheory Filter

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
/- Outside finitely many finite places, an actual idele has local norm one. -/
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
/- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]

/- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
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


namespace Round117H
open MasulloGRH MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev C := HeckeIdeleClasses K
abbrev ell := genuineRealClassLog K
end
end Round117H


namespace Round123C
open MasulloGRH Round117H MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Density of the manuscript's genuine weighted Hilbert space. -/
def density (alpha s : ℝ) (x : C K) : ℝ :=
  Real.exp (2*alpha*|ell K x|) * (1+ell K x^2)^(s/2)

def reflected (phi : C K → ℂ) (x : C K) : ℂ := star (phi x⁻¹)

/-- Kernel relative to weighted Haar measure w dmu, without a cutoff. -/
def weightedKernel (alpha s : ℝ) (phi : C K → ℂ) (x y : C K) : ℂ :=
  phi (x*y⁻¹) / (density K alpha s y : ℂ)

theorem density_pos (alpha s : ℝ) (x : C K) : 0 < density K alpha s x := by
  unfold density
  positivity

/-- The precise weight ratio in the genuine weighted adjoint. -/
theorem genuine_weighted_adjoint_kernel (alpha s : ℝ) (phi : C K → ℂ)
    (x y : C K) :
    star (weightedKernel K alpha s phi y x) =
      ((density K alpha s y / density K alpha s x : ℝ) : ℂ) *
        weightedKernel K alpha s (reflected K phi) x y := by
  have hx : (density K alpha s x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (density_pos K alpha s x))
  have hy : (density K alpha s y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (density_pos K alpha s y))
  change (starRingEnd ℂ) (phi (y*x⁻¹) / (density K alpha s x : ℂ)) = _
  rw [map_div₀, Complex.conj_ofReal]
  simp only [weightedKernel, reflected, mul_inv_rev, inv_inv]
  push_cast
  field_simp
  rfl


/-- The genuine weighted pairing, with its Fubini premise visible. It is
not a nuclearity assumption or a completed bounded-operator construction. -/
theorem genuine_weighted_adjoint_pairing
    (nu : Measure (C K)) [SFinite nu] (alpha s : ℝ)
    (phi f h : C K → ℂ)
    (hfub : Integrable (fun p : C K × C K =>
      star (f p.1) * (weightedKernel K alpha s phi p.1 p.2 * h p.2))
        (nu.prod nu)) :
    (∫ x, star (f x) * (∫ y, weightedKernel K alpha s phi x y * h y ∂nu) ∂nu) =
    ∫ y, star (∫ x,
      (((density K alpha s x / density K alpha s y : ℝ) : ℂ) *
        weightedKernel K alpha s (reflected K phi) y x) * f x ∂nu) * h y ∂nu := by
  calc
    _ = ∫ x, ∫ y, star (f x) * (weightedKernel K alpha s phi x y * h y) ∂nu ∂nu := by
      simp only [integral_const_mul]
    _ = ∫ y, ∫ x, star (f x) * (weightedKernel K alpha s phi x y * h y) ∂nu ∂nu :=
      integral_integral_swap hfub
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      have hc (r : C K → ℂ) : star (∫ x, r x ∂nu) = ∫ x, star (r x) ∂nu :=
        integral_conj.symm
      rw [hc, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      rw [← genuine_weighted_adjoint_kernel K alpha s phi y x]
      simp only [star_mul, star_star]
      ring


/-- Actual weighted Haar realization. Identification with the manuscript's
completion is a remaining obligation, not a definition of the target. -/
def weightedMeasure (mu : Measure (C K)) (alpha s : ℝ) : Measure (C K) :=
  mu.withDensity (fun x => ENNReal.ofReal (density K alpha s x))

/-- Once the two genuine integral actions have bounded realizations, their
Hilbert adjoint is forced by the actual weight ratio. This identifies the
operator required when transferring leading projected nuclear costs. -/
theorem genuine_weighted_bounded_adjoint
    (mu : Measure (C K)) (alpha s : ℝ)
    [SFinite (weightedMeasure K mu alpha s)] (phi : C K → ℂ)
    (A B : Lp ℂ 2 (weightedMeasure K mu alpha s) →L[ℂ]
      Lp ℂ 2 (weightedMeasure K mu alpha s))
    (hA : ∀ h, ∀ᵐ x ∂(weightedMeasure K mu alpha s),
      A h x = ∫ y, weightedKernel K alpha s phi x y * h y
        ∂(weightedMeasure K mu alpha s))
    (hB : ∀ f, ∀ᵐ y ∂(weightedMeasure K mu alpha s),
      B f y = ∫ x,
        (((density K alpha s x / density K alpha s y : ℝ) : ℂ) *
          weightedKernel K alpha s (reflected K phi) y x) * f x
            ∂(weightedMeasure K mu alpha s))
    (hfub : ∀ f h : Lp ℂ 2 (weightedMeasure K mu alpha s),
      Integrable (fun p : C K × C K =>
        star (f p.1) * (weightedKernel K alpha s phi p.1 p.2 * h p.2))
          ((weightedMeasure K mu alpha s).prod (weightedMeasure K mu alpha s))) :
    ContinuousLinearMap.adjoint A = B := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro h
  rw [ContinuousLinearMap.adjoint_inner_left, L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, star (f x) * (∫ y, weightedKernel K alpha s phi x y * h y
        ∂(weightedMeasure K mu alpha s)) ∂(weightedMeasure K mu alpha s) := by
      apply integral_congr_ae
      filter_upwards [hA h] with x hx
      change (A h) x * star (f x) = _
      rw [hx, mul_comm]
    _ = _ := genuine_weighted_adjoint_pairing K (weightedMeasure K mu alpha s)
      alpha s phi f h (hfub f h)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hB f] with y hy
      change star _ * h y = h y * star ((B f) y)
      rw [hy, mul_comm]

#check genuine_weighted_adjoint_kernel
#print axioms genuine_weighted_adjoint_kernel
#check genuine_weighted_adjoint_pairing
#print axioms genuine_weighted_adjoint_pairing
#check genuine_weighted_bounded_adjoint
#print axioms genuine_weighted_bounded_adjoint
end
end Round123C

namespace Round124C
open MasulloGRH Round117H Round123C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem density_measurable (alpha s : ℝ) (hell : Measurable (ell K)) :
    Measurable (density K alpha s) := by
  unfold density
  fun_prop

/-- The weighted-measure kernel acts by the actual Haar convolution. -/
theorem genuine_weighted_convolution_action
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (phi f : C K → ℂ) (x : C K) :
    (∫ y, weightedKernel K alpha s phi x y * f y
      ∂(weightedMeasure K mu alpha s)) =
      ∫ y, phi (x*y⁻¹) * f y ∂mu := by
  unfold weightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((density_measurable K alpha s hell).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with y
  rw [ENNReal.toReal_ofReal (le_of_lt (density_pos K alpha s y))]
  change (density K alpha s y : ℂ) *
    (phi (x*y⁻¹) / (density K alpha s y : ℂ) * f y) = _
  have hy : (density K alpha s y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (density_pos K alpha s y))
  field_simp

/-- The actual adjoint action keeps its weight ratio, for every alpha,s. -/
theorem genuine_weighted_adjoint_action
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (phi f : C K → ℂ) (y : C K) :
    (∫ x, (((density K alpha s x / density K alpha s y : ℝ) : ℂ) *
      weightedKernel K alpha s (reflected K phi) y x) * f x
        ∂(weightedMeasure K mu alpha s)) =
    (density K alpha s y : ℂ)⁻¹ *
      ∫ x, reflected K phi (y*x⁻¹) * ((density K alpha s x : ℂ) * f x) ∂mu := by
  unfold weightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((density_measurable K alpha s hell).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (le_of_lt (density_pos K alpha s x))]
  simp only [weightedKernel, Complex.real_smul, Complex.ofReal_div]
  have hx : (density K alpha s x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (density_pos K alpha s x))
  have hy : (density K alpha s y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (density_pos K alpha s y))
  field_simp

/-- Exact energy transport for the actual idele-class density. -/
theorem genuine_weighted_energy_identity
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (f : C K → ℂ) :
    (∫ x, ‖f x‖^2 ∂(weightedMeasure K mu alpha s)) =
      ∫ x, ‖(Real.sqrt (density K alpha s x) : ℂ) * f x‖^2 ∂mu := by
  unfold weightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((density_measurable K alpha s hell).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (le_of_lt (density_pos K alpha s x))]
  simp only [smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (le_of_lt (density_pos K alpha s x))]

#check genuine_weighted_convolution_action
#print axioms genuine_weighted_convolution_action
#check genuine_weighted_adjoint_action
#print axioms genuine_weighted_adjoint_action
#check genuine_weighted_energy_identity
#print axioms genuine_weighted_energy_identity
end
end Round124C

namespace Round124C
open MasulloGRH Round117H Round123C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Finite energy is transported, not inferred from an equality of totalized
integrals. This is the direct finite-norm bridge for genuine rank-one factors. -/
theorem genuine_weighted_energy_integrable_iff
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (f : C K → ℂ) :
    Integrable (fun x => ‖f x‖^2) (weightedMeasure K mu alpha s) ↔
      Integrable (fun x => ‖(Real.sqrt (density K alpha s x) : ℂ) * f x‖^2) mu := by
  unfold weightedMeasure
  rw [integrable_withDensity_iff
    ((density_measurable K alpha s hell).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have heq : (fun x => ‖f x‖^2 * (ENNReal.ofReal (density K alpha s x)).toReal) =
      (fun x => ‖(Real.sqrt (density K alpha s x) : ℂ) * f x‖^2) := by
    funext x
    rw [ENNReal.toReal_ofReal (le_of_lt (density_pos K alpha s x))]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (le_of_lt (density_pos K alpha s x))]
    ring
  rw [heq]

/-- On genuine measurable profiles, multiplication by sqrt(w) preserves and
reflects L2 membership, uniformly in all real strip/degree parameters. -/
theorem genuine_weighted_memLp_iff
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (f : C K → ℂ) (hf : Measurable f) :
    MemLp f 2 (weightedMeasure K mu alpha s) ↔
      MemLp (fun x => (Real.sqrt (density K alpha s x) : ℂ) * f x) 2 mu := by
  have ht : Measurable (fun x => (Real.sqrt (density K alpha s x) : ℂ) * f x) := by
    have hw := density_measurable K alpha s hell
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable,
    memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable]
  exact genuine_weighted_energy_integrable_iff K mu alpha s hell f

#check genuine_weighted_energy_integrable_iff
#print axioms genuine_weighted_energy_integrable_iff
#check genuine_weighted_memLp_iff
#print axioms genuine_weighted_memLp_iff
end
end Round124C

namespace Round124C
open MasulloGRH Round117H Round123C MeasureTheory
noncomputable section
/-- Reused norm identity from the exact checked Round98F component. -/
theorem toLp_energy {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (g : X → ℂ) (hg : MemLp g 2 mu) :
    ‖hg.toLp g‖^2 = ∫ x, ‖g x‖^2 ∂mu := by
  let v := hg.toLp g
  have hi := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hin : Integrable (fun x => inner ℂ (v x) (v x)) mu := by
    apply hi.ofReal.congr
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  change ‖v‖^2 = _
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re hin]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Exact norm transport for each genuine finite-energy rank-one output. -/
theorem genuine_weighted_profile_norm
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (f : C K → ℂ) (hm : Measurable f)
    (hf : MemLp f 2 (weightedMeasure K mu alpha s)) :
    ‖hf.toLp f‖ =
      ‖((genuine_weighted_memLp_iff K mu alpha s hell f hm).mp hf).toLp
        (fun x => (Real.sqrt (density K alpha s x) : ℂ) * f x)‖ := by
  have he := genuine_weighted_energy_identity K mu alpha s hell f
  rw [← toLp_energy (weightedMeasure K mu alpha s) f hf,
    ← toLp_energy mu _ ((genuine_weighted_memLp_iff K mu alpha s hell f hm).mp hf)] at he
  nlinarith [norm_nonneg (hf.toLp f),
    norm_nonneg (((genuine_weighted_memLp_iff K mu alpha s hell f hm).mp hf).toLp
      (fun x => (Real.sqrt (density K alpha s x) : ℂ) * f x))]

#check genuine_weighted_profile_norm
#print axioms genuine_weighted_profile_norm
end
end Round124C

namespace Round125C
open MasulloGRH Round117H Round123C Round124C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Exact reciprocal-weight energy for a genuine coefficient profile. -/
theorem coefficient_density_identity (alpha s : ℝ) (eta : C K → ℂ) (x : C K) :
    density K alpha s x * ‖eta x / (density K alpha s x : ℂ)‖^2 =
      ‖eta x‖^2 / density K alpha s x := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (density_pos K alpha s x), div_pow]
  field_simp

/-- Construct the actual Haar coefficient functional with its exact dual norm.
Finite reciprocal-weight energy remains explicit; no lift estimate is assumed. -/
theorem genuine_weighted_coefficient_functional
    (mu : Measure (C K)) (alpha s : ℝ) (hell : Measurable (ell K))
    (eta : C K → ℂ) (heta : Measurable eta)
    (he : Integrable (fun x => ‖eta x‖^2 / density K alpha s x) mu) :
    ∃ L : Lp ℂ 2 (weightedMeasure K mu alpha s) →L[ℂ] ℂ,
      (∀ F, L F = ∫ x, eta x * F x ∂mu) ∧
      ‖L‖^2 = ∫ x, ‖eta x‖^2 / density K alpha s x ∂mu := by
  let g : C K → ℂ := fun x => eta x / (density K alpha s x : ℂ)
  have hw := density_measurable K alpha s hell
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hpoint (x : C K) :
      ‖g x‖^2 * (ENNReal.ofReal (density K alpha s x)).toReal =
        ‖eta x‖^2 / density K alpha s x := by
    rw [ENNReal.toReal_ofReal (le_of_lt (density_pos K alpha s x)), mul_comm]
    exact coefficient_density_identity K alpha s eta x
  have hi : Integrable (fun x => ‖g x‖^2) (weightedMeasure K mu alpha s) := by
    unfold weightedMeasure
    rw [integrable_withDensity_iff hw.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simpa only [hpoint] using he
  have hgs : MemLp (fun x => star (g x)) 2 (weightedMeasure K mu alpha s) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable.star).mpr
      (by simpa using hi)
  let v := hgs.toLp (fun x => star (g x))
  refine ⟨innerSL ℂ v, ?_, ?_⟩
  · intro F
    rw [innerSL_apply_apply, L2.inner_def]
    calc
      _ = ∫ x, g x * F x ∂(weightedMeasure K mu alpha s) := by
        apply integral_congr_ae
        filter_upwards [hgs.coeFn_toLp] with x hx
        change inner ℂ ((hgs.toLp (fun x => star (g x))) x) (F x) = _
        rw [hx]
        change F x * star (star (g x)) = _
        rw [star_star, mul_comm]
      _ = _ := by
        unfold weightedMeasure
        rw [integral_withDensity_eq_integral_toReal_smul₀
          hw.ennreal_ofReal.aemeasurable
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
        apply integral_congr_ae
        filter_upwards with x
        rw [ENNReal.toReal_ofReal (le_of_lt (density_pos K alpha s x))]
        change (density K alpha s x : ℂ) *
          (eta x / (density K alpha s x : ℂ) * F x) = _
        have hn : (density K alpha s x : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (ne_of_gt (density_pos K alpha s x))
        field_simp
  · rw [innerSL_apply_norm]
    calc
      ‖v‖^2 = ∫ x, ‖g x‖^2 ∂(weightedMeasure K mu alpha s) := by
        simpa [v] using toLp_energy (weightedMeasure K mu alpha s)
          (fun x => star (g x)) hgs
      _ = _ := by
        unfold weightedMeasure
        rw [integral_withDensity_eq_integral_toReal_smul₀
          hw.ennreal_ofReal.aemeasurable
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
        apply integral_congr_ae
        filter_upwards with x
        simpa only [smul_eq_mul, mul_comm] using hpoint x

#check genuine_weighted_coefficient_functional
#print axioms genuine_weighted_coefficient_functional
end
end Round125C


/- Reused exact scalar estimates from the frozen F90 source. -/
namespace Round89F
theorem stripBoundaryDensity_integrable (α b : ℝ) (hstrip : |b| ≤ α)
    (m d : ℕ) (hmd : m < d) :
    Integrable (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
  have hcont : Continuous (fun t : ℝ => (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  apply integrable_inv_one_add_sq.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hq : 0 < 1+t^2 := by positivity
  have hq1 : 1 ≤ 1+t^2 := by nlinarith [sq_nonneg t]
  have hrew : (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d) =
      (Real.exp (2*b*t-2*α*|t|) * |t|^(2*m)) / (1+t^2)^d := by
    rw [Real.exp_sub, show 2*b*t = b*t+b*t by ring, Real.exp_add]
    rw [show 2*m = m*2 by omega, pow_mul]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hrew, ← one_div]
  have hb : b*t ≤ |b| * |t| := by simpa [abs_mul] using le_abs_self (b*t)
  have hbt := mul_le_mul_of_nonneg_right hstrip (abs_nonneg t)
  have he : Real.exp (2*b*t-2*α*|t|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hp : |t|^(2*m) ≤ (1+t^2)^m := by
    rw [pow_mul, sq_abs]
    exact pow_le_pow_left₀ (sq_nonneg t) (by linarith) m
  apply (div_le_div_iff₀ (pow_pos hq d) hq).mpr
  calc
    _ ≤ (1+t^2)^m * (1+t^2) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_of_le_one_left (by positivity) he).trans hp) (le_of_lt hq)
    _ = (1+t^2)^(m+1) := (pow_succ _ _).symm
    _ ≤ 1 * (1+t^2)^d := by
      simpa only [one_mul] using (pow_le_pow_right₀ hq1 (show m+1 ≤ d by omega))

/-- Quantitative boundary coefficient cost, uniform in every m<d. -/
theorem boundary_dual_energy_le (α b : ℝ) (hstrip : |b| ≤ α)
    (m d : ℕ) (hmd : m < d) :
    (∫ t : ℝ, (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d)) ≤
      ∫ t : ℝ, (1+t^2)⁻¹ := by
  apply integral_mono (stripBoundaryDensity_integrable α b hstrip m d hmd)
    integrable_inv_one_add_sq
  intro t
  dsimp only
  have hq : 0 < 1+t^2 := by positivity
  have hq1 : 1 ≤ 1+t^2 := by nlinarith [sq_nonneg t]
  have hrew : (Real.exp (b*t) * |t|^m)^2 /
      (Real.exp (2*α*|t|) * (1+t^2)^d) =
      (Real.exp (2*b*t-2*α*|t|) * |t|^(2*m)) / (1+t^2)^d := by
    rw [Real.exp_sub, show 2*b*t = b*t+b*t by ring, Real.exp_add]
    rw [show 2*m = m*2 by omega, pow_mul]
    field_simp
  rw [hrew, ← one_div]
  have hb : b*t ≤ |b| * |t| := by simpa [abs_mul] using le_abs_self (b*t)
  have hbt := mul_le_mul_of_nonneg_right hstrip (abs_nonneg t)
  have he : Real.exp (2*b*t-2*α*|t|) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hp : |t|^(2*m) ≤ (1+t^2)^m := by
    rw [pow_mul, sq_abs]
    exact pow_le_pow_left₀ (sq_nonneg t) (by linarith) m
  apply (div_le_div_iff₀ (pow_pos hq d) hq).mpr
  calc
    _ ≤ (1+t^2)^m * (1+t^2) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_of_le_one_left (by positivity) he).trans hp) (le_of_lt hq)
    _ = (1+t^2)^(m+1) := (pow_succ _ _).symm
    _ ≤ 1 * (1+t^2)^d := by
      simpa only [one_mul] using (pow_le_pow_right₀ hq1 (show m+1 ≤ d by omega))
end Round89F

namespace Round125C
open MasulloGRH Round117H Round123C Round124C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def genuineJet (chi : C K →* Circle) (z : ℂ) (m : ℕ) (x : C K) : ℂ :=
  (chi x : ℂ) * Complex.exp (z * (ell K x : ℂ)) * (ell K x : ℂ)^m

/-- A derived coefficient dual norm bound on the genuine idele classes.
The finite-energy hypothesis of the preceding theorem is discharged here. -/
theorem genuine_jet_coefficient_bound
    (mu : Measure (C K)) (hell : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume)
    (alpha : ℝ) (d : ℕ) (chi : C K →* Circle)
    (hchi : Measurable (fun x => (chi x : ℂ)))
    (z : ℂ) (m : ℕ) (hstrip : |z.re| ≤ alpha) (hmd : m < d) :
    ∃ L : Lp ℂ 2 (weightedMeasure K mu alpha (2*(d:ℝ))) →L[ℂ] ℂ,
      (∀ F, L F = ∫ x, genuineJet K chi z m x * F x ∂mu) ∧
      ‖L‖^2 ≤ (V : ℝ) * ∫ t : ℝ, (1+t^2)⁻¹ := by
  let g : ℝ → ℝ := fun t => (Real.exp (z.re*t) * |t|^m)^2 /
    (Real.exp (2*alpha*|t|) * (1+t^2)^d)
  have hg : Continuous g := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro t; positivity
  have heq (x : C K) :
      ‖genuineJet K chi z m x‖^2 / density K alpha (2*(d:ℝ)) x = g (ell K x) := by
    have hd : (2*(d:ℝ))/2 = d := by ring
    simp [genuineJet, density, hd, Real.rpow_natCast, g,
      norm_pow, Complex.norm_exp, Complex.mul_re, Complex.norm_real, Real.norm_eq_abs]
  have hi : Integrable g (Measure.map (ell K) mu) := by
    rw [hpush]
    exact (Round89F.stripBoundaryDensity_integrable alpha z.re hstrip m d hmd).smul_measure
      (by simp)
  have he : Integrable
      (fun x => ‖genuineJet K chi z m x‖^2 / density K alpha (2*(d:ℝ)) x) mu := by
    simp_rw [heq]
    exact (integrable_map_measure hg.aestronglyMeasurable hell.aemeasurable).mp hi
  have hm : Measurable (genuineJet K chi z m) := by
    unfold genuineJet
    fun_prop
  obtain ⟨L, hL, hn⟩ := genuine_weighted_coefficient_functional K mu alpha (2*(d:ℝ))
    hell (genuineJet K chi z m) hm he
  refine ⟨L, hL, ?_⟩
  rw [hn]
  simp_rw [heq]
  calc
    _ = ∫ t, g t ∂Measure.map (ell K) mu :=
      (integral_map hell.aemeasurable hg.aestronglyMeasurable).symm
    _ = (V : ℝ) * ∫ t : ℝ, g t := by
      rw [hpush, integral_smul_measure]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Round89F.boundary_dual_energy_le alpha z.re hstrip m d hmd) V.property

#check genuine_jet_coefficient_bound
#print axioms genuine_jet_coefficient_bound
end
end Round125C

/- Reused exact H89 interior coefficient estimates. -/
namespace NuclearBoundH88
noncomputable def jetDensity (alpha b s : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (2 * b * u - 2 * alpha * |u|) * u ^ (2 * m) /
    (1 + u ^ 2) ^ (s / 2)

theorem jetDensity_continuous (alpha b s : ℝ) (m : ℕ) (hs : 0 ≤ s) :
    Continuous (jetDensity alpha b s m) := by
  unfold jetDensity
  apply Continuous.div
  · fun_prop
  · fun_prop (disch := positivity)
  · intro u
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)

theorem jetDensity_interior_upper (alpha b s delta : ℝ) (m : ℕ)
    (hs : 0 ≤ s) (hmargin : |b| + delta ≤ alpha) (u : ℝ) :
    jetDensity alpha b s m u ≤
      Real.exp (-2 * delta * |u|) * |u| ^ (2 * m) := by
  have hbu : b * u ≤ |b| * |u| := by
    simpa only [abs_mul] using le_abs_self (b * u)
  have hm : 0 ≤ (alpha - |b| - delta) * |u| :=
    mul_nonneg (by linarith) (abs_nonneg u)
  have he : 2 * b * u - 2 * alpha * |u| ≤ -2 * delta * |u| := by
    nlinarith
  have hp : u ^ (2 * m) = |u| ^ (2 * m) := by
    simp [pow_mul, sq_abs]
  have hd : (1 : ℝ) ≤ (1 + u ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg u]) (by positivity)
  unfold jetDensity
  rw [hp]
  calc
    _ ≤ Real.exp (2 * b * u - 2 * alpha * |u|) * |u| ^ (2 * m) :=
      div_le_self (by positivity) hd
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (by positivity)


end NuclearBoundH88
namespace NuclearBoundH89
open MeasureTheory
open NuclearBoundH88

/-- Explicit integral of the coefficient majorant, without assuming integrability. -/
theorem jetMajorant_integrable_integral (r : ℝ) (hr : 0 < r) (n : ℕ) :
    Integrable (fun u : ℝ => |u| ^ n * Real.exp (-(r * |u|))) ∧
    (∫ u : ℝ, |u| ^ n * Real.exp (-(r * |u|))) =
      2 * (n.factorial : ℝ) / r ^ (n + 1) := by
  let g : ℝ → ℝ := fun u => |u| ^ n * Real.exp (-(r * |u|))
  have hh : (∫ u in Set.Ioi (0 : ℝ), g u) =
      (n.factorial : ℝ) / r ^ (n + 1) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (n : ℝ) + 1) (r := r) (by positivity) hr
    simp only [add_sub_cancel_right, Real.rpow_natCast,
      Real.Gamma_nat_eq_factorial] at h
    have hc : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
    rw [hc, Real.rpow_natCast] at h
    calc
      _ = ∫ u in Set.Ioi (0 : ℝ), u ^ n * Real.exp (-(r * u)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        simp only [g, abs_of_pos (Set.mem_Ioi.mp hu)]
      _ = _ := by rw [h, div_pow]; ring
  have hneg : (∫ u in Set.Iic (0 : ℝ), g u) =
      (n.factorial : ℝ) / r ^ (n + 1) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) g
    simp only [neg_zero] at h
    have he : (fun u => g (-u)) = g := by funext u; simp [g]
    rw [he] at h
    exact h.symm.trans hh
  have hp : 0 < (n.factorial : ℝ) / r ^ (n + 1) := by positivity
  have hi1 : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
    by_contra hn
    rw [integral_undef hn] at hh
    linarith
  have hi2 : IntegrableOn g (Set.Iic (0 : ℝ)) := by
    by_contra hn
    rw [integral_undef hn] at hneg
    linarith
  have hun : Set.Ioi (0 : ℝ) ∪ Set.Iic 0 = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioi, Set.mem_Iic, Set.mem_univ, iff_true]
    exact lt_or_ge 0 x
  have hi : Integrable g := by
    have hu := integrableOn_union.mpr ⟨hi1, hi2⟩
    rw [hun] at hu
    exact integrableOn_univ.mp hu
  refine ⟨hi, ?_⟩
  change (∫ u, g u) = _
  have hsum := integral_add_compl (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hi
  rw [Set.compl_Ioi, hh, hneg] at hsum
  rw [← hsum]
  ring

/-- The scalar factor of the actual coefficient norm formula. This is not
an authentic global operator bound; transport and lifted summability remain. -/
theorem jetDensity_integrable_bound (alpha b s delta : ℝ) (m : ℕ)
    (hs : 0 ≤ s) (hd : 0 < delta) (hmargin : |b| + delta ≤ alpha) :
    Integrable (jetDensity alpha b s m) ∧
    (∫ u : ℝ, jetDensity alpha b s m u) ≤
      2 * ((2 * m).factorial : ℝ) / (2 * delta) ^ (2 * m + 1) := by
  obtain ⟨hi, heq⟩ := jetMajorant_integrable_integral (2 * delta) (by positivity) (2 * m)
  have hpoint : ∀ u : ℝ, jetDensity alpha b s m u ≤
      |u| ^ (2 * m) * Real.exp (-(2 * delta * |u|)) := by
    intro u
    convert jetDensity_interior_upper alpha b s delta m hs hmargin u using 1
    ring_nf
  have hnonneg : ∀ u : ℝ, 0 ≤ jetDensity alpha b s m u := by
    intro u
    unfold jetDensity
    have hpow : 0 ≤ u ^ (2 * m) := by rw [pow_mul]; positivity
    exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hpow)
      (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have hj : Integrable (jetDensity alpha b s m) := hi.mono'
    (jetDensity_continuous alpha b s m hs).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg u)]
      exact hpoint u))
  exact ⟨hj, (integral_mono hj hi hpoint).trans_eq heq⟩

#check jetMajorant_integrable_integral
#print axioms jetMajorant_integrable_integral
#check jetDensity_integrable_bound
#print axioms jetDensity_integrable_bound
end NuclearBoundH89

namespace Round125C
open MasulloGRH Round117H Round123C Round124C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Arbitrary interior jet orders have explicit factorial coefficient cost.
This supplies no uniform bound as the jet order grows or the margin shrinks. -/
theorem genuine_interior_jet_coefficient_bound
    (mu : Measure (C K)) (hell : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume)
    (alpha s delta : ℝ) (hs : 0 ≤ s) (hd : 0 < delta)
    (chi : C K →* Circle) (hchi : Measurable (fun x => (chi x : ℂ)))
    (z : ℂ) (m : ℕ) (hmargin : |z.re| + delta ≤ alpha) :
    ∃ L : Lp ℂ 2 (weightedMeasure K mu alpha s) →L[ℂ] ℂ,
      (∀ F, L F = ∫ x, genuineJet K chi z m x * F x ∂mu) ∧
      ‖L‖^2 ≤ (V : ℝ) *
        (2 * ((2*m).factorial : ℝ) / (2*delta)^(2*m+1)) := by
  let g := NuclearBoundH88.jetDensity alpha z.re s m
  have hg : Continuous g := NuclearBoundH88.jetDensity_continuous alpha z.re s m hs
  have heq (x : C K) :
      ‖genuineJet K chi z m x‖^2 / density K alpha s x = g (ell K x) := by
    have hex : (Real.exp (z.re * ell K x))^2 = Real.exp (2*z.re*ell K x) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hp : (|ell K x| ^ m)^2 = (ell K x)^(2*m) := by
      rw [← pow_mul, Nat.mul_comm m 2, pow_mul, sq_abs, pow_mul]
    simp [genuineJet, density, norm_pow, Complex.norm_exp, Complex.mul_re,
      Complex.norm_real, Real.norm_eq_abs, g, NuclearBoundH88.jetDensity,
      mul_pow, hex, Real.exp_sub, hp]
    ring
  obtain ⟨hgi, hbound⟩ := NuclearBoundH89.jetDensity_integrable_bound
    alpha z.re s delta m hs hd hmargin
  have hi : Integrable g (Measure.map (ell K) mu) := by
    rw [hpush]
    exact hgi.smul_measure (by simp)
  have he : Integrable
      (fun x => ‖genuineJet K chi z m x‖^2 / density K alpha s x) mu := by
    simp_rw [heq]
    exact (integrable_map_measure hg.aestronglyMeasurable hell.aemeasurable).mp hi
  have hm : Measurable (genuineJet K chi z m) := by
    unfold genuineJet
    fun_prop
  obtain ⟨L, hL, hn⟩ := genuine_weighted_coefficient_functional K mu alpha s
    hell (genuineJet K chi z m) hm he
  refine ⟨L, hL, ?_⟩
  rw [hn]
  simp_rw [heq]
  calc
    _ = ∫ t, g t ∂Measure.map (ell K) mu :=
      (integral_map hell.aemeasurable hg.aestronglyMeasurable).symm
    _ = (V : ℝ) * ∫ t : ℝ, g t := by
      rw [hpush, integral_smul_measure]
      simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound V.property

#check genuine_interior_jet_coefficient_bound
#print axioms genuine_interior_jet_coefficient_bound
end
end Round125C

/- Reused frozen D89 coefficient-frequency estimates. -/

/-! Round 89 D. Direct obstruction to the proposed lift-norm majorant.
The actual global nuclear bound remains INCOMPLETE. No nuclearity or
summability assumption is used in these necessary lift estimates. -/
namespace Round89D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Every actual biorthogonal lift must obey this lower bound. Thus bounding
convolution only by its operator norm cannot provide a summable majorant. -/
theorem biorthogonal_lift_cost (eta : E →L[ℂ] ℂ) (v : E)
    (h : eta v = 1) : (1 : ℝ) ≤ ‖v‖ * ‖eta‖ := by
  have hn := eta.le_opNorm v
  rw [h, norm_one] at hn
  simpa only [mul_comm] using hn

/-- Close coefficient functionals force large actual primal lifts.
Apply to canonical orthogonal lifts of distinct spectral basis vectors. -/
theorem lift_separation_cost (eta theta : E →L[ℂ] ℂ) (v : E)
    (he : eta v = 1) (ht : theta v = 0) :
    (1 : ℝ) ≤ ‖eta - theta‖ * ‖v‖ := by
  have h := (eta - theta).le_opNorm v
  simpa only [ContinuousLinearMap.sub_apply, he, ht, sub_zero, norm_one] using h

#check biorthogonal_lift_cost
#print axioms biorthogonal_lift_cost
#check lift_separation_cost
#print axioms lift_separation_cost
end Round89D

namespace Round89D

/-- A global Lipschitz majorant for the genuine oscillatory coefficient. -/
theorem phase_sub_one_bound (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ 2 * |x| := by
  by_cases h : |x| ≤ 1
  · have hx : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by
      simpa using h
    simpa using Complex.norm_exp_sub_one_le hx
  · calc
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [Complex.norm_exp_ofReal_mul_I]; norm_num
      _ ≤ _ := by linarith

/-- Exact coefficient-frequency estimate in logarithmic idele coordinates.
No claim about which frequencies are genuine spectral labels is made. -/
theorem phase_difference_bound (t z r : ℝ) :
    ‖Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((z * r : ℝ) : ℂ) * Complex.I)‖ ≤
      2 * |t - z| * |r| := by
  have he : Complex.exp (((t * r : ℝ) : ℂ) * Complex.I) -
      Complex.exp (((z * r : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((z * r : ℝ) : ℂ) * Complex.I) *
        (Complex.exp ((((t - z) * r : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [abs_mul, mul_assoc] using phase_sub_one_bound ((t - z) * r)

noncomputable def coefficientProfile (b t : ℝ) (m : ℕ) (r : ℝ) : ℂ :=
  ((Real.exp (b * r) * r ^ m : ℝ) : ℂ) *
    Complex.exp (((t * r : ℝ) : ℂ) * Complex.I)

/-- Control of the exact coefficient difference by the next jet density.
Multiplication by any common unitary character preserves this inequality. -/
theorem coefficientProfile_difference_bound (b t z r : ℝ) (m : ℕ) :
    ‖coefficientProfile b t m r - coefficientProfile b z m r‖ ≤
      2 * |t - z| * (Real.exp (b * r) * |r| ^ (m + 1)) := by
  unfold coefficientProfile
  rw [← mul_sub, norm_mul]
  have hn : ‖((Real.exp (b * r) * r ^ m : ℝ) : ℂ)‖ =
      Real.exp (b * r) * |r| ^ m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_pow]
  rw [hn]
  calc
    _ ≤ (Real.exp (b * r) * |r| ^ m) * (2 * |t - z| * |r|) :=
      mul_le_mul_of_nonneg_left (phase_difference_bound t z r) (by positivity)
    _ = _ := by rw [pow_succ]; ring

#check phase_difference_bound
#print axioms phase_difference_bound
#check coefficientProfile_difference_bound
#print axioms coefficientProfile_difference_bound
end Round89D

namespace Round89D

/-- The exact manuscript weight in logarithmic coordinates, for real s. -/
noncomputable def stripWeight (alpha s r : ℝ) : ℝ :=
  Real.exp (2 * alpha * |r|) * (1 + r ^ 2) ^ (s / 2)

theorem stripWeight_pos (alpha s r : ℝ) : 0 < stripWeight alpha s r := by
  unfold stripWeight
  positivity

/-- Direct upper bound on the dual coefficient difference energy.
The jet increment and the frequency separation are explicit. -/
theorem coefficient_difference_energy (alpha s b t z r : ℝ) (m : ℕ) :
    ‖coefficientProfile b t m r - coefficientProfile b z m r‖ ^ 2 /
      stripWeight alpha s r ≤
    (4 * |t - z| ^ 2) *
      ((Real.exp (b * r) * |r| ^ (m + 1)) ^ 2 / stripWeight alpha s r) := by
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (coefficientProfile_difference_bound b t z r m) 2
  have h' := div_le_div_of_nonneg_right h (le_of_lt (stripWeight_pos alpha s r))
  calc
    _ ≤ _ := h'
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Required conditioning in the actual convolved rank-one term.
The hypotheses are coefficient action identities, not a norm bound. -/
theorem convolved_lift_separation_cost (A : E →L[ℂ] E)
    (eta theta : E →L[ℂ] ℂ) (v : E) (lambda : ℂ)
    (he : eta (A v) = lambda) (ht : theta (A v) = 0) :
    ‖lambda‖ * ‖eta‖ ≤ (‖A v‖ * ‖eta‖) * ‖eta - theta‖ := by
  have h := (eta - theta).le_opNorm (A v)
  simp only [ContinuousLinearMap.sub_apply, he, ht, sub_zero] at h
  have h' := mul_le_mul_of_nonneg_right h (norm_nonneg eta)
  calc
    _ ≤ _ := h'
    _ = _ := by ring

#check coefficient_difference_energy
#print axioms coefficient_difference_energy
#check convolved_lift_separation_cost
#print axioms convolved_lift_separation_cost
end Round89D

namespace Round89D
open MeasureTheory

/-- Integrated control of this specific coefficient-difference density.
The next-jet moment is an explicit domain hypothesis, not a uniform bound. -/
theorem coefficient_difference_integral (mu : Measure ℝ)
    (alpha s b t z : ℝ) (m : ℕ)
    (hm : AEStronglyMeasurable (fun r =>
      ‖coefficientProfile b t m r - coefficientProfile b z m r‖ ^ 2 /
        stripWeight alpha s r) mu)
    (hj : Integrable (fun r =>
      (Real.exp (b * r) * |r| ^ (m + 1)) ^ 2 / stripWeight alpha s r) mu) :
    Integrable (fun r =>
      ‖coefficientProfile b t m r - coefficientProfile b z m r‖ ^ 2 /
        stripWeight alpha s r) mu ∧
    (∫ r, ‖coefficientProfile b t m r - coefficientProfile b z m r‖ ^ 2 /
      stripWeight alpha s r ∂mu) ≤
    (4 * |t-z| ^ 2) * (∫ r,
      (Real.exp (b*r) * |r| ^ (m+1)) ^ 2 / stripWeight alpha s r ∂mu) := by
  have hmajor := hj.const_mul (4 * |t-z| ^ 2)
  have hi : Integrable (fun r =>
      ‖coefficientProfile b t m r - coefficientProfile b z m r‖ ^ 2 /
        stripWeight alpha s r) mu := by
    apply hmajor.mono' hm
    filter_upwards [] with r
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _)
      (le_of_lt (stripWeight_pos alpha s r)))]
    exact coefficient_difference_energy alpha s b t z r m
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hmajor (fun r =>
    coefficient_difference_energy alpha s b t z r m)
  simpa only [integral_const_mul] using hh

#check coefficient_difference_integral
#print axioms coefficient_difference_integral
end Round89D

namespace Round126C
open MasulloGRH Round117H Round123C Round124C Round125C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Frequency conditioning for actual Haar coefficient functionals.
The required next-jet energy is derived, rather than assumed. -/
theorem genuine_coefficient_frequency_bound
    (mu : Measure (C K)) (hell : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume)
    (alpha b t u : ℝ) (d m : ℕ) (hstrip : |b| ≤ alpha) (hmd : m+1 < d)
    (chi : C K →* Circle) (hchi : Measurable (fun x => (chi x : ℂ))) :
    ∃ D : Lp ℂ 2 (weightedMeasure K mu alpha (2*(d:ℝ))) →L[ℂ] ℂ,
      (∀ F, D F = ∫ x, (chi x : ℂ) *
        (Round89D.coefficientProfile b t m (ell K x) -
         Round89D.coefficientProfile b u m (ell K x)) * F x ∂mu) ∧
      ‖D‖^2 ≤ 4 * |t-u|^2 * ((V:ℝ) * ∫ r : ℝ, (1+r^2)⁻¹) := by
  let c : ℝ → ℝ := fun r =>
    ‖Round89D.coefficientProfile b t m r - Round89D.coefficientProfile b u m r‖^2 /
      Round89D.stripWeight alpha (2*(d:ℝ)) r
  have hw (r : ℝ) : Round89D.stripWeight alpha (2*(d:ℝ)) r =
      Real.exp (2*alpha*|r|) * (1+r^2)^d := by
    simp [Round89D.stripWeight, show (2*(d:ℝ))/2 = d by ring, Real.rpow_natCast]
  have hc : Continuous c := by
    apply Continuous.div
    · unfold Round89D.coefficientProfile
      fun_prop
    · unfold Round89D.stripWeight
      fun_prop (disch := positivity)
    · intro r
      exact ne_of_gt (Round89D.stripWeight_pos alpha (2*(d:ℝ)) r)
  have hj : Integrable (fun r : ℝ =>
      (Real.exp (b*r) * |r|^(m+1))^2 / Round89D.stripWeight alpha (2*(d:ℝ)) r) := by
    simp_rw [hw]
    exact Round89F.stripBoundaryDensity_integrable alpha b hstrip (m+1) d hmd
  obtain ⟨hci, hcb⟩ := Round89D.coefficient_difference_integral volume
    alpha (2*(d:ℝ)) b t u m hc.aestronglyMeasurable hj
  have hcb' : (∫ r, c r) ≤ 4 * |t-u|^2 * ∫ r : ℝ, (1+r^2)⁻¹ := by
    apply hcb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simp_rw [hw]
    exact Round89F.boundary_dual_energy_le alpha b hstrip (m+1) d hmd
  let eta : C K → ℂ := fun x => (chi x : ℂ) *
    (Round89D.coefficientProfile b t m (ell K x) -
     Round89D.coefficientProfile b u m (ell K x))
  have heq (x : C K) : ‖eta x‖^2 / density K alpha (2*(d:ℝ)) x = c (ell K x) := by
    simp [eta, c, density, Round89D.stripWeight]
  have heta : Measurable eta := by
    dsimp [eta]
    unfold Round89D.coefficientProfile
    fun_prop
  have himap : Integrable c (Measure.map (ell K) mu) := by
    rw [hpush]
    exact hci.smul_measure (by simp)
  have he : Integrable (fun x => ‖eta x‖^2 / density K alpha (2*(d:ℝ)) x) mu := by
    simp_rw [heq]
    exact (integrable_map_measure hc.aestronglyMeasurable hell.aemeasurable).mp himap
  obtain ⟨D, hD, hn⟩ := genuine_weighted_coefficient_functional K mu alpha (2*(d:ℝ))
    hell eta heta he
  refine ⟨D, hD, ?_⟩
  rw [hn]
  simp_rw [heq]
  calc
    _ = ∫ r, c r ∂Measure.map (ell K) mu :=
      (integral_map hell.aemeasurable hc.aestronglyMeasurable).symm
    _ = (V:ℝ) * ∫ r, c r := by rw [hpush, integral_smul_measure]; simp
    _ ≤ (V:ℝ) * (4 * |t-u|^2 * ∫ r : ℝ, (1+r^2)⁻¹) :=
      mul_le_mul_of_nonneg_left hcb' V.property
    _ = _ := by ring

#check genuine_coefficient_frequency_bound
#print axioms genuine_coefficient_frequency_bound
end
end Round126C

namespace Round127C
open MasulloGRH Round117H Round123C Round124C Round125C Round126C MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- A necessary estimate for actual smoothed lifts. The output is required
only to represent the literal convolution; its norm is not assumed bounded.
This is not an upper nuclear estimate. -/
theorem genuine_smoothed_lift_frequency_cost
    (mu : Measure (C K)) (hell : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume)
    (alpha b t u : ℝ) (d m : ℕ) (hstrip : |b| ≤ alpha) (hmd : m+1 < d)
    (chi : C K →* Circle) (hchi : Measurable (fun x => (chi x : ℂ)))
    (phi f : C K → ℂ)
    (out : Lp ℂ 2 (weightedMeasure K mu alpha (2*(d:ℝ))))
    (hout : ∀ᵐ x ∂mu, out x = ∫ y, phi (x*y⁻¹) * f y ∂mu) :
    ‖∫ x, ((chi x : ℂ) *
      (Round89D.coefficientProfile b t m (ell K x) -
       Round89D.coefficientProfile b u m (ell K x))) *
        (∫ y, phi (x*y⁻¹) * f y ∂mu) ∂mu‖^2 ≤
      (4 * |t-u|^2 * ((V:ℝ) * ∫ r : ℝ, (1+r^2)⁻¹)) * ‖out‖^2 := by
  obtain ⟨D,hD,hn⟩ := genuine_coefficient_frequency_bound K mu hell V hpush
    alpha b t u d m hstrip hmd chi hchi
  have he : D out = ∫ x, ((chi x : ℂ) *
      (Round89D.coefficientProfile b t m (ell K x) -
       Round89D.coefficientProfile b u m (ell K x))) *
        (∫ y, phi (x*y⁻¹) * f y ∂mu) ∂mu := by
    rw [hD]
    apply integral_congr_ae
    filter_upwards [hout] with x hx
    rw [hx]
  rw [← he]
  calc
    ‖D out‖^2 ≤ (‖D‖ * ‖out‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (D.le_opNorm out) 2
    _ = ‖D‖^2 * ‖out‖^2 := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hn (sq_nonneg _)

/-- Direct quantitative obstruction to a label-independent smoothed-lift
bound. The moment identity is explicit and is not asserted for arbitrary
spectral data. No spectral identification or summability is assumed. -/
theorem genuine_smoothed_lift_separation_requirement
    (mu : Measure (C K)) (hell : Measurable (ell K)) (V : ℝ≥0)
    (hpush : Measure.map (ell K) mu = (V : ℝ≥0∞) • volume)
    (alpha b t u : ℝ) (d m : ℕ) (hstrip : |b| ≤ alpha) (hmd : m+1 < d)
    (chi : C K →* Circle) (hchi : Measurable (fun x => (chi x : ℂ)))
    (phi f : C K → ℂ)
    (out : Lp ℂ 2 (weightedMeasure K mu alpha (2*(d:ℝ))))
    (hout : ∀ᵐ x ∂mu, out x = ∫ y, phi (x*y⁻¹) * f y ∂mu)
    (lambda : ℂ)
    (hmoment : (∫ x, ((chi x : ℂ) *
      (Round89D.coefficientProfile b t m (ell K x) -
       Round89D.coefficientProfile b u m (ell K x))) *
        (∫ y, phi (x*y⁻¹) * f y ∂mu) ∂mu) = lambda) :
    ‖lambda‖^2 ≤
      (4 * |t-u|^2 * ((V:ℝ) * ∫ r : ℝ, (1+r^2)⁻¹)) * ‖out‖^2 := by
  rw [← hmoment]
  exact genuine_smoothed_lift_frequency_cost K mu hell V hpush
    alpha b t u d m hstrip hmd chi hchi phi f out hout

#check genuine_smoothed_lift_frequency_cost
#print axioms genuine_smoothed_lift_frequency_cost
#check genuine_smoothed_lift_separation_requirement
#print axioms genuine_smoothed_lift_separation_requirement
end
end Round127C
