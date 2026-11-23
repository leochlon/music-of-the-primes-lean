import Mathlib

/-! B194. The actual normalized compact-character averaging step in C189's
geometric seed. This proves its theta envelope with the Tate/native Haar
ratio retained. It supplies the seed moments in the global resolvent route;
it does not assert nuclearity or replace the original geometric space. -/
noncomputable section
set_option linter.unusedSimpArgs false
open MeasureTheory
namespace Round194B

def measuredThetaSeed {C : Type*} [MeasurableSpace C]
    (μ : Measure C) (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (t : ℝ) : ℂ :=
  (κ : ℂ) * (Real.exp (a * t) : ℂ) * ∫ y, Φ t y * χ y ∂μ

theorem native_normalized_theta_seed_bound
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a B P : ℝ) (hκ : 0 ≤ κ) (_hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hχ : ∀ y, ‖χ y‖ = 1)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P * Real.exp (-B * |t|))
    (t : ℝ) :
    ‖measuredThetaSeed μ κ a Φ χ t‖ ≤
      κ * P * Real.exp (-(B - |a|) * |t|) := by
  have havg : ‖∫ y, Φ t y * χ y ∂μ‖ ≤ P * Real.exp (-B * |t|) := by
    have hb : ∀ᵐ y ∂μ, ‖Φ t y * χ y‖ ≤ P * Real.exp (-B * |t|) :=
      Filter.Eventually.of_forall fun y => by
        simpa only [Pi.mul_apply, norm_mul, hχ y, mul_one] using hdecay t y
    simpa using norm_integral_le_of_norm_le_const hb
  have hat : a * t ≤ |a| * |t| := by
    calc
      a * t ≤ |a * t| := le_abs_self _
      _ = |a| * |t| := abs_mul _ _
  have hexp : Real.exp (a * t) ≤ Real.exp (|a| * |t|) := Real.exp_le_exp.mpr hat
  calc
    ‖measuredThetaSeed μ κ a Φ χ t‖ =
        κ * Real.exp (a * t) * ‖∫ y, Φ t y * χ y ∂μ‖ := by
      simp only [measuredThetaSeed, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hκ, abs_of_pos (Real.exp_pos _)]
    _ ≤ κ * Real.exp (|a| * |t|) * (P * Real.exp (-B * |t|)) := by
      gcongr
    _ = κ * P * Real.exp (-(B - |a|) * |t|) := by
      rw [show κ * Real.exp (|a| * |t|) * (P * Real.exp (-B * |t|)) =
        κ * P * (Real.exp (|a| * |t|) * Real.exp (-B * |t|)) by ring]
      rw [← Real.exp_add]
      congr 2
      ring

#check native_normalized_theta_seed_bound
#print axioms native_normalized_theta_seed_bound

/-- Both existence of the compact Bochner integral and its native seed
normalization. For the actual application the two measurability hypotheses
come from the continuous theta function and compact unitary character. -/
theorem native_seed_normalization
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a B P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : ∀ t, AEStronglyMeasurable (Φ t) μ)
    (hc : AEStronglyMeasurable χ μ)
    (hχ : ∀ y, ‖χ y‖ = 1)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P * Real.exp (-B * |t|)) :
    ∀ t, Integrable (fun y => Φ t y * χ y) μ ∧
      ‖measuredThetaSeed μ κ a Φ χ t‖ ≤
        κ * P * Real.exp (-(B - |a|) * |t|) := by
  intro t
  constructor
  · apply (integrable_const (P * Real.exp (-B * |t|))).mono' ((hΦ t).mul hc)
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Pi.mul_apply, norm_mul, hχ y, mul_one] using hdecay t y
  · exact native_normalized_theta_seed_bound μ κ a B P hκ hP Φ χ hχ hdecay t

#check native_seed_normalization
#print axioms native_seed_normalization
end Round194B

namespace Round195B
open Round194B

/-- Changing only the auxiliary theta Haar by r multiplies its seed by r;
this identity does not rescale the original convolution operator. -/
theorem measuredThetaSeed_haar_rescale
    {C : Type*} [MeasurableSpace C] (μ : Measure C) (r : NNReal)
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ) (t : ℝ) :
    measuredThetaSeed ((r : ENNReal) • μ) κ a Φ χ t =
      measuredThetaSeed μ ((r : ℝ) * κ) a Φ χ t := by
  simp only [measuredThetaSeed, integral_smul_measure, ENNReal.coe_toReal,
    Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The native real tilt changes the Mellin coordinate by a, with the
Tate/native scalar retained outside the whole transform. -/
theorem measuredThetaSeed_mellin_shift
    {C : Type*} [MeasurableSpace C] (μ : Measure C)
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ) (z : ℂ) :
    (∫ t : ℝ, measuredThetaSeed μ κ a Φ χ t * Complex.exp (z * (t : ℂ))) =
      (κ : ℂ) * ∫ t : ℝ, (∫ y, Φ t y * χ y ∂μ) *
        Complex.exp (((a : ℂ) + z) * (t : ℂ)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only [measuredThetaSeed]
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
    calc
      _ = (κ : ℂ) * (∫ y, Φ t y * χ y ∂μ) *
          (Complex.exp ((a : ℂ) * (t : ℂ)) * Complex.exp (z * (t : ℂ))) := by ring
      _ = _ := by rw [← Complex.exp_add, ← add_mul]; ring

/-- Measurability of the measured seed is derived from the actual joint
measurability input, not from a default value of a Bochner integral. -/
theorem measuredThetaSeed_stronglyMeasurable
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [SFinite μ]
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hχ : StronglyMeasurable χ) :
    StronglyMeasurable (measuredThetaSeed μ κ a Φ χ) := by
  have hpair : StronglyMeasurable
      (Function.uncurry (fun t y => Φ t y * χ y)) :=
    hΦ.mul (hχ.comp_measurable measurable_snd)
  have havg := hpair.integral_prod_right (ν := μ)
  have he : StronglyMeasurable (fun t : ℝ => (Real.exp (a*t) : ℂ)) :=
    (by fun_prop : Continuous (fun t : ℝ => (Real.exp (a*t) : ℂ))).stronglyMeasurable
  exact (stronglyMeasurable_const.mul he).mul havg

#check measuredThetaSeed_haar_rescale
#print axioms measuredThetaSeed_haar_rescale
#check measuredThetaSeed_mellin_shift
#print axioms measuredThetaSeed_mellin_shift
#check measuredThetaSeed_stronglyMeasurable
#print axioms measuredThetaSeed_stronglyMeasurable
end Round195B


/-! Round 193 G: the ACTUAL archimedean pole-clearing Tate seeds.
This discharges finite-interval additive-mass identities within
LOCAL_TO_NATIVE_SEED of GLOBAL_ESTIMATE.md. It does not assert global
nuclearity or presume a spectral sum. -/
noncomputable section
open MeasureTheory
namespace Round193G

def realSeed (A x : ℝ) : ℝ :=
  (4*A^2*x^4-6*A*x^2)*Real.exp (-A*x^2)
def realPrimitive (A x : ℝ) : ℝ :=
  (-2*A)*x^3*Real.exp (-A*x^2)
def complexRadialSeed (A r : ℝ) : ℝ :=
  (A^2*r^5-2*A*r^3)*Real.exp (-A*r^2)
def complexPrimitive (A r : ℝ) : ℝ :=
  (-A/2)*r^4*Real.exp (-A*r^2)

theorem real_seed_derivative (A x : ℝ) :
    HasDerivAt (realPrimitive A) (realSeed A x) x := by
  unfold realPrimitive realSeed
  convert (((hasDerivAt_id x).pow 3).const_mul (-2*A)).mul
    ((((hasDerivAt_id x).pow 2).const_mul (-A)).exp) using 1
  simp only [Pi.pow_apply, id_eq]
  ring

theorem complex_seed_radial_derivative (A r : ℝ) :
    HasDerivAt (complexPrimitive A) (complexRadialSeed A r) r := by
  unfold complexPrimitive complexRadialSeed
  convert (((hasDerivAt_id r).pow 4).const_mul (-A/2)).mul
    ((((hasDerivAt_id r).pow 2).const_mul (-A)).exp) using 1
  simp only [Pi.pow_apply, id_eq]
  ring

/-- These are the real additive integral and the complex additive polar
integral of the actual local seeds. No moment identity is a hypothesis. -/
theorem archimedean_seed_boundary_integrals (A a b : ℝ) :
    (∫ x in a..b, realSeed A x) = realPrimitive A b - realPrimitive A a ∧
    (∫ r in a..b, complexRadialSeed A r) =
      complexPrimitive A b - complexPrimitive A a := by
  constructor
  · apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => real_seed_derivative A x)
    exact (by unfold realSeed; fun_prop : Continuous (realSeed A)).intervalIntegrable a b
  · apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => complex_seed_radial_derivative A r)
    exact (by unfold complexRadialSeed; fun_prop : Continuous (complexRadialSeed A)).intervalIntegrable a b

#check real_seed_derivative
#print axioms real_seed_derivative
#check complex_seed_radial_derivative
#print axioms complex_seed_radial_derivative
#check archimedean_seed_boundary_integrals
#print axioms archimedean_seed_boundary_integrals
end Round193G

namespace Round194G
open Round193G
/-- Origin conditions of the actual local pole-clearing seeds. -/
theorem archimedean_seed_origin_values (A : ℝ) :
    realSeed A 0 = 0 ∧ complexRadialSeed A 0 = 0 := by
  simp [realSeed, complexRadialSeed]
#check archimedean_seed_origin_values
#print axioms archimedean_seed_origin_values
end Round194G

namespace Round194G
open Round193G Filter
open scoped Topology

theorem actual_seed_integrable (A : ℝ) (hA : 0 < A) :
    Integrable (realSeed A) ∧ Integrable (complexRadialSeed A) := by
  have h (n : ℕ) : Integrable (fun x : ℝ => x^n * Real.exp (-A*x^2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq hA (s := (n : ℝ)) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
  constructor
  · convert ((h 4).const_mul (4*A^2)).sub ((h 2).const_mul (6*A)) using 1
    ext x
    dsimp only [realSeed, Pi.sub_apply]
    ring
  · convert ((h 5).const_mul (A^2)).sub ((h 3).const_mul (2*A)) using 1
    ext x
    dsimp only [complexRadialSeed, Pi.sub_apply]
    ring

theorem actual_seed_zero_masses (A : ℝ) (hA : 0 < A) :
    (∫ x : ℝ, realSeed A x) = 0 ∧
    (∫ r : ℝ in Set.Ioi 0, complexRadialSeed A r) = 0 := by
  have hlim (n : ℕ) : Tendsto
      (fun x : ℝ => x^n * Real.exp (-A*x^2)) (cocompact ℝ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hA (n : ℝ)
  have hr : Tendsto (realPrimitive A) (cocompact ℝ) (𝓝 0) := by
    change Tendsto (fun x : ℝ => (-2*A)*x^3*Real.exp (-A*x^2)) _ _
    simpa only [mul_assoc, mul_zero] using (hlim 3).const_mul (-2*A)
  have hc : Tendsto (complexPrimitive A) (cocompact ℝ) (𝓝 0) := by
    change Tendsto (fun x : ℝ => (-A/2)*x^4*Real.exp (-A*x^2)) _ _
    simpa only [mul_assoc, mul_zero] using (hlim 4).const_mul (-A/2)
  constructor
  · have hi := integral_of_hasDerivAt_of_tendsto
      (real_seed_derivative A) (actual_seed_integrable A hA).1
      (hr.mono_left atBot_le_cocompact) (hr.mono_left atTop_le_cocompact)
    simpa using hi
  · have hi := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := complexPrimitive A) (a := 0)
      (by unfold complexPrimitive; fun_prop)
      (fun x _ => complex_seed_radial_derivative A x)
      (actual_seed_integrable A hA).2.integrableOn
      (hc.mono_left atTop_le_cocompact)
    simpa [complexPrimitive] using hi

#check actual_seed_integrable
#print axioms actual_seed_integrable
#check actual_seed_zero_masses
#print axioms actual_seed_zero_masses
end Round194G

namespace Round195B
open Round194B

/-- This supplies F194's continuous scalar-seed premise from continuity
of the compact theta family and the compact character. -/
theorem measuredThetaSeed_continuous
    {C : Type*} [TopologicalSpace C] [MeasurableSpace C]
    [BorelSpace C] [CompactSpace C]
    (μ : Measure C) [IsFiniteMeasure μ]
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : Continuous (Function.uncurry Φ)) (hχ : Continuous χ) :
    Continuous (measuredThetaSeed μ κ a Φ χ) := by
  have hp : Continuous (Function.uncurry (fun t y => Φ t y * χ y)) :=
    hΦ.mul (hχ.comp continuous_snd)
  have havg : Continuous (fun t : ℝ => ∫ y, Φ t y * χ y ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous hp
      (s := Set.univ) isCompact_univ
  have he : Continuous (fun t : ℝ => (Real.exp (a*t) : ℂ)) := by fun_prop
  exact (continuous_const.mul he).mul havg

#check measuredThetaSeed_continuous
#print axioms measuredThetaSeed_continuous
end Round195B

namespace Round195B
/-- Left translation of the primal compact character average has the inverse
character, as required by the manuscript's bilinear dual convention. -/
theorem character_average_inverse_isotype
    {C : Type*} [Group C] [MeasurableSpace C] [MeasurableMul C]
    (μ : Measure C) [μ.IsMulLeftInvariant]
    (χ : C →* ℂˣ) (f : C → ℂ) (x : C) :
    (∫ y, f (x*y) * (χ y : ℂ) ∂μ) =
      (χ x : ℂ)⁻¹ * ∫ y, f y * (χ y : ℂ) ∂μ := by
  apply mul_left_cancel₀ (Units.ne_zero (χ x))
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (χ x)), one_mul,
    ← integral_const_mul]
  calc
    _ = ∫ y, f (x*y) * (χ (x*y) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [map_mul, Units.val_mul]
        ring
    _ = _ := integral_mul_left_eq_self (fun y => f y * (χ y : ℂ)) x

#check character_average_inverse_isotype
#print axioms character_average_inverse_isotype
end Round195B

namespace Round196B
open Round193G Round194G

/-- The actual complex pole-clearing local Gaussian before polar coordinates.
The additive Haar measure is Mathlib's complex Lebesgue measure. -/
def complexAdditiveSeed (A : ℝ) (z : ℂ) : ℝ :=
  (A^2 * ‖z‖^4 - 2*A*‖z‖^2) * Real.exp (-A*‖z‖^2)

theorem complex_additive_seed_polar (A : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ polarCoord.target) :
    p.1 • complexAdditiveSeed A (Complex.polarCoord.symm p) =
      complexRadialSeed A p.1 := by
  have hp0 : 0 < p.1 := hp.1
  simp only [complexAdditiveSeed, Complex.norm_polarCoord_symm,
    abs_of_pos hp0, smul_eq_mul, complexRadialSeed]
  ring

theorem complex_additive_seed_integrable (A : ℝ) (hA : 0 < A) :
    Integrable (complexAdditiveSeed A) := by
  have hc : Continuous (complexAdditiveSeed A) := by
    unfold complexAdditiveSeed
    fun_prop
  have hi : Integrable (fun p : ℝ × ℝ => complexRadialSeed A p.1 * (1 : ℝ))
      (volume.restrict polarCoord.target) := by
    change Integrable _ ((volume.prod volume).restrict
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi))
    rw [← Measure.prod_restrict]
    exact (actual_seed_integrable A hA).2.integrableOn.mul_prod (integrable_const 1)
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have he : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
      ENNReal.ofReal ‖complexAdditiveSeed A (Complex.polarCoord.symm p)‖)
      =ᵐ[volume.restrict polarCoord.target]
      (fun p => ENNReal.ofReal ‖complexRadialSeed A p.1 * (1 : ℝ)‖) := by
    filter_upwards [ae_restrict_mem (by
      change MeasurableSet (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      measurability)] with p hp
    have hp0 : 0 ≤ p.1 := le_of_lt hp.1
    rw [smul_eq_mul, ← ENNReal.ofReal_mul hp0, mul_one]
    congr 1
    rw [← complex_additive_seed_polar A p hp, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg hp0]
  rw [lintegral_congr_ae he]
  exact (hasFiniteIntegral_iff_norm _).mp hi.2

theorem complex_additive_seed_zero_mass (A : ℝ) (hA : 0 < A) :
    (∫ z : ℂ, complexAdditiveSeed A z) = 0 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    _ = ∫ p : ℝ × ℝ in polarCoord.target, complexRadialSeed A p.1 * (1 : ℝ) := by
      apply setIntegral_congr_fun
      · change MeasurableSet (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
        measurability
      · intro p hp
        simpa only [mul_one] using complex_additive_seed_polar A p hp
    _ = (∫ r : ℝ in Set.Ioi 0, complexRadialSeed A r) *
        (∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) :=
      by simpa only [polarCoord_target] using
        (setIntegral_prod_mul (μ := (volume : Measure ℝ))
          (ν := (volume : Measure ℝ)) (complexRadialSeed A)
          (fun _ : ℝ => (1 : ℝ)) (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi))
    _ = 0 := by rw [(actual_seed_zero_masses A hA).2, zero_mul]

#check complex_additive_seed_polar
#print axioms complex_additive_seed_polar
#check complex_additive_seed_integrable
#print axioms complex_additive_seed_integrable
#check complex_additive_seed_zero_mass
#print axioms complex_additive_seed_zero_mass
end Round196B

namespace Round196B
/-- C189's actual complex local test, with its prescribed nonzero Tate
normalization 4/κ, after applying the pole-clearing dilation operator. -/
def complexTatePoleClearingSeed (κ A : ℝ) (z : ℂ) : ℂ :=
  ((4 / κ : ℝ) : ℂ) * (complexAdditiveSeed A z : ℂ)

/-- The local additive S_0 conditions hold for every finite local Haar
scale, including the self-dual complex Haar 2*Lebesgue. The test's Tate
normalization factor is proved nonzero from κ>0. -/
theorem complex_tate_seed_local_conditions (κ A : ℝ)
    (hκ : 0 < κ) (hA : 0 < A) (r : NNReal) :
    Integrable (complexTatePoleClearingSeed κ A)
        ((r : ENNReal) • (volume : Measure ℂ)) ∧
      complexTatePoleClearingSeed κ A 0 = 0 ∧
      (∫ z : ℂ, complexTatePoleClearingSeed κ A z
        ∂((r : ENNReal) • volume)) = 0 ∧
      ((4 / κ : ℝ) : ℂ) ≠ 0 := by
  have hi : Integrable (fun z : ℂ => (complexAdditiveSeed A z : ℂ)) :=
    (complex_additive_seed_integrable A hA).ofReal
  refine ⟨(hi.const_mul _).smul_measure (by simp), ?_, ?_, ?_⟩
  · simp [complexTatePoleClearingSeed, complexAdditiveSeed]
  · rw [integral_smul_measure]
    unfold complexTatePoleClearingSeed
    have hz : (∫ z : ℂ, (complexAdditiveSeed A z : ℂ)) = 0 := by
      calc
        _ = Complex.ofRealCLM (∫ z : ℂ, complexAdditiveSeed A z) :=
          Complex.ofRealCLM.integral_comp_comm (complex_additive_seed_integrable A hA)
        _ = 0 := by rw [complex_additive_seed_zero_mass A hA]; rfl
    rw [integral_const_mul, hz]
    simp
  · exact_mod_cast (div_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hκ))

#check complex_tate_seed_local_conditions
#print axioms complex_tate_seed_local_conditions
end Round196B

namespace Round197B
open Round196B Filter

/-- The smoothness field of the actual local Schwartz seed. -/
theorem complex_tate_seed_smooth (κ A : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (complexTatePoleClearingSeed κ A) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => ‖z‖^2) := contDiff_norm_sq ℂ
  have hs : ContDiff ℝ (⊤ : ℕ∞) (complexAdditiveSeed A) := by
    have hh : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ =>
      (A^2 * (‖z‖^2)^2 - (2*A)*‖z‖^2) * Real.exp ((-A)*‖z‖^2)) :=
      ((contDiff_const.mul (hq.pow 2)).sub
        (contDiff_const.mul hq)).mul (Real.contDiff_exp.comp (contDiff_const.mul hq))
    convert hh using 1;
      (first | rfl | (funext z; dsimp [complexAdditiveSeed]; ring))
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hs)

/-- Arbitrary polynomial decay of the actual local seed. This discharges
exactly the derivative-order-zero Schwartz decay field used by F's lattice
majorant; higher derivative orders are still needed for full packaging. -/
theorem complex_tate_seed_polynomial_decay (κ A : ℝ) (hA : 0 < A) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖z‖^k * ‖complexTatePoleClearingSeed κ A z‖ ≤ C := by
  let p : ℝ → ℝ := fun r =>
    A^2 * (|r|^(k+4) * Real.exp (-A*r^2)) +
      |2*A| * (|r|^(k+2) * Real.exp (-A*r^2))
  have hc : Continuous p := by dsimp [p]; fun_prop
  have hl (n : ℕ) : Tendsto (fun r : ℝ => |r|^n * Real.exp (-A*r^2))
      (cocompact ℝ) (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hA (n : ℝ)
  have ht : Tendsto p (cocompact ℝ) (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      ((hl (k+4)).const_mul (A^2)).add ((hl (k+2)).const_mul |2*A|)
  let g : ZeroAtInftyContinuousMap ℝ ℝ := ⟨⟨p, hc⟩, ht⟩
  refine ⟨|4/κ| * ‖g.toBCF‖, by positivity, ?_⟩
  intro z
  have hp : |A^2 * ‖z‖^4 - 2*A*‖z‖^2| ≤
      A^2*‖z‖^4 + |2*A| *‖z‖^2 := by
    calc
      _ ≤ |A^2 * ‖z‖^4| + |2*A*‖z‖^2| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg A),
        abs_of_nonneg (pow_nonneg (norm_nonneg z) 4),
        abs_of_nonneg (sq_nonneg ‖z‖)]
  have hm : ‖z‖^k * ‖complexAdditiveSeed A z‖ ≤ p ‖z‖ := by
    rw [complexAdditiveSeed, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ ‖z‖^k * ((A^2*‖z‖^4 + |2*A| *‖z‖^2) *
        Real.exp (-A*‖z‖^2)) := by gcongr
      _ = _ := by dsimp [p]; rw [abs_of_nonneg (norm_nonneg z)];
                  simp only [pow_add]; ring
  have hb : p ‖z‖ ≤ ‖g.toBCF‖ :=
    le_trans (le_abs_self _) (g.toBCF.norm_coe_le_norm ‖z‖)
  calc
    _ = |4/κ| * (‖z‖^k * ‖complexAdditiveSeed A z‖) := by
      simp only [complexTatePoleClearingSeed, norm_mul, Complex.norm_real,
        Real.norm_eq_abs]; ring
    _ ≤ |4/κ| * p ‖z‖ := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)

#check complex_tate_seed_smooth
#print axioms complex_tate_seed_smooth
#check complex_tate_seed_polynomial_decay
#print axioms complex_tate_seed_polynomial_decay
end Round197B

namespace Round197B
open Round196B
open scoped BigOperators
theorem actual_complex_seed_lattice_decay
    (L : Submodule ℤ ℂ) [DiscreteTopology L]
    (κ A : ℝ) (hA : 0 < A) (n : ℕ) (hn : Module.finrank ℤ L < n)
    {C : Type*} (T : ℝ → C → ℂ → ℂ) (c delta B : ℝ) (hc : 0 < c)
    (hB : B ≤ (n : ℝ) * delta)
    (hscale : ∀ t, 0 ≤ t → ∀ y (x : L),
      c * Real.exp (delta*t) * ‖x‖ ≤ ‖T t y x‖) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t, 0 ≤ t → ∀ y,
      Summable (fun x : {x : L // x ≠ 0} => ‖complexTatePoleClearingSeed κ A (T t y x.1)‖) ∧
      (∑' x : {x : L // x ≠ 0}, ‖complexTatePoleClearingSeed κ A (T t y x.1)‖) ≤
        P * Real.exp (-B*t) := by
  obtain ⟨S, hS, hSf⟩ := complex_tate_seed_polynomial_decay κ A hA n
  let w : {x : L // x ≠ 0} → ℝ := fun x => ‖x.1‖⁻¹ ^ n
  have hw : Summable w :=
    (ZLattice.summable_norm_pow_inv L n hn).subtype {x : L | x ≠ 0}
  have hw0 : ∀ x, 0 ≤ w x := by intro x; positivity
  refine ⟨S * c⁻¹^n * ∑' x, w x, by positivity, ?_⟩
  intro t ht y
  have hterm (x : {x : L // x ≠ 0}) :
      ‖complexTatePoleClearingSeed κ A (T t y x.1)‖ ≤ (S * c⁻¹^n * Real.exp (-B*t)) * w x := by
    have hx : (x.1 : ℂ) ≠ 0 := by
      intro he
      apply x.2
      exact Subtype.ext he
    let r := c * Real.exp (delta*t)
    have hr : 0 < r := mul_pos hc (Real.exp_pos _)
    have hbase : 0 < r * ‖(x.1 : ℂ)‖ := mul_pos hr (norm_pos_iff.mpr hx)
    have hpow : (r * ‖(x.1 : ℂ)‖)^n *
        ‖complexTatePoleClearingSeed κ A (T t y x.1)‖ ≤ S :=
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase.le (hscale t ht y x.1) n) (norm_nonneg _)).trans
        (hSf (T t y x.1))
    have hp : ‖complexTatePoleClearingSeed κ A (T t y x.1)‖ ≤
        S * r⁻¹^n * ‖(x.1 : ℂ)‖⁻¹^n := by
      calc
        _ ≤ S / (r * ‖(x.1 : ℂ)‖)^n :=
          (le_div_iff₀ (pow_pos hbase n)).mpr (by nlinarith [hpow])
        _ = _ := by simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow]; ring
    have he : Real.exp (-((n : ℝ)*delta)*t) ≤ Real.exp (-B*t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      ‖complexTatePoleClearingSeed κ A (T t y x.1)‖ ≤ S * (c * Real.exp (delta*t))⁻¹^n * ‖(x.1 : ℂ)‖⁻¹^n := hp
      _ = (S * c⁻¹^n * Real.exp (-((n : ℝ)*delta)*t)) * w x := by
        change S * (c * Real.exp (delta*t))⁻¹^n * ‖(x.1 : ℂ)‖⁻¹^n =
          (S * c⁻¹^n * Real.exp (-((n : ℝ)*delta)*t)) * ‖(x.1 : ℂ)‖⁻¹^n
        rw [mul_inv_rev, mul_pow, ← Real.exp_neg, ← Real.exp_nat_mul]
        have heq : (n : ℝ) * -(delta*t) = -((n : ℝ)*delta)*t := by ring
        rw [heq]
        ring
      _ ≤ (S * c⁻¹^n * Real.exp (-B*t)) * w x := by gcongr
  have hmajor : Summable (fun x => (S * c⁻¹^n * Real.exp (-B*t)) * w x) :=
    hw.mul_left _
  have hs : Summable (fun x : {x : L // x ≠ 0} => ‖complexTatePoleClearingSeed κ A (T t y x.1)‖) :=
    hmajor.of_norm_bounded (fun x => by simpa only [norm_norm] using hterm x)
  refine ⟨hs, ?_⟩
  calc
    ∑' x : {x : L // x ≠ 0}, ‖complexTatePoleClearingSeed κ A (T t y x.1)‖ ≤
        ∑' x, (S * c⁻¹^n * Real.exp (-B*t)) * w x :=
      hs.tsum_le_tsum hterm hmajor
    _ = (S * c⁻¹^n * ∑' x, w x) * Real.exp (-B*t) := by
      rw [tsum_mul_left]
      ring

#check actual_complex_seed_lattice_decay
#print axioms actual_complex_seed_lattice_decay
end Round197B
