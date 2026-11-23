import Mathlib
noncomputable section

namespace Round150E
/-- L1-native: the actual radial Gaussian theta Poisson identity.
The separate adelic-to-radial identification and native integrability
remain obligations; this theorem assumes no Poisson identity. -/
theorem rational_gaussian_theta_poisson (x : ℝ) (hx : 0 < x) :
    jacobiTheta (Complex.I * ((x : ℂ)⁻¹)^2) =
      (x : ℂ) * jacobiTheta (Complex.I * (x : ℂ)^2) := by
  let τ : UpperHalfPlane := ⟨Complex.I * (x : ℂ)^2, by
    simpa [← Complex.ofReal_pow] using sq_pos_of_pos hx⟩
  have hp := jacobiTheta_S_smul τ
  have ht : (↑(ModularGroup.S • τ) : ℂ) =
      Complex.I * ((x : ℂ)⁻¹)^2 := by
    norm_num [UpperHalfPlane.coe_smul, UpperHalfPlane.num,
      UpperHalfPlane.denom, UpperHalfPlane.σ, ModularGroup.S, τ,
      div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have hb : -Complex.I * (↑τ : ℂ) = ((x^2 : ℝ) : ℂ) := by
    dsimp [τ]
    push_cast
    simp [← mul_assoc]
  have hc : (-Complex.I * (↑τ : ℂ)) ^ (1 / 2 : ℂ) = (x : ℂ) := by
    rw [hb]
    have hh := Complex.ofReal_cpow (sq_nonneg x) (1/2 : ℝ)
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hh
    rw [← hh, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs, abs_of_pos hx]
  rw [ht, hc] at hp
  exact hp
#check rational_gaussian_theta_poisson
#print axioms rational_gaussian_theta_poisson
end Round150E

namespace Round151E
/-- The precise radial theta series used by the rational Gaussian seed.
Its identification with the genuine adelic orbit sum remains separate. -/
def rationalTheta (x : ℝ) : ℂ := jacobiTheta (Complex.I * (x : ℂ)^2) - 1

def compensatedRationalTheta (x : ℝ) : ℂ :=
  2 * rationalTheta x - 3 * rationalTheta (x/2) + rationalTheta (x/4)

/-- L1-native, inversion part: derived Poisson formula, with no assumed
theta functional equation or native integrability. -/
theorem rationalTheta_inversion (x : ℝ) (hx : 0 < x) :
    rationalTheta x = (x : ℂ)⁻¹ - 1 +
      (x : ℂ)⁻¹ * rationalTheta x⁻¹ := by
  have h := Round150E.rational_gaussian_theta_poisson x hx
  have hn : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  unfold rationalTheta
  simp only [Complex.ofReal_inv]
  rw [h]
  field_simp
  ring

/-- L1-native: both polar terms cancel in the explicit compensated seed.
This is the small-x identity required to use Gaussian decay in its native
weighted norm. It is not a projected nuclear estimate. -/
theorem compensated_rational_theta_inversion (x : ℝ) (hx : 0 < x) :
    compensatedRationalTheta x = (x : ℂ)⁻¹ *
      (2 * rationalTheta (1/x) - 6 * rationalTheta (2/x) +
        4 * rationalTheta (4/x)) := by
  have hn : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  unfold compensatedRationalTheta
  rw [rationalTheta_inversion x hx,
    rationalTheta_inversion (x/2) (by positivity),
    rationalTheta_inversion (x/4) (by positivity)]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, inv_div, one_div]
  field_simp
  ring

#check compensated_rational_theta_inversion
#print axioms compensated_rational_theta_inversion
end Round151E

namespace Round151E
def gaussianThetaBound (x : ℝ) : ℝ :=
  2 / (1 - Real.exp (-Real.pi * x^2)) * Real.exp (-Real.pi * x^2)

theorem rationalTheta_norm_le (x : ℝ) (hx : 0 < x) :
    ‖rationalTheta x‖ ≤ gaussianThetaBound x := by
  have ht : 0 < (Complex.I * (x : ℂ)^2).im := by
    simpa [← Complex.ofReal_pow] using sq_pos_of_pos hx
  simpa [rationalTheta, gaussianThetaBound, ← Complex.ofReal_pow] using
    norm_jacobiTheta_sub_one_le ht

/-- L1-native, small-tail majorant: the actual compensated radial seed,
with the polar terms removed, is bounded by three Gaussian tails.
This discharges the pointwise small-tail premise, not native attachment. -/
theorem compensated_rational_theta_small_majorant (x : ℝ) (hx : 0 < x) :
    ‖compensatedRationalTheta x‖ ≤ x⁻¹ *
      (2 * gaussianThetaBound (1/x) + 6 * gaussianThetaBound (2/x) +
        4 * gaussianThetaBound (4/x)) := by
  rw [compensated_rational_theta_inversion x hx, norm_mul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr hx))
  calc
    ‖2 * rationalTheta (1/x) - 6 * rationalTheta (2/x) +
        4 * rationalTheta (4/x)‖ ≤
        ‖2 * rationalTheta (1/x) - 6 * rationalTheta (2/x)‖ +
          ‖4 * rationalTheta (4/x)‖ := norm_add_le _ _
    _ ≤ (‖2 * rationalTheta (1/x)‖ + ‖6 * rationalTheta (2/x)‖) +
          ‖4 * rationalTheta (4/x)‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ = 2 * ‖rationalTheta (1/x)‖ + 6 * ‖rationalTheta (2/x)‖ +
          4 * ‖rationalTheta (4/x)‖ := by norm_num [norm_mul]
    _ ≤ _ := by
      gcongr
      · exact rationalTheta_norm_le _ (by positivity)
      · exact rationalTheta_norm_le _ (by positivity)
      · exact rationalTheta_norm_le _ (by positivity)

#check compensated_rational_theta_small_majorant
#print axioms compensated_rational_theta_small_majorant
end Round151E

namespace Round152E
open MeasureTheory
/-- The actual dilation used in the rational compensated adelic seed. -/
def realDilationEquiv (c : ℝ) (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by simp [hc]
  right_inv x := by simp [hc]
  map_add' x y := by ring
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def realDilation (c : ℝ) (hc : c ≠ 0) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilationEquiv c hc) f

@[simp] theorem realDilation_apply (c : ℝ) (hc : c ≠ 0)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    realDilation c hc f x = f (c * x) := rfl

/-- G1-Schwartz, real factor: produces the exact compensated real datum
as a Schwartz map, and derives its integrability and both polar constraints.
Finite-adelic tensor and native geometric attachment remain separate. -/
theorem compensated_real_seed_schwartz_polar (f : SchwartzMap ℝ ℂ) :
    ∃ q : SchwartzMap ℝ ℂ,
      (∀ x, q x = 2 * f x - 3 * f ((1/2 : ℝ) * x) + f ((1/4 : ℝ) * x)) ∧
      q 0 = 0 ∧ Integrable q ∧ (∫ x : ℝ, q x) = 0 := by
  let f2 := realDilation (1/2) (by norm_num) f
  let f4 := realDilation (1/4) (by norm_num) f
  let q : SchwartzMap ℝ ℂ := (2 : ℂ) • f - (3 : ℂ) • f2 + f4
  have he (x : ℝ) : q x = 2 * f x - 3 * f ((1/2 : ℝ)*x) +
      f ((1/4 : ℝ)*x) := rfl
  refine ⟨q, he, ?_, q.integrable, ?_⟩
  · rw [he]
    norm_num
    ring
  · have h2 : (∫ x : ℝ, f2 x) = (2 : ℂ) * ∫ x : ℝ, f x := by
      change (∫ x : ℝ, f ((1/2 : ℝ)*x)) = _
      rw [Measure.integral_comp_mul_left]
      norm_num [Complex.real_smul]
    have h4 : (∫ x : ℝ, f4 x) = (4 : ℂ) * ∫ x : ℝ, f x := by
      change (∫ x : ℝ, f ((1/4 : ℝ)*x)) = _
      rw [Measure.integral_comp_mul_left]
      norm_num [Complex.real_smul]
    change (∫ x : ℝ, (2 : ℂ) * f x - (3 : ℂ) * f2 x + f4 x) = 0
    have hi0 : Integrable (fun x : ℝ => (2 : ℂ) * f x) :=
      f.integrable.const_mul (2 : ℂ)
    have hi1 : Integrable (fun x : ℝ => (3 : ℂ) * f2 x) :=
      f2.integrable.const_mul (3 : ℂ)
    have hsplit := integral_add (hi0.sub hi1) f4.integrable
    simp only [Pi.sub_apply] at hsplit
    rw [hsplit, integral_sub hi0 hi1, integral_const_mul,
      integral_const_mul, h2, h4]
    ring

#check compensated_real_seed_schwartz_polar
#print axioms compensated_real_seed_schwartz_polar
end Round152E

namespace Round154E
open Round151E
/-- The actual real Gaussian used in the rational adelic seed. -/
def realGaussian (x : ℝ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (x : ℂ)^2)

def compensatedGaussian (x : ℝ) : ℂ :=
  2 * realGaussian x - 3 * realGaussian (x/2) + realGaussian (x/4)

/-- G1-orbit-real: the convergent positive-integer Gaussian orbit sum.
This is the radial orbit attachment input, not a nuclear assertion. -/
theorem realGaussian_orbit_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => realGaussian (((n : ℝ) + 1) * x))
      (rationalTheta x / 2) := by
  have ht : 0 < (Complex.I * (x : ℂ)^2).im := by
    simpa [← Complex.ofReal_pow] using sq_pos_of_pos hx
  have h := hasSum_nat_jacobiTheta ht
  convert h using 1
  · funext n
    unfold realGaussian
    congr 1
    push_cast
    ring_nf
    simp [Complex.I_sq, add_assoc, sub_eq_add_neg]

/-- G1-orbit-real, exact compensated datum: proves convergence and the
radial theta identity from the actual Gaussian orbit, without assuming
summability. The finite-adelic identification and native ideal remain open. -/
theorem compensatedGaussian_orbit_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => compensatedGaussian (((n : ℝ) + 1) * x))
      (compensatedRationalTheta x / 2) := by
  have h0 := realGaussian_orbit_hasSum x hx
  have h2 := realGaussian_orbit_hasSum (x/2) (by positivity)
  have h4 := realGaussian_orbit_hasSum (x/4) (by positivity)
  have h := ((h0.mul_left (2 : ℂ)).sub (h2.mul_left (3 : ℂ))).add h4
  convert h using 1
  · funext n
    simp only [compensatedGaussian]
    congr 2 <;> congr 1 <;> ring
  · unfold compensatedRationalTheta
    ring

#check compensatedGaussian_orbit_hasSum
#print axioms compensatedGaussian_orbit_hasSum
end Round154E

set_option maxHeartbeats 1000000
namespace Round156E
open MeasureTheory Round154E
/-- G1-polar-real: the concrete compensated Gaussian has both polar
constraints and a genuine finite additive integral. This removes the
uninstantiated Schwartz-map premise for these polar statements only;
adelic Schwartz and native geometric attachment still remain. -/
theorem compensatedGaussian_integrable_polar :
    Integrable compensatedGaussian ∧ compensatedGaussian 0 = 0 ∧
      (∫ x : ℝ, compensatedGaussian x) = 0 := by
  have hi : Integrable realGaussian := by
    simpa only [realGaussian] using
      (integrable_cexp_neg_mul_sq (b := (Real.pi : ℂ))
        (by simpa only [Complex.ofReal_re] using Real.pi_pos))
  have hd (c : ℝ) (hc : 0 < c) :
      Integrable (fun x : ℝ => realGaussian (c*x)) := by
    have heq : (fun x : ℝ => realGaussian (c*x)) =
        (fun x : ℝ => Complex.exp (-((Real.pi*c^2 : ℝ) : ℂ)*(x : ℂ)^2)) := by
      funext x
      unfold realGaussian
      congr 1
      push_cast
      ring
    rw [heq]
    exact integrable_cexp_neg_mul_sq (by
      simpa only [Complex.ofReal_re] using
        mul_pos Real.pi_pos (sq_pos_of_pos hc))
  have hi2 : Integrable (fun x : ℝ => realGaussian ((1/2 : ℝ)*x)) :=
    hd (1/2) (by norm_num)
  have hi4 : Integrable (fun x : ℝ => realGaussian ((1/4 : ℝ)*x)) :=
    hd (1/4) (by norm_num)
  have he (x : ℝ) : compensatedGaussian x =
      2 * realGaussian x - 3 * realGaussian ((1/2 : ℝ)*x) +
        realGaussian ((1/4 : ℝ)*x) := by
    simp only [compensatedGaussian, div_eq_mul_inv, one_mul, mul_comm]
  have hfun : compensatedGaussian = fun x : ℝ =>
      2 * realGaussian x - 3 * realGaussian ((1/2 : ℝ)*x) +
        realGaussian ((1/4 : ℝ)*x) := funext he
  have h2 : (∫ x : ℝ, realGaussian ((1/2 : ℝ)*x)) =
      (2 : ℂ) * ∫ x : ℝ, realGaussian x := by
    rw [Measure.integral_comp_mul_left]
    norm_num [Complex.real_smul]
  have h4 : (∫ x : ℝ, realGaussian ((1/4 : ℝ)*x)) =
      (4 : ℂ) * ∫ x : ℝ, realGaussian x := by
    rw [Measure.integral_comp_mul_left]
    norm_num [Complex.real_smul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact ((hi.const_mul 2).sub (hi2.const_mul 3)).add hi4
  · norm_num [compensatedGaussian, realGaussian]
  · rw [hfun]
    have hsplit := integral_add ((hi.const_mul (2 : ℂ)).sub
      (hi2.const_mul (3 : ℂ))) hi4
    simp only [Pi.sub_apply] at hsplit
    rw [hsplit, integral_sub (hi.const_mul (2 : ℂ)) (hi2.const_mul (3 : ℂ)),
      integral_const_mul, integral_const_mul, h2, h4]
    ring

#check compensatedGaussian_integrable_polar
#print axioms compensatedGaussian_integrable_polar
end Round156E

namespace Round157E
open Round151E
/-- G1-native-moments: a fixed-denominator estimate for the actual theta
seed, used only to derive the native weighted norm in the leading route. -/
theorem rationalTheta_fixed_decay (x : ℝ) (hx : (1/4 : ℝ) ≤ x) :
    ‖rationalTheta x‖ ≤
      (2 / (1 - Real.exp (-Real.pi / 16))) * Real.exp (-Real.pi*x^2) := by
  have hx0 : 0 < x := by linarith
  have hs : (1/16 : ℝ) ≤ x^2 := by nlinarith
  have he : Real.exp (-Real.pi*x^2) ≤ Real.exp (-Real.pi/16) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hd : 0 < 1 - Real.exp (-Real.pi/16) := by
    have := Real.exp_lt_one_iff.mpr (show -Real.pi/16 < 0 by nlinarith [Real.pi_pos])
    linarith
  have hd' : 0 < 1 - Real.exp (-Real.pi*x^2) := by linarith
  calc
    ‖rationalTheta x‖ ≤ gaussianThetaBound x := rationalTheta_norm_le x hx0
    _ ≤ _ := by
      unfold gaussianThetaBound
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Real.exp_pos _))
      apply (div_le_div_iff₀ hd' hd).mpr
      nlinarith

/-- G1-native-moments, positive logarithmic tail of the explicit compensated
seed. Together with the inherited inversion estimate this gives its finite
native weighted norm and all fixed translation moments. It is not S1. -/
theorem compensatedTheta_native_positive_tail (x : ℝ) (hx : 1 ≤ x) :
    ‖compensatedRationalTheta x‖ ≤
      (12 / (1 - Real.exp (-Real.pi / 16))) * Real.exp (-Real.pi*(x/4)^2) := by
  let D : ℝ := 2 / (1 - Real.exp (-Real.pi / 16))
  have hd : 0 ≤ D := by
    dsimp [D]
    apply div_nonneg (by norm_num)
    have := Real.exp_lt_one_iff.mpr (show -Real.pi/16 < 0 by nlinarith [Real.pi_pos])
    linarith
  have h0 := rationalTheta_fixed_decay x (by linarith)
  have h2 := rationalTheta_fixed_decay (x/2) (by linarith)
  have h4 := rationalTheta_fixed_decay (x/4) (by linarith)
  have e0 : Real.exp (-Real.pi*x^2) ≤ Real.exp (-Real.pi*(x/4)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, sq_nonneg x]
  have e2 : Real.exp (-Real.pi*(x/2)^2) ≤ Real.exp (-Real.pi*(x/4)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, sq_nonneg x]
  have h0' : ‖rationalTheta x‖ ≤ D * Real.exp (-Real.pi*(x/4)^2) :=
    h0.trans (mul_le_mul_of_nonneg_left e0 hd)
  have h2' : ‖rationalTheta (x/2)‖ ≤ D * Real.exp (-Real.pi*(x/4)^2) :=
    h2.trans (mul_le_mul_of_nonneg_left e2 hd)
  calc
    ‖compensatedRationalTheta x‖ ≤
        2 * ‖rationalTheta x‖ + 3 * ‖rationalTheta (x/2)‖ +
          ‖rationalTheta (x/4)‖ := by
      unfold compensatedRationalTheta
      calc
        ‖2 * rationalTheta x - 3 * rationalTheta (x/2) + rationalTheta (x/4)‖ ≤
            ‖2 * rationalTheta x - 3 * rationalTheta (x/2)‖ + ‖rationalTheta (x/4)‖ := norm_add_le _ _
        _ ≤ _ := by
          have ht := norm_sub_le (2 * rationalTheta x) (3 * rationalTheta (x/2))
          norm_num [norm_mul] at ht
          linarith
    _ ≤ 6 * D * Real.exp (-Real.pi*(x/4)^2) := by
      change ‖rationalTheta (x/4)‖ ≤ D * Real.exp (-Real.pi*(x/4)^2) at h4
      linarith
    _ = _ := by dsimp [D]; ring
#check compensatedTheta_native_positive_tail
#print axioms compensatedTheta_native_positive_tail
end Round157E

namespace Round158E
open Round151E Round154E Round156E
/-- G1-native-geometric-seed: evenness needed to attach the actual
rational adelic orbit, which includes positive and negative integers. -/
theorem compensatedGaussian_even (x : ℝ) :
    compensatedGaussian (-x) = compensatedGaussian x := by
  simp only [compensatedGaussian, realGaussian, neg_div,
    Complex.ofReal_neg, neg_sq]

/-- G1-native-geometric-seed, full rational integral orbit step.
The sum is derived from the actual compensated Gaussian, not assumed.
The finite adelic and native geometric ideal attachment remain explicit. -/
theorem compensatedGaussian_integer_orbit_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℤ => compensatedGaussian ((n : ℝ)*x))
      (compensatedRationalTheta x) := by
  have hz := compensatedGaussian_integrable_polar.2.1
  have hn : HasSum (fun n : ℕ => compensatedGaussian ((n : ℝ)*x))
      (compensatedRationalTheta x / 2) := by
    have h := (hasSum_nat_add_iff (g := compensatedRationalTheta x / 2)
      (f := fun n : ℕ => compensatedGaussian ((n : ℝ)*x)) 1).mp (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          compensatedGaussian_orbit_hasSum x hx)
    simpa [hz] using h
  have hp : HasSum (fun n : ℕ => compensatedGaussian (((n : ℤ) : ℝ)*x))
      (compensatedRationalTheta x / 2) := by simpa using hn
  have hm : HasSum (fun n : ℕ => compensatedGaussian (((-(n : ℤ)) : ℝ)*x))
      (compensatedRationalTheta x / 2) := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_mul,
      compensatedGaussian_even] using hn
  have h := HasSum.of_nat_of_neg
    (f := fun n : ℤ => compensatedGaussian ((n : ℝ)*x)) hp
      (by simpa only [Int.cast_neg] using hm)
  convert h using 1
  simp only [Int.cast_zero, zero_mul, hz]
  ring
#check compensatedGaussian_integer_orbit_hasSum
#print axioms compensatedGaussian_integer_orbit_hasSum
end Round158E

namespace Round160E
open scoped NumberField
open IsDedekindDomain HeightOneSpectrum
abbrev RationalAdeles := NumberField.AdeleRing (𝓞 ℚ) ℚ
/-- The genuine finite-adelic integral cutoff of the rational seed. -/
def finiteIntegral (z : RationalAdeles) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 ℚ), z.2 v ∈ v.adicCompletionIntegers ℚ
#check HeightOneSpectrum.mem_adicCompletionIntegers
#check HeightOneSpectrum.coe_mem_adicCompletionIntegers
/-- G1-native-geometric-seed: the actual principal rational orbit survives
its finite-adelic integral cutoff exactly at integers. This removes the
finite-support restriction premise; it does not assert nuclearity. -/
theorem genuine_rational_finite_orbit (q : ℚ) :
    finiteIntegral (algebraMap ℚ RationalAdeles q) ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    have hv : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q ≤ 1 := by
      intro v
      have hh := h v
      simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using hh
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q hv
    obtain ⟨n, hn⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) r
    refine ⟨n, ?_⟩
    rw [← hn] at hr
    simpa using hr
  · rintro ⟨n, rfl⟩ v
    change (algebraMap ℚ (v.adicCompletion ℚ) (n : ℚ)) ∈ v.adicCompletionIntegers ℚ
    simpa only [map_intCast] using (intCast_mem (v.adicCompletionIntegers ℚ) n)
#check genuine_rational_finite_orbit
#print axioms genuine_rational_finite_orbit
end Round160E

namespace Round161E
open Round151E Round154E Round158E Round160E
/-- Actual principal-rational finite-adelic cutoff term of the compensated
seed. G1-native-geometric-seed requires identifying this orbit. -/
noncomputable def rationalCutoffTerm (x : ℝ) (q : ℚ) : ℂ := by
  classical
  exact if finiteIntegral (algebraMap ℚ RationalAdeles q) then
    compensatedGaussian ((q : ℝ)*x) else 0

/-- G1-native-geometric-seed / Q-finite-orbit: attaches the convergent
integer sum to the actual finite-integrality cutoff over all rationals.
Schwartz-Bruhat and native geometric membership remain separate premises. -/
theorem genuine_rational_cutoff_orbit_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (rationalCutoffTerm x) (compensatedRationalTheta x) := by
  classical
  have hi : Function.Injective (fun n : ℤ => (n : ℚ)) := Int.cast_injective
  have hz : ∀ q ∉ Set.range (fun n : ℤ => (n : ℚ)),
      rationalCutoffTerm x q = 0 := by
    intro q hq
    unfold rationalCutoffTerm
    apply if_neg
    intro hf
    exact hq ((genuine_rational_finite_orbit q).mp hf)
  have hs : HasSum (rationalCutoffTerm x ∘ (fun n : ℤ => (n : ℚ)))
      (compensatedRationalTheta x) := by
    convert compensatedGaussian_integer_orbit_hasSum x hx using 1
    funext n
    have hf : finiteIntegral (algebraMap ℚ RationalAdeles (n : ℚ)) :=
      (genuine_rational_finite_orbit (n : ℚ)).mpr ⟨n, rfl⟩
    simp only [Function.comp_apply, rationalCutoffTerm, if_pos hf, Rat.cast_intCast]
  exact (hi.hasSum_iff hz).mp hs
#check genuine_rational_cutoff_orbit_hasSum
#print axioms genuine_rational_cutoff_orbit_hasSum
/-- The actual multiplicative rational indexing of Phi_Q: the zero term
is removed using the proved polar condition, not by assuming convergence. -/
theorem genuine_rational_unit_cutoff_orbit_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun u : ℚˣ => rationalCutoffTerm x (u : ℚ))
      (compensatedRationalTheta x) := by
  classical
  have hz : ∀ q ∉ Set.range (fun u : ℚˣ => (u : ℚ)),
      rationalCutoffTerm x q = 0 := by
    intro q hq
    have hq0 : q = 0 := by
      by_contra h
      exact hq ⟨Units.mk0 q h, rfl⟩
    subst q
    simp [rationalCutoffTerm, Round156E.compensatedGaussian_integrable_polar.2.1]
  exact (Units.val_injective.hasSum_iff hz).mpr
    (genuine_rational_cutoff_orbit_hasSum x hx)
#check genuine_rational_unit_cutoff_orbit_hasSum
#print axioms genuine_rational_unit_cutoff_orbit_hasSum
/-- The finite cutoff is unchanged by a genuine adelic unit integral
with integral inverse at every finite place. This supplies the finite-unit
uniformity of G1-native-geometric-seed in the rational case. -/
theorem genuine_finite_unit_cutoff (u : RationalAdelesˣ)
    (hu : finiteIntegral (u : RationalAdeles))
    (hui : finiteIntegral ((u⁻¹ : RationalAdelesˣ) : RationalAdeles)) (q : ℚ) :
    finiteIntegral (algebraMap ℚ RationalAdeles q * (u : RationalAdeles)) ↔
      ∃ n : ℤ, (n : ℚ) = q := by
  have hm {z z' : RationalAdeles} (hz : finiteIntegral z)
      (hz' : finiteIntegral z') : finiteIntegral (z*z') := by
    intro v
    change z.2 v * z'.2 v ∈ v.adicCompletionIntegers ℚ
    exact mul_mem (hz v) (hz' v)
  rw [← genuine_rational_finite_orbit]
  constructor
  · intro h
    have hh := hm h hui
    simpa only [mul_assoc, Units.mul_inv, mul_one] using hh
  · intro h
    exact hm h hu
#check genuine_finite_unit_cutoff
#print axioms genuine_finite_unit_cutoff
end Round161E

namespace Round163E
open Round151E Round154E Round160E Round161E
open NumberField

/-- The actual real-place coordinate of a rational adele. -/
def realArch (v : InfinitePlace ℚ) (hv : v.IsReal) (z : RationalAdeles) : ℝ :=
  InfinitePlace.Completion.extensionEmbeddingOfIsReal hv (z.1 v)

theorem realArch_principal_mul (v : InfinitePlace ℚ) (hv : v.IsReal)
    (q : ℚ) (z : RationalAdeles) :
    realArch v hv (algebraMap ℚ RationalAdeles q * z) =
      (q : ℝ) * realArch v hv z := by
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
    (((algebraMap ℚ (InfiniteAdeleRing ℚ) q) v) * z.1 v) = _
  rw [map_mul, InfiniteAdeleRing.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe]
  simp [realArch]

/-- Literal adelic tensor function for G1-native-geometric-seed.
Its Schwartz-Bruhat membership is a separate unresolved obligation. -/
def adelicSeed (v : InfinitePlace ℚ) (hv : v.IsReal) (z : RationalAdeles) : ℂ := by
  classical
  exact if finiteIntegral z then compensatedGaussian (realArch v hv z) else 0

/-- G1-adelic-orbit attachment: on an actual idele integral with integral
inverse at every finite place, the full principal rational orbit of the
literal adelic seed is the previously derived compensated theta series.
This discharges the tensor evaluation/orbit identification premise only;
Schwartz-Bruhat membership, native range, and projected nuclear cost remain. -/
theorem genuine_adelic_seed_orbit_hasSum (v : InfinitePlace ℚ) (hv : v.IsReal)
    (u : RationalAdelesˣ) (hu : finiteIntegral (u : RationalAdeles))
    (hui : finiteIntegral ((u⁻¹ : RationalAdelesˣ) : RationalAdeles))
    (hx : 0 < realArch v hv (u : RationalAdeles)) :
    HasSum (fun q : ℚˣ => adelicSeed v hv
      (algebraMap ℚ RationalAdeles (q : ℚ) * (u : RationalAdeles)))
      (compensatedRationalTheta (realArch v hv (u : RationalAdeles))) := by
  classical
  convert genuine_rational_unit_cutoff_orbit_hasSum
    (realArch v hv (u : RationalAdeles)) hx using 1
  funext q
  unfold adelicSeed rationalCutoffTerm
  rw [genuine_finite_unit_cutoff u hu hui, genuine_rational_finite_orbit,
    realArch_principal_mul]

#check genuine_adelic_seed_orbit_hasSum
#print axioms genuine_adelic_seed_orbit_hasSum

/-- Actual principal-rational periodization. On the normalized ideles
above its convergence is proved, rather than supplied as a hypothesis. -/
def adelicTheta (v : InfinitePlace ℚ) (hv : v.IsReal) (z : RationalAdeles) : ℂ :=
  ∑' q : ℚˣ, adelicSeed v hv (algebraMap ℚ RationalAdeles (q : ℚ) * z)

/-- G1-quotient descent: the literal seed periodization is unchanged by
the actual principal rational action. This is the representative
independence needed before native geometric membership can be asserted. -/
theorem genuine_adelic_theta_principal_invariant (v : InfinitePlace ℚ)
    (hv : v.IsReal) (r : ℚˣ) (z : RationalAdeles) :
    adelicTheta v hv (algebraMap ℚ RationalAdeles (r : ℚ) * z) =
      adelicTheta v hv z := by
  unfold adelicTheta
  have he (q : ℚˣ) :
      algebraMap ℚ RationalAdeles (q : ℚ) *
        (algebraMap ℚ RationalAdeles (r : ℚ) * z) =
      algebraMap ℚ RationalAdeles ((q * r : ℚˣ) : ℚ) * z := by
    rw [Units.val_mul, map_mul, mul_assoc]
  simp_rw [he]
  exact (Equiv.mulRight r).tsum_eq
    (fun q : ℚˣ => adelicSeed v hv (algebraMap ℚ RationalAdeles (q : ℚ) * z))

#check genuine_adelic_theta_principal_invariant
#print axioms genuine_adelic_theta_principal_invariant
end Round163E
