import Mathlib

/-! Direct analysis of the coefficient norm in manuscript Proposition 10.2.2.2.
After logarithmic Haar disintegration the squared dual norm is the positive
Haar scalar times the integral of `jetDensity`. This file proves an explicit
lower bound on its [2,3] contribution. It does not assert global nuclearity.
-/

namespace NuclearBoundH88

noncomputable def jetDensity (alpha b s : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (2 * b * u - 2 * alpha * |u|) * u ^ (2 * m) /
    (1 + u ^ 2) ^ (s / 2)

/-- A fixed positive logarithmic slab already forces exponential jet growth.
The bound is uniform over b in [-alpha,alpha]; no spectral multiplicity bound
or uniform coefficient norm is assumed. -/
theorem jetDensity_slab_lower (alpha b s : ℝ) (m : ℕ)
    (ha : 0 ≤ alpha) (hb : -alpha ≤ b) (hs : 0 ≤ s)
    (u : ℝ) (hu : u ∈ Set.Icc (2 : ℝ) 3) :
    Real.exp (-12 * alpha) * (4 : ℝ) ^ m / (10 : ℝ) ^ (s / 2) ≤
      jetDensity alpha b s m u := by
  have hu0 : 0 ≤ u := by linarith [hu.1]
  have hexp : -12 * alpha ≤ 2 * b * u - 2 * alpha * |u| := by
    rw [abs_of_nonneg hu0]
    have h1 : 0 ≤ (b + alpha) * u := mul_nonneg (by linarith) hu0
    have h2 : 0 ≤ alpha * (3 - u) := mul_nonneg ha (by linarith [hu.2])
    nlinarith
  have hu2 : (4 : ℝ) ≤ u ^ 2 := by nlinarith [hu.1]
  have hp : (4 : ℝ) ^ m ≤ u ^ (2 * m) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) hu2 m
  have hn : Real.exp (-12 * alpha) * (4 : ℝ) ^ m ≤
      Real.exp (2 * b * u - 2 * alpha * |u|) * u ^ (2 * m) :=
    mul_le_mul (Real.exp_le_exp.mpr hexp) hp (by positivity) (by positivity)
  have hd : (1 + u ^ 2) ^ (s / 2) ≤ (10 : ℝ) ^ (s / 2) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    nlinarith [hu.1, hu.2]
  unfold jetDensity
  exact div_le_div₀ (by positivity) hn (by positivity) hd

theorem jetDensity_continuous (alpha b s : ℝ) (m : ℕ) (hs : 0 ≤ s) :
    Continuous (jetDensity alpha b s m) := by
  unfold jetDensity
  apply Continuous.div
  · fun_prop
  · fun_prop (disch := positivity)
  · intro u
    exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)

/-- An unconditional, finite-slab contribution to the actual coefficient
norm formula. Haar normalization multiplies both sides by its positive scalar. -/
theorem jetDensity_integral_slab_lower (alpha b s : ℝ) (m : ℕ)
    (ha : 0 ≤ alpha) (hb : -alpha ≤ b) (hs : 0 ≤ s) :
    Real.exp (-12 * alpha) * (4 : ℝ) ^ m / (10 : ℝ) ^ (s / 2) ≤
      ∫ u in (2 : ℝ)..3, jetDensity alpha b s m u := by
  calc
    _ = ∫ _u in (2 : ℝ)..3,
        Real.exp (-12 * alpha) * (4 : ℝ) ^ m / (10 : ℝ) ^ (s / 2) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      norm_num
    _ ≤ _ := intervalIntegral.integral_mono_on (by norm_num)
      (intervalIntegrable_const) ((jetDensity_continuous alpha b s m hs).intervalIntegrable 2 3)
      (fun u hu => jetDensity_slab_lower alpha b s m ha hb hs u hu)

/-- A direct alternative upper majorant retains the distance delta to the
strip boundary, rather than suppressing that dependence in a constant. -/
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

/-- This obstruction concerns unrestricted jet orders; it makes no assertion
that the genuine spectral multiplicities are unbounded. -/
theorem jetDensity_slab_no_uniform_jet_bound (alpha b s : ℝ)
    (ha : 0 ≤ alpha) (hb : -alpha ≤ b) (hs : 0 ≤ s) :
    ¬ ∃ C : ℝ, ∀ m : ℕ, (∫ u in (2 : ℝ)..3, jetDensity alpha b s m u) ≤ C := by
  intro ⟨C, hC⟩
  let c : ℝ := Real.exp (-12 * alpha) / (10 : ℝ) ^ (s / 2)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (C / c)
  have hp : ∀ m : ℕ, (m : ℝ) + 1 ≤ (4 : ℝ) ^ m := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [pow_succ]
      push_cast
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
  have hlow := jetDensity_integral_slab_lower alpha b s n ha hb hs
  have hlow' : c * (4 : ℝ) ^ n ≤ C := by
    calc
      _ = Real.exp (-12 * alpha) * (4 : ℝ) ^ n / (10 : ℝ) ^ (s / 2) := by
        dsimp [c]; ring
      _ ≤ _ := hlow.trans (hC n)
  have hn' : C < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have hpn := mul_le_mul_of_nonneg_left (hp n) (le_of_lt hc)
  nlinarith

#check jetDensity_slab_lower
#print axioms jetDensity_slab_lower
#check jetDensity_integral_slab_lower
#print axioms jetDensity_integral_slab_lower
#check jetDensity_interior_upper
#print axioms jetDensity_interior_upper
#check jetDensity_slab_no_uniform_jet_bound
#print axioms jetDensity_slab_no_uniform_jet_bound

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


/- Direct necessary bounds on the manuscript's actual biorthogonal lifts.
   These do not establish nuclearity or supply an upper lift bound. -/
namespace Round90E

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem biorthogonal_lift_separation
    (eta theta : H →L[ℂ] ℂ) (u : H)
    (heta : eta u = 1) (htheta : theta u = 0) :
    1 ≤ ‖eta - theta‖ * ‖u‖ := by
  have h := (eta - theta).le_opNorm u
  simpa [heta, htheta] using h

theorem biorthogonal_lift_relative_conditioning
    (eta theta : H →L[ℂ] ℂ) (u : H) (eps : ℝ)
    (heta : eta u = 1) (htheta : theta u = 0)
    (hclose : ‖eta - theta‖ ≤ eps * ‖eta‖) :
    1 ≤ eps * (‖u‖ * ‖eta‖) := by
  calc
    1 ≤ ‖eta - theta‖ * ‖u‖ :=
      biorthogonal_lift_separation eta theta u heta htheta
    _ ≤ (eps * ‖eta‖) * ‖u‖ :=
      mul_le_mul_of_nonneg_right hclose (norm_nonneg u)
    _ = eps * (‖u‖ * ‖eta‖) := by ring

theorem phase_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ 2 * |x| := by
  by_cases hx : |x| ≤ 1
  · have hz : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
    simpa using Complex.norm_exp_sub_one_le hz
  · calc
      _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [Complex.norm_exp_ofReal_mul_I]
      _ ≤ 2 * |x| := by linarith

theorem phase_difference_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
      Complex.exp ((y : ℂ) * Complex.I)‖ ≤ 2 * |x-y| := by
  have he : (x : ℂ) * Complex.I =
      ((x-y : ℝ) : ℂ) * Complex.I + (y : ℂ) * Complex.I := by
    push_cast; ring
  rw [he, Complex.exp_add]
  have hf : Complex.exp (((x-y : ℝ) : ℂ) * Complex.I) *
      Complex.exp ((y : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
      (Complex.exp (((x-y : ℝ) : ℂ) * Complex.I) - 1) *
        Complex.exp ((y : ℂ) * Complex.I) := by ring
  rw [hf, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact phase_sub_one_le (x-y)

end Round90E
#check Round90E.biorthogonal_lift_separation
#print axioms Round90E.biorthogonal_lift_separation
#check Round90E.biorthogonal_lift_relative_conditioning
#print axioms Round90E.biorthogonal_lift_relative_conditioning

#check Round90E.phase_difference_le
#print axioms Round90E.phase_difference_le

namespace Round90E
open MeasureTheory NuclearBoundH88 NuclearBoundH89

noncomputable def coefficientDifferenceDensity (alpha b s t v u : ℝ) : ℝ :=
  ‖Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) -
    Complex.exp (((v*u : ℝ) : ℂ) * Complex.I)‖ ^ 2 *
    Real.exp (2*b*u - 2*alpha*|u|) / (1+u^2)^(s/2)

theorem coefficientDifferenceDensity_le (alpha b s t v u : ℝ) :
    coefficientDifferenceDensity alpha b s t v u ≤
      (4*(t-v)^2) * jetDensity alpha b s 1 u := by
  have hp := phase_difference_le (t*u) (v*u)
  rw [← sub_mul, abs_mul] at hp
  have hsq : ‖Complex.exp (((t*u : ℝ) : ℂ) * Complex.I) -
    Complex.exp (((v*u : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      4*(t-v)^2*u^2 := by
    calc
      _ ≤ (2 * (|t-v| * |u|))^2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      _ = _ := by simp only [mul_pow, sq_abs]; norm_num; ring
  unfold coefficientDifferenceDensity jetDensity
  have hd : 0 < (1+u^2)^(s/2) := Real.rpow_pos_of_pos (by positivity) _
  calc
    _ ≤ (4*(t-v)^2*u^2) * Real.exp (2*b*u-2*alpha*|u|) /
      (1+u^2)^(s/2) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq (le_of_lt (Real.exp_pos _))) (le_of_lt hd)
    _ = _ := by norm_num; ring

theorem coefficientDifferenceDensity_integral_bound
    (alpha b s delta t v : ℝ) (hs : 0 ≤ s) (hd : 0 < delta)
    (hmargin : |b| + delta ≤ alpha) :
    Integrable (coefficientDifferenceDensity alpha b s t v) ∧
    (∫ u : ℝ, coefficientDifferenceDensity alpha b s t v u) ≤
      (4*(t-v)^2) * (2 * ((2 : ℕ).factorial : ℝ) / (2*delta)^3) := by
  obtain ⟨hj, hb⟩ := jetDensity_integrable_bound alpha b s delta 1 hs hd hmargin
  have hi := hj.const_mul (4*(t-v)^2)
  have hc : Continuous (coefficientDifferenceDensity alpha b s t v) := by
    unfold coefficientDifferenceDensity
    apply Continuous.div
    · fun_prop
    · fun_prop (disch := positivity)
    · intro u; exact ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)
  have hn : ∀ u, 0 ≤ coefficientDifferenceDensity alpha b s t v u := by
    intro u; unfold coefficientDifferenceDensity; positivity
  have hk : Integrable (coefficientDifferenceDensity alpha b s t v) :=
    hi.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn u)]
      exact coefficientDifferenceDensity_le alpha b s t v u))
  refine ⟨hk, ?_⟩
  calc
    _ ≤ ∫ u : ℝ, (4*(t-v)^2) * jetDensity alpha b s 1 u :=
      integral_mono hk hi (coefficientDifferenceDensity_le alpha b s t v)
    _ = (4*(t-v)^2) * ∫ u : ℝ, jetDensity alpha b s 1 u := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa using hb) (by positivity)

end Round90E
#check Round90E.coefficientDifferenceDensity_le
#print axioms Round90E.coefficientDifferenceDensity_le
#check Round90E.coefficientDifferenceDensity_integral_bound
#print axioms Round90E.coefficientDifferenceDensity_integral_bound
