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

namespace NuclearBoundH90
open MeasureTheory NuclearBoundH88

/-- Boundary-safe majorant for the scalar density of the actual coefficient
norm. The Sobolev cost grows explicitly with the jet order. -/
theorem jetDensity_boundary_cauchy_domination (alpha b s : ℝ) (m : ℕ)
    (hb : |b| ≤ alpha) (hs : 2 * (m : ℝ) + 2 ≤ s) (u : ℝ) :
    jetDensity alpha b s m u ≤ (1 + u ^ 2)⁻¹ := by
  have hbu : b * u ≤ |b| * |u| := by
    simpa only [abs_mul] using le_abs_self (b * u)
  have hm : |b| * |u| ≤ alpha * |u| :=
    mul_le_mul_of_nonneg_right hb (abs_nonneg u)
  have he : Real.exp (2 * b * u - 2 * alpha * |u|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith)
  have hu : 0 < 1 + u ^ 2 := by positivity
  have hpow : 0 ≤ u ^ (2 * m) := by rw [pow_mul]; positivity
  have hp : u ^ (2 * m) ≤ (1 + u ^ 2) ^ m := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg u) (by linarith) m
  have hd : (1 + u ^ 2) ^ (m + 1) ≤ (1 + u ^ 2) ^ (s / 2) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg u])
    push_cast
    linarith
  have hn : Real.exp (2 * b * u - 2 * alpha * |u|) * u ^ (2 * m) ≤
      (1 + u ^ 2) ^ m := by
    calc
      _ ≤ 1 * u ^ (2 * m) := mul_le_mul_of_nonneg_right he hpow
      _ ≤ _ := by simpa only [one_mul] using hp
  unfold jetDensity
  calc
    _ ≤ (1 + u ^ 2) ^ m / (1 + u ^ 2) ^ (m + 1) :=
      div_le_div₀ (by positivity) hn (by positivity) hd
    _ = _ := by rw [pow_succ]; field_simp; ring

/-- Uniform strip-boundary integrability, with no assumed integrability or
summability. This controls the dual factor only; actual lift bounds remain. -/
theorem jetDensity_boundary_integrable_bound (alpha b s : ℝ) (m : ℕ)
    (hb : |b| ≤ alpha) (hs : 2 * (m : ℝ) + 2 ≤ s) :
    Integrable (jetDensity alpha b s m) ∧
    (∫ u : ℝ, jetDensity alpha b s m u) ≤
      ∫ u : ℝ, (1 + u ^ 2)⁻¹ := by
  have hs0 : 0 ≤ s := by have hm := Nat.cast_nonneg (α := ℝ) m; linarith
  have hn : ∀ u : ℝ, 0 ≤ jetDensity alpha b s m u := by
    intro u
    unfold jetDensity
    have hp : 0 ≤ u ^ (2 * m) := by rw [pow_mul]; positivity
    exact div_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hp)
      (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have hi : Integrable (jetDensity alpha b s m) :=
    integrable_inv_one_add_sq.mono'
      (jetDensity_continuous alpha b s m hs0).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hn u)]
        exact jetDensity_boundary_cauchy_domination alpha b s m hb hs u))
  exact ⟨hi, integral_mono hi integrable_inv_one_add_sq
    (jetDensity_boundary_cauchy_domination alpha b s m hb hs)⟩

#check jetDensity_boundary_cauchy_domination
#print axioms jetDensity_boundary_cauchy_domination
#check jetDensity_boundary_integrable_bound
#print axioms jetDensity_boundary_integrable_bound
end NuclearBoundH90

namespace NuclearBoundH90
open MeasureTheory NuclearBoundH88

/-- Explicit finite bound for the coefficient factor, valid up to the strip
boundary. The actual squared coefficient norm is this mass times Haar volume,
after the independently required genuine norm-transport theorem. -/
theorem jetDensity_boundary_integrable_pi (alpha b s : ℝ) (m : ℕ)
    (hb : |b| ≤ alpha) (hs : 2 * (m : ℝ) + 2 ≤ s) :
    Integrable (jetDensity alpha b s m) ∧
    (∫ u : ℝ, jetDensity alpha b s m u) ≤ Real.pi := by
  obtain ⟨hi, hbnd⟩ := jetDensity_boundary_integrable_bound alpha b s m hb hs
  exact ⟨hi, hbnd.trans_eq integral_univ_inv_one_add_sq⟩

/-- At even integral Sobolev degree, every allowed boundary jet m<d has the
same scalar bound. Neither d nor m is hidden inside the bound. -/
theorem jetDensity_boundary_integer_degree (alpha b : ℝ) (d m : ℕ)
    (hb : |b| ≤ alpha) (hm : m < d) :
    Integrable (jetDensity alpha b (2 * (d : ℝ)) m) ∧
    (∫ u : ℝ, jetDensity alpha b (2 * (d : ℝ)) m u) ≤ Real.pi := by
  apply jetDensity_boundary_integrable_pi alpha b (2 * (d : ℝ)) m hb
  have hmd : (m : ℝ) + 1 ≤ d := by exact_mod_cast hm
  linarith

#check jetDensity_boundary_integrable_pi
#print axioms jetDensity_boundary_integrable_pi
#check jetDensity_boundary_integer_degree
#print axioms jetDensity_boundary_integer_degree
end NuclearBoundH90
