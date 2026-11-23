import Mathlib

set_option linter.unusedSimpArgs false

open scoped ComplexInnerProductSpace

namespace Round183H

/-- The resolvent identity converts the native generator's numerical-range
bound into a squared-column bound. It does not assume any nuclearity. -/
theorem native_resolvent_column_coercivity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (D R : E →L[ℂ] E) (c b : ℝ)
    (hD : ∀ v : E, (inner ℂ v (D v)).re ≤ b * ‖v‖ ^ 2)
    (hR : ∀ v : E, (c : ℂ) • R v - D (R v) = v) (v : E) :
    (c - b) * ‖R v‖ ^ 2 ≤ (inner ℂ (R v) v).re := by
  have heq : (inner ℂ (R v) v).re =
      c * ‖R v‖ ^ 2 - (inner ℂ (R v) (D (R v))).re := by
    calc
      (inner ℂ (R v) v).re =
          (inner ℂ (R v) ((c : ℂ) • R v - D (R v))).re :=
        congrArg (fun w : E => (inner ℂ (R v) w).re) (hR v).symm
      _ = c * ‖R v‖ ^ 2 - (inner ℂ (R v) (D (R v))).re := by
        simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq, pow_two, Complex.mul_re]
  rw [heq]
  nlinarith [hD (R v)]

/-- Applied to an orthonormal basis of the actual full spectral window,
this bounds the Hilbert--Schmidt resolvent norm by the real resolvent trace.
All inverse Gram factors remain inside R and are controlled at once. -/
theorem whole_window_resolvent_coercivity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {ι : Type*} [Fintype ι] (e : ι → E)
    (D R : E →L[ℂ] E) (c b : ℝ)
    (hD : ∀ v : E, (inner ℂ v (D v)).re ≤ b * ‖v‖ ^ 2)
    (hR : ∀ v : E, (c : ℂ) • R v - D (R v) = v) :
    (c - b) * (∑ j, ‖R (e j)‖ ^ 2) ≤
      ∑ j, (inner ℂ (R (e j)) (e j)).re := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    native_resolvent_column_coercivity D R c b hD hR (e j)

end Round183H

#check Round183H.native_resolvent_column_coercivity
#print axioms Round183H.native_resolvent_column_coercivity
#check Round183H.whole_window_resolvent_coercivity
#print axioms Round183H.whole_window_resolvent_coercivity

namespace Round184H

/-- Comparison with the positive completed-Hecke zero weight at 2.
This is the arithmetic weight used in GLOBAL_ESTIMATE.md, not a
supposition that any spectral series converges. -/
theorem completed_zero_weight_dominates_native_frequency
    (b t : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    1 / (1 + t ^ 2) ≤ 2 * ((2 - b) / ((2 - b) ^ 2 + t ^ 2)) := by
  have hd : 0 < (2 - b) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have ht : 0 < 1 + t ^ 2 := by positivity
  have hb : b * (2 - b) ≥ 0 := mul_nonneg hb0 (by linarith)
  have hx : (3 - 2 * b) * t ^ 2 ≥ 0 :=
    mul_nonneg (by linarith) (sq_nonneg t)
  apply (div_le_iff₀ ht).2
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).2
  nlinarith

/-- The finite multiplicity-weighted comparison is uniform in the window.
Its infinite use additionally requires the canonical-product derivation
in GLOBAL_ESTIMATE.md, which is not an axiom of this theorem. -/
theorem native_zero_window_le_completed_weight
    {ι : Type*} (J : Finset ι) (b t w : ι → ℝ)
    (hb0 : ∀ j ∈ J, 0 ≤ b j) (hb1 : ∀ j ∈ J, b j ≤ 1)
    (hw : ∀ j ∈ J, 0 ≤ w j) :
    (∑ j ∈ J, w j / (1 + (t j) ^ 2)) ≤
      2 * ∑ j ∈ J, w j * ((2 - b j) / ((2 - b j) ^ 2 + (t j) ^ 2)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_left
    (completed_zero_weight_dominates_native_frequency (b j) (t j)
      (hb0 j hj) (hb1 j hj)) (hw j hj)
  simpa only [mul_one_div, mul_left_comm, mul_assoc] using h

end Round184H

#check Round184H.native_zero_window_le_completed_weight
#print axioms Round184H.native_zero_window_le_completed_weight

/-! Round 187 H: the concrete finite-dilation seed used on the original
adelic Schwartz space. For T = rho(y), |y| = exp(1), the two covariance
identities below are exactly evaluation at zero and the additive integral.
For the measured zeta functional Z, r = chi(y) * |y|^w. No derivative of
an adelic Schwartz representation, nuclearity, or summability is assumed.
The native instantiation and added zero lattices are derived in
GLOBAL_ESTIMATE.md; this certificate checks precisely the seed algebra. -/
namespace Round187H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def finiteDilationSeed (T : Module.End ℂ V) (q : ℂ) (f : V) : V :=
  T (T f) - (1 + q) • T f + q • f

/-- The actual S_0 defining moments vanish, and its Mellin multiplier is
explicit. The covariance hypotheses are local change-of-variable laws,
not the target nuclearity or an equivalent global estimate. -/
theorem finite_dilation_seed_moments_and_mellin
    (T : Module.End ℂ V) (d0 d1 Z : V →ₗ[ℂ] ℂ) (q r : ℂ)
    (h0 : ∀ f, d0 (T f) = d0 f)
    (h1 : ∀ f, d1 (T f) = q * d1 f)
    (hZ : ∀ f, Z (T f) = r * Z f) (f : V) :
    finiteDilationSeed T q f ∈ d0.ker ⊓ d1.ker ∧
      Z (finiteDilationSeed T q f) = (r - 1) * (r - q) * Z f := by
  have hz0 : d0 (finiteDilationSeed T q f) = 0 := by
    simp only [finiteDilationSeed, map_add, map_sub, map_smul, h0,
      smul_eq_mul]
    ring
  have hz1 : d1 (finiteDilationSeed T q f) = 0 := by
    simp only [finiteDilationSeed, map_add, map_sub, map_smul, h1,
      smul_eq_mul]
    ring
  constructor
  · exact ⟨hz0, hz1⟩
  · simp only [finiteDilationSeed, map_add, map_sub, map_smul, hZ,
      smul_eq_mul]
    ring

#check finite_dilation_seed_moments_and_mellin
#print axioms finite_dilation_seed_moments_and_mellin
end Round187H


/-! Round 188 H. The two finite-dilation seeds with log steps 1 and sqrt(2)
have disjoint nonzero period lattices. This is the new divisor-removal
premise in the native geometric-annihilator resolvent construction.
It is not a nuclearity assertion. -/
namespace Round188H

theorem irrational_dilation_periods
    (m n : ℤ) (h : Real.sqrt 2 * (m : ℝ) = (n : ℝ)) :
    m = 0 ∧ n = 0 := by
  have hm : m = 0 := by
    by_contra hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have heq : Real.sqrt 2 = (((n : ℚ) / (m : ℚ) : ℚ) : ℝ) := by
      push_cast
      exact (eq_div_iff hm').2 h
    exact irrational_sqrt_two.ne_rat _ heq
  refine ⟨hm, ?_⟩
  subst m
  simp only [Int.cast_zero, mul_zero] at h
  exact_mod_cast h.symm

#check irrational_dilation_periods
#print axioms irrational_dilation_periods
end Round188H

/-! Round 190 H. The averaged canonical-product head loss used in the
native horizontal resolvent estimate is 48 + 3 R / |rho| per root.
This theorem controls that precise loss by the reciprocal-square zero
moment, retaining arbitrary true multiplicities. The averaging and native
contour attachment are derived in GLOBAL_ESTIMATE.md, not assumed here. -/
namespace Round190H

theorem canonical_head_loss_le_square_weight
    (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (hrR : r ≤ 6 * R) :
    48 + 3 * R / r ≤ 1746 * R ^ 2 / r ^ 2 := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hs : r ^ 2 ≤ 36 * R ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 6 * R - r)
      (by linarith : 0 ≤ 6 * R + r)]
  have hm : R * r ≤ 6 * R ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hrR hR]
  apply (le_div_iff₀ hr2).2
  have he : (48 + 3 * R / r) * r ^ 2 = 48 * r ^ 2 + 3 * R * r := by
    field_simp
  rw [he]
  nlinarith

theorem native_contour_head_loss_le_zero_square_tail
    {ι : Type*} (J : Finset ι) (rho : ι → ℂ) (mult : ι → ℕ)
    (R : ℝ) (hR : 0 ≤ R)
    (hzero : ∀ j ∈ J, rho j ≠ 0)
    (hradius : ∀ j ∈ J, ‖rho j‖ ≤ 6 * R) :
    (∑ j ∈ J, (mult j : ℝ) * (48 + 3 * R / ‖rho j‖)) ≤
      1746 * R ^ 2 * ∑ j ∈ J, (mult j : ℝ) / ‖rho j‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := mul_le_mul_of_nonneg_left
    (canonical_head_loss_le_square_weight R ‖rho j‖ hR
      (norm_pos_iff.mpr (hzero j hj)) (hradius j hj))
    (Nat.cast_nonneg (mult j) : (0 : ℝ) ≤ (mult j : ℝ))
  convert h using 1
  ring

#check native_contour_head_loss_le_zero_square_tail
#print axioms native_contour_head_loss_le_zero_square_tail
end Round190H

namespace Round189H

/-- Quantitative separation of the two actual finite-dilation seed periods.
Used to bound the joint seed denominator in the native resolvent, not to
assert spectral summability or nuclearity. -/
theorem two_seed_integer_separation (m n : ℤ) (hm : m ≠ 0) :
    1 ≤ |Real.sqrt 2 * (m : ℝ) - (n : ℝ)| *
      (Real.sqrt 2 * |(m : ℝ)| + |(n : ℝ)|) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hgap : (2 * m ^ 2 - n ^ 2 : ℤ) ≠ 0 := by
    intro hz
    have hz' : (2 : ℝ) * (m : ℝ) ^ 2 - (n : ℝ) ^ 2 = 0 := by
      exact_mod_cast hz
    have he : (Real.sqrt 2 * (m : ℝ)) ^ 2 = (n : ℝ) ^ 2 := by
      nlinarith [hs]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 he with h | h
    · exact hm (Round188H.irrational_dilation_periods m n h).1
    · have hn : Real.sqrt 2 * (m : ℝ) = ((-n : ℤ) : ℝ) := by
        simpa using h
      exact hm (Round188H.irrational_dilation_periods m (-n) hn).1
  have hgap1 : (1 : ℤ) ≤ |2 * m ^ 2 - n ^ 2| := by
    have := abs_pos.mpr hgap
    omega
  have hr : (1 : ℝ) ≤ |2 * (m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
    exact_mod_cast hgap1
  have hf : 2 * (m : ℝ) ^ 2 - (n : ℝ) ^ 2 =
      (Real.sqrt 2 * (m : ℝ) - (n : ℝ)) *
      (Real.sqrt 2 * (m : ℝ) + (n : ℝ)) := by
    nlinarith [hs]
  rw [hf, abs_mul] at hr
  apply hr.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    |Real.sqrt 2 * (m : ℝ) + (n : ℝ)| ≤
        |Real.sqrt 2 * (m : ℝ)| + |(n : ℝ)| := by
          simpa only [Real.norm_eq_abs] using
            (norm_add_le (Real.sqrt 2 * (m : ℝ)) (n : ℝ))
    _ = Real.sqrt 2 * |(m : ℝ)| + |(n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]

#check two_seed_integer_separation
#print axioms two_seed_integer_separation
end Round189H


namespace Round188H

/-- Precisely the additional zeros of the pole-cleared finite-dilation
multiplier, after its removable points 0 and 1 are filled in. -/
def extraDilationZero (step : ℝ) (z : ℂ) : Prop :=
  (z.re = 0 ∨ z.re = 1) ∧
    ∃ n : ℤ, n ≠ 0 ∧ z.im = 2 * Real.pi * (n : ℝ) / step

/-- The original completed divisor is the entire common divisor of the
two actual trivial-character seed symbols. This statement checks the
only extra-lattice obstruction, not the native resolvent attachment. -/
theorem trivial_seed_extra_lattices_disjoint (z : ℂ) :
    ¬ (extraDilationZero 1 z ∧ extraDilationZero (Real.sqrt 2) z) := by
  rintro ⟨⟨_, m, hm, hz1⟩, ⟨_, n, _, hz2⟩⟩
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hfreq : 2 * Real.pi * (m : ℝ) =
      2 * Real.pi * (n : ℝ) / Real.sqrt 2 := by
    simpa only [div_one] using hz1.symm.trans hz2
  have hmul := (eq_div_iff hs).1 hfreq
  have hp : 2 * Real.pi ≠ 0 := ne_of_gt (by positivity)
  have hper : Real.sqrt 2 * (m : ℝ) = (n : ℝ) := by
    apply mul_left_cancel₀ hp
    calc
      (2 * Real.pi) * (Real.sqrt 2 * (m : ℝ)) =
          (2 * Real.pi * (m : ℝ)) * Real.sqrt 2 := by ring
      _ = (2 * Real.pi) * (n : ℝ) := hmul
  exact hm (irrational_dilation_periods m n hper).1

#check trivial_seed_extra_lattices_disjoint
#print axioms trivial_seed_extra_lattices_disjoint
end Round188H

/-! The adaptive Gaussian exponent in the actual native contour estimate.
The operator derivation, including the choice of H from measured zero losses,
is in GLOBAL_ESTIMATE.md. This lemma certifies only its exponent inequality. -/
namespace Round191H

theorem adaptive_native_contour_exponent
    (R H K : ℝ) (hR : 0 < R) (hH : 1 ≤ H)
    (hsmall : 4 * H ≤ R ^ 2) (hK : K ≤ H) :
    K - (Real.sqrt H / R) * R ^ 2 ≤ -(R * Real.sqrt H) / 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hs0 : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hs2 : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt hH0
  have hsR : 2 * Real.sqrt H ≤ R := by nlinarith
  have hmul := mul_nonneg hs0 (sub_nonneg.mpr hsR)
  have hid : (Real.sqrt H / R) * R ^ 2 = R * Real.sqrt H := by
    field_simp
  rw [hid]
  nlinarith

#check adaptive_native_contour_exponent
#print axioms adaptive_native_contour_exponent
end Round191H
