import Mathlib

/-! Round 183 B. Native whole-window resolvent cost.
The logarithmic derivative on the ACTUAL dual weight satisfies
Re <v,Dv> <= (alpha+s/4)||v||^2. This new finite Hilbert inequality
converts that bound to a Hilbert-Schmidt resolvent cost without any
inverse Gram estimate. Native attachment and arithmetic counting are
written out separately in GLOBAL_ESTIMATE.md; full nuclearity is NOT
asserted by this theorem. -/
noncomputable section
open scoped InnerProductSpace
namespace Round183B
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*}

theorem accretive_resolvent_column_bound
    (D R : H →L[ℂ] H) (c l : ℝ)
    (hD : ∀ v : H, (⟪v, D v⟫_ℂ).re ≤ c * ‖v‖ ^ 2)
    (hR : ∀ x : H, (l : ℂ) • R x - D (R x) = x)
    (x : H) :
    (l - c) * ‖R x‖ ^ 2 ≤ (⟪R x, x⟫_ℂ).re := by
  have hid : (⟪R x, x⟫_ℂ).re =
      l * ‖R x‖ ^ 2 - (⟪R x, D (R x)⟫_ℂ).re := by
    calc
      (⟪R x, x⟫_ℂ).re =
          (⟪R x, (l : ℂ) • R x - D (R x)⟫_ℂ).re := by rw [hR x]
      _ = _ := by
        simp only [inner_sub_right, inner_smul_right, Complex.sub_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, inner_self_eq_norm_sq_to_K]
        simp [pow_two, Complex.mul_re]
  rw [hid]
  nlinarith [hD (R x)]

/-- With b orthonormal, the left side is the actual squared HS norm.
The right side is Re trace(R)/(l-c), subsequently evaluated from the
native triangular derivative action, counting true multiplicities. -/
theorem accretive_resolvent_hilbert_schmidt_cost
    (D R : H →L[ℂ] H) (c l : ℝ) (hl : c < l)
    (hD : ∀ v : H, (⟪v, D v⟫_ℂ).re ≤ c * ‖v‖ ^ 2)
    (hR : ∀ x : H, (l : ℂ) • R x - D (R x) = x)
    (J : Finset ι) (b : ι → H) :
    (∑ i ∈ J, ‖R (b i)‖ ^ 2) ≤
      (∑ i ∈ J, (⟪R (b i), b i⟫_ℂ).re) / (l - c) := by
  apply (le_div_iff₀ (sub_pos.mpr hl)).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  simpa [mul_comm] using accretive_resolvent_column_bound D R c l hD hR (b i)

#check accretive_resolvent_column_bound
#print axioms accretive_resolvent_column_bound
#check accretive_resolvent_hilbert_schmidt_cost
#print axioms accretive_resolvent_hilbert_schmidt_cost
end Round183B

/-! Round 185 B: native endpoint membership and the polynomial weight
estimate used in the new a-line synthesis argument. These statements do
not assert synthesis on a positive-width strip or the full nuclear bound.
The complete paper derivation and exact remaining premise are recorded in
GLOBAL_ESTIMATE.md. -/
namespace Round185B
open MeasureTheory Set

/-- The tail model of the ACTUAL squared native boundary-jet norm has a
strict endpoint. The manuscript's rounded cap cannot include equality. -/
theorem native_endpoint_tail_iff (m : ℕ) (s : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ ((2 : ℝ) * (m : ℝ) - s)) (Ioi 1) ↔
      (2 : ℝ) * (m : ℝ) < s - 1 := by
  rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  constructor <;> intro h <;> linarith

theorem native_critical_endpoint_diverges (m : ℕ) :
    ¬ IntegrableOn
      (fun x : ℝ => x ^ ((2 : ℝ) * (m : ℝ) - (2 * (m : ℝ) + 1)))
      (Ioi 1) := by
  rw [native_endpoint_tail_iff]
  push_neg
  linarith

/-- This native polynomial-weight inequality supplies the uniform
translation domination for the smooth frequency cutoffs when alpha=0. -/
theorem native_polynomial_translation_control (x t : ℝ) :
    1 + (x + t) ^ 2 ≤ 2 * (1 + x ^ 2) * (1 + t ^ 2) := by
  nlinarith [sq_nonneg (x - t), sq_nonneg (x * t)]

#check native_endpoint_tail_iff
#print axioms native_endpoint_tail_iff
#check native_critical_endpoint_diverges
#print axioms native_critical_endpoint_diverges
#check native_polynomial_translation_control
#print axioms native_polynomial_translation_control
end Round185B

/-! Round187B. Named premise: ACTUAL_TRIVIAL_CHARACTER_S0_SEED.
This constructs the two-moment kernel element from the manuscript's
finite-translation covariance, without a derivative of the adelic action.
The native specialization and additional-zero cost are derived in
GLOBAL_ESTIMATE.md. No global nuclearity is assumed or concluded here. -/
namespace Round187B
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def twoMomentSeed (T : V →ₗ[ℂ] V) (r : ℂ) (f : V) : V :=
  T (T f - r • f) - (T f - r • f)

theorem finite_translation_seed
    (T : V →ₗ[ℂ] V) (r : ℂ) (f : V)
    (origin mass : V →ₗ[ℂ] ℂ)
    (M : ℂ → V →ₗ[ℂ] ℂ) (q : ℂ → ℂ)
    (horigin : ∀ v, origin (T v) = origin v)
    (hmass : ∀ v, mass (T v) = r * mass v)
    (hM : ∀ z v, M z (T v) = q z * M z v) :
    origin (twoMomentSeed T r f) = 0 ∧
    mass (twoMomentSeed T r f) = 0 ∧
    ∀ z, M z (twoMomentSeed T r f) =
      (q z - 1) * (q z - r) * M z f := by
  constructor
  · simp only [twoMomentSeed, map_sub, horigin, sub_self]
  constructor
  · simp only [twoMomentSeed, map_sub, map_smul, hmass, smul_eq_mul]
    ring
  · intro z
    simp only [twoMomentSeed, map_sub, map_smul, hM, smul_eq_mul]
    ring

#check finite_translation_seed
#print axioms finite_translation_seed
end Round187B

/-! Round188B: pole-selection in the ACTUAL two finite-translation seeds.
The zero sets below are the added zero divisors after removing the poles
of the completed trivial-character Hecke function at 0 and 1. Their
empty intersection removes artificial poles from the native resolvent;
GLOBAL_ESTIMATE.md gives that implication and the exact global bound. -/
namespace Round188B

def extraSeedZero (t : ℝ) (z : ℂ) : Prop :=
  ∃ (r : Fin 2) (n : ℤ), n ≠ 0 ∧
    z = (r.val : ℂ) + ((2 * Real.pi * (n : ℝ) / t : ℝ) : ℂ) * Complex.I

theorem two_scale_seed_zero_divisors_disjoint (z : ℂ) :
    ¬ (extraSeedZero 1 z ∧ extraSeedZero (Real.sqrt 2) z) := by
  rintro ⟨⟨r, n, hn, h1⟩, ⟨s, m, hm, h2⟩⟩
  have hi := congrArg Complex.im (h1.symm.trans h2)
  simp only [Complex.add_im, Complex.natCast_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_im, Complex.I_re,
    mul_one, zero_mul, add_zero, zero_add, div_one] at hi
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have he : Real.sqrt 2 = (m : ℝ) / (n : ℝ) := by
    have hi' := (eq_div_iff hs).1 hi
    apply (eq_div_iff hnR).2
    apply mul_left_cancel₀ hp
    nlinarith [hi']
  have hr : Real.sqrt 2 = ((m : ℚ) / (n : ℚ) : ℚ) := by
    simpa only [Rat.cast_div, Rat.cast_intCast] using he
  exact irrational_sqrt_two ⟨(m : ℚ) / (n : ℚ), hr.symm⟩

#check two_scale_seed_zero_divisors_disjoint
#print axioms two_scale_seed_zero_divisors_disjoint
end Round188B
