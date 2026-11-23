import Mathlib

/- Extracted from Fermat's Hadamard solution, lines 2044--2060.
   Only Mathlib is imported; no RH/nonvanishing conclusion is an input.
   The application below keeps omitted copies, including boundary copies. -/
open Complex Filter Topology
namespace CorrectionHadamardR01

theorem eventually_large_norm {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, R ≤ ‖ρ j‖ := by
  have h0 := hsum.tendsto_atTop_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]

theorem reciprocal_square_bound {z ρ : ℂ} (hρ : ρ ≠ 0)
    (hfar : 2 * ‖z‖ ≤ ‖ρ‖) :
    ‖((z - ρ)^2)⁻¹‖ ≤ 4 * (Complex.normSq ρ)⁻¹ := by
  have hr : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hd : ‖ρ‖ / 2 ≤ ‖z - ρ‖ := by
    have ht : ‖ρ‖ - ‖z‖ ≤ ‖z - ρ‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    linarith
  have hdpos : 0 < ‖z - ρ‖ := lt_of_lt_of_le (by positivity) hd
  rw [norm_inv, norm_pow, Complex.normSq_eq_norm_sq]
  calc
    (‖z - ρ‖ ^ 2)⁻¹ ≤ ((‖ρ‖ / 2)^2)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
      nlinarith [norm_nonneg (z - ρ)]
    _ = 4 * (‖ρ‖^2)⁻¹ := by field_simp; norm_num

/-- Exact zero-copy selection: a copy is omitted iff it is neither interior
nor an admitted boundary jet. This is the actual strip multiplicity rule. -/
noncomputable def omittedCopy (width weight : ℝ) (ρ : ℂ) (k : ℕ) : ℂ :=
  if |ρ.re - 1/2| < width ∨
      (|ρ.re - 1/2| = width ∧ (2 : ℝ) * k + 1 < weight) then 0 else 1

theorem omittedCopy_norm (width weight : ℝ) (ρ : ℂ) (k : ℕ) :
    ‖omittedCopy width weight ρ k‖ ≤ 1 := by
  unfold omittedCopy
  split_ifs <;> norm_num

/-- Fermat's independently proved inverse-square estimate controls the
actual omitted-copy series. No restriction to the critical line is made. -/
theorem omitted_series_summable (width weight : ℝ) (ρ : ℕ → ℂ) (jet : ℕ → ℕ)
    (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) (z : ℂ) :
    Summable (fun j => omittedCopy width weight (ρ j) (jet j) *
      ((z - ρ j)^2)⁻¹) := by
  apply (hsum.mul_left 4).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_large_norm hρ0 hsum
    (show 0 < 2 * (‖z‖ + 1) by positivity)] with j hj
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖((z - ρ j)^2)⁻¹‖ :=
      mul_le_mul_of_nonneg_right (omittedCopy_norm _ _ _ _) (norm_nonneg _)
    _ ≤ 4 * (Complex.normSq (ρ j))⁻¹ := by
      simpa using reciprocal_square_bound (hρ0 j) (by linarith)

/-- At a point strictly right of the SAME strip, every copy there remains.
Boundary subtraction cannot change its double-pole coefficient. -/
theorem omittedCopy_at_right (width weight : ℝ) (q : ℂ) (k : ℕ)
    (hq : width < q.re - 1/2) : omittedCopy width weight q k = 1 := by
  have ha : width < |q.re - 1/2| := lt_of_lt_of_le hq (le_abs_self _)
  simp only [omittedCopy]
  rw [if_neg]
  intro h
  rcases h with h | h
  · linarith
  · linarith [h.1]

end CorrectionHadamardR01
#print axioms CorrectionHadamardR01.eventually_large_norm
#print axioms CorrectionHadamardR01.omitted_series_summable
#print axioms CorrectionHadamardR01.omittedCopy_at_right
