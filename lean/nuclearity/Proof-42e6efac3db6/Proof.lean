import Mathlib

/-!
Round 182 D. First new premise in GLOBAL_ESTIMATE.md:
NATIVE_RESOLVENT_COERCIVITY_TO_HILBERT_SCHMIDT.
The native logarithmic weight gives the numerical-range hypothesis with
c = alpha + s/4. This lemma turns that bound into a resolvent column-square
bound, retaining the real trace instead of inverse jet/Gram norms.
The native attachment, zero counting and global contour sum are not
formalized here and no nuclearity conclusion is asserted.
-/
noncomputable section
set_option linter.unusedSimpArgs false
open scoped InnerProductSpace
namespace Round182D

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_column_coercivity
    (D R : H →L[ℂ] H) (c : ℝ) (z : ℂ)
    (hnum : ∀ v : H, (inner ℂ v (D v)).re ≤ c * ‖v‖ ^ 2)
    (hres : ∀ x : H, z • R x - D (R x) = x) (x : H) :
    (z.re - c) * ‖R x‖ ^ 2 ≤ (inner ℂ (R x) x).re := by
  have hid : (inner ℂ (R x) x).re =
      z.re * ‖R x‖ ^ 2 - (inner ℂ (R x) (D (R x))).re := by
    calc
      _ = (inner ℂ (R x) (z • R x - D (R x))).re :=
        congrArg (fun y : H => (inner ℂ (R x) y).re) (hres x).symm
      _ = _ := by
        simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
          Complex.mul_re, ← Complex.ofReal_pow]
  rw [hid]
  nlinarith [hnum (R x)]

/-- For an orthonormal basis the numerator is Re(trace R) and the left
side is the squared Hilbert-Schmidt norm. No eigenvector conditioning
or nuclear/summability hypothesis is present. -/
theorem resolvent_column_square_sum_le
    {ι : Type*} (J : Finset ι) (e : ι → H)
    (D R : H →L[ℂ] H) (c : ℝ) (z : ℂ) (hz : c < z.re)
    (hnum : ∀ v : H, (inner ℂ v (D v)).re ≤ c * ‖v‖ ^ 2)
    (hres : ∀ x : H, z • R x - D (R x) = x) :
    (∑ j ∈ J, ‖R (e j)‖ ^ 2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) / (z.re - c) := by
  apply (le_div_iff₀ (sub_pos.mpr hz)).2
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    resolvent_column_coercivity D R c z hnum hres (e j)

#check resolvent_column_coercivity
#print axioms resolvent_column_coercivity
#check resolvent_column_square_sum_le
#print axioms resolvent_column_square_sum_le
end Round182D
