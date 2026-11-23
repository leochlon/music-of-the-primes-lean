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

/-! Round185F: algebraic cancellation in the NEW full-annihilator
resolvent construction. Here V is the generator domain, j its injection,
Q is the divided-convolution numerator, and m is the actual scalar Mellin
value. Native domain/integral attachment is derived in GLOBAL_ESTIMATE.md,
not asserted by this finite algebraic certificate. -/
namespace Round185F
variable {E V : Type*} [AddCommGroup E] [Module ℂ E]
  [AddCommGroup V] [Module ℂ V]

theorem full_annihilator_resolvent_right_inverse
    (j D : V →ₗ[ℂ] E) (Q : E →ₗ[ℂ] V) (z m : ℂ)
    (hm : m ≠ 0)
    (hnum : ∀ x, z • j (Q x) - D (Q x) = m • x) (x : E) :
    z • j (m⁻¹ • Q x) - D (m⁻¹ • Q x) = x := by
  calc
    _ = m⁻¹ • (z • j (Q x) - D (Q x)) := by
      simp only [map_smul, smul_sub, smul_smul]
      congr 1
      ring
    _ = m⁻¹ • (m • x) := by rw [hnum]
    _ = x := by simp [smul_smul, hm]

#check full_annihilator_resolvent_right_inverse
#print axioms full_annihilator_resolvent_right_inverse
end Round185F

/-! Round 187 F. The new coefficient bound for the explicit native
resolvent nuclear series. The second operator is the adjoint in the native
application. Its diagonal equality and both numerical-range/resolvent
identities are explicit; this does not certify the native attachments or
assume an infinite nuclear sum. -/
namespace Round187F
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_column_row_product_le
    (D R Dstar Rstar : H →L[ℂ] H) (beta c : ℝ) (hc : beta < c)
    (hnum : ∀ v : H, (inner ℂ v (D v)).re ≤ beta * ‖v‖ ^ 2)
    (hnums : ∀ v : H, (inner ℂ v (Dstar v)).re ≤ beta * ‖v‖ ^ 2)
    (hres : ∀ x : H, (c : ℂ) • R x - D (R x) = x)
    (hress : ∀ x : H, (c : ℂ) • Rstar x - Dstar (Rstar x) = x)
    (hdiag : ∀ x : H, (inner ℂ (Rstar x) x).re = (inner ℂ (R x) x).re)
    (x : H) :
    ‖R x‖ * ‖Rstar x‖ ≤ (inner ℂ (R x) x).re / (c - beta) := by
  have h1 := Round182D.resolvent_column_coercivity D R beta (c : ℂ) hnum hres x
  have h2 := Round182D.resolvent_column_coercivity Dstar Rstar beta (c : ℂ) hnums hress x
  simp only [Complex.ofReal_re] at h1 h2
  rw [hdiag] at h2
  have hgap : 0 < c - beta := sub_pos.mpr hc
  have hsq : 0 ≤ (c - beta) * (‖R x‖ - ‖Rstar x‖)^2 :=
    mul_nonneg hgap.le (sq_nonneg _)
  apply (le_div_iff₀ hgap).2
  nlinarith

#check resolvent_column_row_product_le
#print axioms resolvent_column_row_product_le
end Round187F
