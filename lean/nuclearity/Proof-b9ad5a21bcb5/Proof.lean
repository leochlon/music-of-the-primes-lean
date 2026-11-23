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

/-! Round184B: comparison needed to attach the positive completed-Hecke
zero sum to the native resolvent trace. This is ONLY the numerical bridge;
the analytic zero identity and native attachment are documented separately. -/
namespace Round184B
/-- With x=2-Re(rho), every nontrivial Hecke zero has 1<=x<=2.
This converts the positive logarithmic-derivative zero kernel to the
native squared-resolvent majorant, without any spacing assumption. -/
theorem hecke_zero_kernel_dominates_native_weight
    (x t : ℝ) (hx : 1 ≤ x) (hx2 : x ≤ 2) :
    1 / (1 + t ^ 2) ≤ 2 * (x / (x ^ 2 + t ^ 2)) := by
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hq : 0 < x ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hxx : x ^ 2 ≤ 2 * x := by nlinarith
  have hxt : t ^ 2 ≤ 2 * x * t ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * x - 1 by linarith) (sq_nonneg t)]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hp hq).mpr
  nlinarith
#check hecke_zero_kernel_dominates_native_weight
#print axioms hecke_zero_kernel_dominates_native_weight
end Round184B
