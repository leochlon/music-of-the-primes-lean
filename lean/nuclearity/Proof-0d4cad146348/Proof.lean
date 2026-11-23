import Mathlib

/-! Round 182C. New premise RESOLVENT_ENERGY in GLOBAL_ESTIMATE.md.
This proves the conditioning-free finite-window energy estimate. The native
translation generator and the all-character zero count are NOT axioms here.
No infinite nuclearity claim is made by this file. -/
noncomputable section
open scoped InnerProductSpace
namespace Round182C
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_energy_bound
    (B R : H →L[ℂ] H) (z omega : ℝ)
    (hnum : ∀ y : H, (⟪y, B y⟫_ℂ).re ≤ omega * ‖y‖ ^ 2)
    (hres : ∀ x : H, (z : ℂ) • R x - B (R x) = x) (x : H) :
    (z - omega) * ‖R x‖ ^ 2 ≤ (⟪R x, x⟫_ℂ).re := by
  have he : (⟪R x, x⟫_ℂ).re =
      z * ‖R x‖ ^ 2 - (⟪R x, B (R x)⟫_ℂ).re := by
    calc
      (⟪R x, x⟫_ℂ).re = (⟪R x, (z : ℂ) • R x - B (R x)⟫_ℂ).re :=
        congrArg (fun y : H => (⟪R x, y⟫_ℂ).re) (hres x).symm
      _ = _ := by simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  rw [he]
  nlinarith [hnum (R x)]

/-- For an orthonormal basis e of a genuine invariant spectral window,
the left side is (z-omega) times the squared Hilbert--Schmidt norm;
the right side is Re trace R. No inverse jet/Gram norm appears. -/
theorem finite_window_resolvent_energy
    {J : Type*} [Fintype J] (e : J → H)
    (B R : H →L[ℂ] H) (z omega : ℝ)
    (hnum : ∀ y : H, (⟪y, B y⟫_ℂ).re ≤ omega * ‖y‖ ^ 2)
    (hres : ∀ x : H, (z : ℂ) • R x - B (R x) = x) :
    (z - omega) * (∑ j, ‖R (e j)‖ ^ 2) ≤
      ∑ j, (⟪R (e j), e j⟫_ℂ).re := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => resolvent_energy_bound B R z omega hnum hres (e j))

#check resolvent_energy_bound
#print axioms resolvent_energy_bound
#check finite_window_resolvent_energy
#print axioms finite_window_resolvent_energy
end Round182C
