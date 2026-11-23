import Mathlib

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

end Round90E
#check Round90E.biorthogonal_lift_separation
#print axioms Round90E.biorthogonal_lift_separation
#check Round90E.biorthogonal_lift_relative_conditioning
#print axioms Round90E.biorthogonal_lift_relative_conditioning
