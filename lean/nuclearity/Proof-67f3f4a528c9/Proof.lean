import Mathlib

/- Round 88, E: a necessary lower bound for the actual biorthogonal lifts.
   Instantiate H with the manuscript's weighted Hilbert space W_I^s(C_F),
   eta/theta with its two coefficient functionals, and v with a lift.
   This is a lower-bound obstruction, not a proof of nuclearity. -/

namespace Round88E

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Biorthogonality forces the norm of a lift to grow when coefficients approach. -/
theorem biorthogonal_lift_separation
    (eta theta : H →L[ℂ] ℂ) (v : H)
    (heta : eta v = 1) (htheta : theta v = 0) :
    1 ≤ ‖eta - theta‖ * ‖v‖ := by
  have h := (eta - theta).le_opNorm v
  simpa [heta, htheta] using h

/-- A proposed uniform lift bound forces a uniform dual separation. -/
theorem bounded_lift_forces_separation
    (eta theta : H →L[ℂ] ℂ) (v : H) (C : ℝ)
    (heta : eta v = 1) (htheta : theta v = 0) (hv : ‖v‖ ≤ C) :
    1 ≤ ‖eta - theta‖ * C := by
  exact (biorthogonal_lift_separation eta theta v heta htheta).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg _))

#check biorthogonal_lift_separation
#print axioms biorthogonal_lift_separation
#check bounded_lift_forces_separation
#print axioms bounded_lift_forces_separation

/-- The squared-norm density of the manuscript's actual strip space,
    in the coordinate u = log |g|_F. -/
def stripWeight (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (1 + u ^ 2) ^ (s / 2)

/-- A corrected translation estimate, valid for every nonnegative strip width
    and real Sobolev parameter; unlike (9.3.1.6), it does not vanish at identity. -/
theorem stripWeight_translate_bound (alpha s u v : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    stripWeight alpha s (u + v) ≤
      (Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)) *
        stripWeight alpha s v := by
  have hp : 1 + (u + v) ^ 2 ≤ (2 * (1 + u ^ 2)) * (1 + v ^ 2) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u * v)]
  have he : Real.exp (2 * alpha * |u + v|) ≤
      Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_add_le u v]
  have hw : (1 + (u + v) ^ 2) ^ (s / 2) ≤
      (2 * (1 + u ^ 2)) ^ (s / 2) * (1 + v ^ 2) ^ (s / 2) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * (1 + u ^ 2))
      (by positivity : 0 ≤ 1 + v ^ 2)]
    exact Real.rpow_le_rpow (by positivity) hp (by positivity)
  unfold stripWeight
  calc
    _ ≤ (Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|)) *
        ((2 * (1 + u ^ 2)) ^ (s / 2) * (1 + v ^ 2) ^ (s / 2)) :=
      mul_le_mul he hw (by positivity) (by positivity)
    _ = _ := by ring

/-- Direct pointwise domination of the actual squared norm integrand after
    translating by a group element of logarithmic module u. -/
theorem translated_lift_integrand_bound (alpha s u v : ℝ) (z : ℂ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    ‖z‖ ^ 2 * stripWeight alpha s (u + v) ≤
      (Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)) *
        (‖z‖ ^ 2 * stripWeight alpha s v) := by
  have h := mul_le_mul_of_nonneg_left
    (stripWeight_translate_bound alpha s u v ha hs) (sq_nonneg ‖z‖)
  calc
    _ ≤ ‖z‖ ^ 2 * ((Real.exp (2 * alpha * |u|) *
        (2 * (1 + u ^ 2)) ^ (s / 2)) * stripWeight alpha s v) := h
    _ = _ := by ring

#check stripWeight_translate_bound
#print axioms stripWeight_translate_bound
#check translated_lift_integrand_bound
#print axioms translated_lift_integrand_bound

open MeasureTheory

/-- Integration of the corrected weight domination. Apply with logModule(x)
    equal to log |x|_F, mu the genuine Haar measure and f an actual lift.
    No norm bound for f or nuclear summability is assumed here. -/
theorem translated_lift_squaredNorm_bound
    {G : Type*} [MeasurableSpace G] (mu : Measure G)
    (logModule : G → ℝ) (f : G → ℂ) (alpha s u : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hf : Integrable (fun x => ‖f x‖ ^ 2 * stripWeight alpha s (logModule x)) mu)
    (hm : AEStronglyMeasurable
      (fun x => ‖f x‖ ^ 2 * stripWeight alpha s (u + logModule x)) mu) :
    Integrable (fun x => ‖f x‖ ^ 2 * stripWeight alpha s (u + logModule x)) mu ∧
    (∫ x, ‖f x‖ ^ 2 * stripWeight alpha s (u + logModule x) ∂mu) ≤
      (Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)) *
        (∫ x, ‖f x‖ ^ 2 * stripWeight alpha s (logModule x) ∂mu) := by
  let c := Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)
  have hb (x : G) : ‖f x‖ ^ 2 * stripWeight alpha s (u + logModule x) ≤
      c * (‖f x‖ ^ 2 * stripWeight alpha s (logModule x)) :=
    translated_lift_integrand_bound alpha s u (logModule x) (f x) ha hs
  have ht : Integrable
      (fun x => ‖f x‖ ^ 2 * stripWeight alpha s (u + logModule x)) mu := by
    apply (hf.const_mul c).mono' hm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hb x
    · unfold stripWeight
      positivity
  refine ⟨ht, ?_⟩
  calc
    _ ≤ ∫ x, c * (‖f x‖ ^ 2 * stripWeight alpha s (logModule x)) ∂mu :=
      integral_mono ht (hf.const_mul c) hb
    _ = _ := integral_const_mul c _

#check translated_lift_squaredNorm_bound
#print axioms translated_lift_squaredNorm_bound

end

end Round88E
