import Mathlib

open MeasureTheory
open scoped InnerProductSpace

namespace GeometricCutoffC26

/-- The functional-slot projection gives PA; both cutoff slots remain in their
original positions. The complement is (1-P)A. No commutation is used. -/
theorem genuine_projection_cutoff_decomposition
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [CompleteSpace E]
    (A L R : H →L[ℂ] H) (x : H) :
    L (A (R x)) = L (E.starProjection (A (R x))) +
      L (A (R x) - E.starProjection (A (R x))) := by
  rw [map_sub]
  abel

/-- Invariance of the original geometric kernel yields PAP=PA and an explicit
cutoff defect if the output-slot AP expression is used instead. -/
theorem genuine_projection_wrong_order_cutoff_defect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [CompleteSpace E]
    (A L R : H →L[ℂ] H)
    (hinv : ∀ x, E.starProjection (A (x - E.starProjection x)) = 0)
    (x : H) :
    L (A (E.starProjection (R x))) - L (E.starProjection (A (R x))) =
      L (A (E.starProjection (R x)) -
        E.starProjection (A (E.starProjection (R x)))) := by
  have h := hinv (R x)
  simp only [map_sub] at h
  have he := sub_eq_zero.mp h
  rw [map_sub, he]

/-- Exact same-measure kernel subtraction, retaining the output smoothing and
input cutoff. In the manuscript kP must represent PA on the same weighted
space; the orbital theorem must still establish that representation. -/
theorem ordered_smoothed_complement_kernel
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (kA kP : X → X → ℂ) (rho alpha f : X → ℂ)
    (A PA : (X → ℂ) → X → ℂ)
    (hA : ∀ x, Integrable (fun y => kA x y * (alpha y * f y)) mu)
    (hP : ∀ x, Integrable (fun y => kP x y * (alpha y * f y)) mu)
    (hArep : ∀ x, (∫ y, kA x y * (alpha y * f y) ∂mu) =
      A (fun y => alpha y * f y) x)
    (hPrep : ∀ x, (∫ y, kP x y * (alpha y * f y) ∂mu) =
      PA (fun y => alpha y * f y) x) (x : X) :
    (∫ y, rho x * ((kA x y - kP x y) * (alpha y * f y)) ∂mu) =
      rho x * (A (fun y => alpha y * f y) x -
        PA (fun y => alpha y * f y) x) := by
  rw [integral_const_mul]
  simp_rw [sub_mul]
  rw [integral_sub (hA x) (hP x), hArep x, hPrep x]

/-- Strong convergence of cutoff vectors alone gives convergence of each
fixed matrix coefficient of the correctly ordered complement. It supplies no
interchange with an infinite trace or orbital sum. -/
theorem ordered_complement_cutoff_strong_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (E : Submodule ℂ H) [CompleteSpace E]
    (A : H →L[ℂ] H) (R : ℕ → H →L[ℂ] H)
    (hR : ∀ x, Filter.Tendsto (fun n => R n x) Filter.atTop (nhds x))
    (x : H) :
    Filter.Tendsto (fun n => A (R n x) - E.starProjection (A (R n x)))
      Filter.atTop (nhds (A x - E.starProjection (A x))) := by
  exact ((A.continuous.tendsto x).comp (hR x)).sub
    ((E.starProjection.continuous.tendsto (A x)).comp
      ((A.continuous.tendsto x).comp (hR x)))

#print axioms genuine_projection_cutoff_decomposition
#print axioms genuine_projection_wrong_order_cutoff_defect
#print axioms ordered_smoothed_complement_kernel
#print axioms ordered_complement_cutoff_strong_limit
end GeometricCutoffC26
