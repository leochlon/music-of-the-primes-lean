import Mathlib

/- Scalar spectral convergence, not trace-norm convergence of an operator.
   The analytic cutoff estimate and zero-counting bound must supply `b`. -/
namespace GeometricTraceRoundFour
open Filter
open scoped Topology

theorem spectral_absolute_error_tends_to_zero {J : Type*}
    (f : ℕ → J → ℂ) (g : J → ℂ) (b : J → ℝ)
    (hb : Summable b)
    (hf : ∀ n j, ‖f n j‖ ≤ b j)
    (hg : ∀ j, ‖g j‖ ≤ b j)
    (hp : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j))) :
    Tendsto (fun n => ∑' j, ‖f n j - g j‖) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun n j => ‖f n j - g j‖) (g := fun _ => (0 : ℝ))
    (bound := fun j => b j + b j) (hb.add hb) ?_ ?_
  · simpa using h
  · intro j
    simpa using ((hp j).sub_const (g j)).norm
  · exact Eventually.of_forall fun n j => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (hf n j) (hg j))

theorem spectral_sum_tends_to_sum {J : Type*}
    (f : ℕ → J → ℂ) (g : J → ℂ) (b : J → ℝ)
    (hb : Summable b)
    (hf : ∀ n j, ‖f n j‖ ≤ b j)
    (hp : ∀ j, Tendsto (fun n => f n j) atTop (𝓝 (g j))) :
    Tendsto (fun n => ∑' j, f n j) atTop (𝓝 (∑' j, g j)) := by
  exact tendsto_tsum_of_dominated_convergence hb hp
    (Eventually.of_forall hf)

#print axioms spectral_absolute_error_tends_to_zero
#print axioms spectral_sum_tends_to_sum
end GeometricTraceRoundFour
