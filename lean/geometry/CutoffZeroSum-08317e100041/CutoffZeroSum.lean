import Mathlib

/-! Scalar convergence needed to remove a shrinking norm-one cutoff.
This is not a trace-class theorem. The adelic application must prove
the displayed summable majorant and pointwise convergence. -/
namespace GeometricTraceRound4
open Filter Topology

theorem cutoff_zero_sum {ι : Type*} {f : ℕ → ι → ℂ} {b : ι → ℝ}
    (hb : Summable b)
    (hlim : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 0))
    (hbound : ∀ n i, ‖f n i‖ ≤ b i) :
    Tendsto (fun n => ∑' i, f n i) atTop (𝓝 0) := by
  simpa using tendsto_tsum_of_dominated_convergence hb hlim
    (Filter.Eventually.of_forall hbound)

theorem finite_band_estimate {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    {ε C D L : ℝ} (hε : 0 < ε) (hD : 0 ≤ D)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ D * ε ^ 2)
    (hcount : (s.card : ℝ) ≤ C / ε * L) :
    ‖∑ i ∈ s, f i‖ ≤ C * D * ε * L := by
  calc
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, D * ε ^ 2 := Finset.sum_le_sum hf
    _ = (s.card : ℝ) * (D * ε ^ 2) := by simp
    _ ≤ (C / ε * L) * (D * ε ^ 2) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg hD (sq_nonneg ε))
    _ = C * D * ε * L := by field_simp

#print axioms cutoff_zero_sum
#print axioms finite_band_estimate

end GeometricTraceRound4
