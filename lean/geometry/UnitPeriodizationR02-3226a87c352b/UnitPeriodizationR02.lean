import Mathlib

/-! The independent lower cutoff requested in manuscript 12.4.1, footnote 2.
The integral hypothesis is verified for each actual Schwartz orbital profile
in APPLICATION_R01.md. No geometric trace identity is assumed here. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ActualGeometricTrace

def clip (R t : ℝ) : ℝ := max (-R) (min R t)

theorem clip_eq (R t : ℝ) (hlo : -R ≤ t) (hhi : t ≤ R) :
    clip R t = t := by simp [clip, min_eq_right hhi, max_eq_right hlo]

theorem abs_clip_le (R t : ℝ) (hR : 0 ≤ R) : |clip R t| ≤ |t| := by
  by_cases hlo : t < -R
  · have ht : t ≤ R := by linarith
    rw [clip, min_eq_right ht, max_eq_left hlo.le, abs_neg, abs_of_nonneg hR]
    exact le_trans (by linarith : R ≤ -t) (neg_le_abs t)
  · by_cases hhi : R < t
    · rw [clip, min_eq_left hhi.le, max_eq_right (by linarith), abs_of_nonneg hR]
      exact le_trans hhi.le (le_abs_self t)
    · rw [clip_eq R t (le_of_not_gt hlo) (le_of_not_gt hhi)]

theorem annulus_volume_remainder (R t : ℝ) (hR : 0 ≤ R) :
    max 0 (R - max t (-R)) - R = -clip R t := by
  by_cases hlo : t ≤ -R
  · have ht : t ≤ R := by linarith
    simp only [max_eq_right hlo, clip, min_eq_right ht, max_eq_left hlo]
    rw [max_eq_right (by linarith : 0 ≤ R - -R)]
    ring
  · by_cases hhi : R ≤ t
    · have ht : -R ≤ t := by linarith
      rw [max_eq_left ht, max_eq_left (by linarith : R - t ≤ 0)]
      simp [clip, min_eq_left hhi, max_eq_right (by linarith : -R ≤ R)]
    · have ht : -R ≤ t := (lt_of_not_ge hlo).le
      rw [max_eq_left ht, max_eq_right (by linarith : 0 ≤ R - t)]
      rw [clip_eq R t ht (le_of_not_ge hhi)]
      ring

theorem clip_eventually_eq (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, clip (n : ℝ) t = t := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  apply clip_eq <;> linarith [le_abs_self t, neg_le_abs t]

theorem lower_cutoff_integral_limit {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ell : X → ℝ) (F : X → ℂ)
    (hell : AEStronglyMeasurable ell μ) (hF : AEStronglyMeasurable F μ)
    (hbound : Integrable (fun x => |ell x| * ‖F x‖) μ) :
    Tendsto (fun n : ℕ => ∫ x, (clip (n : ℝ) (ell x) : ℂ) * F x ∂μ)
      atTop (𝓝 (∫ x, (ell x : ℂ) * F x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |ell x| * ‖F x‖)
  · intro n
    have hc : Continuous (fun t : ℝ => (clip (n : ℝ) t : ℂ)) := by
      unfold clip
      fun_prop
    exact (hc.comp_aestronglyMeasurable hell).mul hF
  · exact hbound
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_clip_le _ _ (Nat.cast_nonneg n)) (norm_nonneg _)
  · apply Eventually.of_forall
    intro x
    apply tendsto_const_nhds.congr'
    filter_upwards [clip_eventually_eq (ell x)] with n hn
    rw [hn]

end ActualGeometricTrace
#print axioms ActualGeometricTrace.annulus_volume_remainder
#print axioms ActualGeometricTrace.lower_cutoff_integral_limit


/-! The cutoff contraction and summed limit used for the actual S-unit
Fourier coefficients in APPLICATION_R02.md. The Fourier-decay estimate is
proved there in written mathematics, not assumed to be a trace identity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ActualGeometricTrace

theorem clip_difference_bound (R x y : ℝ) :
    |clip R x - clip R y| ≤ |x-y| := by
  simp only [clip, max_def, min_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;>
    linarith [le_abs_self (x-y), neg_le_abs (x-y)]

theorem periodized_lower_cutoff_limit {U X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ell : X → ℝ) (F : U → X → ℂ)
    (hell : AEStronglyMeasurable ell μ)
    (hF : ∀ u, AEStronglyMeasurable (F u) μ)
    (hint : ∀ u, Integrable (fun x => |ell x| * ‖F u x‖) μ)
    (M : U → ℝ) (hM : Summable M)
    (hdecay : ∀ n : ℕ, ∀ u,
      ‖∫ x, (clip (n : ℝ) (ell x) : ℂ) * F u x ∂μ‖ ≤ M u) :
    Tendsto (fun n : ℕ => ∑' u,
        ∫ x, (clip (n : ℝ) (ell x) : ℂ) * F u x ∂μ)
      atTop (𝓝 (∑' u, ∫ x, (ell x : ℂ) * F u x ∂μ)) := by
  exact tendsto_tsum_of_dominated_convergence hM
    (fun u => lower_cutoff_integral_limit μ ell (F u) hell (hF u) (hint u))
    (Eventually.of_forall hdecay)

end ActualGeometricTrace
#print axioms ActualGeometricTrace.clip_difference_bound
#print axioms ActualGeometricTrace.periodized_lower_cutoff_limit
