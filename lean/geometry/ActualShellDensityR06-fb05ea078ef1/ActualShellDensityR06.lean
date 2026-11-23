import Mathlib

/- Actual multiplier-density repair for GLOBAL_DENSITY_R06.md.
The squared Holder estimate is ported from ALPO HilbertSchmidtKernel:12--25;
Fermat L2KernelOperator:29--63 uses the same two-two Holder step.
No adelic trace equality is assumed by these analytic declarations. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology ComplexConjugate
namespace ActualShellDensityR06

variable {X : Type*} [MeasurableSpace X]

theorem column_density_bound (mu : Measure X) (u v : X → ℂ)
    (hu : AEStronglyMeasurable u mu) (hv : AEStronglyMeasurable v mu) :
    (∫⁻ x, ‖u x * conj (v x)‖ₑ ∂mu) ^ 2 ≤
      (∫⁻ x, ‖u x‖ₑ ^ 2 ∂mu) * ∫⁻ x, ‖v x‖ₑ ^ 2 ∂mu := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two hu.enorm hv.enorm
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  have hc : (fun x => ‖u x * conj (v x)‖ₑ) =
      fun x => ‖u x‖ₑ * ‖v x‖ₑ := by
    funext x
    simp
  rw [hc]
  calc (∫⁻ x, ‖u x‖ₑ * ‖v x‖ₑ ∂mu) ^ 2
      ≤ ((∫⁻ x, ‖u x‖ₑ ^ 2 ∂mu) ^ (1 / 2 : ℝ) *
          (∫⁻ x, ‖v x‖ₑ ^ 2 ∂mu) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

theorem multiplier_error_bound (mu : Measure X) (d e eta : X → ℂ)
    (hd : Integrable d mu) (he : Integrable e mu)
    (heta : ∀ᵐ x ∂mu, ‖eta x‖ ≤ 1) :
    ‖∫ x, eta x * (d x - e x) ∂mu‖ ≤ ∫ x, ‖d x - e x‖ ∂mu := by
  apply norm_integral_le_of_norm_le (hd.sub he).norm
  filter_upwards [heta] with x hx
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- This gives L1 convergence of the ACTUAL density, not just its integral. -/
theorem physical_density_cutoff (mu : Measure X) (d : X → ℂ)
    (hd : Integrable d mu) (rho : ℕ → X → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n x, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (ht : ∀ x, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, ‖(rho n x : ℂ) * d x - d x‖ ∂mu)
      atTop (𝓝 0) := by
  have hbound : ∀ n x, ‖(rho n x : ℂ) * d x - d x‖ ≤ ‖d x‖ := by
    intro n x
    have heq : (rho n x : ℂ) * d x - d x = ((rho n x - 1 : ℝ) : ℂ) * d x := by
      push_cast
      ring
    rw [heq, norm_mul]
    have hr : ‖((rho n x - 1 : ℝ) : ℂ)‖ ≤ 1 := by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonpos (sub_nonpos.mpr (hb n x).2)]
      linarith [(hb n x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) hr
  have h := tendsto_integral_of_dominated_convergence
    (μ := mu) (F := fun n x => ‖(rho n x : ℂ) * d x - d x‖)
    (f := fun _ => (0 : ℝ)) (fun x => ‖d x‖)
    (fun n => (((Complex.continuous_ofReal.comp_aestronglyMeasurable (hm n)).mul
      hd.aestronglyMeasurable).sub hd.aestronglyMeasurable).norm)
    hd.norm (fun n => Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_norm] using hbound n x)
    (Filter.Eventually.of_forall fun x => by
      have hh := (((Complex.continuous_ofReal.tendsto 1).comp (ht x)).mul
        (tendsto_const_nhds (x := d x))).sub (tendsto_const_nhds (x := d x))
      simpa using hh.norm)
  simpa using h

end ActualShellDensityR06
#print axioms ActualShellDensityR06.column_density_bound
#print axioms ActualShellDensityR06.multiplier_error_bound
#print axioms ActualShellDensityR06.physical_density_cutoff
