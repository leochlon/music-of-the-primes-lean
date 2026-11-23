import Mathlib

/- B/R06. Analytic row estimate used for the actual projected shell density.
   This checks the L1 estimate and localization convention, not an assumed
   arithmetic identity. See GLOBAL_REVIEW_R06.md for the adelic application. -/
noncomputable section
namespace ActualShellDensityR06
open MeasureTheory
open scoped InnerProductSpace

variable {X H : Type*} [MeasurableSpace X] {mu : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem row_integrable {u v : X → H} (hu : MemLp u 2 mu)
    (hv : MemLp v 2 mu) : Integrable (fun x => ⟪u x, v x⟫_ℂ) mu := by
  refine (L2.integrable_inner (𝕜 := ℂ) (hu.toLp u) (hv.toLp v)).congr ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hx hy
  rw [hx, hy]

theorem row_L1_bound {u v : X → H} (hu : MemLp u 2 mu)
    (hv : MemLp v 2 mu) :
    (∫ x, ‖⟪u x, v x⟫_ℂ‖ ∂mu) ≤
      ‖hu.norm.toLp (fun x => ‖u x‖)‖ *
      ‖hv.norm.toLp (fun x => ‖v x‖)‖ := by
  let U := hu.norm.toLp (fun x => ‖u x‖)
  let V := hv.norm.toLp (fun x => ‖v x‖)
  have hm : Integrable (fun x => ‖u x‖ * ‖v x‖) mu := by
    refine (L2.integrable_inner (𝕜 := ℝ) U V).congr ?_
    filter_upwards [hu.norm.coeFn_toLp, hv.norm.coeFn_toLp] with x hx hy
    simp only [U, V, hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]
  have hi : (∫ x, ‖u x‖ * ‖v x‖ ∂mu) = ⟪U, V⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu.norm.coeFn_toLp, hv.norm.coeFn_toLp] with x hx hy
    simp only [U, V, hx, hy, RCLike.inner_apply, conj_trivial, mul_comm]
  calc
    (∫ x, ‖⟪u x, v x⟫_ℂ‖ ∂mu) ≤ ∫ x, ‖u x‖ * ‖v x‖ ∂mu :=
      integral_mono_ae (row_integrable hu hv).norm hm
        (Filter.Eventually.of_forall fun x => norm_inner_le_norm _ _)
    _ = ⟪U, V⟫_ℝ := hi
    _ ≤ ‖U‖ * ‖V‖ := real_inner_le_norm _ _

/-- A multiplier on the OUTPUT is conjugated in the first row. Cyclically
moving factors before inserting that multiplier does not preserve density. -/
theorem output_multiplier_row (eta : ℂ) (u v : H) :
    ⟪(starRingEnd ℂ eta) • u, v⟫_ℂ = eta * ⟪u, v⟫_ℂ := by
  simp [mul_comm]

/-- The local diagonal cannot be inferred from cyclicity of total trace. -/
theorem cyclic_diagonal_countercheck :
    let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
    let C : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
    (B * C) 0 0 = 1 ∧ (C * B) 0 0 = 0 := by
  norm_num [Matrix.mul_apply, Fin.sum_univ_two]

end ActualShellDensityR06
#print axioms ActualShellDensityR06.row_L1_bound
#print axioms ActualShellDensityR06.output_multiplier_row
#print axioms ActualShellDensityR06.cyclic_diagonal_countercheck
