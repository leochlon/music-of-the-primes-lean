import Mathlib

/-! Round 189 E. Native boundary-jet norm, not merely the power-tail model.
The global derivation uses this to exclude noncontinuous residue vectors
at the Sobolev threshold. It does not assert spectral totality or nuclearity.
-/
noncomputable section
open MeasureTheory Set
namespace Round189E

def nativeBoundaryDensity (m : ℕ) (s x : ℝ) : ℝ :=
  x ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2)

theorem native_boundary_density_comparison (m : ℕ) (s x : ℝ)
    (hs : 0 ≤ s) (hx : 1 ≤ x) :
    (2 : ℝ) ^ (-s / 2) * x ^ ((2 : ℝ) * m - s) ≤
      nativeBoundaryDensity m s x ∧
    nativeBoundaryDensity m s x ≤ x ^ ((2 : ℝ) * m - s) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hexp : -s / 2 ≤ 0 := by linarith
  have hpower : x ^ (2 * m) * (x ^ 2) ^ (-s / 2) =
      x ^ ((2 : ℝ) * m - s) := by
    rw [← Real.rpow_natCast x (2 * m), ← Real.rpow_natCast x 2,
      ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  have hlo : (2 * x ^ 2) ^ (-s / 2) ≤ (1 + x ^ 2) ^ (-s / 2) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ hexp
    nlinarith [sq_nonneg (x - 1)]
  have hhi : (1 + x ^ 2) ^ (-s / 2) ≤ (x ^ 2) ^ (-s / 2) := by
    exact Real.rpow_le_rpow_of_nonpos hx2 (by linarith) hexp
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ x ^ (2*m))
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx2.le] at h
    calc
      _ = x ^ (2*m) * ((2 : ℝ) ^ (-s/2) * (x^2) ^ (-s/2)) := by
        rw [← hpower]
        ring
      _ ≤ _ := h
  · exact (mul_le_mul_of_nonneg_left hhi (by positivity)).trans_eq hpower

theorem native_boundary_jet_norm_integrable_iff (m : ℕ) (s : ℝ)
    (hs : 0 ≤ s) :
    IntegrableOn (nativeBoundaryDensity m s) (Ioi 1) ↔
      (2 : ℝ) * m + 1 < s := by
  have hmeas : AEStronglyMeasurable (nativeBoundaryDensity m s)
      (volume.restrict (Ioi 1)) := by
    apply Measurable.aestronglyMeasurable
    unfold nativeBoundaryDensity
    fun_prop
  have hmodel : IntegrableOn
      (fun x : ℝ => x ^ ((2 : ℝ) * m - s)) (Ioi 1) ↔
      (2 : ℝ) * m + 1 < s := by
    rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    constructor <;> intro h <;> linarith
  have hbound : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)),
      (2 : ℝ) ^ (-s/2) * x ^ ((2 : ℝ)*m-s) ≤ nativeBoundaryDensity m s x ∧
      nativeBoundaryDensity m s x ≤ x ^ ((2 : ℝ)*m-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact native_boundary_density_comparison m s x hs (le_of_lt hx)
  have hpos : 0 < (2 : ℝ) ^ (-s/2) := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · intro hf
    apply hmodel.mp
    have hg : Integrable
        (fun x : ℝ => (2 : ℝ)^(-s/2) * x^((2 : ℝ)*m-s))
        (volume.restrict (Ioi 1)) := by
      apply hf.mono'
      · exact (by fun_prop : Measurable
          (fun x : ℝ => (2 : ℝ)^(-s/2) * x^((2 : ℝ)*m-s))).aestronglyMeasurable
      · filter_upwards [hbound, ae_restrict_mem measurableSet_Ioi] with x hb hx
        have hx0 : 0 ≤ x := le_trans (by norm_num) (le_of_lt hx)
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg hpos.le (Real.rpow_nonneg hx0 _))]
        exact hb.1
    have hh := hg.const_mul ((2 : ℝ)^(-s/2))⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul] using hh
  · intro h
    apply (hmodel.mpr h).mono' hmeas
    filter_upwards [hbound] with x hb
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hb.2
    · unfold nativeBoundaryDensity
      exact mul_nonneg
        (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
        (Real.rpow_nonneg (by nlinarith [sq_nonneg x]) _)

#check native_boundary_density_comparison
#print axioms native_boundary_density_comparison
#check native_boundary_jet_norm_integrable_iff
#print axioms native_boundary_jet_norm_integrable_iff
end Round189E
