import Mathlib

/-! Participant B, round 1. Exact premise addressed: holomorphic norm-coordinate
cutoffs and their size estimates in manuscript 1.4.2; boundary-kernel obstruction
to the uniform Archimedean estimate asserted in 1.4.3. No trace axiom is declared.
The genuine arithmetic input remains preserved in HeckeInput.lean. -/
namespace ConditionalGRH.B

noncomputable def logTest (h : ℝ → ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (h x : ℂ) * Complex.exp (-z * (x : ℂ))

/-- Discharges the parameter-holomorphy premise of 1.4.2 at each log-norm. -/
theorem logTest_entire (h : ℝ → ℝ) (x : ℝ) :
    Differentiable ℂ (fun z => logTest h z x) := by
  unfold logTest
  fun_prop

/-- Discharges exact norm-one vanishing when the scalar cutoff vanishes at zero. -/
theorem logTest_zero (h : ℝ → ℝ) (hh : h 0 = 0) (z : ℂ) :
    logTest h z 0 = 0 := by
  simp [logTest, hh]

/-- Exact local size; this does not assert integrability against the singular kernel. -/
theorem logTest_norm (h : ℝ → ℝ) (z : ℂ) (x : ℝ) :
    ‖logTest h z x‖ = |h x| * Real.exp (-z.re * x) := by
  simp [logTest, Complex.norm_exp, Complex.mul_re]

/-- Uniform envelope on a closed right half-plane, independent of the cutoff. -/
theorem logTest_bound (h : ℝ → ℝ) (z : ℂ) (x σ : ℝ)
    (hh0 : 0 ≤ h x) (hh1 : h x ≤ 1) (hx : 0 ≤ x) (hz : σ ≤ z.re) :
    ‖logTest h z x‖ ≤ Real.exp (-σ * x) := by
  rw [logTest_norm, abs_of_nonneg hh0]
  calc
    h x * Real.exp (-z.re * x) ≤ 1 * Real.exp (-z.re * x) :=
      mul_le_mul_of_nonneg_right hh1 (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (-σ * x) := by
      simp only [one_mul]
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The real-place positive branch at z=3/2 is 1/(t²(t-1)).
This lower bound identifies the precise nonintegrable boundary majorant in 1.4.3. -/
theorem realPlace_boundary_lower_bound (t : ℝ) (ht : 1 < t) (ht2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ 1 / (t ^ 2 * (t - 1)) := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t ^ 2 * (t - 1) := mul_pos (sq_pos_of_pos ht0) (sub_pos.mpr ht)
  apply one_div_le_one_div_of_le hd
  have ht_sq : t ^ 2 ≤ 4 := by nlinarith
  nlinarith

#check logTest_entire
#print axioms logTest_entire
#check logTest_zero
#print axioms logTest_zero
#check logTest_norm
#print axioms logTest_norm
#check logTest_bound
#print axioms logTest_bound
#check realPlace_boundary_lower_bound
#print axioms realPlace_boundary_lower_bound
/-- An explicit Mathlib smooth bump supported strictly above log-norm zero.
Its plateau is [2δ, 2R-2δ], so δ↓0 and R↑∞ exhaust every positive log-norm. -/
noncomputable def logCutoff (δ R : ℝ) (hδ : 0 < δ) (hR : 2 * δ < R) :
    ContDiffBump R where
  rIn := R - 2 * δ
  rOut := R - δ
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- Discharges smoothness, compact support and [0,1] cutoff requirements in 1.4.2. -/
theorem logCutoff_regular (δ R : ℝ) (hδ : 0 < δ) (hR : 2 * δ < R) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => logCutoff δ R hδ hR x) ∧
    HasCompactSupport (fun x => logCutoff δ R hδ hR x) ∧
    (∀ x, 0 ≤ logCutoff δ R hδ hR x ∧ logCutoff δ R hδ hR x ≤ 1) := by
  exact ⟨(logCutoff δ R hδ hR).contDiff,
    (logCutoff δ R hδ hR).hasCompactSupport,
    fun _ => ⟨(logCutoff δ R hδ hR).nonneg, (logCutoff δ R hδ hR).le_one⟩⟩

/-- Discharges the support gap at norm one, stronger than pointwise vanishing. -/
theorem logCutoff_zero_below (δ R : ℝ) (hδ : 0 < δ) (hR : 2 * δ < R)
    (x : ℝ) (hx : x ≤ δ) : logCutoff δ R hδ hR x = 0 := by
  apply (logCutoff δ R hδ hR).zero_of_le_dist
  change R - δ ≤ dist x R
  rw [Real.dist_eq, abs_of_nonpos (by linarith : x - R ≤ 0)]
  linarith

/-- Exact equality on the plateau gives uniform approximation on any compact
positive log-norm interval, simultaneously for every complex parameter. -/
theorem logCutoff_one (δ R : ℝ) (hδ : 0 < δ) (hR : 2 * δ < R)
    (x : ℝ) (hx0 : 2 * δ ≤ x) (hx1 : x ≤ 2 * R - 2 * δ) :
    logCutoff δ R hδ hR x = 1 := by
  apply (logCutoff δ R hδ hR).one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  change |x - R| ≤ R - 2 * δ
  rw [abs_le]
  constructor <;> linarith

/-- Exact compact-interior approximation premise, with no assumed convergence. -/
theorem cutoffTest_exact_on_plateau (δ R : ℝ) (hδ : 0 < δ) (hR : 2 * δ < R)
    (x : ℝ) (hx0 : 2 * δ ≤ x) (hx1 : x ≤ 2 * R - 2 * δ) (z : ℂ) :
    logTest (fun x => logCutoff δ R hδ hR x) z x = Complex.exp (-z * (x : ℂ)) := by
  simp [logTest, logCutoff_one δ R hδ hR x hx0 hx1]

#check logCutoff_regular
#print axioms logCutoff_regular
#check logCutoff_zero_below
#print axioms logCutoff_zero_below
#check logCutoff_one
#print axioms logCutoff_one
#check cutoffTest_exact_on_plateau
#print axioms cutoffTest_exact_on_plateau
end ConditionalGRH.B
