import Mathlib

/-! Scalar checks for the actual radial tests in GLOBAL_R04.md.
No adelic trace equality is assumed or claimed by this file. -/
noncomputable section
namespace GeometricTraceC.NormalizationWitness

def bump (t : ℝ) : ℝ :=
  if 1 < t ∧ t < 2 then Real.exp (-((t - 1) * (2 - t))⁻¹) else 0

def sharp0 (u : ℝ) : ℝ := bump (-u)
def sharp1 (u : ℝ) : ℝ := -u * sharp0 u
def complexKernel (u : ℝ) : ℝ := Real.exp (u / 2) / (1 - Real.exp u)

theorem bump_nonneg (t : ℝ) : 0 ≤ bump t := by
  unfold bump
  split_ifs
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem sharp0_pos {u : ℝ} (hu : -2 < u ∧ u < -1) : 0 < sharp0 u := by
  have hb : 1 < -u ∧ -u < 2 := by constructor <;> linarith [hu.1, hu.2]
  simp only [sharp0, bump, if_pos hb]
  exact Real.exp_pos _

theorem sharp1_pos {u : ℝ} (hu : -2 < u ∧ u < -1) : 0 < sharp1 u := by
  exact mul_pos (by linarith [hu.2]) (sharp0_pos hu)

theorem norm_one_vanishing : sharp0 0 = 0 ∧ sharp1 0 = 0 := by
  norm_num [sharp0, sharp1, bump]

theorem complexKernel_pos {u : ℝ} (hu : u < 0) : 0 < complexKernel u := by
  exact div_pos (Real.exp_pos _) (sub_pos.mpr (Real.exp_lt_one_iff.mpr hu))

theorem both_local_integrands_pos {u : ℝ} (hu : -2 < u ∧ u < -1) :
    0 < sharp0 u * complexKernel u ∧ 0 < sharp1 u * complexKernel u := by
  have hk : 0 < complexKernel u := complexKernel_pos (by linarith [hu.2])
  exact ⟨mul_pos (sharp0_pos hu) hk, mul_pos (sharp1_pos hu) hk⟩

theorem gaussian_volume_pos_lt_one : 0 < Real.pi / 4 ∧ Real.pi / 4 < 1 := by
  constructor
  · positivity
  · linarith [Real.pi_lt_four]

/-- Instantiation of the nonunit Haar scalar, not an assumed trace formula. -/
theorem gaussian_scaling_strict {localValue : ℝ} (h : 0 < localValue) :
    (Real.pi / 4) * localValue < localValue := by
  have hb := mul_lt_mul_of_pos_right gaussian_volume_pos_lt_one.2 h
  simpa only [one_mul] using hb

theorem normalized_identity_excludes_printed
    (poles traceValue localValue : ℝ) (hpos : 0 < localValue)
    (h : poles - traceValue = (Real.pi / 4) * localValue) :
    poles - traceValue ≠ localValue := by
  rw [h]
  exact ne_of_lt (gaussian_scaling_strict hpos)

end GeometricTraceC.NormalizationWitness
#print axioms GeometricTraceC.NormalizationWitness.both_local_integrands_pos
#print axioms GeometricTraceC.NormalizationWitness.gaussian_volume_pos_lt_one
#print axioms GeometricTraceC.NormalizationWitness.normalized_identity_excludes_printed
