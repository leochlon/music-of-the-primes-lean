import Mathlib

noncomputable section
open Filter Topology
set_option linter.unnecessarySeqFocus false

/- Round 1, participant E. Supporting algebra for restricted spectral recovery.
   This file does not construct Hecke L-functions or prove GRH. -/
namespace MasulloGRH

def centralMask (c : ℂ) (m : ℕ) (z : ℂ) : ℂ := (z - c) ^ m

/-- A central vanishing factor does not annihilate an off-center point. -/
theorem centralMask_ne_zero {c z : ℂ} (m : ℕ) (h : z ≠ c) :
    centralMask c m z ≠ 0 := by
  exact pow_ne_zero _ (sub_ne_zero.mpr h)

/-- The normalization of a unitary norm twist preserves the critical line. -/
theorem unitary_shift_real_part (s : ℂ) (t : ℝ) :
    (s + (t : ℂ) * Complex.I).re = s.re := by
  simp

#check centralMask_ne_zero
#print axioms centralMask_ne_zero
#check unitary_shift_real_part
#print axioms unitary_shift_real_part

/-- The real-place positive kernel at z=3/2, after including dt/t. -/
def archKernel (t : ℝ) : ℝ := 1 / (t ^ 2 * (t - 1))

def archPrimitive (t : ℝ) : ℝ := Real.log (t - 1) - Real.log t + 1 / t

/-- A quantitative lower bound for the singularity near t=1. -/
theorem archKernel_lower {t : ℝ} (h1 : 1 < t) (h2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ archKernel t := by
  have ht : 0 < t := by linarith
  have hs : 0 < t - 1 := by linarith
  have hsq : t ^ 2 ≤ 4 := by nlinarith
  unfold archKernel
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (t - 1))
    (by positivity : 0 < t ^ 2 * (t - 1))).2
  nlinarith

/-- For two sample parameters the common singular term cancels exactly. -/
theorem archKernel_sub_reference {t : ℝ} (h0 : t ≠ 0) (h1 : t ≠ 1) :
    archKernel t - 1 / (t * (t - 1)) = -(1 / t ^ 2) := by
  unfold archKernel
  field_simp [h0, sub_ne_zero.mpr h1]
  <;> ring

#check archKernel_lower
#print axioms archKernel_lower
#check archKernel_sub_reference
#print axioms archKernel_sub_reference

/-- The singular kernel has an explicit classical primitive on (1,infinity). -/
theorem hasDerivAt_archPrimitive {t : ℝ} (ht : 1 < t) :
    HasDerivAt archPrimitive (archKernel t) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 ≠ 0 := by linarith
  have hlog := (Real.hasDerivAt_log ht1).comp t ((hasDerivAt_id t).sub_const 1)
  have hdiv := (hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0
  convert (hlog.sub (Real.hasDerivAt_log ht0)).add hdiv using 1 <;>
    dsimp [archPrimitive, archKernel] <;> field_simp [ht0, ht1] <;> ring

/-- Exact cutoff integral, with no improper-integral convention hidden. -/
theorem archKernel_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, archKernel t) = archPrimitive b - archPrimitive a := by
  have hxgt : ∀ x ∈ Set.uIcc a b, 1 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_archPrimitive (hxgt x hx)
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have hpos : 0 < x := by linarith [hxgt x hx]
    have hsub : 0 < x - 1 := by linarith [hxgt x hx]
    exact (continuousAt_const.div
      ((continuousAt_id.pow 2).mul (continuousAt_id.sub continuousAt_const))
      (by positivity)).continuousWithinAt

#check hasDerivAt_archPrimitive
#print axioms hasDerivAt_archPrimitive
#check archKernel_integral
#print axioms archKernel_integral

/-- The cutoff primitive diverges at its singular endpoint. -/
theorem archPrimitive_tendsto_atBot :
    Tendsto (fun ε : ℝ => archPrimitive (1 + ε)) (𝓝[>] 0) atBot := by
  have he : Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 1) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun ε : ℝ => 1 + ε) (𝓝[>] 0) (𝓝 (1 + 0)))
  have hl : Tendsto (fun ε : ℝ => Real.log (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp he
  have hi : Tendsto (fun ε : ℝ => 1 / (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    convert ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
      (𝓝[>] 0) (𝓝 1)).div he (by norm_num : (1 : ℝ) ≠ 0)) using 1 <;> norm_num
  have h := Real.tendsto_log_nhdsGT_zero.atBot_add (hl.neg.add hi)
  simpa [archPrimitive, sub_eq_add_neg, add_assoc] using h

#check archPrimitive_tendsto_atBot
#print axioms archPrimitive_tendsto_atBot

/-- The actual cutoff integrals, not just pointwise kernels, are unbounded. -/
theorem archKernel_integral_tendsto_atTop :
    Tendsto (fun ε : ℝ => ∫ t in (1 + ε)..2, archKernel t) (𝓝[>] 0) atTop := by
  have hneg := tendsto_neg_atBot_atTop.comp archPrimitive_tendsto_atBot
  have h : Tendsto (fun ε : ℝ => archPrimitive 2 - archPrimitive (1 + ε))
      (𝓝[>] 0) atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => archPrimitive 2)
        (𝓝[>] 0) (𝓝 (archPrimitive 2))).add_atTop hneg
  apply h.congr'
  have hu : Set.Iio (1 : ℝ) ∈ (𝓝[>] (0 : ℝ)) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [self_mem_nhdsWithin, hu] with ε hε hε1
  have he0 : 0 < ε := hε
  have he1 : ε < 1 := hε1
  exact (archKernel_integral (by linarith : 1 < 1 + ε)
    (by linarith : 1 + ε ≤ 2)).symm

/-- Paired spectral resolvents gain a second denominator. -/
theorem paired_resolvent (z w u : ℂ) (hz : z ≠ u) (hw : w ≠ u) :
    1 / (z - u) - 1 / (w - u) = (w - z) / ((z - u) * (w - u)) := by
  field_simp [sub_ne_zero.mpr hz, sub_ne_zero.mpr hw]
  <;> ring

#check archKernel_integral_tendsto_atTop
#print axioms archKernel_integral_tendsto_atTop
#check paired_resolvent
#print axioms paired_resolvent

/-- Quantitative tail bound for the proposed regularized spectral series. -/
theorem paired_resolvent_norm_le (z w u : ℂ)
    (hu : 0 < ‖u‖) (hz : 2 * ‖z‖ ≤ ‖u‖) (hw : 2 * ‖w‖ ≤ ‖u‖) :
    ‖1 / (z - u) - 1 / (w - u)‖ ≤ 4 * ‖w - z‖ / ‖u‖ ^ 2 := by
  have hzu : ‖u‖ / 2 ≤ ‖z - u‖ := by
    have h := norm_sub_norm_le u z
    rw [norm_sub_rev u z] at h
    linarith
  have hwu : ‖u‖ / 2 ≤ ‖w - u‖ := by
    have h := norm_sub_norm_le u w
    rw [norm_sub_rev u w] at h
    linarith
  have hzp : 0 < ‖z - u‖ := by linarith
  have hwp : 0 < ‖w - u‖ := by linarith
  have hzn : z ≠ u := by
    intro he
    simp [he] at hzp
  have hwn : w ≠ u := by
    intro he
    simp [he] at hwp
  rw [paired_resolvent z w u hzn hwn, norm_div, norm_mul]
  apply (div_le_div_iff₀ (mul_pos hzp hwp) (sq_pos_of_pos hu)).2
  have hprod := mul_le_mul hzu hwu (by positivity : 0 ≤ ‖u‖ / 2) (norm_nonneg (z-u))
  have hsq : ‖u‖ ^ 2 ≤ 4 * (‖z-u‖ * ‖w-u‖) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq (norm_nonneg (w-z))
  nlinarith

#check paired_resolvent_norm_le
#print axioms paired_resolvent_norm_le

/-- A bound uniform for both parameters in a closed disk. -/
theorem paired_resolvent_uniform_bound (z w u : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hu : 0 < ‖u‖) (hR : 2 * R ≤ ‖u‖) :
    ‖1 / (z - u) - 1 / (w - u)‖ ≤ 8 * R / ‖u‖ ^ 2 := by
  have hzw : ‖w-z‖ ≤ 2 * R := by
    calc
      ‖w-z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le w z
      _ ≤ 2 * R := by linarith
  calc
    ‖1 / (z-u) - 1 / (w-u)‖ ≤ 4 * ‖w-z‖ / ‖u‖ ^ 2 :=
      paired_resolvent_norm_le z w u hu (by linarith) (by linarith)
    _ ≤ 8 * R / ‖u‖ ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg ‖u‖)

#check paired_resolvent_uniform_bound
#print axioms paired_resolvent_uniform_bound
end MasulloGRH






