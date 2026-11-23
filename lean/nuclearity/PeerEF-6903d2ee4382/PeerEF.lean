import Mathlib



noncomputable section
open Filter Topology
set_option linter.unnecessarySeqFocus false

/- Round 3, participant E. Inherited public supporting lemmas. Supporting algebra for restricted spectral recovery.
   This file does not construct Hecke L-functions or prove GRH. -/
namespace Round3PeerE

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
/-- Absolute convergence of paired resolvents from an explicit inverse-square
    summability hypothesis and a cofinite tail separation. This is conditional
    analysis; no genuine Hecke counting theorem is supplied by this statement. -/
theorem paired_resolvent_summable {ι : Type*} (u : ι → ℂ) (z w : ℂ)
    (hs : Summable (fun i => 1 / ‖u i‖ ^ 2))
    (ht : ∀ᶠ i in cofinite, 0 < ‖u i‖ ∧
      2 * ‖z‖ ≤ ‖u i‖ ∧ 2 * ‖w‖ ≤ ‖u i‖) :
    Summable (fun i => 1 / (z - u i) - 1 / (w - u i)) := by
  have hb : Summable (fun i => 4 * ‖w-z‖ / ‖u i‖ ^ 2) := by
    simpa only [mul_one_div] using (Summable.mul_left (4 * ‖w-z‖) hs)
  apply hb.of_norm_bounded_eventually
  filter_upwards [ht] with i hi
  exact paired_resolvent_norm_le z w (u i) hi.1 hi.2.1 hi.2.2

/-- Uniform convergence on a parameter disk of a separated spectral tail.
    A finite complementary spectrum must be treated separately in applications. -/
theorem paired_resolvent_uniform_tsum {ι : Type*} (u : ι → ℂ) (w : ℂ) (R : ℝ)
    (hw : ‖w‖ ≤ R) (hu : ∀ i, 0 < ‖u i‖ ∧ 2 * R ≤ ‖u i‖)
    (hs : Summable (fun i => 1 / ‖u i‖ ^ 2)) :
    TendstoUniformlyOn
      (fun (s : Finset ι) z => ∑ i ∈ s, (1 / (z-u i) - 1 / (w-u i)))
      (fun z => ∑' i, (1 / (z-u i) - 1 / (w-u i)))
      atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hb : Summable (fun i => 8 * R / ‖u i‖ ^ 2) := by
    simpa only [mul_one_div] using (Summable.mul_left (8 * R) hs)
  apply tendstoUniformlyOn_tsum hb
  intro i z hz
  exact paired_resolvent_uniform_bound z w (u i) R hz hw (hu i).1 (hu i).2

/-- The exact extra hypotheses needed to pass cutoff transforms to their
    paired-resolvent limit. In particular, the bound is uniform in the cutoff. -/
theorem cutoff_spectral_limit {ι : Type*} (u : ι → ℂ) (z w : ℂ)
    (a : ℕ → ι → ℂ) (C : ℝ)
    (hs : Summable (fun i => 1 / ‖u i‖ ^ 2))
    (hl : ∀ i, Tendsto (fun n => a n i) atTop
      (𝓝 (1 / (z-u i) - 1 / (w-u i))))
    (hb : ∀ᶠ n in atTop, ∀ i, ‖a n i‖ ≤ C / ‖u i‖ ^ 2) :
    Tendsto (fun n => ∑' i, a n i) atTop
      (𝓝 (∑' i, (1 / (z-u i) - 1 / (w-u i)))) := by
  have hsum : Summable (fun i => C / ‖u i‖ ^ 2) := by
    simpa only [mul_one_div] using (Summable.mul_left C hs)
  exact tendsto_tsum_of_dominated_convergence hsum hl hb

#check paired_resolvent_summable
#print axioms paired_resolvent_summable
#check paired_resolvent_uniform_tsum
#print axioms paired_resolvent_uniform_tsum
#check cutoff_spectral_limit
#print axioms cutoff_spectral_limit
/-- Coefficient cancelling the zeroth Mellin moment of a paired family.
    The reference parameters w and v must differ in the intended application. -/
def momentCoefficient (z w v : ℂ) : ℂ := v * (w-z) / (z * (w-v))

def momentCorrected (z w v u : ℂ) : ℂ :=
  (1 / (z-u) - 1 / (w-u)) -
    momentCoefficient z w v * (1 / (v-u) - 1 / (w-u))

/-- Exact three-parameter correction; the factor u records central vanishing. -/
theorem momentCorrected_eq (z w v u : ℂ) (hz : z ≠ 0)
    (hzw : w ≠ v) (hzu : z ≠ u) (hwu : w ≠ u) (hvu : v ≠ u) :
    momentCorrected z w v u =
      u * (w-z) * (v-z) / (z * (w-u) * (z-u) * (v-u)) := by
  unfold momentCorrected momentCoefficient
  field_simp [hz, sub_ne_zero.mpr hzw, sub_ne_zero.mpr hzu,
    sub_ne_zero.mpr hwu, sub_ne_zero.mpr hvu]
  <;> ring

/-- This limiting family has the missing zeroth Mellin moment exactly zero. -/
theorem momentCorrected_at_zero (z w v : ℂ) (hz : z ≠ 0)
    (hw : w ≠ 0) (hv : v ≠ 0) (hwv : w ≠ v) :
    momentCorrected z w v 0 = 0 := by
  rw [momentCorrected_eq z w v 0 hz hwv hz hw hv]
  simp

/-- The correction still detects every off-center point away from its poles,
    provided the three transform parameters are pairwise distinct. -/
theorem momentCorrected_ne_zero (z w v u : ℂ) (hz : z ≠ 0)
    (hwv : w ≠ v) (hwz : w ≠ z) (hvz : v ≠ z) (hu : u ≠ 0)
    (hzu : z ≠ u) (hwu : w ≠ u) (hvu : v ≠ u) :
    momentCorrected z w v u ≠ 0 := by
  rw [momentCorrected_eq z w v u hz hwv hzu hwu hvu]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero hu (sub_ne_zero.mpr hwz)) (sub_ne_zero.mpr hvz))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr hwu))
      (sub_ne_zero.mpr hzu)) (sub_ne_zero.mpr hvu))

/-- Finite moment correction preserves absolute spectral summability.
    The inverse-square hypothesis is still an explicit, unproved Hecke input. -/
theorem momentCorrected_summable {ι : Type*} (u : ι → ℂ) (z w v : ℂ)
    (hs : Summable (fun i => 1 / ‖u i‖ ^ 2))
    (ht : ∀ᶠ i in cofinite, 0 < ‖u i‖ ∧ 2 * ‖z‖ ≤ ‖u i‖ ∧
      2 * ‖w‖ ≤ ‖u i‖ ∧ 2 * ‖v‖ ≤ ‖u i‖) :
    Summable (fun i => momentCorrected z w v (u i)) := by
  have hz := paired_resolvent_summable u z w hs (ht.mono fun _ h =>
    ⟨h.1, h.2.1, h.2.2.1⟩)
  have hv := paired_resolvent_summable u v w hs (ht.mono fun _ h =>
    ⟨h.1, h.2.2.2, h.2.2.1⟩)
  exact hz.sub (Summable.mul_left (momentCoefficient z w v) hv)

#check momentCorrected_eq
#print axioms momentCorrected_eq
#check momentCorrected_at_zero
#print axioms momentCorrected_at_zero
#check momentCorrected_ne_zero
#print axioms momentCorrected_ne_zero
#check momentCorrected_summable
#print axioms momentCorrected_summable
/-- Cutoff domination with a weight that also handles the central point u=0.
    The actual cutoff coefficient bound remains an explicit hypothesis. -/
theorem cutoff_spectral_limit_regular_weight {ι : Type*} (u : ι → ℂ)
    (a : ℕ → ι → ℂ) (b : ι → ℂ) (C : ℝ)
    (hs : Summable (fun i => 1 / (1 + ‖u i‖ ^ 2)))
    (hl : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (b i)))
    (hb : ∀ᶠ n in atTop, ∀ i, ‖a n i‖ ≤ C / (1 + ‖u i‖ ^ 2)) :
    Tendsto (fun n => ∑' i, a n i) atTop (𝓝 (∑' i, b i)) := by
  have hsum : Summable (fun i => C / (1 + ‖u i‖ ^ 2)) := by
    simpa only [mul_one_div] using (Summable.mul_left C hs)
  exact tendsto_tsum_of_dominated_convergence hsum hl hb

/-- Pointwise scaling estimate for the second derivative of a cutoff product.
    Multiplying by the transition interval length cancels the inverse scale.
    Variables h0,h1,h2 and g0,g1,g2 represent derivative values; no unstated
    differentiability or integration theorem is included in this statement. -/
theorem cutoff_transition_bound (h0 h1 h2 g0 g1 g2 : ℂ)
    (ε A B C M1 M2 : ℝ) (he : 0 < ε) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh0 : ‖h0‖ ≤ 1) (hh1 : ε * ‖h1‖ ≤ M1)
    (hh2 : ε ^ 2 * ‖h2‖ ≤ M2) (hg0 : ‖g0‖ ≤ A * ε)
    (hg1 : ‖g1‖ ≤ B) (hg2 : ‖g2‖ ≤ C) :
    ε * ‖h2*g0 + 2*h1*g1 + h0*g2‖ ≤ M2*A + 2*M1*B + ε*C := by
  have hs := (norm_add_le (h2*g0 + 2*h1*g1) (h0*g2)).trans
    (add_le_add (norm_add_le (h2*g0) (2*h1*g1)) le_rfl)
  norm_num [norm_mul] at hs
  have ht0 : ε * (‖h2‖ * ‖g0‖) ≤ M2*A := by
    calc
      ε * (‖h2‖ * ‖g0‖) ≤ ε * (‖h2‖ * (A*ε)) := by gcongr
      _ = (ε^2 * ‖h2‖) * A := by ring
      _ ≤ M2*A := mul_le_mul_of_nonneg_right hh2 hA
  have ht1 : ε * (2*‖h1‖*‖g1‖) ≤ 2*M1*B := by
    calc
      ε * (2*‖h1‖*‖g1‖) ≤ ε * (2*‖h1‖*B) := by gcongr
      _ = 2*(ε*‖h1‖)*B := by ring
      _ ≤ 2*M1*B := by gcongr
  have ht2 : ε * (‖h0‖ * ‖g2‖) ≤ ε*C := by
    calc
      ε * (‖h0‖ * ‖g2‖) ≤ ε * (1 * ‖g2‖) := by gcongr
      _ ≤ ε*C := by simpa only [one_mul] using mul_le_mul_of_nonneg_left hg2 he.le
  have hf := mul_le_mul_of_nonneg_left hs he.le
  nlinarith

#check cutoff_spectral_limit_regular_weight
#print axioms cutoff_spectral_limit_regular_weight
#check cutoff_transition_bound
#print axioms cutoff_transition_bound


/-- Exact correction of any finite collection of continuous moments.
    The dual test family is a substantive, explicit application hypothesis. -/
def finiteMomentCorrection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (M : ι → E →L[ℂ] ℂ) (ψ : ι → E) (f : E) : E :=
  f - ∑ j, M j f • ψ j

/-- Every finite cutoff has zero moments once corrected using actual errors. -/
theorem finiteMomentCorrection_moment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → E →L[ℂ] ℂ) (ψ : ι → E)
    (hdual : ∀ j k, M j (ψ k) = if j = k then 1 else 0) (f : E) (j : ι) :
    M j (finiteMomentCorrection M ψ f) = 0 := by
  simp [finiteMomentCorrection, map_sum, hdual, smul_eq_mul]

/-- Exact moment correction converges back to the desired zero-moment limit. -/
theorem finiteMomentCorrection_limit {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (M : ι → E →L[ℂ] ℂ) (ψ : ι → E) (f : ℕ → E) (g : E)
    (hf : Tendsto f atTop (𝓝 g)) (hg : ∀ j, M j g = 0) :
    Tendsto (fun n => finiteMomentCorrection M ψ (f n)) atTop (𝓝 g) := by
  have hc : ∀ j, Tendsto (fun n => M j (f n) • ψ j) atTop (𝓝 (0 : E)) := by
    intro j
    have h := ((M j).continuous.tendsto g).comp hf
    simpa [hg j] using h.smul_const (ψ j)
  have hs : Tendsto (fun n => ∑ j, M j (f n) • ψ j) atTop (𝓝 (0 : E)) := by
    simpa using tendsto_finset_sum Finset.univ (fun j _ => hc j)
  simpa [finiteMomentCorrection] using hf.sub hs

/-- A common transform majorant survives the finite moment correction.
    This is a pointwise norm estimate, not a Mellin realization theorem. -/
theorem finite_correction_bound {ι : Type*} [Fintype ι]
    (a : ℂ) (e b : ι → ℂ) (A : ℝ) (B C : ι → ℝ) (q : ℝ)
    (hA : ‖a‖ ≤ A*q)
    (he : ∀ j, ‖e j‖ ≤ C j) (hb : ∀ j, ‖b j‖ ≤ B j*q) :
    ‖a - ∑ j, e j * b j‖ ≤ (A + ∑ j, C j * B j)*q := by
  have hC : ∀ j, 0 ≤ C j := fun j => (norm_nonneg _).trans (he j)
  calc
    ‖a - ∑ j, e j*b j‖ ≤ ‖a‖ + ‖∑ j, e j*b j‖ := norm_sub_le _ _
    _ ≤ A*q + ∑ j, ‖e j*b j‖ := add_le_add hA (norm_sum_le _ _)
    _ ≤ A*q + ∑ j, C j * (B j*q) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (he j) (hb j) (norm_nonneg _) (hC j)
    _ = (A + ∑ j, C j*B j)*q := by
      rw [add_mul, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The elementary, finite-cutoff one-moment normalization. -/
theorem cutoff_one_moment_exact (a b : ℂ) (hb : b ≠ 0) :
    a - (a / b) * b = 0 := by
  rw [div_mul_cancel₀ a hb, sub_self]

/-- Its coefficient has the expected limit once the limiting reference moment
    is nonzero. No lower bound is silently assumed at all cutoff indices. -/
theorem cutoff_one_moment_coefficient_limit (a b : ℕ → ℂ) (A B : ℂ)
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (hB : B ≠ 0) :
    Tendsto (fun n => a n / b n) atTop (𝓝 (A/B)) := by
  exact ha.div hb hB

#check finiteMomentCorrection_moment
#print axioms finiteMomentCorrection_moment
#check finiteMomentCorrection_limit
#print axioms finiteMomentCorrection_limit
#check finite_correction_bound
#print axioms finite_correction_bound
#check cutoff_one_moment_exact
#print axioms cutoff_one_moment_exact
#check cutoff_one_moment_coefficient_limit
#print axioms cutoff_one_moment_coefficient_limit


/-- Inverse moment matrix gives fixed reference tests with dual moments. -/
def inverseMomentFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → E)
    (A : Matrix ι ι ℂ) (k : ι) : E := ∑ l, A⁻¹ l k • φ l

/-- The matrix in this statement is the ACTUAL moment matrix. Its determinant
    condition is explicit; a smooth Gram construction is described separately. -/
theorem inverseMomentFamily_dual {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → E →L[ℂ] ℂ) (φ : ι → E) (A : Matrix ι ι ℂ)
    (hA : ∀ j k, M j (φ k) = A j k) (hdet : A.det ≠ 0) (j k : ι) :
    M j (inverseMomentFamily φ A k) = if j = k then 1 else 0 := by
  calc
    M j (inverseMomentFamily φ A k) = (A * A⁻¹) j k := by
      simp [inverseMomentFamily, map_sum, hA, Matrix.mul_apply, mul_comm]
    _ = if j = k then 1 else 0 := by
      rw [Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)]
      rfl

/-- Exact all-order correction obtained from an invertible actual matrix,
    rather than assuming a dual family already exists. -/
theorem inverseMomentCorrection_moment {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : ι → E →L[ℂ] ℂ) (φ : ι → E) (A : Matrix ι ι ℂ)
    (hA : ∀ j k, M j (φ k) = A j k) (hdet : A.det ≠ 0) (f : E) (j : ι) :
    M j (finiteMomentCorrection M (inverseMomentFamily φ A) f) = 0 := by
  exact finiteMomentCorrection_moment M (inverseMomentFamily φ A)
    (inverseMomentFamily_dual M φ A hA hdet) f j

#check inverseMomentFamily_dual
#print axioms inverseMomentFamily_dual
#check inverseMomentCorrection_moment
#print axioms inverseMomentCorrection_moment


/-- Vanishing limiting moments give a simultaneous eventual coefficient bound
    for the finite correction. No separate bound on each cutoff is assumed. -/
theorem moment_errors_eventually_bounded {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
    (M : ι → E →L[ℂ] ℂ) (f : ℕ → E) (g : E)
    (hf : Tendsto f atTop (𝓝 g)) (hg : ∀ j, M j g = 0) :
    ∀ᶠ n in atTop, ∀ j, ‖M j (f n)‖ ≤ 1 := by
  rw [Filter.eventually_all]
  intro j
  have h := ((M j).continuous.tendsto g).comp hf
  have ho : IsOpen {z : ℂ | ‖z‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hz : M j g ∈ {z : ℂ | ‖z‖ < 1} := by simp [hg j]
  exact (h.eventually (ho.mem_nhds hz)).mono fun _ hn => le_of_lt hn

#check moment_errors_eventually_bounded
#print axioms moment_errors_eventually_bounded
end Round3PeerE




/-!
Participant F, round 3, proof phase. Initial checkpoint from frozen round 2. Supporting results only.
The target is GRH for all genuine unitary Hecke characters over all number fields.
No theorem below claims to construct their L-functions or prove that target.

At the trivial real place and real parameter z = 3/2, the positive-t summand
on manuscript PDF p.29, with dt/t included, tends to 1/(t^2*(t-1)).
The following identities isolate the singularity and a possible subtraction repair.
-/
namespace Round3PeerF

noncomputable def archKernel (t : ℝ) : ℝ := 1 / (t ^ 2 * (t - 1))

theorem archKernel_partialFractions (t : ℝ) (ht : t ≠ 0) (h1 : t ≠ 1) :
    archKernel t = 1 / (t - 1) - 1 / t - 1 / t ^ 2 := by
  unfold archKernel
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

theorem archKernel_subtraction (t : ℝ) (ht : t ≠ 0) (h1 : t ≠ 1) :
    archKernel t - 1 / (t ^ 3 * (t - 1)) = 1 / t ^ 3 := by
  unfold archKernel
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

theorem archKernel_lowerBound (t : ℝ) (hlo : 1 < t) (hhi : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ archKernel t := by
  unfold archKernel
  have ht : 0 < t := by linarith
  have hs : 0 < t - 1 := by linarith
  apply one_div_le_one_div_of_le (by positivity)
  have hsq : t ^ 2 ≤ 4 := by nlinarith
  nlinarith

theorem resolvent_subtraction (z w r : ℂ) (hz : z ≠ r) (hw : w ≠ r) :
    1 / (z - r) - 1 / (w - r) = (w - z) / ((z - r) * (w - r)) := by
  have hz' : z - r ≠ 0 := sub_ne_zero.mpr hz
  have hw' : w - r ≠ 0 := sub_ne_zero.mpr hw
  field_simp
  ring

theorem resolvent_norm_bound (z w r : ℂ) (R : ℝ) (hR : 0 < R)
    (hz : R ≤ ‖z - r‖) (hw : R ≤ ‖w - r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ ‖w - z‖ / R ^ 2 := by
  have hz0 : z ≠ r := by
    intro heq
    rw [heq, sub_self, norm_zero] at hz
    linarith
  have hw0 : w ≠ r := by
    intro heq
    rw [heq, sub_self, norm_zero] at hw
    linarith
  rw [resolvent_subtraction z w r hz0 hw0, norm_div, norm_mul]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hR)
  have h := mul_le_mul hz hw (le_of_lt hR) (norm_nonneg (z - r))
  nlinarith

theorem logarithmic_endpoint_unbounded (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ B < -Real.log δ := by
  refine ⟨Real.exp (-(|B| + 1)), Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have := abs_nonneg B
    linarith
  · rw [Real.log_exp]
    have := le_abs_self B
    linarith

theorem singular_integral (δ : ℝ) (hδ : 0 < δ) :
    (∫ t in (1 + δ)..2, 1 / (t - 1)) = -Real.log δ := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => 1 / x) 1]
  have ha : 1 + δ - 1 = δ := by ring
  rw [ha]
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num]
  rw [integral_one_div_of_pos hδ (by norm_num),
    Real.log_div (by norm_num) (ne_of_gt hδ), Real.log_one, zero_sub]

theorem archKernel_integral_lowerBound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    -Real.log δ / 4 ≤ ∫ t in (1 + δ)..2, archKernel t := by
  have hab : 1 + δ ≤ (2 : ℝ) := by linarith
  have hp : ∀ t ∈ Set.uIcc (1 + δ) 2, 1 < t := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    linarith [ht.1]
  have hc : ContinuousOn (fun t : ℝ => 1 / (t - 1)) (Set.uIcc (1 + δ) 2) := by
    apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    intro t ht
    change t - 1 ≠ 0
    linarith [hp t ht]
  have hk : ContinuousOn archKernel (Set.uIcc (1 + δ) 2) := by
    unfold archKernel
    apply continuousOn_const.div ((continuousOn_id.pow 2).mul
      (continuousOn_id.sub continuousOn_const))
    intro t ht
    have h : 1 < t := hp t ht
    change t ^ 2 * (t - 1) ≠ 0
    have ht0 : 0 < t := by linarith
    have hs : 0 < t - 1 := by linarith
    positivity
  have hcomp := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hc.intervalIntegrable.div_const 4) hk.intervalIntegrable
    (fun t ht => by
      have ht1 : 1 < t := by linarith [ht.1]
      have h := archKernel_lowerBound t ht1 ht.2
      simpa only [div_div, mul_comm] using h)
  rw [intervalIntegral.integral_div, singular_integral δ hδ] at hcomp
  exact hcomp

theorem archKernel_integral_unbounded (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ B < ∫ t in (1 + δ)..2, archKernel t := by
  obtain ⟨δ, hδ, hδ1, hlarge⟩ := logarithmic_endpoint_unbounded (4 * B)
  refine ⟨δ, hδ, hδ1, ?_⟩
  have h := archKernel_integral_lowerBound δ hδ hδ1
  linarith

end Round3PeerF

#check Round3PeerF.archKernel_partialFractions
#print axioms Round3PeerF.archKernel_partialFractions
#check Round3PeerF.archKernel_subtraction
#print axioms Round3PeerF.archKernel_subtraction
#check Round3PeerF.archKernel_lowerBound
#print axioms Round3PeerF.archKernel_lowerBound
#check Round3PeerF.resolvent_subtraction
#print axioms Round3PeerF.resolvent_subtraction
#check Round3PeerF.resolvent_norm_bound
#print axioms Round3PeerF.resolvent_norm_bound
#check Round3PeerF.logarithmic_endpoint_unbounded
#print axioms Round3PeerF.logarithmic_endpoint_unbounded
#check Round3PeerF.singular_integral
#print axioms Round3PeerF.singular_integral
#check Round3PeerF.archKernel_integral_lowerBound
#print axioms Round3PeerF.archKernel_integral_lowerBound
#check Round3PeerF.archKernel_integral_unbounded
#print axioms Round3PeerF.archKernel_integral_unbounded

namespace Round3PeerF

/-- Triangle-inequality specialization of the round-1 denominator bound.
Adapted from frozen round-1 C/E, with the denominator estimate proved here. -/
theorem resolvent_tail_bound (z w r : ℂ) (hr : 0 < ‖r‖)
    (hz : 2 * ‖z‖ ≤ ‖r‖) (hw : 2 * ‖w‖ ≤ ‖r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ 4 * ‖w - z‖ / ‖r‖ ^ 2 := by
  have hzL : ‖r‖ / 2 ≤ ‖z - r‖ := by
    have h := norm_sub_norm_le r z
    rw [norm_sub_rev] at h
    linarith
  have hwL : ‖r‖ / 2 ≤ ‖w - r‖ := by
    have h := norm_sub_norm_le r w
    rw [norm_sub_rev] at h
    linarith
  have h := resolvent_norm_bound z w r (‖r‖ / 2) (by positivity) hzL hwL
  convert h using 1
  ring

/-- A common summable majorant on a parameter disk; this controls the limiting
resolvents, not the Mellin transforms of cutoff approximants. -/
theorem resolvent_disk_bound (z w r : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hr : 0 < ‖r‖)
    (hlarge : 2 * R ≤ ‖r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ (8 * R) * (1 / ‖r‖ ^ 2) := by
  have hzw : ‖w - z‖ ≤ 2 * R := (norm_sub_le w z).trans (by linarith)
  calc
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ 4 * ‖w - z‖ / ‖r‖ ^ 2 :=
      resolvent_tail_bound z w r hr (by linarith) (by linarith)
    _ ≤ (8 * R) * (1 / ‖r‖ ^ 2) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

/-- Absolute convergence of the paired resolvent tail from an explicit
inverse-square summability hypothesis. No Hecke zero count is assumed proved. -/
theorem paired_resolvent_summable (r : ℕ → ℂ) (z w : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 0 < ‖r n‖) (hlarge : ∀ n, 2 * R ≤ ‖r n‖)
    (hs : Summable (fun n => 1 / ‖r n‖ ^ 2)) :
    Summable (fun n => 1 / (z - r n) - 1 / (w - r n)) := by
  exact (hs.mul_left (8 * R)).of_norm_bounded
    (fun n => resolvent_disk_bound z w (r n) R hz hw (hr n) (hlarge n))

/-- The paired resolvent tail converges uniformly on a closed parameter disk.
The summability hypothesis must still be established for genuine Hecke zeros. -/
theorem paired_resolvent_uniform_convergence (r : ℕ → ℂ) (w : ℂ) (R : ℝ)
    (hw : ‖w‖ ≤ R) (hr : ∀ n, 0 < ‖r n‖)
    (hlarge : ∀ n, 2 * R ≤ ‖r n‖)
    (hs : Summable (fun n => 1 / ‖r n‖ ^ 2)) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, (1 / (z - r n) - 1 / (w - r n)))
      (fun z => ∑' n, (1 / (z - r n) - 1 / (w - r n)))
      Filter.atTop {z : ℂ | ‖z‖ ≤ R} := by
  exact tendstoUniformlyOn_tsum_nat (hs.mul_left (8 * R))
    (fun n z hz => resolvent_disk_bound z w (r n) R hz hw (hr n) (hlarge n))

end Round3PeerF
#check Round3PeerF.resolvent_tail_bound
#print axioms Round3PeerF.resolvent_tail_bound
#check Round3PeerF.resolvent_disk_bound
#print axioms Round3PeerF.resolvent_disk_bound
#check Round3PeerF.paired_resolvent_summable
#print axioms Round3PeerF.paired_resolvent_summable
#check Round3PeerF.paired_resolvent_uniform_convergence
#print axioms Round3PeerF.paired_resolvent_uniform_convergence

namespace Round3PeerF

/-- Holomorphy of the paired resolvent tail. This is conditional analytic
work: the genuine zero divisor and its inverse-square count are not built here. -/
theorem paired_resolvent_differentiableOn (r : ℕ → ℂ) (w : ℂ) (R : ℝ)
    (hw : ‖w‖ ≤ R) (hr : ∀ n, 0 < ‖r n‖)
    (hlarge : ∀ n, 2 * R ≤ ‖r n‖)
    (hs : Summable (fun n => 1 / ‖r n‖ ^ 2)) :
    DifferentiableOn ℂ
      (fun z => ∑' n, (1 / (z - r n) - 1 / (w - r n)))
      {z : ℂ | ‖z‖ < R} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (hs.mul_left (8 * R))
  · intro n
    apply DifferentiableOn.sub _ (differentiableOn_const _)
    apply (differentiableOn_const _).div (differentiableOn_id.sub (differentiableOn_const _))
    intro z hz
    apply sub_ne_zero.mpr
    intro heq
    have hzR : ‖z‖ < R := hz
    rw [heq] at hzR
    have hn := hlarge n
    have hp := hr n
    linarith
  · exact isOpen_lt continuous_norm continuous_const
  · intro n z hz
    exact resolvent_disk_bound z w (r n) R (le_of_lt hz) hw (hr n) (hlarge n)

/-- The correct sufficient hypothesis for moving a cutoff limit through the
spectral sum is a bound uniform in the cutoff index. This theorem does not
construct cutoff coefficients or assert that the manuscript supplies the bound. -/
theorem paired_resolvent_cutoff_limit (r : ℕ → ℂ) (z w : ℂ) (C : ℝ)
    (hs : Summable (fun k => 1 / ‖r k‖ ^ 2))
    (a : ℕ → ℕ → ℂ)
    (ha : ∀ k, Filter.Tendsto (fun n => a n k) Filter.atTop
      (nhds (1 / (z - r k) - 1 / (w - r k))))
    (hb : ∀ n k, ‖a n k‖ ≤ C * (1 / ‖r k‖ ^ 2)) :
    Filter.Tendsto (fun n => ∑' k, a n k) Filter.atTop
      (nhds (∑' k, (1 / (z - r k) - 1 / (w - r k)))) := by
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left C) ha
    (Filter.Eventually.of_forall hb)

end Round3PeerF
#check Round3PeerF.paired_resolvent_differentiableOn
#print axioms Round3PeerF.paired_resolvent_differentiableOn
#check Round3PeerF.paired_resolvent_cutoff_limit
#print axioms Round3PeerF.paired_resolvent_cutoff_limit

namespace Round3PeerF

/-- The intersection of the kernels of evaluations of height at most T shrinks
as T increases. This audits manuscript (9.3.2.10), PDF p.426. -/
theorem low_constraint_antitone {V I : Type*} (e : I → V → ℂ)
    (height : I → ℝ) (T U : ℝ) (hTU : T ≤ U) :
    {v : V | ∀ i, height i ≤ U → e i v = 0} ⊆
      {v : V | ∀ i, height i ≤ T → e i v = 0} := by
  intro v hv i hi
  exact hv i (hi.trans hTU)

/-- Strong convergence to the identity is incompatible with eventually
annihilating a fixed nonzero continuous coordinate of a vector. -/
theorem strong_limit_preserves_zero_coordinate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : E →L[ℂ] ℂ) (P : ℕ → E → E) (v : E) (N : ℕ)
    (hzero : ∀ n, N ≤ n → e (P n v) = 0)
    (hlim : Filter.Tendsto (fun n => P n v) Filter.atTop (nhds v)) :
    e v = 0 := by
  have hmap := (e.continuous.tendsto v).comp hlim
  have hzeroLim : Filter.Tendsto (fun n => e (P n v)) Filter.atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact (hzero n hn).symm
  exact tendsto_nhds_unique hmap hzeroLim

/-- A nonzero coordinate gives an explicit obstruction to the literal
low-zero-kernel projection scheme of Theorem 9.3.2.6. -/
theorem low_kernel_projection_not_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : E →L[ℂ] ℂ) (P : ℕ → E → E) (v : E) (N : ℕ)
    (hv : e v ≠ 0) (hzero : ∀ n, N ≤ n → e (P n v) = 0) :
    ¬ Filter.Tendsto (fun n => P n v) Filter.atTop (nhds v) := by
  intro hlim
  exact hv (strong_limit_preserves_zero_coordinate e P v N hzero hlim)

end Round3PeerF
#check Round3PeerF.low_constraint_antitone
#print axioms Round3PeerF.low_constraint_antitone
#check Round3PeerF.strong_limit_preserves_zero_coordinate
#print axioms Round3PeerF.strong_limit_preserves_zero_coordinate
#check Round3PeerF.low_kernel_projection_not_identity
#print axioms Round3PeerF.low_kernel_projection_not_identity

namespace Round3PeerF

/-- Defense against C's central-zero objection: the regular weight is positive
at r=0, so this conditional cutoff theorem can cover finite central terms too.
The coefficient bounds and genuine divisor count remain explicit hypotheses. -/
theorem paired_resolvent_cutoff_limit_regular_weight
    (r : ℕ → ℂ) (z w : ℂ) (C : ℝ)
    (hs : Summable (fun k => 1 / (1 + ‖r k‖ ^ 2)))
    (a : ℕ → ℕ → ℂ)
    (ha : ∀ k, Filter.Tendsto (fun n => a n k) Filter.atTop
      (nhds (1 / (z - r k) - 1 / (w - r k))))
    (hb : ∀ n k, ‖a n k‖ ≤ C * (1 / (1 + ‖r k‖ ^ 2))) :
    Filter.Tendsto (fun n => ∑' k, a n k) Filter.atTop
      (nhds (∑' k, (1 / (z - r k) - 1 / (w - r k)))) := by
  exact tendsto_tsum_of_dominated_convergence (hs.mul_left C) ha
    (Filter.Eventually.of_forall hb)

end Round3PeerF
#check Round3PeerF.paired_resolvent_cutoff_limit_regular_weight
#print axioms Round3PeerF.paired_resolvent_cutoff_limit_regular_weight

namespace Round3PeerF

/-- The regular weight detects bounded occurrences, including repeated zeros.
Consequently its summability forces the entire indexed divisor to escape. -/
theorem regular_weight_norm_escape (r : ℕ → ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2)))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∀ n, N ≤ n → R ≤ ‖r n‖ := by
  have he := hs.tendsto_atTop_zero.eventually_lt_const
    (by positivity : (0 : ℝ) < 1 / (1 + R ^ 2))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  by_contra h
  have hlt : ‖r n‖ < R := lt_of_not_ge h
  have hi : 1 / (1 + R ^ 2) ≤ 1 / (1 + ‖r n‖ ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [norm_nonneg (r n)]
  exact (not_lt_of_ge hi) (hN n hn)

/-- On a tail outside the unit disk the regular summable weight controls
inverse squares. Unlike the singular weight, it cannot hide zero entries. -/
theorem inverse_square_summable_of_regular (r : ℕ → ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2)))
    (hr : ∀ n, 1 ≤ ‖r n‖) :
    Summable (fun n => 1 / ‖r n‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (hs.mul_left 2)
  intro n
  have hh := hr n
  have hp : 0 < ‖r n‖ ^ 2 := by positivity
  rw [mul_one_div]
  apply (div_le_div_iff₀ hp (by positivity)).2
  nlinarith

/-- Full pointwise summability, with all finite low points retained. This is
still an abstract divisor theorem, not a constructed Hecke zero count. -/
theorem paired_resolvent_summable_regular (r : ℕ → ℂ) (z w : ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2))) :
    Summable (fun n => 1 / (z - r n) - 1 / (w - r n)) := by
  let R : ℝ := ‖z‖ + ‖w‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨N, hN⟩ := regular_weight_norm_escape r hs (2 * R) (by positivity)
  apply (summable_nat_add_iff N).mp
  have hsN : Summable (fun n => 1 / (1 + ‖r (n + N)‖ ^ 2)) :=
    (summable_nat_add_iff N).mpr hs
  have ht : ∀ n, 2 * R ≤ ‖r (n + N)‖ := fun n => hN _ (Nat.le_add_left N n)
  have hu : ∀ n, 1 ≤ ‖r (n + N)‖ := by
    intro n
    have hh := ht n
    dsimp [R] at hh
    linarith [norm_nonneg z, norm_nonneg w]
  exact paired_resolvent_summable (fun n => r (n + N)) z w R
    (by dsimp [R]; linarith [norm_nonneg w])
    (by dsimp [R]; linarith [norm_nonneg z])
    (fun n => lt_of_lt_of_le (by norm_num) (hu n)) ht
    (inverse_square_summable_of_regular _ hsN hu)

/-- The full paired series is holomorphic at every point outside the indexed
divisor. A finite initial part is kept explicitly; no far-tail hypothesis on
the whole divisor is needed. Repetitions are allowed. -/
theorem paired_resolvent_differentiableAt_regular (r : ℕ → ℂ) (z w : ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2)))
    (hz : ∀ n, z ≠ r n) :
    DifferentiableAt ℂ (fun u => ∑' n, (1 / (u - r n) - 1 / (w - r n))) z := by
  let R : ℝ := ‖z‖ + ‖w‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨N, hN⟩ := regular_weight_norm_escape r hs (2 * R) (by positivity)
  have hsN : Summable (fun n => 1 / (1 + ‖r (n + N)‖ ^ 2)) :=
    (summable_nat_add_iff N).mpr hs
  have ht : ∀ n, 2 * R ≤ ‖r (n + N)‖ := fun n => hN _ (Nat.le_add_left N n)
  have hu : ∀ n, 1 ≤ ‖r (n + N)‖ := by
    intro n
    have hh := ht n
    dsimp [R] at hh
    linarith [norm_nonneg z, norm_nonneg w]
  have htail := paired_resolvent_differentiableOn (fun n => r (n + N)) w R
    (by dsimp [R]; linarith [norm_nonneg z])
    (fun n => lt_of_lt_of_le (by norm_num) (hu n)) ht
    (inverse_square_summable_of_regular _ hsN hu)
  have htailAt := htail.differentiableAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by dsimp [R]; linarith [norm_nonneg w] : ‖z‖ < R))
  have hhead : DifferentiableAt ℂ
      (fun u => ∑ n ∈ Finset.range N, (1 / (u - r n) - 1 / (w - r n))) z := by
    apply DifferentiableAt.fun_sum
    intro n _
    exact ((differentiableAt_const (1 : ℂ)).div
      (differentiableAt_id.sub_const (r n)) (sub_ne_zero.mpr (hz n))).sub_const _
  have heq : (fun u => (∑ n ∈ Finset.range N, (1 / (u - r n) - 1 / (w - r n))) +
      ∑' n, (1 / (u - r (n + N)) - 1 / (w - r (n + N)))) =
      (fun u => ∑' n, (1 / (u - r n) - 1 / (w - r n))) := by
    funext u
    exact (paired_resolvent_summable_regular r u w hs).sum_add_tsum_nat_add N
  rw [← heq]
  exact hhead.add htailAt

end Round3PeerF
#check Round3PeerF.regular_weight_norm_escape
#print axioms Round3PeerF.regular_weight_norm_escape
#check Round3PeerF.inverse_square_summable_of_regular
#print axioms Round3PeerF.inverse_square_summable_of_regular
#check Round3PeerF.paired_resolvent_summable_regular
#print axioms Round3PeerF.paired_resolvent_summable_regular
#check Round3PeerF.paired_resolvent_differentiableAt_regular
#print axioms Round3PeerF.paired_resolvent_differentiableAt_regular

namespace Round3PeerF

/-- One summand contributes one at its pole and zero at every other point.
This is a punctured limit and is independent of the totalized pole value. -/
theorem paired_resolvent_scaled_limit (q r w : ℂ) :
    Filter.Tendsto (fun u : ℂ => (u-q) * (1/(u-r) - 1/(w-r)))
      (nhdsWithin q ({q}ᶜ : Set ℂ)) (nhds (if r = q then 1 else 0)) := by
  classical
  by_cases hr : r = q
  · subst r
    simp only [ite_true]
    have hh : ContinuousAt (fun u : ℂ => 1 - (u-q) * (1/(w-q))) q := by fun_prop
    have hl : Filter.Tendsto (fun u : ℂ => 1 - (u-q) * (1/(w-q)))
        (nhdsWithin q ({q}ᶜ : Set ℂ)) (nhds 1) := by
      simpa using hh.tendsto.mono_left nhdsWithin_le_nhds
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    have huq : u-q ≠ 0 := sub_ne_zero.mpr (by simpa using hu)
    field_simp
  · simp only [if_neg hr]
    have hh : ContinuousAt (fun u : ℂ => (u-q) * (1/(u-r) - 1/(w-r))) q := by
      apply (continuousAt_id.sub_const q).mul
      exact (continuousAt_const.div (continuousAt_id.sub_const r)
        (sub_ne_zero.mpr (Ne.symm hr))).sub continuousAt_const
    simpa using hh.tendsto.mono_left nhdsWithin_le_nhds

/-- Every residue of the entire paired series is the finite number of its
indexed occurrences. Holomorphy of the infinite remainder is derived from
regular-weight summability, not inserted as a premise. -/
theorem paired_resolvent_residue_regular (r : ℕ → ℂ) (q w : ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2))) :
    ∃ N : ℕ, (∀ n, N ≤ n → r n ≠ q) ∧
      Filter.Tendsto (fun u : ℂ => (u-q) *
        (∑' n, (1/(u-r n) - 1/(w-r n))))
        (nhdsWithin q ({q}ᶜ : Set ℂ))
        (nhds (∑ n ∈ Finset.range N, if r n = q then (1 : ℂ) else 0)) := by
  classical
  let R : ℝ := ‖q‖ + ‖w‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨N, hN⟩ := regular_weight_norm_escape r hs (2 * R) (by positivity)
  have hsN : Summable (fun n => 1 / (1 + ‖r (n + N)‖ ^ 2)) :=
    (summable_nat_add_iff N).mpr hs
  have ht : ∀ n, 2 * R ≤ ‖r (n + N)‖ := fun n => hN _ (Nat.le_add_left N n)
  have hu : ∀ n, 1 ≤ ‖r (n + N)‖ := by
    intro n
    have hh := ht n
    dsimp [R] at hh
    linarith [norm_nonneg q, norm_nonneg w]
  have htail := paired_resolvent_differentiableOn (fun n => r (n + N)) w R
    (by dsimp [R]; linarith [norm_nonneg q])
    (fun n => lt_of_lt_of_le (by norm_num) (hu n)) ht
    (inverse_square_summable_of_regular _ hsN hu)
  have hc := (htail.differentiableAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (by dsimp [R]; linarith [norm_nonneg w] : ‖q‖ < R))).continuousAt
  have hzero : Filter.Tendsto (fun u : ℂ => (u-q) *
      (∑' n, (1/(u-r (n+N)) - 1/(w-r (n+N)))))
      (nhdsWithin q ({q}ᶜ : Set ℂ)) (nhds 0) := by
    simpa using ((continuousAt_id.sub_const q).mul hc).mono_left
      (nhdsWithin_le_nhds : nhdsWithin q ({q}ᶜ : Set ℂ) ≤ nhds q)
  have hhead := tendsto_finset_sum (Finset.range N)
    (fun n _ => paired_resolvent_scaled_limit q (r n) w)
  have hall := hhead.add hzero
  simp only [add_zero] at hall
  refine ⟨N, ?_, ?_⟩
  · intro n hn heq
    have hh := hN n hn
    rw [heq] at hh
    dsimp [R] at hh
    linarith [norm_nonneg q, norm_nonneg w]
  · convert hall using 1
    funext u
    rw [← (paired_resolvent_summable_regular r u w hs).sum_add_tsum_nat_add N,
      mul_add, Finset.mul_sum]

/-- Positive multiplicities cannot cancel: every point that actually occurs
is a nonremovable singularity of the complete paired series. -/
theorem paired_resolvent_not_continuousAt_regular (r : ℕ → ℂ) (q w : ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2)))
    (hq : ∃ n, r n = q) :
    ¬ ContinuousAt (fun u => ∑' n, (1/(u-r n) - 1/(w-r n))) q := by
  classical
  obtain ⟨N, hN, hres⟩ := paired_resolvent_residue_regular r q w hs
  obtain ⟨i, hi⟩ := hq
  have hiN : i < N := by
    by_contra hh
    exact hN i (Nat.le_of_not_gt hh) hi
  have hpos : 0 < ∑ n ∈ Finset.range N, if r n = q then (1 : ℝ) else 0 := by
    apply Finset.sum_pos'
    · intro n _
      split_ifs <;> norm_num
    · exact ⟨i, Finset.mem_range.mpr hiN, by simp [hi]⟩
  have hne : (∑ n ∈ Finset.range N, if r n = q then (1 : ℂ) else 0) ≠ 0 := by
    have hh : (∑ n ∈ Finset.range N, if r n = q then (1 : ℝ) else 0) ≠ 0 := ne_of_gt hpos
    exact_mod_cast hh
  intro hc
  have hz : Filter.Tendsto (fun u : ℂ => (u-q) *
      (∑' n, (1/(u-r n) - 1/(w-r n))))
      (nhdsWithin q ({q}ᶜ : Set ℂ)) (nhds 0) := by
    simpa using ((continuousAt_id.sub_const q).mul hc).mono_left
      (nhdsWithin_le_nhds : nhdsWithin q ({q}ᶜ : Set ℂ) ≤ nhds q)
  exact hne (tendsto_nhds_unique hres hz)

end Round3PeerF
#check Round3PeerF.paired_resolvent_scaled_limit
#print axioms Round3PeerF.paired_resolvent_scaled_limit
#check Round3PeerF.paired_resolvent_residue_regular
#print axioms Round3PeerF.paired_resolvent_residue_regular
#check Round3PeerF.paired_resolvent_not_continuousAt_regular
#print axioms Round3PeerF.paired_resolvent_not_continuousAt_regular

namespace Round3PeerF
/-- Exact recovery of the support of an abstract positive divisor from the
singularities of its entire paired sum, under one summable regular weight. -/
theorem paired_resolvent_continuousAt_iff (r : ℕ → ℂ) (q w : ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2))) :
    ContinuousAt (fun u => ∑' n, (1/(u-r n) - 1/(w-r n))) q ↔
      ∀ n, q ≠ r n := by
  constructor
  · intro hc n hn
    exact paired_resolvent_not_continuousAt_regular r q w hs ⟨n, hn.symm⟩ hc
  · intro hq
    exact (paired_resolvent_differentiableAt_regular r q w hs hq).continuousAt

/-- No omitted finite spectral point is concealed by the analytic tail. -/
theorem paired_resolvent_differentiableAt_iff (r : ℕ → ℂ) (q w : ℂ)
    (hs : Summable (fun n => 1 / (1 + ‖r n‖ ^ 2))) :
    DifferentiableAt ℂ (fun u => ∑' n, (1/(u-r n) - 1/(w-r n))) q ↔
      ∀ n, q ≠ r n := by
  constructor
  · intro hd
    exact (paired_resolvent_continuousAt_iff r q w hs).mp hd.continuousAt
  · exact paired_resolvent_differentiableAt_regular r q w hs
end Round3PeerF
#check Round3PeerF.paired_resolvent_continuousAt_iff
#print axioms Round3PeerF.paired_resolvent_continuousAt_iff
#check Round3PeerF.paired_resolvent_differentiableAt_iff
#print axioms Round3PeerF.paired_resolvent_differentiableAt_iff

