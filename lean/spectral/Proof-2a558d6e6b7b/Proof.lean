import Mathlib

/-! E, round 18. Supporting analysis for manuscript §§1.4.2–1.4.5.
The original finite-idelic source and receipt are preserved in preserved/.
This file proves a quantitative bound for the SUBTRACTED Mellin resolvent.
It discharges the limiting-kernel part of obligation T4, not the cutoff
limit T3, genuine-Hecke zero count, or the trace-to-GRH theorem.
No zero set or substitute spectral operator is defined here. -/

namespace CriticalLineReview

/-- Algebra of the Mellin transform after subtraction at a fixed parameter.
Named premise T4: cancellation improves one resolvent to two denominators. -/
theorem resolvent_difference (z w u : ℂ) (hz : z - u ≠ 0) (hw : w - u ≠ 0) :
    (z - u)⁻¹ - (w - u)⁻¹ = (w - z) / ((z - u) * (w - u)) := by
  field_simp
  ring

/-- Named premise T4: a common integrable inverse-square majorant for the
limiting subtracted Mellin transform, with an explicit constant. -/
theorem norm_resolvent_difference_le (z w u : ℂ) (d R : ℝ)
    (hd : 0 < d) (hz : d ≤ ‖z - u‖) (hw : d ≤ ‖w - u‖)
    (hzR : ‖z‖ ≤ R) (hwR : ‖w‖ ≤ R) :
    ‖(z - u)⁻¹ - (w - u)⁻¹‖ ≤
      ((1 + (1 + R) / d)^2 * ‖w - z‖) / (1 + ‖u‖^2) := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hzR
  have hz0 : z - u ≠ 0 := norm_pos_iff.mp (hd.trans_le hz)
  have hw0 : w - u ≠ 0 := norm_pos_iff.mp (hd.trans_le hw)
  have hc : 0 ≤ 1 + (1 + R) / d := by positivity
  have hztri : ‖u‖ ≤ ‖z - u‖ + R := by
    calc
      ‖u‖ = ‖(u - z) + z‖ := by congr 1; ring
      _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z - u‖ + R := by rw [norm_sub_rev u z]; linarith
  have hwtri : ‖u‖ ≤ ‖w - u‖ + R := by
    calc
      ‖u‖ = ‖(u - w) + w‖ := by congr 1; ring
      _ ≤ ‖u - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ‖w - u‖ + R := by rw [norm_sub_rev u w]; linarith
  have hzlin : 1 + ‖u‖ ≤ (1 + (1 + R) / d) * ‖z - u‖ := by
    have hmul := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ (1 + R) / d)
    have heq : (1 + R) / d * d = 1 + R := div_mul_cancel₀ _ (ne_of_gt hd)
    rw [heq] at hmul
    nlinarith
  have hwlin : 1 + ‖u‖ ≤ (1 + (1 + R) / d) * ‖w - u‖ := by
    have hmul := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (1 + R) / d)
    have heq : (1 + R) / d * d = 1 + R := div_mul_cancel₀ _ (ne_of_gt hd)
    rw [heq] at hmul
    nlinarith
  have hp := mul_le_mul hzlin hwlin (by positivity : 0 ≤ 1 + ‖u‖)
    (mul_nonneg hc (norm_nonneg (z - u)))
  have hquad : 1 + ‖u‖^2 ≤
      (1 + (1 + R) / d)^2 * (‖z - u‖ * ‖w - u‖) := by
    nlinarith [norm_nonneg u]
  rw [resolvent_difference z w u hz0 hw0, norm_div, norm_mul]
  apply (div_le_div_iff₀ (mul_pos (hd.trans_le hz) (hd.trans_le hw))
    (by positivity : 0 < 1 + ‖u‖^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hquad (norm_nonneg (w-z))]

/-- Named premise T4: absolute convergence of the regularized zero-side
kernel from an ordinary inverse-square count bound. `u` and `m` are arbitrary
indexed data here; actual Hecke zero attachment and the count bound remain
separate obligations. The real-part margin is derived from the chosen
selected window, never from a zero-free half-plane. -/
theorem summable_regularized_resolvent {ι : Type*} (u : ι → ℂ) (m : ι → ℕ)
    (a d : ℝ) (hd : 0 < d) (z w : ℂ)
    (hz : a + d ≤ z.re) (hw : a + d ≤ w.re)
    (hu : ∀ i, (u i).re ≤ a)
    (hcount : Summable (fun i => (m i : ℝ) / (1 + ‖u i‖^2))) :
    Summable (fun i => ‖(m i : ℂ) * ((z - u i)⁻¹ - (w - u i)⁻¹)‖) := by
  let R : ℝ := max ‖z‖ ‖w‖
  let C : ℝ := (1 + (1 + R) / d)^2 * ‖w - z‖
  have hbound (i : ι) : ‖(z - u i)⁻¹ - (w - u i)⁻¹‖ ≤ C / (1 + ‖u i‖^2) := by
    have hzi : d ≤ ‖z - u i‖ := by
      have hh := Complex.re_le_norm (z - u i)
      simp only [Complex.sub_re] at hh
      linarith [hu i]
    have hwi : d ≤ ‖w - u i‖ := by
      have hh := Complex.re_le_norm (w - u i)
      simp only [Complex.sub_re] at hh
      linarith [hu i]
    exact norm_resolvent_difference_le z w (u i) d R hd hzi hwi
      (le_max_left _ _) (le_max_right _ _)
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) _ (hcount.mul_left C)
  intro i
  rw [norm_mul, Complex.norm_natCast]
  calc
    (m i : ℝ) * ‖(z - u i)⁻¹ - (w - u i)⁻¹‖ ≤
        (m i : ℝ) * (C / (1 + ‖u i‖^2)) :=
      mul_le_mul_of_nonneg_left (hbound i) (Nat.cast_nonneg _)
    _ = C * ((m i : ℝ) / (1 + ‖u i‖^2)) := by ring

#check norm_resolvent_difference_le
#print axioms norm_resolvent_difference_le
#check summable_regularized_resolvent
#print axioms summable_regularized_resolvent
end CriticalLineReview


namespace CriticalLine19

/-- T4 uniform-series premise: one majorant on a bounded parameter set.
The separation is from the selected window, not a zero-free assumption. -/
theorem regularized_uniform_majorant {ι : Type*} (u : ι → ℂ) (m : ι → ℕ)
    (a d R : ℝ) (hd : 0 < d) (w : ℂ) (K : Set ℂ)
    (hw : a + d ≤ w.re) (hwR : ‖w‖ ≤ R)
    (hK : ∀ z ∈ K, a + d ≤ z.re ∧ ‖z‖ ≤ R)
    (hu : ∀ i, (u i).re ≤ a) :
    ∀ i z, z ∈ K →
      ‖(m i : ℂ) * ((z - u i)⁻¹ - (w - u i)⁻¹)‖ ≤
        ((1 + (1 + R) / d)^2 * (2 * R)) *
          ((m i : ℝ) / (1 + ‖u i‖^2)) := by
  intro i z hz
  obtain ⟨hz, hzR⟩ := hK z hz
  have hzi : d ≤ ‖z - u i‖ := by
    have hh := Complex.re_le_norm (z - u i)
    simp only [Complex.sub_re] at hh
    linarith [hu i]
  have hwi : d ≤ ‖w - u i‖ := by
    have hh := Complex.re_le_norm (w - u i)
    simp only [Complex.sub_re] at hh
    linarith [hu i]
  have hzw : ‖w - z‖ ≤ 2 * R := by
    calc
      ‖w - z‖ ≤ ‖w‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have hb := CriticalLineReview.norm_resolvent_difference_le z w (u i) d R
    hd hzi hwi hzR hwR
  rw [norm_mul, Complex.norm_natCast]
  calc
    (m i : ℝ) * ‖(z-u i)⁻¹ - (w-u i)⁻¹‖ ≤
        (m i : ℝ) * (((1+(1+R)/d)^2 * ‖w-z‖)/(1+‖u i‖^2)) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (m i : ℝ) * (((1+(1+R)/d)^2 * (2*R))/(1+‖u i‖^2)) := by
      gcongr
    _ = _ := by ring

#check regularized_uniform_majorant
#print axioms regularized_uniform_majorant

/-- T4: finite subsums converge uniformly on every bounded parameter set
with a positive margin from the selected window. No cutoff bound is assumed. -/
theorem regularized_series_uniform {ι : Type*} (u : ι → ℂ) (m : ι → ℕ)
    (a d R : ℝ) (hd : 0 < d) (w : ℂ) (K : Set ℂ)
    (hw : a + d ≤ w.re) (hwR : ‖w‖ ≤ R)
    (hK : ∀ z ∈ K, a + d ≤ z.re ∧ ‖z‖ ≤ R)
    (hu : ∀ i, (u i).re ≤ a)
    (hcount : Summable (fun i => (m i : ℝ) / (1 + ‖u i‖^2))) :
    TendstoUniformlyOn
      (fun t : Finset ι => fun z => ∑ i ∈ t,
        (m i : ℂ) * ((z - u i)⁻¹ - (w - u i)⁻¹))
      (fun z => ∑' i, (m i : ℂ) * ((z - u i)⁻¹ - (w - u i)⁻¹))
      Filter.atTop K := by
  apply tendstoUniformlyOn_tsum
    (hcount.mul_left ((1 + (1 + R) / d)^2 * (2 * R)))
  exact regularized_uniform_majorant u m a d R hd w K hw hwR hK hu

#check regularized_series_uniform
#print axioms regularized_series_uniform

/-- T4: holomorphy follows from the proved uniform convergence, on every
open bounded set with a positive margin. Genuine zero attachment remains open. -/
theorem regularized_series_holomorphic {ι : Type*} (u : ι → ℂ) (m : ι → ℕ)
    (a d R : ℝ) (hd : 0 < d) (w : ℂ) (K : Set ℂ) (hopen : IsOpen K)
    (hw : a + d ≤ w.re) (hwR : ‖w‖ ≤ R)
    (hK : ∀ z ∈ K, a + d ≤ z.re ∧ ‖z‖ ≤ R)
    (hu : ∀ i, (u i).re ≤ a)
    (hcount : Summable (fun i => (m i : ℝ) / (1 + ‖u i‖^2))) :
    DifferentiableOn ℂ
      (fun z => ∑' i, (m i : ℂ) * ((z - u i)⁻¹ - (w - u i)⁻¹)) K := by
  apply (regularized_series_uniform u m a d R hd w K hw hwR hK hu hcount).tendstoLocallyUniformlyOn.differentiableOn
  · refine Filter.Eventually.of_forall (fun t => ?_)
    have hs : DifferentiableOn ℂ
        (∑ i ∈ t, (fun z : ℂ => (m i : ℂ) *
          ((z - u i)⁻¹ - (w - u i)⁻¹))) K := by
      apply DifferentiableOn.sum
      intro i hi z hz
      have hne : z - u i ≠ 0 := by
        intro he
        have hre : z.re = (u i).re := congrArg Complex.re (sub_eq_zero.mp he)
        linarith [(hK z hz).1, hu i]
      exact (((differentiableAt_id.sub_const (u i)).inv hne).sub
        (differentiableAt_const ((w - u i)⁻¹))).const_mul (m i : ℂ) |>.differentiableWithinAt
    convert hs using 1
    ext z
    simp only [Finset.sum_apply]
  · exact hopen

#check regularized_series_holomorphic
#print axioms regularized_series_holomorphic
end CriticalLine19


open Filter Topology

namespace CriticalLineF

/- This file discharges ONLY the local premise in §1.4.5 that a positive
finite-order zero produces a nonremovable logarithmic-derivative pole.
The factor (z-r)^(n+1) u(z) represents the local germ. Attachment to the
actual completed Hecke function, trace limits, and continuation are open. -/

theorem scaled_logDeriv_factor
    (u : ℂ → ℂ) (r z : ℂ) (n : ℕ)
    (hz : z ≠ r) (hu : u z ≠ 0) (hd : DifferentiableAt ℂ u z) :
    (z-r) * logDeriv (fun w => (w-r)^(n+1) * u w) z =
      ((n+1 : ℕ) : ℂ) + (z-r) * deriv u z / u z := by
  have h := (((hasDerivAt_id z).sub_const r).pow (n+1)).mul hd.hasDerivAt
  rw [logDeriv]
  change (z-r) * (deriv (fun w => (w-r)^(n+1) * u w) z /
    ((z-r)^(n+1) * u z)) = _
  have hder : HasDerivAt (fun w => (w-r)^(n+1) * u w)
      (((n+1 : ℕ) : ℂ) * (z-r)^n * u z + (z-r)^(n+1) * deriv u z) z := by
    simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one] using h
  rw [hder.deriv]
  field_simp [sub_ne_zero.mpr hz, hu]
  ring

/-- The exact residue coefficient is the positive zero multiplicity. -/
theorem zero_logDeriv_residue
    (u : ℂ → ℂ) (r : ℂ) (n : ℕ)
    (hc : ContinuousAt u r) (hc' : ContinuousAt (deriv u) r)
    (hd : ∀ᶠ z in 𝓝 r, DifferentiableAt ℂ u z) (hu : u r ≠ 0) :
    Tendsto (fun z => (z-r) * logDeriv (fun w => (w-r)^(n+1) * u w) z)
      (𝓝[≠] r) (𝓝 (((n+1 : ℕ) : ℂ))) := by
  have hcont : ContinuousAt
      (fun z => ((n+1 : ℕ) : ℂ) + (z-r) * deriv u z / u z) r :=
    continuousAt_const.add
      (((continuousAt_id.sub continuousAt_const).mul hc').div hc hu)
  have ht : Tendsto
      (fun z => ((n+1 : ℕ) : ℂ) + (z-r) * deriv u z / u z)
      (𝓝[≠] r) (𝓝 (((n+1 : ℕ) : ℂ))) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  have hn : ∀ᶠ z in 𝓝 r, u z ≠ 0 := hc.eventually (eventually_ne_nhds hu)
  filter_upwards [hd.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hdz hnz hzr
  exact (scaled_logDeriv_factor u r z n (by simpa using hzr) hnz hdz).symm

/-- Named target premise ZERO-POLE: no continuous, hence no holomorphic,
local extension of this logarithmic derivative exists at the zero.
This assumes no half-plane zero-freeness and no global analytic extension. -/
theorem zero_logDeriv_no_continuous_extension
    (u : ℂ → ℂ) (r : ℂ) (n : ℕ)
    (hc : ContinuousAt u r) (hc' : ContinuousAt (deriv u) r)
    (hd : ∀ᶠ z in 𝓝 r, DifferentiableAt ℂ u z) (hu : u r ≠ 0) :
    ¬ ∃ H : ℂ → ℂ, ContinuousAt H r ∧
      (fun z => logDeriv (fun w => (w-r)^(n+1) * u w) z) =ᶠ[𝓝[≠] r] H := by
  rintro ⟨H, hH, heq⟩
  have hzero : Tendsto (fun z => (z-r) * H z) (𝓝[≠] r) (𝓝 0) := by
    have ht : ContinuousAt (fun z => (z-r) * H z) r :=
      (continuousAt_id.sub continuousAt_const).mul hH
    simpa using ht.tendsto.mono_left nhdsWithin_le_nhds
  have hzero' : Tendsto
      (fun z => (z-r) * logDeriv (fun w => (w-r)^(n+1) * u w) z)
      (𝓝[≠] r) (𝓝 0) := by
    apply hzero.congr'
    filter_upwards [heq] with z hz
    rw [hz]
  have hbad := tendsto_nhds_unique (zero_logDeriv_residue u r n hc hc' hd hu) hzero'
  exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n) : ((n+1 : ℕ) : ℂ) ≠ 0) hbad

#check zero_logDeriv_residue
#print axioms zero_logDeriv_residue
#check zero_logDeriv_no_continuous_extension
#print axioms zero_logDeriv_no_continuous_extension

end CriticalLineF

namespace CriticalLineF

/-- Premise CONTINUE of §1.4.5: continue the cross-multiplied identity
from an Euler-domain germ. This does not assume the sought zero-free region.
The trace-limit construction of H and the genuine Hecke attachments remain open. -/
theorem continue_differential_identity
    (f H : ℂ → ℂ) (D : Set ℂ) (b : ℂ)
    (hf : AnalyticOnNhd ℂ f D) (hf' : AnalyticOnNhd ℂ (deriv f) D)
    (hH : AnalyticOnNhd ℂ H D) (hD : IsPreconnected D) (hb : b ∈ D)
    (hbase : deriv f =ᶠ[𝓝 b] (fun z => H z * f z)) :
    Set.EqOn (deriv f) (fun z => H z * f z) D :=
  hf'.eqOn_of_preconnected_of_eventuallyEq (hH.mul hf) hD hb hbase

/-- Premises CONTINUE + ZERO-POLE: an identity known only on an Euler germ
excludes any positive finite-order zero after continuation. Local factorization
is germ equality with the SAME f, not an invented zero configuration.
D must avoid the known poles; no functional equation or Hecke scope is claimed. -/
theorem no_zero_germ_of_continued_identity
    (f H u : ℂ → ℂ) (D : Set ℂ) (b r : ℂ) (n : ℕ)
    (hopen : IsOpen D) (hD : IsPreconnected D) (hb : b ∈ D) (hr : r ∈ D)
    (hf : AnalyticOnNhd ℂ f D) (hf' : AnalyticOnNhd ℂ (deriv f) D)
    (hH : AnalyticOnNhd ℂ H D)
    (hbase : deriv f =ᶠ[𝓝 b] (fun z => H z * f z))
    (hfactor : f =ᶠ[𝓝 r] (fun z => (z-r)^(n+1) * u z))
    (hc : ContinuousAt u r) (hc' : ContinuousAt (deriv u) r)
    (hd : ∀ᶠ z in 𝓝 r, DifferentiableAt ℂ u z) (hu : u r ≠ 0) : False := by
  have heq := continue_differential_identity f H D b hf hf' hH hD hb hbase
  have hder : deriv f =ᶠ[𝓝 r] deriv (fun z => (z-r)^(n+1) * u z) :=
    hfactor.deriv
  have hne : ∀ᶠ z in 𝓝 r, u z ≠ 0 := hc.eventually (eventually_ne_nhds hu)
  have hmem : ∀ᶠ z in 𝓝 r, z ∈ D := hopen.mem_nhds hr
  apply zero_logDeriv_no_continuous_extension u r n hc hc' hd hu
  refine ⟨H, (hH r hr).continuousAt, ?_⟩
  filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds,
    hder.filter_mono nhdsWithin_le_nhds,
    hne.filter_mono nhdsWithin_le_nhds,
    hmem.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hdz hnz hzD hzr
  have hzr' : z ≠ r := by simpa using hzr
  have hfz : f z ≠ 0 := by rw [hz]; exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzr')) hnz
  change deriv (fun w => (w-r)^(n+1) * u w) z / ((z-r)^(n+1) * u z) = H z
  rw [← hdz, ← hz, heq hzD]
  exact mul_div_cancel_right₀ (H z) hfz

#check continue_differential_identity
#print axioms continue_differential_identity
#check no_zero_germ_of_continued_identity
#print axioms no_zero_germ_of_continued_identity

end CriticalLineF

namespace CriticalLineF

/-- Under chi = chi_0 norm^(i tau), the two completed pole locations are
-i tau and 1-i tau. Delta must be supplied by the genuine character theorem. -/
noncomputable def knownPoleCorrection (tau : ℝ) (delta : ℂ) (z : ℂ) : ℂ :=
  delta * ((z + (tau : ℂ) * Complex.I)⁻¹ + (z - 1 + (tau : ℂ) * Complex.I)⁻¹)

/-- Premise POLE-CORRECTION: the explicit shifted correction is analytic
away from its two displayed possible poles, for every real norm twist. -/
theorem knownPoleCorrection_analyticOnNhd (tau : ℝ) (delta : ℂ) (D : Set ℂ)
    (hp : ∀ z ∈ D, z + (tau : ℂ) * Complex.I ≠ 0 ∧
      z - 1 + (tau : ℂ) * Complex.I ≠ 0) :
    AnalyticOnNhd ℂ (knownPoleCorrection tau delta) D := by
  intro z hz
  exact analyticAt_const.mul
    (((analyticAt_id.add analyticAt_const).inv (hp z hz).1).add
      (((analyticAt_id.sub analyticAt_const).add analyticAt_const).inv (hp z hz).2))

/-- Pole-aware CONTINUE + ZERO-POLE reduction. The trace-derived analytic H
and its Euler-domain germ identity are explicit unproved inputs when this is
applied to Hecke functions. This is not a conditional-on-trace-alone GRH theorem. -/
theorem no_zero_germ_of_pole_corrected_identity
    (f H u : ℂ → ℂ) (D : Set ℂ) (b r : ℂ) (n : ℕ) (tau : ℝ) (delta : ℂ)
    (hopen : IsOpen D) (hD : IsPreconnected D) (hb : b ∈ D) (hr : r ∈ D)
    (hf : AnalyticOnNhd ℂ f D) (hf' : AnalyticOnNhd ℂ (deriv f) D)
    (hH : AnalyticOnNhd ℂ H D)
    (hp : ∀ z ∈ D, z + (tau : ℂ) * Complex.I ≠ 0 ∧
      z - 1 + (tau : ℂ) * Complex.I ≠ 0)
    (hbase : deriv f =ᶠ[𝓝 b]
      (fun z => (H z - knownPoleCorrection tau delta z) * f z))
    (hfactor : f =ᶠ[𝓝 r] (fun z => (z-r)^(n+1) * u z))
    (hc : ContinuousAt u r) (hc' : ContinuousAt (deriv u) r)
    (hd : ∀ᶠ z in 𝓝 r, DifferentiableAt ℂ u z) (hu : u r ≠ 0) : False :=
  no_zero_germ_of_continued_identity f (fun z => H z - knownPoleCorrection tau delta z)
    u D b r n hopen hD hb hr hf hf'
    (hH.sub (knownPoleCorrection_analyticOnNhd tau delta D hp)) hbase hfactor hc hc' hd hu

#check no_zero_germ_of_pole_corrected_identity
#print axioms no_zero_germ_of_pole_corrected_identity

end CriticalLineF

namespace CriticalLine20

/-- Named premises T4 + CONTINUE + ZERO-POLE of the critical-line target.
This integrates the proved regularized selected-zero series with analytic
continuation BEFORE division by the genuine candidate function f.
The Euler-domain identity is required only as a germ at b. The selected data
u,m and the ordinary inverse-square count do not assert any zero-free region.
Unresolved for Hecke: actual moving-test limits, local correction A, Euler germ,
genuine zero/count attachment and genuine local factorization of the SAME f. -/
theorem no_zero_germ_from_regularized_trace {ι : Type*}
    (u : ι → ℂ) (m : ι → ℕ) (a d R : ℝ) (hd : 0 < d)
    (w : ℂ) (D : Set ℂ) (b r : ℂ) (n : ℕ)
    (f A v : ℂ → ℂ) (tau : ℝ) (delta : ℂ)
    (hopen : IsOpen D) (hconn : IsPreconnected D) (hb : b ∈ D) (hr : r ∈ D)
    (hw : a + d ≤ w.re) (hwR : ‖w‖ ≤ R)
    (hD : ∀ z ∈ D, a + d ≤ z.re ∧ ‖z‖ ≤ R)
    (hu : ∀ i, (u i).re ≤ a)
    (hcount : Summable (fun i => (m i : ℝ) / (1 + ‖u i‖^2)))
    (hf : AnalyticOnNhd ℂ f D) (hf' : AnalyticOnNhd ℂ (deriv f) D)
    (hA : AnalyticOnNhd ℂ A D)
    (hp : ∀ z ∈ D, z + (tau : ℂ) * Complex.I ≠ 0 ∧
      z - 1 + (tau : ℂ) * Complex.I ≠ 0)
    (hbase : deriv f =ᶠ[𝓝 b] (fun z =>
      (A z + (∑' i, (m i : ℂ) * ((z-u i)⁻¹ - (w-u i)⁻¹)) -
        CriticalLineF.knownPoleCorrection tau delta z) * f z))
    (hfactor : f =ᶠ[𝓝 r] (fun z => (z-r)^(n+1) * v z))
    (hc : ContinuousAt v r) (hc' : ContinuousAt (deriv v) r)
    (hv : ∀ᶠ z in 𝓝 r, DifferentiableAt ℂ v z) (hv0 : v r ≠ 0) : False := by
  have hs := CriticalLine19.regularized_series_holomorphic u m a d R hd w D
    hopen hw hwR hD hu hcount
  have has : AnalyticOnNhd ℂ
      (fun z => ∑' i, (m i : ℂ) * ((z-u i)⁻¹ - (w-u i)⁻¹)) D :=
    hs.analyticOnNhd hopen
  exact CriticalLineF.no_zero_germ_of_pole_corrected_identity f
    (fun z => A z + ∑' i, (m i : ℂ) * ((z-u i)⁻¹ - (w-u i)⁻¹))
    v D b r n tau delta hopen hconn hb hr hf hf' (hA.add has) hp
    hbase hfactor hc hc' hv hv0

#check no_zero_germ_from_regularized_trace
#print axioms no_zero_germ_from_regularized_trace
end CriticalLine20

namespace CriticalLineF

/-- Finite positive multiplicity of an ACTUAL zero of the same function.
This is ordinary local analytic factorization, not an assigned zero set. -/
def PositiveZeroGerm (f : ℂ → ℂ) (r : ℂ) : Prop :=
  ∃ (n : ℕ) (u : ℂ → ℂ),
    f =ᶠ[𝓝 r] (fun z => (z-r)^(n+1) * u z) ∧
    ContinuousAt u r ∧ ContinuousAt (deriv u) r ∧
    (∀ᶠ z in 𝓝 r, DifferentiableAt ℂ u z) ∧ u r ≠ 0


end CriticalLineF

namespace CriticalLine21

/-- Explicit local inputs AFTER the moving trace limits, not RT itself.
Named target premises T3/T4/T5 are exposed: selected data/count and Euler germ.
The coefficient's holomorphy is DERIVED by E20, never a field of this record.
No arithmetic attachment or genuine-Hecke instance is asserted. -/
structure RegularizedGermData (ι : Type*) (f : ℂ → ℂ)
    (tau : ℝ) (delta : ℂ) (r : ℂ) where
  u : ι → ℂ
  m : ι → ℕ
  alpha : ℝ
  alpha_pos : 0 < alpha
  d : ℝ
  d_pos : 0 < d
  R : ℝ
  w : ℂ
  D : Set ℂ
  b : ℂ
  A : ℂ → ℂ
  open_domain : IsOpen D
  connected : IsPreconnected D
  base_mem : b ∈ D
  base_euler : 1 < b.re
  point_mem : r ∈ D
  reference_margin : 1/2 + alpha + d ≤ w.re
  reference_bound : ‖w‖ ≤ R
  domain_bound : ∀ z ∈ D, 1/2 + alpha + d ≤ z.re ∧ ‖z‖ ≤ R
  selected_bound : ∀ i, (u i).re ≤ 1/2 + alpha
  ordinary_count : Summable (fun i => (m i : ℝ) / (1 + ‖u i‖^2))
  analytic : AnalyticOnNhd ℂ f D
  analytic_deriv : AnalyticOnNhd ℂ (deriv f) D
  analytic_local_term : AnalyticOnNhd ℂ A D
  avoids_poles : ∀ z ∈ D, z + (tau : ℂ) * Complex.I ≠ 0 ∧
    z - 1 + (tau : ℂ) * Complex.I ≠ 0
  euler_germ : deriv f =ᶠ[𝓝 b] (fun z =>
    (A z + (∑' i, (m i : ℂ) * ((z-u i)⁻¹ - (w-u i)⁻¹)) -
      CriticalLineF.knownPoleCorrection tau delta z) * f z)

/-- Integrates quantitative zero-series control with the positive-zero
obstruction on a bounded domain chosen for this point, as needed by §1.4.5. -/
theorem no_zero_germ_of_regularized_data {ι : Type*}
    (f : ℂ → ℂ) (tau : ℝ) (delta : ℂ) (r : ℂ)
    (data : RegularizedGermData ι f tau delta r)
    (hfactor : CriticalLineF.PositiveZeroGerm f r) : False := by
  obtain ⟨n, v, hfac, hc, hc', hd, hv⟩ := hfactor
  exact CriticalLine20.no_zero_germ_from_regularized_trace data.u data.m
    (1/2 + data.alpha) data.d data.R data.d_pos data.w data.D data.b r n
    f data.A v tau delta data.open_domain data.connected data.base_mem
    data.point_mem data.reference_margin data.reference_bound data.domain_bound
    data.selected_bound data.ordinary_count data.analytic data.analytic_deriv
    data.analytic_local_term data.avoids_poles data.euler_germ hfac hc hc' hd hv

/-- CONDITIONAL integrated analytic tail of the ORIGINAL full target.
Unlike assuming an analytic series coefficient, its holomorphy follows from
ordinary inverse-square counts and quantitative window separation in each
local packet. The packets for BOTH functions still require actual trace limits
and genuine Euler germs; no instance is claimed here. Reflection is applied
only after the continued differential identity excludes a positive-order zero.
The target's genuine-Hecke objects, test construction and FE remain obligations. -/
theorem critical_line_of_regularized_trace_germs {ι κ : Type*}
    (f g : ℂ → ℂ) (tau : ℝ) (delta epsilon : ℂ)
    (data_f : ∀ r : ℂ, 1/2 < r.re → r.re < 1 →
      Nonempty (RegularizedGermData ι f tau delta r))
    (data_g : ∀ r : ℂ, 1/2 < r.re → r.re < 1 →
      Nonempty (RegularizedGermData κ g (-tau) delta r))
    (hfactor_f : ∀ z : ℂ, 0 < z.re → z.re < 1 → f z = 0 →
      CriticalLineF.PositiveZeroGerm f z)
    (hfactor_g : ∀ z : ℂ, 0 < z.re → z.re < 1 → g z = 0 →
      CriticalLineF.PositiveZeroGerm g z)
    (hepsilon : epsilon ≠ 0)
    (hFE : ∀ z : ℂ, 0 < z.re → z.re < 1 → f z = epsilon * g (1-z))
    (r : ℂ) (hr0 : 0 < r.re) (hr1 : r.re < 1) (hzero : f r = 0) :
    r.re = 1/2 := by
  rcases lt_trichotomy r.re (1/2) with hleft | heq | hright
  · have hsre : (1-r).re = 1-r.re := by simp
    have hs0 : 0 < (1-r).re := by rw [hsre]; linarith
    have hs1 : (1-r).re < 1 := by rw [hsre]; linarith
    have hsright : 1/2 < (1-r).re := by rw [hsre]; linarith
    have hmul : epsilon * g (1-r) = 0 := (hFE r hr0 hr1).symm.trans hzero
    have hgz : g (1-r) = 0 := (mul_eq_zero.mp hmul).resolve_left hepsilon
    obtain ⟨dg⟩ := data_g (1-r) hsright hs1
    exact (no_zero_germ_of_regularized_data g (-tau) delta (1-r) dg
      (hfactor_g (1-r) hs0 hs1 hgz)).elim
  · exact heq
  · obtain ⟨df⟩ := data_f r hright hr1
    exact (no_zero_germ_of_regularized_data f tau delta r df
      (hfactor_f r hr0 hr1 hzero)).elim

#check critical_line_of_regularized_trace_germs
#print axioms critical_line_of_regularized_trace_germs
end CriticalLine21
