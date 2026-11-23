import Mathlib

/-!
Participant D, round 2; inherited supporting results from frozen r01/final/D. Supporting results only; no Hecke GRH theorem is claimed.
The first lemma isolates the positive singularity in the real Archimedean
integral at z = 3/2 (PDF p.29). The second isolates the linear ambiguity of
agreement on test functions with vanishing jets (PDF p.522).
-/
namespace MasulloGRH

/-- On (1,2], the Archimedean integrand at real z=3/2 dominates
one quarter of the non-integrable kernel 1/(t-1). -/
theorem archimedean_kernel_lower_bound (t : ℝ) (h1 : 1 < t) (h2 : t ≤ 2) :
    1 / (4 * (t - 1)) ≤ 1 / (t ^ 2 * (t - 1)) := by
  have ht : 0 < t := by linarith
  have hd : 0 < t - 1 := sub_pos.mpr h1
  have hs : t ^ 2 ≤ 4 := by nlinarith
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * (t - 1))
    (by positivity : 0 < t ^ 2 * (t - 1))).2
  nlinarith

/-- Agreement on ker J determines a functional only modulo the jet values.
The splitting hypothesis is explicit and is not constructed for Mellin tests. -/
theorem restricted_functional_difference
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (J : V →ₗ[ℂ] W) (S : W →ₗ[ℂ] V)
    (hS : ∀ w, J (S w) = w)
    (L R : V →ₗ[ℂ] ℂ)
    (h : ∀ v, J v = 0 → L v = R v) (v : V) :
    L v - R v = L (S (J v)) - R (S (J v)) := by
  have hj : J (v - S (J v)) = 0 := by simp [hS]
  have he := h (v - S (J v)) hj
  simp only [map_sub] at he
  linear_combination he

/-- Exact reciprocal cutoff integral, used to quantify the singularity. -/
theorem reciprocal_cutoff_integral (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    (∫ x in e..1, (1 : ℝ) / x) = -Real.log e := by
  have hxpos : ∀ x ∈ Set.uIcc e 1, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le he1] at hx
    exact lt_of_lt_of_le he hx.1
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (Set.uIcc e 1) :=
    continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (hxpos x hx))
  have hd : ∀ x ∈ Set.uIcc e 1, HasDerivAt Real.log (1 / x) x := by
    intro x hx
    simpa only [one_div] using Real.hasDerivAt_log (ne_of_gt (hxpos x hx))
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable

/-- Quantitative logarithmic lower bound for the shifted Archimedean integral. -/
theorem archimedean_cutoff_lower_bound (e : ℝ) (he : 0 < e) (he1 : e ≤ 1) :
    -Real.log e / 4 ≤ ∫ x in e..1, (1 : ℝ) / ((x + 1) ^ 2 * x) := by
  have hxpos : ∀ x ∈ Set.uIcc e 1, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le he1] at hx
    exact lt_of_lt_of_le he hx.1
  have hc : ContinuousOn (fun x : ℝ => 1 / x) (Set.uIcc e 1) :=
    continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (hxpos x hx))
  have hk : ContinuousOn (fun x : ℝ => 1 / ((x + 1) ^ 2 * x))
      (Set.uIcc e 1) := by
    apply continuousOn_const.div
      (((continuousOn_id.add continuousOn_const).pow 2).mul continuousOn_id)
    intro x hx
    have hp := hxpos x hx
    positivity
  have hm := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) he1
    ((continuousOn_const.mul hc).intervalIntegrable)
    hk.intervalIntegrable (fun x hx => show (1 / 4 : ℝ) * (1 / x) ≤
      1 / ((x + 1) ^ 2 * x) from by
        have hxp : 0 < x := lt_of_lt_of_le he hx.1
        have h := archimedean_kernel_lower_bound (x + 1) (by linarith) (by linarith [hx.2])
        calc
          (1 / 4 : ℝ) * (1 / x) = 1 / (4 * x) := by ring
          _ ≤ 1 / ((x + 1) ^ 2 * x) := by simpa using h)
  rw [intervalIntegral.integral_const_mul, reciprocal_cutoff_integral e he he1] at hm
  linarith

/-- The positive Archimedean cutoff integrals have no uniform upper bound. -/
theorem archimedean_cutoffs_unbounded (A : ℝ) :
    ∃ e : ℝ, 0 < e ∧ e < 1 ∧
      A < ∫ x in e..1, (1 : ℝ) / ((x + 1) ^ 2 * x) := by
  let e := Real.exp (-4 * (|A| + 1))
  have he : 0 < e := Real.exp_pos _
  have he1 : e < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [abs_nonneg A])
  refine ⟨e, he, he1, ?_⟩
  have hb := archimedean_cutoff_lower_bound e he he1.le
  have hlog : Real.log e = -4 * (|A| + 1) := Real.log_exp _
  rw [hlog] at hb
  linarith [le_abs_self A]

/-- Subtracting at two parameters cancels the endpoint singularity exactly. -/
theorem archimedean_subtraction (t : ℝ) (h1 : 1 < t) :
    1 / (t ^ 2 * (t - 1)) - 1 / (t * (t - 1)) = -(1 / t ^ 2) := by
  have ht : t ≠ 0 := by linarith
  have hd : t - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The spectral counterpart of subtracting at a fixed parameter. -/
theorem resolvent_subtraction (z w r : ℂ) (hz : z ≠ r) (hw : w ≠ r) :
    1 / (z - r) - 1 / (w - r) = (w - z) / ((z - r) * (w - r)) := by
  have hzr : z - r ≠ 0 := sub_ne_zero.mpr hz
  have hwr : w - r ≠ 0 := sub_ne_zero.mpr hw
  field_simp
  ring

/-- Uniform inverse-square decay after subtraction, outside twice the parameter disk. -/
theorem resolvent_subtraction_bound (z w r : ℂ) (R : ℝ)
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hr : 2 * R ≤ ‖r‖) (hr0 : 0 < ‖r‖) :
    ‖1 / (z - r) - 1 / (w - r)‖ ≤ 4 * ‖w - z‖ / ‖r‖ ^ 2 := by
  have hzr : ‖r‖ / 2 ≤ ‖z - r‖ := by
    have h := norm_sub_norm_le r z
    rw [norm_sub_rev] at h
    linarith
  have hwr : ‖r‖ / 2 ≤ ‖w - r‖ := by
    have h := norm_sub_norm_le r w
    rw [norm_sub_rev] at h
    linarith
  have hpz : 0 < ‖z - r‖ := by linarith
  have hpw : 0 < ‖w - r‖ := by linarith
  have hz_ne : z ≠ r := by
    intro h
    simp [h] at hpz
  have hw_ne : w ≠ r := by
    intro h
    simp [h] at hpw
  rw [resolvent_subtraction z w r hz_ne hw_ne, norm_div, norm_mul]
  apply (div_le_div_iff₀ (mul_pos hpz hpw) (sq_pos_of_pos hr0)).2
  have hm : ‖r‖ ^ 2 ≤ 4 * (‖z - r‖ * ‖w - r‖) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzr) (sub_nonneg.mpr hwr)]
  nlinarith [mul_le_mul_of_nonneg_left hm (norm_nonneg (w - z))]

#check resolvent_subtraction
#print axioms resolvent_subtraction
#check resolvent_subtraction_bound
#print axioms resolvent_subtraction_bound
#check archimedean_cutoff_lower_bound
#print axioms archimedean_cutoff_lower_bound
#check archimedean_cutoffs_unbounded
#print axioms archimedean_cutoffs_unbounded
#check reciprocal_cutoff_integral
#print axioms reciprocal_cutoff_integral
#check archimedean_subtraction
#print axioms archimedean_subtraction
#check archimedean_kernel_lower_bound
#print axioms archimedean_kernel_lower_bound
#check restricted_functional_difference
#print axioms restricted_functional_difference

/-- A normally convergent tail: the spectrum is outside twice the parameter
radius and its inverse-square norms are summable. These are explicit hypotheses,
not claims about genuine Hecke zeros. Repetition of indices permits multiplicity. -/
theorem subtracted_resolvent_uniform_bound {ι : Type*} (r : ι → ℂ)
    (w : ℂ) (R : ℝ) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 2 * R ≤ ‖r n‖) (hr0 : ∀ n, 0 < ‖r n‖)
    (n : ι) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖1 / (z - r n) - 1 / (w - r n)‖ ≤ 8 * R / ‖r n‖ ^ 2 := by
  have hb := resolvent_subtraction_bound z w (r n) R hz hw (hr n) (hr0 n)
  have hd : ‖w - z‖ ≤ 2 * R := by
    have ht := norm_sub_le w z
    linarith
  exact hb.trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

/-- Uniform convergence of finite partial sums of the subtracted tail on a
closed disk. This is the actual Weierstrass-test step, conditional on the
explicit spectrum and summability assumptions. -/
theorem subtracted_resolvent_tendstoUniformlyOn {ι : Type*} (r : ι → ℂ)
    (w : ℂ) (R : ℝ) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 2 * R ≤ ‖r n‖) (hr0 : ∀ n, 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    TendstoUniformlyOn
      (fun (t : Finset ι) z => ∑ n ∈ t, (1 / (z - r n) - 1 / (w - r n)))
      (fun z => ∑' n, (1 / (z - r n) - 1 / (w - r n)))
      Filter.atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hmajor : Summable (fun n => 8 * R / ‖r n‖ ^ 2) := by
    simpa only [mul_one_div] using hs.mul_left (8 * R)
  exact tendstoUniformlyOn_tsum hmajor
    (fun n z hz => subtracted_resolvent_uniform_bound r w R hw hr hr0 n z hz)

/-- Holomorphy of the normally convergent subtracted tail on the open disk.
No trace identity or identification with a genuine logarithmic derivative is assumed. -/
theorem subtracted_resolvent_differentiableOn {ι : Type*} (r : ι → ℂ)
    (w : ℂ) (R : ℝ) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 2 * R ≤ ‖r n‖) (hr0 : ∀ n, 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    DifferentiableOn ℂ (fun z => ∑' n, (1 / (z - r n) - 1 / (w - r n)))
      {z : ℂ | ‖z‖ < R} := by
  have hmajor : Summable (fun n => 8 * R / ‖r n‖ ^ 2) := by
    simpa only [mul_one_div] using hs.mul_left (8 * R)
  apply Complex.differentiableOn_tsum_of_summable_norm hmajor
  · intro n z hz
    have hne : z - r n ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have hw0 : 0 ≤ R := (norm_nonneg w).trans hw
      have hz' : ‖z‖ < R := hz
      have hn := hr n
      rw [← heq] at hn
      linarith
    simpa only [one_div] using
      ((((hasDerivAt_id z).sub_const (r n)).inv hne).sub_const
        (1 / (w - r n))).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_norm continuous_const
  · intro n z hz
    exact subtracted_resolvent_uniform_bound r w R hw hr hr0 n z (le_of_lt hz)

/-- Pointwise summability allows finitely many exceptional spectrum points.
The norm-escape hypothesis and inverse-square summability must still be proved
for a genuine spectral enumeration. -/
theorem subtracted_resolvent_summable {ι : Type*} (r : ι → ℂ)
    (z w : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ᶠ n in Filter.cofinite, 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    Summable (fun n => 1 / (z - r n) - 1 / (w - r n)) := by
  have hmajor : Summable (fun n => 4 * ‖w - z‖ / ‖r n‖ ^ 2) := by
    simpa only [mul_one_div] using hs.mul_left (4 * ‖w - z‖)
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [hr] with n hn
  exact resolvent_subtraction_bound z w (r n) R hz hw hn.1 hn.2

#check subtracted_resolvent_uniform_bound
#print axioms subtracted_resolvent_uniform_bound
#check subtracted_resolvent_tendstoUniformlyOn
#print axioms subtracted_resolvent_tendstoUniformlyOn
#check subtracted_resolvent_differentiableOn
#print axioms subtracted_resolvent_differentiableOn
#check subtracted_resolvent_summable
#print axioms subtracted_resolvent_summable

/-- The displayed intersection of low-height evaluation kernels on PDF p.426
is decreasing as the cutoff grows. This is a set-theoretic audit of that formula. -/
theorem low_kernel_antitone {V ι : Type*} (height : ι → ℝ) (J : ι → V → ℂ)
    (T U : ℝ) (hTU : T ≤ U) :
    {v : V | ∀ n, height n ≤ U → J n v = 0} ⊆
    {v : V | ∀ n, height n ≤ T → J n v = 0} := by
  intro v hv n hn
  exact hv n (hn.trans hTU)

/-- Maps whose images eventually lie in one fixed proper closed evaluation
kernel cannot converge pointwise to the identity. No orthogonality is needed. -/
theorem no_identity_limit_of_eventual_kernel
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (L : V →L[ℂ] ℂ) (P : ℕ → V → V)
    (v : V) (hv : L v ≠ 0)
    (hk : ∀ᶠ n in Filter.atTop, L (P n v) = 0) :
    ¬ Filter.Tendsto (fun n => P n v) Filter.atTop (nhds v) := by
  intro hp
  have hl : Filter.Tendsto (fun n => L (P n v)) Filter.atTop (nhds (L v)) :=
    L.continuous.continuousAt.tendsto.comp hp
  have hz : Filter.Tendsto (fun n => L (P n v)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [hk] with n hn using hn.symm)
  exact hv (tendsto_nhds_unique hl hz)

#check low_kernel_antitone
#print axioms low_kernel_antitone
#check no_identity_limit_of_eventual_kernel
#print axioms no_identity_limit_of_eventual_kernel

/-- Rational central-jet correction, proposed for the alternative p.522 test
space. The explicit factor supplies central vanishing without polynomial growth
at spectral infinity. Mellin realization of admissible cutoffs is not asserted. -/
noncomputable def jetCorrectedResolvent (m : ℕ) (c z w r : ℂ) : ℂ :=
  ((r - c) / (w - r)) ^ m * (1 / (z - r) - 1 / (w - r))

/-- The correction has an explicit order-m central factor. -/
theorem jetCorrectedResolvent_factor (m : ℕ) (c z w r : ℂ) :
    jetCorrectedResolvent m c z w r =
    (r - c) ^ m * ((1 / (z - r) - 1 / (w - r)) / (w - r) ^ m) := by
  unfold jetCorrectedResolvent
  rw [div_pow]
  ring

/-- In particular every positive-order correction has zero central value. -/
theorem jetCorrectedResolvent_center (m : ℕ) (hm : 0 < m) (c z w : ℂ) :
    jetCorrectedResolvent m c z w c = 0 := by
  simp [jetCorrectedResolvent, zero_pow (Nat.ne_of_gt hm)]

/-- Central correction does not erase a distinct evaluation away from poles. -/
theorem jetCorrectedResolvent_ne_zero (m : ℕ) (c z w r : ℂ)
    (hc : r ≠ c) (hz : z ≠ r) (hw : w ≠ r) (hzw : z ≠ w) :
    jetCorrectedResolvent m c z w r ≠ 0 := by
  unfold jetCorrectedResolvent
  apply mul_ne_zero (pow_ne_zero m (div_ne_zero (sub_ne_zero.mpr hc) (sub_ne_zero.mpr hw)))
  rw [resolvent_subtraction z w r hz hw]
  exact div_ne_zero (sub_ne_zero.mpr hzw.symm)
    (mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw))

/-- The central correction factor remains uniformly bounded in the tail. -/
theorem central_ratio_bound (c w r : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : 2 * R ≤ ‖r‖) (hr0 : 0 < ‖r‖) :
    ‖(r - c) / (w - r)‖ ≤ 3 := by
  have hd : ‖r‖ / 2 ≤ ‖w - r‖ := by
    have h := norm_sub_norm_le r w
    rw [norm_sub_rev] at h
    linarith
  have hp : 0 < ‖w - r‖ := by linarith
  have hn := norm_sub_le r c
  rw [norm_div]
  apply (div_le_iff₀ hp).2
  linarith

#check jetCorrectedResolvent_factor
#print axioms jetCorrectedResolvent_factor
#check jetCorrectedResolvent_center
#print axioms jetCorrectedResolvent_center
#check jetCorrectedResolvent_ne_zero
#print axioms jetCorrectedResolvent_ne_zero
#check central_ratio_bound
#print axioms central_ratio_bound

/-- Central-jet correction retains the summable inverse-square majorant. -/
theorem jetCorrectedResolvent_uniform_bound (m : ℕ) (c z w r : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : 2 * R ≤ ‖r‖) (hr0 : 0 < ‖r‖) :
    ‖jetCorrectedResolvent m c z w r‖ ≤ (3 : ℝ) ^ m * (8 * R / ‖r‖ ^ 2) := by
  have hm : ‖(r - c) / (w - r)‖ ^ m ≤ (3 : ℝ) ^ m := by
    gcongr
    exact central_ratio_bound c w r R hc hw hr hr0
  have hb := subtracted_resolvent_uniform_bound (fun _ : Unit => r) w R hw
    (fun _ => hr) (fun _ => hr0) () z hz
  rw [jetCorrectedResolvent, norm_mul, norm_pow]
  exact mul_le_mul hm hb (norm_nonneg _) (by positivity)

/-- A central-vanishing rational family with uniformly convergent spectral tail. -/
theorem jetCorrectedResolvent_tendstoUniformlyOn {ι : Type*}
    (r : ι → ℂ) (m : ℕ) (c w : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 2 * R ≤ ‖r n‖) (hr0 : ∀ n, 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    TendstoUniformlyOn
      (fun (t : Finset ι) z => ∑ n ∈ t, jetCorrectedResolvent m c z w (r n))
      (fun z => ∑' n, jetCorrectedResolvent m c z w (r n))
      Filter.atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hmajor : Summable (fun n => (3 : ℝ) ^ m * (8 * R / ‖r n‖ ^ 2)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hs.mul_left ((3 : ℝ) ^ m * (8 * R))
  exact tendstoUniformlyOn_tsum hmajor
    (fun n z hz => jetCorrectedResolvent_uniform_bound m c z w (r n) R hc hz hw
      (hr n) (hr0 n))

#check jetCorrectedResolvent_uniform_bound
#print axioms jetCorrectedResolvent_uniform_bound
#check jetCorrectedResolvent_tendstoUniformlyOn
#print axioms jetCorrectedResolvent_tendstoUniformlyOn

/-- Holomorphy is preserved by the rational central correction because its
factor is independent of the holomorphic parameter z. -/
theorem jetCorrectedResolvent_differentiableOn {ι : Type*}
    (r : ι → ℂ) (m : ℕ) (c w : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, 2 * R ≤ ‖r n‖) (hr0 : ∀ n, 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    DifferentiableOn ℂ (fun z => ∑' n, jetCorrectedResolvent m c z w (r n))
      {z : ℂ | ‖z‖ < R} := by
  have hmajor : Summable (fun n => (3 : ℝ) ^ m * (8 * R / ‖r n‖ ^ 2)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hs.mul_left ((3 : ℝ) ^ m * (8 * R))
  apply Complex.differentiableOn_tsum_of_summable_norm hmajor
  · intro n z hz
    have hne : z - r n ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have hw0 : 0 ≤ R := (norm_nonneg w).trans hw
      have hz' : ‖z‖ < R := hz
      have hn := hr n
      rw [← heq] at hn
      linarith
    simpa only [jetCorrectedResolvent, one_div] using
      (((((hasDerivAt_id z).sub_const (r n)).inv hne).sub_const
        (1 / (w - r n))).const_mul (((r n - c) / (w - r n)) ^ m)).differentiableAt.differentiableWithinAt
  · exact isOpen_lt continuous_norm continuous_const
  · intro n z hz
    exact jetCorrectedResolvent_uniform_bound m c z w (r n) R hc (le_of_lt hz) hw
      (hr n) (hr0 n)

#check jetCorrectedResolvent_differentiableOn
#print axioms jetCorrectedResolvent_differentiableOn

end MasulloGRH
