import Mathlib



/-!
Participant D, round 3 proof phase; inherited supporting results from frozen r01/final/D. Supporting results only; no Hecke GRH theorem is claimed.
The first lemma isolates the positive singularity in the real Archimedean
integral at z = 3/2 (PDF p.29). The second isolates the linear ambiguity of
agreement on test functions with vanishing jets (PDF p.522).
-/
namespace FrozenD

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


/-- Finite exceptional points do not obstruct pointwise summability of the
corrected series. Pole values are still Lean's totalized values here. -/
theorem jetCorrectedResolvent_summable {ι : Type*} (r : ι → ℂ)
    (m : ℕ) (c z w : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ᶠ n in Filter.cofinite, 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    Summable (fun n => jetCorrectedResolvent m c z w (r n)) := by
  have hmajor : Summable (fun n => (3 : ℝ) ^ m * (8 * R / ‖r n‖ ^ 2)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_assoc] using
      hs.mul_left ((3 : ℝ) ^ m * (8 * R))
  apply hmajor.of_norm_bounded_eventually
  filter_upwards [hr] with n hn
  exact jetCorrectedResolvent_uniform_bound m c z w (r n) R hc hz hw hn.1 hn.2

/-- The finite head plus the separated tail is holomorphic at every point
inside the disk that avoids the finitely many exceptional spectral points. -/
theorem jetCorrectedResolvent_finite_complement_differentiableAt
    {ι : Type*} (r : ι → ℂ) (s : Finset ι) (m : ℕ) (c w z₀ : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R) (hz : ‖z₀‖ < R)
    (hr : ∀ n, n ∉ s → 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖)
    (hne : ∀ n ∈ s, z₀ ≠ r n)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    DifferentiableAt ℂ
      (fun z => (∑ n ∈ s, jetCorrectedResolvent m c z w (r n)) +
        ∑' n : {n // n ∉ s}, jetCorrectedResolvent m c z w (r n)) z₀ := by
  classical
  have hf : DifferentiableAt ℂ
      (fun z => ∑ n ∈ s, jetCorrectedResolvent m c z w (r n)) z₀ := by
    apply DifferentiableAt.fun_sum
    intro n hn
    simpa only [jetCorrectedResolvent, one_div] using
      (((((hasDerivAt_id z₀).sub_const (r n)).inv (sub_ne_zero.mpr (hne n hn))).sub_const
        (1 / (w - r n))).const_mul (((r n - c) / (w - r n)) ^ m)).differentiableAt
  have ht := jetCorrectedResolvent_differentiableOn
    (fun n : {n // n ∉ s} => r n) m c w R hc hw
    (fun n => (hr n n.property).1) (fun n => (hr n n.property).2)
    (hs.subtype {n | n ∉ s})
  exact hf.add (ht.differentiableAt ((isOpen_lt continuous_norm continuous_const).mem_nhds hz))

/-- Full-series holomorphy on the disk with its finite exceptional poles removed.
Unlike the earlier tail-only theorem, the sum here includes every index. -/
theorem jetCorrectedResolvent_series_differentiableOn
    {ι : Type*} (r : ι → ℂ) (s : Finset ι) (m : ℕ) (c w : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R)
    (hr : ∀ n, n ∉ s → 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    DifferentiableOn ℂ (fun z => ∑' n, jetCorrectedResolvent m c z w (r n))
      {z | ‖z‖ < R ∧ ∀ n ∈ s, z ≠ r n} := by
  classical
  have he : ∀ᶠ n in Filter.cofinite, 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖ := by
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with n hn
    exact hr n hn
  have hd : DifferentiableOn ℂ
      (fun z => (∑ n ∈ s, jetCorrectedResolvent m c z w (r n)) +
        ∑' n : {n // n ∉ s}, jetCorrectedResolvent m c z w (r n))
      {z | ‖z‖ < R ∧ ∀ n ∈ s, z ≠ r n} := by
    intro z hz
    exact (jetCorrectedResolvent_finite_complement_differentiableAt r s m c w z R
      hc hw hz.1 hr hz.2 hs).differentiableWithinAt
  apply hd.congr
  intro z hz
  exact ((jetCorrectedResolvent_summable r m c z w R hc hz.1.le hw he hs).sum_add_tsum_subtype_compl s).symm

#check jetCorrectedResolvent_summable
#print axioms jetCorrectedResolvent_summable
#check jetCorrectedResolvent_finite_complement_differentiableAt
#print axioms jetCorrectedResolvent_finite_complement_differentiableAt
#check jetCorrectedResolvent_series_differentiableOn
#print axioms jetCorrectedResolvent_series_differentiableOn


/-- Local version of the finite-exception repair for the original full sum. -/
theorem jetCorrectedResolvent_series_differentiableAt
    {ι : Type*} (r : ι → ℂ) (s : Finset ι) (m : ℕ) (c w z₀ : ℂ) (R : ℝ)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R) (hz : ‖z₀‖ < R)
    (hr : ∀ n, n ∉ s → 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖)
    (hne : ∀ n ∈ s, z₀ ≠ r n)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    DifferentiableAt ℂ (fun z => ∑' n, jetCorrectedResolvent m c z w (r n)) z₀ := by
  classical
  have he : ∀ᶠ n in Filter.cofinite, 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖ := by
    filter_upwards [s.finite_toSet.compl_mem_cofinite] with n hn
    exact hr n hn
  apply (jetCorrectedResolvent_finite_complement_differentiableAt r s m c w z₀ R
    hc hw hz hr hne hs).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with z hz
  exact ((jetCorrectedResolvent_summable r m c z w R hc hz.le hw he hs).sum_add_tsum_subtype_compl s).symm

/-- Explicit removal of the movable pole, without assigning it a regular value. -/
theorem jetCorrectedResolvent_scaled (m : ℕ) (c z w r : ℂ) (hz : z ≠ r) :
    (z - r) * jetCorrectedResolvent m c z w r =
      ((r - c) / (w - r)) ^ m * (1 - (z - r) / (w - r)) := by
  unfold jetCorrectedResolvent
  have hzr := sub_ne_zero.mpr hz
  field_simp

#check jetCorrectedResolvent_series_differentiableAt
#print axioms jetCorrectedResolvent_series_differentiableAt
#check jetCorrectedResolvent_scaled
#print axioms jetCorrectedResolvent_scaled


/-- Punctured residue limit for the actual corrected kernel. -/
theorem jetCorrectedResolvent_residue_limit (m : ℕ) (c w r : ℂ) :
    Filter.Tendsto (fun z : ℂ => (z - r) * jetCorrectedResolvent m c z w r)
      (nhdsWithin r ({r}ᶜ : Set ℂ)) (nhds (((r - c) / (w - r)) ^ m)) := by
  have hc : Continuous (fun z : ℂ =>
      ((r - c) / (w - r)) ^ m * (1 - (z - r) / (w - r))) := by fun_prop
  have ht := (hc.tendsto r).mono_left
    (nhdsWithin_le_nhds : nhdsWithin r ({r}ᶜ : Set ℂ) ≤ nhds r)
  simp only [sub_self, zero_div, sub_zero, mul_one] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z ≠ r := by simpa using hz
  exact (jetCorrectedResolvent_scaled m c z w r hne).symm

/-- Noncentral poles of the corrected kernel are not removable. -/
theorem jetCorrectedResolvent_not_continuousAt (m : ℕ) (c w r : ℂ)
    (hc : r ≠ c) (hw : w ≠ r) :
    ¬ ContinuousAt (fun z => jetCorrectedResolvent m c z w r) r := by
  intro h
  have hprod : ContinuousAt (fun z : ℂ => (z - r) * jetCorrectedResolvent m c z w r) r :=
    (continuousAt_id.sub_const r).mul h
  have hlim := hprod.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin r ({r}ᶜ : Set ℂ) ≤ nhds r)
  have hzero : Filter.Tendsto (fun z : ℂ => (z - r) * jetCorrectedResolvent m c z w r)
      (nhdsWithin r ({r}ᶜ : Set ℂ)) (nhds 0) := by
    simpa only [sub_self, zero_mul] using hlim
  have hne : ((r - c) / (w - r)) ^ m ≠ 0 :=
    pow_ne_zero m (div_ne_zero (sub_ne_zero.mpr hc) (sub_ne_zero.mpr hw))
  exact hne (tendsto_nhds_unique (jetCorrectedResolvent_residue_limit m c w r) hzero)

/-- Positive finite multiplicity survives addition of the explicitly constructed
infinite complementary series. Its continuity is proved, not assumed. This is
still conditional on the stated divisor separation and summability data. -/
theorem jetCorrectedResolvent_cluster_with_series_not_continuousAt
    {ι : Type*} (r : ι → ℂ) (s : Finset ι) (m k : ℕ) (hk : 0 < k)
    (c w a : ℂ) (R : ℝ) (hac : a ≠ c) (hwa : w ≠ a)
    (hc : ‖c‖ ≤ R) (hw : ‖w‖ ≤ R) (ha : ‖a‖ < R)
    (hr : ∀ n, n ∉ s → 2 * R ≤ ‖r n‖ ∧ 0 < ‖r n‖)
    (hne : ∀ n ∈ s, a ≠ r n)
    (hs : Summable (fun n => (1 : ℝ) / ‖r n‖ ^ 2)) :
    ¬ ContinuousAt
      (fun z => (k : ℂ) * jetCorrectedResolvent m c z w a +
        ∑' n, jetCorrectedResolvent m c z w (r n)) a := by
  intro h
  have hH := (jetCorrectedResolvent_series_differentiableAt r s m c w a R
    hc hw ha hr hne hs).continuousAt
  have hp : ContinuousAt (fun z => (k : ℂ) * jetCorrectedResolvent m c z w a) a := by
    simpa only [add_sub_cancel_right] using h.sub hH
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  apply jetCorrectedResolvent_not_continuousAt m c w a hac hwa
  simpa only [← mul_assoc, inv_mul_cancel₀ hk0, one_mul] using hp.const_mul ((k : ℂ)⁻¹)

#check jetCorrectedResolvent_residue_limit
#print axioms jetCorrectedResolvent_residue_limit
#check jetCorrectedResolvent_not_continuousAt
#print axioms jetCorrectedResolvent_not_continuousAt
#check jetCorrectedResolvent_cluster_with_series_not_continuousAt
#print axioms jetCorrectedResolvent_cluster_with_series_not_continuousAt

end FrozenD




noncomputable section
open Filter Topology
set_option linter.unnecessarySeqFocus false

/- Round 3, participant E. Inherited public supporting lemmas. Supporting algebra for restricted spectral recovery.
   This file does not construct Hecke L-functions or prove GRH. -/
namespace FrozenE

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
end FrozenE


namespace GAttack

theorem reference_collision_erases_term (c z w : ℂ) :
    FrozenD.jetCorrectedResolvent 1 c z w w = 0 := by
  simp [FrozenD.jetCorrectedResolvent]

theorem corrected_residue_is_weighted :
    (((1 : ℂ) - 0) / (3 - 1)) ^ (1 : ℕ) = (1 / 2 : ℂ) := by norm_num

theorem nonzero_scalar_matrices_can_have_unbounded_inverses (A : ℝ) :
    ∃ t : ℝ, t ≠ 0 ∧ A < |t⁻¹| := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max A 0)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right A 0) hn
  refine ⟨(n : ℝ)⁻¹, inv_ne_zero (ne_of_gt hn0), ?_⟩
  rw [inv_inv, abs_of_pos hn0]
  exact lt_of_le_of_lt (le_max_left A 0) hn

#check reference_collision_erases_term
#print axioms reference_collision_erases_term
#check corrected_residue_is_weighted
#print axioms corrected_residue_is_weighted
#check nonzero_scalar_matrices_can_have_unbounded_inverses
#print axioms nonzero_scalar_matrices_can_have_unbounded_inverses
end GAttack
