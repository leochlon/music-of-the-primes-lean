import Mathlib

/-! Participant E, round 1. Direct audit of the local uniform-bound premise in
§1.4.3. For the trivial character at a real place and z = 3/2, the positive
branch, with dt/t included and u = t - 1, has scalar density below.
This is an actual archimedean summand, not a replacement spectral operator. -/
namespace CriticalLineAudit

noncomputable def realPlaceDensity (u : ℝ) : ℝ :=
  1 / ((1 + u)^2 * u)

/-- Discharges the elementary lower-bound premise needed to audit the claimed
uniform bound for the §1.4.2 cutoffs at the identity. -/
theorem realPlaceDensity_lower {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    1 / (4 * u) ≤ realPlaceDensity u := by
  unfold realPlaceDensity
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * u)
    (by positivity : 0 < (1 + u)^2 * u)).2
  have hsq : (1 + u)^2 ≤ 4 := by nlinarith [mul_nonneg (le_of_lt hu) (sub_nonneg.mpr hu1)]
  simpa using mul_le_mul_of_nonneg_right hsq (le_of_lt hu)

/-- The actual local density has a logarithmically divergent truncated mass.
This audits precisely the uniform archimedean bound asserted in §1.4.3. -/
theorem realPlace_truncated_lower {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    -Real.log ε / 4 ≤ ∫ u in ε..1, realPlaceDensity u := by
  have hc : ContinuousOn realPlaceDensity (Set.Icc ε 1) := by
    unfold realPlaceDensity
    apply ContinuousOn.div continuousOn_const
      (((continuousOn_const.add continuousOn_id).pow 2).mul continuousOn_id)
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hε hu.1
    positivity
  have hd : IntervalIntegrable realPlaceDensity MeasureTheory.volume ε 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hε1] using hc
  have hi : IntervalIntegrable (fun u : ℝ => 1 / (4 * u)) MeasureTheory.volume ε 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hε1]
    apply ContinuousOn.div continuousOn_const (continuousOn_const.mul continuousOn_id)
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hε hu.1
    positivity
  calc
    -Real.log ε / 4 = ∫ u in ε..1, 1 / (4 * u) := by
      have heq : (fun u : ℝ => 1 / (4 * u)) = fun u => (1 / 4 : ℝ) * (1 / u) := by
        funext u
        simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
      rw [heq, intervalIntegral.integral_const_mul,
        integral_one_div_of_pos hε zero_lt_one,
        Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hε), Real.log_one]
      ring
    _ ≤ ∫ u in ε..1, realPlaceDensity u := by
      apply intervalIntegral.integral_mono_on hε1 hi hd
      intro u hu
      exact realPlaceDensity_lower (lt_of_lt_of_le hε hu.1) hu.2

/-- There is no finite bound even on the truncated positive real-place masses
at the fixed parameter z = 3/2 for the trivial character. -/
theorem realPlace_truncated_unbounded (B : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ B < ∫ u in ε..1, realPlaceDensity u := by
  let ε : ℝ := Real.exp (-4 * (max B 0 + 1))
  have hε : 0 < ε := Real.exp_pos _
  have hmax : 0 ≤ max B 0 := le_max_right _ _
  have hB : B ≤ max B 0 := le_max_left _ _
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [Real.exp_lt_one_iff]
    linarith
  refine ⟨ε, hε, hε1, ?_⟩
  have h := realPlace_truncated_lower hε (le_of_lt hε1)
  have he : Real.log ε = -4 * (max B 0 + 1) := Real.log_exp _
  rw [he] at h
  linarith

/-- The manuscript's radial family, with the discontinuity killed by a
cutoff supported above 1. No mollifier is needed on that support. -/
noncomputable def radialTest (h : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (h t : ℂ) * Complex.exp (-z * (Real.log t : ℂ))

/-- Discharges pointwise holomorphic parameter dependence for any fixed
cutoff. It does not assert holomorphy of an integral or an infinite zero sum. -/
theorem radialTest_entire (h : ℝ → ℝ) (t : ℝ) :
    Differentiable ℂ (fun z => radialTest h z t) := by
  unfold radialTest
  fun_prop

/-- Discharges the radial vanishing restriction at norm 1 and below;
smoothness and compact support of the chosen cutoff remain separate. -/
theorem radialTest_vanishes (h : ℝ → ℝ) (hh : ∀ t ≤ 1, h t = 0)
    (z : ℂ) {t : ℝ} (ht : t ≤ 1) : radialTest h z t = 0 := by
  simp [radialTest, hh t ht]

/-- Direct next step for a possible repaired trace identity: the difference
of the genuine real-place densities at z=3/2 and z=5/2 cancels the pole.
This does not justify any spectral sum or continuation. -/
theorem realPlace_adjacent_parameter_difference {u : ℝ} (hu : 0 < u) :
    realPlaceDensity u - 1 / ((1 + u)^3 * u) = 1 / (1 + u)^3 := by
  unfold realPlaceDensity
  have hu0 : u ≠ 0 := ne_of_gt hu
  have h1 : 1 + u ≠ 0 := ne_of_gt (by linarith : 0 < 1 + u)
  field_simp [hu0, h1]
  ring

/-- Round 2: discharges the cutoff-independent local integral bound for the
specific repaired difference z=3/2 minus z=5/2. By the preceding identity the
integrand is the difference of the actual positive real-place densities.
This is only a scalar local premise: general complex parameters, the genuine
idelic test attachment, and the spectral zero-sum limit remain unresolved. -/
theorem realPlace_adjacent_cutoff_bound (h : ℝ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hc : ContinuousOn h (Set.Icc ε 1))
    (hh : ∀ u ∈ Set.Icc ε 1, 0 ≤ h u ∧ h u ≤ 1) :
    0 ≤ (∫ u in ε..1, h u / (1 + u)^3) ∧
      (∫ u in ε..1, h u / (1 + u)^3) ≤ 1 := by
  have hi : IntervalIntegrable (fun u => h u / (1 + u)^3)
      MeasureTheory.volume ε 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hε1]
    apply hc.div ((continuousOn_const.add continuousOn_id).pow 3)
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hε hu.1
    positivity
  constructor
  · have hl : (∫ u in ε..1, (0 : ℝ)) ≤
        ∫ u in ε..1, h u / (1 + u)^3 := by
      apply intervalIntegral.integral_mono_on hε1 intervalIntegrable_const hi
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hε hu.1
      exact div_nonneg (hh u hu).1 (by positivity)
    simpa using hl
  · have hl : (∫ u in ε..1, h u / (1 + u)^3) ≤
        ∫ u in ε..1, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hε1 hi intervalIntegrable_const
      intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hε hu.1
      apply (div_le_iff₀ (by positivity : 0 < (1 + u)^3)).2
      have hh1 := (hh u hu).2
      nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) (le_of_lt hu0)]
    have hl' : (∫ u in ε..1, h u / (1 + u)^3) ≤ 1 - ε := by
      simpa using hl
    linarith

#check realPlace_adjacent_cutoff_bound
#print axioms realPlace_adjacent_cutoff_bound
#check realPlace_adjacent_parameter_difference
#print axioms realPlace_adjacent_parameter_difference
#check radialTest_entire
#print axioms radialTest_entire
#check radialTest_vanishes
#print axioms radialTest_vanishes
#check realPlaceDensity_lower
#print axioms realPlaceDensity_lower
#check realPlace_truncated_lower
#print axioms realPlace_truncated_lower
#check realPlace_truncated_unbounded
#print axioms realPlace_truncated_unbounded

/-- Explicit logarithmic cutoff for the §1.4.2 one-sided family. -/
noncomputable def logCutoff (N x : ℝ) : ℝ :=
  Real.smoothTransition (N * x - 1) * Real.smoothTransition (N + 1 - x)

/-- Discharges smoothness of the scalar radial cutoff. -/
theorem logCutoff_smooth (N : ℝ) : ContDiff ℝ (↑(⊤ : ENat)) (logCutoff N) := by
  unfold logCutoff
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)
  · exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- Discharges the required cutoff range, independently of the parameter. -/
theorem logCutoff_bounds (N x : ℝ) : 0 ≤ logCutoff N x ∧ logCutoff N x ≤ 1 := by
  have ha := Real.smoothTransition.nonneg (N * x - 1)
  have hb := Real.smoothTransition.nonneg (N + 1 - x)
  have hc := Real.smoothTransition.le_one (N * x - 1)
  have hd := Real.smoothTransition.le_one (N + 1 - x)
  unfold logCutoff
  constructor
  · exact mul_nonneg ha hb
  · nlinarith

/-- Discharges vanishing on a full neighborhood of log-norm zero. -/
theorem logCutoff_zero_left {N x : ℝ} (hN : 0 < N) (hx : x ≤ 1 / N) :
    logCutoff N x = 0 := by
  have h : N * x - 1 ≤ 0 := by
    have := (le_div_iff₀ hN).mp hx
    nlinarith
  simp [logCutoff, Real.smoothTransition.zero_of_nonpos h]

/-- Discharges the upper support bound for each finite cutoff. -/
theorem logCutoff_zero_right {N x : ℝ} (hx : N + 1 ≤ x) :
    logCutoff N x = 0 := by
  simp [logCutoff, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx)]

/-- Discharges compact radial support; genuine compact norm-fiber attachment
is a separate arithmetic/topological premise. -/
theorem logCutoff_compactSupport {N : ℝ} (hN : 0 < N) :
    HasCompactSupport (logCutoff N) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / N) (N + 1))
    isCompact_Icc
  intro x hx
  change logCutoff N x ≠ 0 at hx
  constructor
  · by_contra h
    exact hx (logCutoff_zero_left hN (le_of_not_ge h))
  · by_contra h
    exact hx (logCutoff_zero_right (le_of_not_ge h))

/-- Discharges eventual exact agreement away from the norm-one boundary. -/
theorem logCutoff_eq_one {N x : ℝ} (hlo : 2 ≤ N * x) (hhi : x ≤ N) :
    logCutoff N x = 1 := by
  have h1 : 1 ≤ N * x - 1 := by linarith
  have h2 : 1 ≤ N + 1 - x := by linarith
  simp [logCutoff, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2]

/-- The concrete cutoffs eventually equal one at every positive log-norm;
this proves the scalar pointwise approximation premise without zero assumptions. -/
theorem logCutoff_eventually_one {x : ℝ} (hx : 0 < x) :
    ∀ᶠ n : ℕ in Filter.atTop, logCutoff (n + 1) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 / x) x)
  apply Filter.eventually_atTop.mpr
  refine ⟨N, fun n hn => ?_⟩
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hl : 2 / x ≤ (n : ℝ) + 1 := by
    have := le_max_left (2 / x) x
    linarith
  have hh : x ≤ (n : ℝ) + 1 := by
    have := le_max_right (2 / x) x
    linarith
  exact logCutoff_eq_one ((div_le_iff₀ hx).mp hl) hh

#check logCutoff_smooth
#print axioms logCutoff_smooth
#check logCutoff_bounds
#print axioms logCutoff_bounds
#check logCutoff_zero_left
#print axioms logCutoff_zero_left
#check logCutoff_zero_right
#print axioms logCutoff_zero_right
#check logCutoff_compactSupport
#print axioms logCutoff_compactSupport
#check logCutoff_eq_one
#print axioms logCutoff_eq_one
#check logCutoff_eventually_one
#print axioms logCutoff_eventually_one

/-- Actual scalar logarithmic-coordinate difference test, prior to attachment
by the idelic norm and inverse character. -/
noncomputable def logTest (N : ℝ) (z w : ℂ) (x : ℝ) : ℂ :=
  (logCutoff N x : ℂ) *
    (Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ)))

/-- Discharges smoothness in the radial coordinate for each finite test. -/
theorem logTest_smooth (N : ℝ) (z w : ℂ) :
    ContDiff ℝ (↑(⊤ : ENat)) (logTest N z w) := by
  have hh : ContDiff ℝ (↑(⊤ : ENat)) (fun x => (logCutoff N x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (logCutoff_smooth N)
  apply hh.mul
  apply ContDiff.sub
  · exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  · exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

/-- Discharges complex parameter holomorphy of the constructed finite test. -/
theorem logTest_entire (N x : ℝ) (w : ℂ) :
    Differentiable ℂ (fun z => logTest N z w x) := by
  unfold logTest
  fun_prop

/-- Discharges compact support and the one-sided vanishing restriction in
logarithmic coordinates, uniformly in both complex parameters. -/
theorem logTest_support {N : ℝ} (hN : 0 < N) (z w : ℂ) :
    HasCompactSupport (logTest N z w) ∧
      ∀ x ≤ 1 / N, logTest N z w x = 0 := by
  have hz : ∀ x, logCutoff N x = 0 → logTest N z w x = 0 := by
    intro x hx
    simp [logTest, hx]
  constructor
  · apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (1 / N) (N + 1)) isCompact_Icc
    intro x hx
    change logTest N z w x ≠ 0 at hx
    constructor
    · by_contra h
      exact hx (hz x (logCutoff_zero_left hN (le_of_not_ge h)))
    · by_contra h
      exact hx (hz x (logCutoff_zero_right (le_of_not_ge h)))
  · intro x hx
    exact hz x (logCutoff_zero_left hN hx)

/-- Discharges pointwise convergence by eventual exact equality for every
positive log-norm, uniformly as an equality in the complex parameters. -/
theorem logTest_eventually_eq {x : ℝ} (hx : 0 < x) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ z w : ℂ,
      logTest (n + 1) z w x =
        Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ)) := by
  filter_upwards [logCutoff_eventually_one hx] with n hn
  intro z w
  simp [logTest, hn]

#check logTest_smooth
#print axioms logTest_smooth
#check logTest_entire
#print axioms logTest_entire
#check logTest_support
#print axioms logTest_support
#check logTest_eventually_eq
#print axioms logTest_eventually_eq

/-- Round 4. Supplies the compact-parameter Lipschitz estimate needed to
cancel the norm-one singularity of the actual radial difference test. -/
theorem exp_difference_bound {a b : ℂ} {R : ℝ}
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖Complex.exp a - Complex.exp b‖ ≤ Real.exp R * ‖a - b‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Complex.exp) (s := Metric.closedBall 0 R)
  · intro t ht
    exact Complex.differentiable_exp.differentiableAt
  · intro t ht
    rw [Complex.deriv_exp, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm t).trans (by simpa using ht)
  · exact convex_closedBall (0 : ℂ) R
  · simpa using hb
  · simpa using ha

/-- Supplies a cutoff-independent O(x) bound for the radial difference on
0<=x<=1. This is the numerator estimate for the real archimedean kernel. -/
theorem logTest_near_zero_bound (N : ℝ) {z w : ℂ} {R x : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    ‖logTest N z w x‖ ≤ Real.exp R * ‖z - w‖ * x := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have ha : ‖-z * (x : ℂ)‖ ≤ R := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    nlinarith [norm_nonneg z]
  have hb : ‖-w * (x : ℂ)‖ ≤ R := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    nlinarith [norm_nonneg w]
  have he := exp_difference_bound ha hb
  have heq : -z * (x : ℂ) - -w * (x : ℂ) = -(z-w) * (x : ℂ) := by ring
  rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx] at he
  have hc := logCutoff_bounds N x
  calc
    ‖logTest N z w x‖ = logCutoff N x *
        ‖Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ))‖ := by
      simp [logTest, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1]
    _ ≤ ‖Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hc.2
    _ ≤ Real.exp R * ‖z-w‖ * x := by simpa [mul_assoc] using he

/-- Actual positive real-place radial density after x=log(t), omitting the
fixed Haar prefactor and unitary character. The arithmetic attachment and
change-of-variables theorem remain explicit separate premises. -/
noncomputable def realPlaceLogDifference (N : ℝ) (z w : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * logTest N z w x / (Real.exp x - 1 : ℝ)

/-- Discharges local uniform domination at the norm-one boundary for the
constructed difference family, uniformly in every cutoff and bounded pair
of complex parameters. No zero or spectral summability hypothesis occurs. -/
theorem realPlaceLogDifference_bound (N : ℝ) {z w : ℂ} {R x : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖realPlaceLogDifference N z w x‖ ≤
      Real.exp (1 / 2) * Real.exp R * ‖z - w‖ := by
  have hd : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hdp : 0 < Real.exp x - 1 := lt_of_lt_of_le hx hd
  have hn := logTest_near_zero_bound N hz hw (le_of_lt hx) hx1
  have he : Real.exp (x / 2) ≤ Real.exp (1 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold realPlaceLogDifference
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdp]
  apply (div_le_iff₀ hdp).2
  calc
    Real.exp (x / 2) * ‖logTest N z w x‖ ≤
        Real.exp (1 / 2) * (Real.exp R * ‖z-w‖ * x) :=
      mul_le_mul he hn (norm_nonneg _) (le_of_lt (Real.exp_pos _))
    _ = (Real.exp (1 / 2) * Real.exp R * ‖z-w‖) * x := by ring
    _ ≤ (Real.exp (1 / 2) * Real.exp R * ‖z-w‖) * (Real.exp x - 1) :=
      mul_le_mul_of_nonneg_left hd (by positivity)

#check exp_difference_bound
#print axioms exp_difference_bound
#check logTest_near_zero_bound
#print axioms logTest_near_zero_bound
#check realPlaceLogDifference_bound
#print axioms realPlaceLogDifference_bound

/-- Makes the preceding estimate uniform over both parameter balls; this
is the near-identity domination premise required before integral limits. -/
theorem realPlaceLogDifference_uniform_bound (N : ℝ) {z w : ℂ} {R x : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖realPlaceLogDifference N z w x‖ ≤
      Real.exp (1 / 2) * Real.exp R * (2 * R) := by
  apply (realPlaceLogDifference_bound N hz hw hx hx1).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := norm_sub_le z w
  linarith

#check realPlaceLogDifference_uniform_bound
#print axioms realPlaceLogDifference_uniform_bound

/-- Discharges a uniform small-boundary integral estimate, with explicit
interval length; it is the local error control needed in the cutoff limit. -/
theorem realPlaceLogDifference_integral_bound (N : ℝ) {z w : ℂ} {R a b : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ‖∫ x in a..b, realPlaceLogDifference N z w x‖ ≤
      (Real.exp (1 / 2) * Real.exp R * (2 * R)) * (b-a) := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := realPlaceLogDifference N z w)
    (C := Real.exp (1 / 2) * Real.exp R * (2 * R)) (by
      intro x hx
      rw [Set.uIoc_of_le hab] at hx
      exact realPlaceLogDifference_uniform_bound N hz hw
        (lt_of_le_of_lt ha hx.1) (hx.2.trans hb))
  simpa [abs_of_nonneg (sub_nonneg.mpr hab)] using h

/-- Supplies actual measurability, rather than assuming it, for dominated
convergence of the real-place radial differences near norm one. -/
theorem realPlaceLogDifference_measurable (N : ℝ) (z w : ℂ) :
    Measurable (realPlaceLogDifference N z w) := by
  have ht := (logTest_smooth N z w).continuous.measurable
  unfold realPlaceLogDifference
  fun_prop

/-- The unsubcutoff parameter difference of the same local density. Its
value at zero uses field division by zero and is irrelevant to the integral. -/
noncomputable def realPlaceLogLimit (z w : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) *
    (Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ))) /
      (Real.exp x - 1 : ℝ)

/-- Discharges the near-identity real-place integral/cutoff-limit interchange
for every complex parameter pair, without any zero-free or summability
assumption. Tail, angular and spectral limits remain separate premises. -/
theorem realPlaceLogDifference_integral_tendsto (z w : ℂ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in Set.Ioc (0 : ℝ) 1,
        realPlaceLogDifference (n+1) z w x)
      Filter.atTop
      (nhds (∫ x in Set.Ioc (0 : ℝ) 1, realPlaceLogLimit z w x)) := by
  let R : ℝ := max ‖z‖ ‖w‖
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (1 / 2) * Real.exp R * (2 * R))
  · intro n
    exact (realPlaceLogDifference_measurable (n+1) z w).aestronglyMeasurable
  · exact MeasureTheory.integrable_const _
  · intro n
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact realPlaceLogDifference_uniform_bound (n+1)
      (le_max_left _ _) (le_max_right _ _) hx.1 hx.2
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [logTest_eventually_eq hx.1] with n hn
    simp only [realPlaceLogDifference, realPlaceLogLimit, hn]

#check realPlaceLogDifference_integral_bound
#print axioms realPlaceLogDifference_integral_bound
#check realPlaceLogDifference_measurable
#print axioms realPlaceLogDifference_measurable
#check realPlaceLogDifference_integral_tendsto
#print axioms realPlaceLogDifference_integral_tendsto

/-- Round 5: supplies the uncut local-density majorant used for uniform
parameter convergence, derived from the checked cutoff bound. -/
theorem realPlaceLogLimit_bound {z w : ℂ} {R x : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖realPlaceLogLimit z w x‖ ≤ Real.exp (1 / 2) * Real.exp R * (2 * R) := by
  obtain ⟨n, hn⟩ := (logTest_eventually_eq hx).exists
  have h := realPlaceLogDifference_uniform_bound (n+1) hz hw hx hx1
  simpa only [realPlaceLogDifference, realPlaceLogLimit, hn] using h

/-- Supplies measurable limiting densities for the parameter-uniform local
integral error estimate; no analytic hypothesis is assumed. -/
theorem realPlaceLogLimit_measurable (z w : ℂ) :
    Measurable (realPlaceLogLimit z w) := by
  unfold realPlaceLogLimit
  fun_prop

/-- Discharges the exact common-error factorization for the real-place
cutoff family. The scalar error is independent of both complex parameters. -/
theorem realPlaceLogDifference_error_factor (N x : ℝ) (z w : ℂ) :
    realPlaceLogDifference N z w x - realPlaceLogLimit z w x =
      ((logCutoff N x - 1 : ℝ) : ℂ) * realPlaceLogLimit z w x := by
  unfold realPlaceLogDifference realPlaceLogLimit logTest
  push_cast
  ring

/-- Discharges the parameter-uniform, integrable local error majorant
required before the normal-family argument can be invoked. -/
theorem realPlaceLogDifference_error_bound (N : ℝ) {z w : ℂ} {R x : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖realPlaceLogDifference N z w x - realPlaceLogLimit z w x‖ ≤
      (1 - logCutoff N x) * (Real.exp (1 / 2) * Real.exp R * (2 * R)) := by
  rw [realPlaceLogDifference_error_factor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (logCutoff_bounds N x).2)]
  have h := mul_le_mul_of_nonneg_left (realPlaceLogLimit_bound hz hw hx hx1)
    (sub_nonneg.mpr (logCutoff_bounds N x).2)
  simpa only [neg_sub] using h

#check realPlaceLogLimit_bound
#print axioms realPlaceLogLimit_bound
#check realPlaceLogLimit_measurable
#print axioms realPlaceLogLimit_measurable
#check realPlaceLogDifference_error_factor
#print axioms realPlaceLogDifference_error_factor
#check realPlaceLogDifference_error_bound
#print axioms realPlaceLogDifference_error_bound

/-- Supplies actual absolute integrability of both local densities so that
subtracting their integrals in the uniform-limit argument is legitimate. -/
theorem realPlaceLog_integrable (N : ℝ) (z w : ℂ) :
    MeasureTheory.Integrable (realPlaceLogDifference N z w)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    MeasureTheory.Integrable (realPlaceLogLimit z w)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  let R := max ‖z‖ ‖w‖
  have hi : MeasureTheory.Integrable
      (fun _ : ℝ => Real.exp (1 / 2) * Real.exp R * (2 * R))
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    MeasureTheory.integrable_const _
  constructor
  · apply hi.mono' (realPlaceLogDifference_measurable N z w).aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact realPlaceLogDifference_uniform_bound N (le_max_left _ _) (le_max_right _ _)
      hx.1 hx.2
  · apply hi.mono' (realPlaceLogLimit_measurable z w).aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact realPlaceLogLimit_bound (le_max_left _ _) (le_max_right _ _) hx.1 hx.2

/-- Supplies integrability of the common scalar error majorant; this is a
cutoff lemma for the assigned uniform local integral limit. -/
theorem logCutoff_error_integrable (N : ℝ) :
    MeasureTheory.Integrable (fun x => 1 - logCutoff N x)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  apply (MeasureTheory.integrable_const (1 : ℝ)).mono'
    (continuous_const.sub (logCutoff_smooth N).continuous).measurable.aestronglyMeasurable
  filter_upwards [] with x
  have hc := logCutoff_bounds N x
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc.2)]
  linarith [hc.1]

/-- The scalar error mass controlling every parameter pair in a bounded ball. -/
noncomputable def cutoffErrorMass (n : ℕ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, 1 - logCutoff (n+1) x

/-- Discharges the vanishing common-majorant premise for the uniform local
cutoff limit, by dominated convergence independent of the parameters. -/
theorem cutoffErrorMass_tendsto :
    Filter.Tendsto cutoffErrorMass Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto
      (fun n : ℕ => ∫ x in Set.Ioc (0 : ℝ) 1, 1 - logCutoff (n+1) x)
      Filter.atTop (nhds (∫ x in Set.Ioc (0 : ℝ) 1, (0 : ℝ))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro n
      exact (logCutoff_error_integrable (n+1)).aestronglyMeasurable
    · exact MeasureTheory.integrable_const _
    · intro n
      filter_upwards [] with x
      have hc := logCutoff_bounds (n+1) x
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc.2)]
      linarith [hc.1]
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [logCutoff_eventually_one hx.1] with n hn
      simp [hn]
  simpa [cutoffErrorMass] using h

/-- Discharges a common bound on the difference of actual local integrals,
with all integrability needed for integral subtraction proved above. -/
theorem realPlaceLogDifference_integral_error_bound (n : ℕ) {z w : ℂ} {R : ℝ}
    (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖(∫ x in Set.Ioc (0 : ℝ) 1, realPlaceLogDifference (n+1) z w x) -
      (∫ x in Set.Ioc (0 : ℝ) 1, realPlaceLogLimit z w x)‖ ≤
    cutoffErrorMass n * (Real.exp (1 / 2) * Real.exp R * (2 * R)) := by
  obtain ⟨hi, hj⟩ := realPlaceLog_integrable (n+1) z w
  rw [← MeasureTheory.integral_sub hi hj]
  have h := MeasureTheory.norm_integral_le_of_norm_le
    ((logCutoff_error_integrable (n+1)).mul_const
      (Real.exp (1 / 2) * Real.exp R * (2 * R))) (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      exact realPlaceLogDifference_error_bound (n+1) hz hw hx.1 hx.2)
  simpa only [MeasureTheory.integral_mul_const, cutoffErrorMass] using h

/-- Discharges uniform convergence of the near-identity positive real-place
integrals on EVERY bounded pair of complex parameter balls. This supplies
one local limit premise of the manuscript's holomorphic-family route; no
zero-free region, zero count, trace identity or spectral sum is assumed. -/
theorem realPlaceLogDifference_integral_tendstoUniformlyOn (R : ℝ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℂ => ∫ x in Set.Ioc (0 : ℝ) 1,
        realPlaceLogDifference (n+1) p.1 p.2 x)
      (fun p : ℂ × ℂ => ∫ x in Set.Ioc (0 : ℝ) 1, realPlaceLogLimit p.1 p.2 x)
      Filter.atTop {p | ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Filter.Tendsto
      (fun n => cutoffErrorMass n * (Real.exp (1 / 2) * Real.exp R * (2 * R)))
      Filter.atTop (nhds 0) := by
    simpa using cutoffErrorMass_tendsto.mul_const
      (Real.exp (1 / 2) * Real.exp R * (2 * R))
  filter_upwards [Filter.Tendsto.eventually_lt_const hε ht] with n hn
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (realPlaceLogDifference_integral_error_bound n hp.1 hp.2).trans_lt hn

#check realPlaceLog_integrable
#print axioms realPlaceLog_integrable
#check logCutoff_error_integrable
#print axioms logCutoff_error_integrable
#check cutoffErrorMass_tendsto
#print axioms cutoffErrorMass_tendsto
#check realPlaceLogDifference_integral_error_bound
#print axioms realPlaceLogDifference_integral_error_bound
#check realPlaceLogDifference_integral_tendstoUniformlyOn
#print axioms realPlaceLogDifference_integral_tendstoUniformlyOn

/-- Supplies the exponential numerator bound needed for the positive
real-place tail majorant uniformly in all cutoffs and a right half-plane. -/
theorem logTest_halfplane_bound (N : ℝ) {z w : ℂ} {σ x : ℝ}
    (hz : σ ≤ z.re) (hw : σ ≤ w.re) (hx : 0 ≤ x) :
    ‖logTest N z w x‖ ≤ 2 * Real.exp (-σ * x) := by
  have he (v : ℂ) (hv : σ ≤ v.re) :
      ‖Complex.exp (-v * (x : ℂ))‖ ≤ Real.exp (-σ * x) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  have hc := logCutoff_bounds N x
  calc
    ‖logTest N z w x‖ = logCutoff N x *
        ‖Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ))‖ := by
      simp [logTest, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1]
    _ ≤ ‖Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ))‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hc.2
    _ ≤ ‖Complex.exp (-z * (x : ℂ))‖ + ‖Complex.exp (-w * (x : ℂ))‖ := norm_sub_le _ _
    _ ≤ 2 * Real.exp (-σ * x) := by linarith [he z hz, he w hw]

/-- Discharges the uniform exponential decay estimate for the positive
real-place tail. Integrating it requires σ > -1/2; neither a zero-free
region nor any spectral summability is a hypothesis. -/
theorem realPlaceLogDifference_tail_bound (N : ℝ) {z w : ℂ} {σ x : ℝ}
    (hz : σ ≤ z.re) (hw : σ ≤ w.re) (hx : 1 ≤ x) :
    ‖realPlaceLogDifference N z w x‖ ≤ 4 * Real.exp (-(σ + 1 / 2) * x) := by
  have he : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hd : 0 < Real.exp x - 1 := by linarith
  have hn := logTest_halfplane_bound N hz hw (by linarith : 0 ≤ x)
  unfold realPlaceLogDifference
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  calc
    Real.exp (x / 2) * ‖logTest N z w x‖ ≤
      Real.exp (x / 2) * (2 * Real.exp (-σ * x)) :=
        mul_le_mul_of_nonneg_left hn (le_of_lt (Real.exp_pos _))
    _ = 2 * (Real.exp (x / 2) * Real.exp (-σ * x)) := by ring
    _ = 2 * Real.exp (x / 2 + -σ * x) := by rw [Real.exp_add]
    _ = 2 * Real.exp (-(σ + 1 / 2) * x + x) := by congr 2; ring
    _ = (2 * Real.exp (-(σ + 1 / 2) * x)) * Real.exp x := by rw [Real.exp_add]; ring
    _ ≤ (2 * Real.exp (-(σ + 1 / 2) * x)) * (2 * (Real.exp x - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (4 * Real.exp (-(σ + 1 / 2) * x)) * (Real.exp x - 1) := by ring

#check logTest_halfplane_bound
#print axioms logTest_halfplane_bound
#check realPlaceLogDifference_tail_bound
#print axioms realPlaceLogDifference_tail_bound

/-- Round 6: discharges the integrable majorant premise on the positive
real-place tail in the assigned cutoff/limit argument. -/
theorem realTailMajorant_integrable {σ : ℝ} (hσ : -(1/2 : ℝ) < σ) :
    MeasureTheory.Integrable (fun x : ℝ => 4 * Real.exp (-(σ+1/2)*x))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hi : MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.exp (-(σ+1/2)*x)) (Set.Ioi (1 : ℝ)) := by
    apply integrableOn_exp_mul_Ioi
    linarith
  exact hi.const_mul 4

/-- Supplies the uncut tail bound for the same actual scalar density;
this is needed to justify subtracting its integral from the cutoff integral. -/
theorem realPlaceLogLimit_tail_bound {z w : ℂ} {σ x : ℝ}
    (hz : σ ≤ z.re) (hw : σ ≤ w.re) (hx : 1 ≤ x) :
    ‖realPlaceLogLimit z w x‖ ≤ 4 * Real.exp (-(σ+1/2)*x) := by
  obtain ⟨n, hn⟩ := (logTest_eventually_eq (by linarith : 0 < x)).exists
  have h := realPlaceLogDifference_tail_bound (n+1) hz hw hx
  simpa only [realPlaceLogDifference, realPlaceLogLimit, hn] using h

/-- Discharges absolute integrability of both positive real-place tails,
derived from Re(z),Re(w)>-1/2 rather than assumed as a spectral premise. -/
theorem realPlaceLog_tail_integrable (N : ℝ) {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    MeasureTheory.Integrable (realPlaceLogDifference N z w)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) ∧
    MeasureTheory.Integrable (realPlaceLogLimit z w)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
  constructor
  · apply (realTailMajorant_integrable hσ).mono'
      (realPlaceLogDifference_measurable N z w).aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact realPlaceLogDifference_tail_bound N hz hw (le_of_lt hx)
  · apply (realTailMajorant_integrable hσ).mono'
      (realPlaceLogLimit_measurable z w).aestronglyMeasurable
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    exact realPlaceLogLimit_tail_bound hz hw (le_of_lt hx)

/-- The common tail error mass depends only on the half-plane margin and
cutoff; its vanishing will supply uniformity in both complex parameters. -/
noncomputable def tailErrorMass (σ : ℝ) (n : ℕ) : ℝ :=
  ∫ x in Set.Ioi (1 : ℝ),
    (1-logCutoff (n+1) x) * (4 * Real.exp (-(σ+1/2)*x))

/-- Discharges integrability of the tail error majorant before applying
dominated convergence or bounding an integral difference. -/
theorem tailError_integrable {σ : ℝ} (hσ : -(1/2 : ℝ) < σ) (N : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => (1-logCutoff N x) * (4 * Real.exp (-(σ+1/2)*x)))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
  apply (realTailMajorant_integrable hσ).mono'
    ((continuous_const.sub (logCutoff_smooth N).continuous).mul
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)))).measurable.aestronglyMeasurable
  filter_upwards [] with x
  have hc := logCutoff_bounds N x
  have he : 0 ≤ 4 * Real.exp (-(σ+1/2)*x) := by positivity
  have hp := mul_nonneg (sub_nonneg.mpr hc.2) he
  change |(1-logCutoff N x) * (4 * Real.exp (-(σ+1/2)*x))| ≤ 4 * Real.exp (-(σ+1/2)*x)
  rw [abs_of_nonneg hp]
  exact mul_le_of_le_one_left he (by linarith [hc.1])

/-- Discharges the vanishing uniform tail-error premise of the manuscript's
normal-family route; domination is proved independently of all zero data. -/
theorem tailErrorMass_tendsto {σ : ℝ} (hσ : -(1/2 : ℝ) < σ) :
    Filter.Tendsto (tailErrorMass σ) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto
      (fun n : ℕ => ∫ x in Set.Ioi (1 : ℝ),
        (1-logCutoff (n+1) x) * (4 * Real.exp (-(σ+1/2)*x)))
      Filter.atTop (nhds (∫ x in Set.Ioi (1 : ℝ), (0 : ℝ))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : ℝ => 4 * Real.exp (-(σ+1/2)*x))
    · intro n
      exact (tailError_integrable hσ (n+1)).aestronglyMeasurable
    · exact realTailMajorant_integrable hσ
    · intro n
      filter_upwards [] with x
      have hc := logCutoff_bounds (n+1) x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hc.2) (by positivity))]
      exact mul_le_of_le_one_left (by positivity) (by linarith [hc.1])
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [logCutoff_eventually_one (lt_trans zero_lt_one hx)] with n hn
      simp [hn]
  simpa only [MeasureTheory.integral_zero] using h

/-- Supplies the exact uniform tail error estimate for the actual cutoff
integrals, including all needed integral-subtraction hypotheses. -/
theorem realPlaceLogDifference_tail_integral_error_bound (n : ℕ) {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    ‖(∫ x in Set.Ioi (1 : ℝ), realPlaceLogDifference (n+1) z w x) -
      (∫ x in Set.Ioi (1 : ℝ), realPlaceLogLimit z w x)‖ ≤ tailErrorMass σ n := by
  obtain ⟨hi,hj⟩ := realPlaceLog_tail_integrable (n+1) hσ hz hw
  rw [← MeasureTheory.integral_sub hi hj]
  apply MeasureTheory.norm_integral_le_of_norm_le (tailError_integrable hσ (n+1))
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  rw [realPlaceLogDifference_error_factor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (logCutoff_bounds (n+1) x).2)]
  simpa only [neg_sub] using mul_le_mul_of_nonneg_left
    (realPlaceLogLimit_tail_bound hz hw (le_of_lt hx))
    (sub_nonneg.mpr (logCutoff_bounds (n+1) x).2)

/-- Discharges full-sequence uniform convergence of the positive real-place
TAIL on every closed parameter half-plane Re(z),Re(w)>=σ>-1/2.
This is one analytic premise of §§1.4.2-1.4.4, not a critical-line theorem. -/
theorem realPlaceLogDifference_tail_tendstoUniformlyOn {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℂ => ∫ x in Set.Ioi (1 : ℝ),
        realPlaceLogDifference (n+1) p.1 p.2 x)
      (fun p : ℂ × ℂ => ∫ x in Set.Ioi (1 : ℝ), realPlaceLogLimit p.1 p.2 x)
      Filter.atTop {p | σ ≤ p.1.re ∧ σ ≤ p.2.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Filter.Tendsto.eventually_lt_const hε (tailErrorMass_tendsto hσ)] with n hn
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (realPlaceLogDifference_tail_integral_error_bound n hσ hp.1 hp.2).trans_lt hn

#check realTailMajorant_integrable
#print axioms realTailMajorant_integrable
#check realPlaceLogLimit_tail_bound
#print axioms realPlaceLogLimit_tail_bound
#check realPlaceLog_tail_integrable
#print axioms realPlaceLog_tail_integrable
#check tailError_integrable
#print axioms tailError_integrable
#check tailErrorMass_tendsto
#print axioms tailErrorMass_tendsto
#check realPlaceLogDifference_tail_integral_error_bound
#print axioms realPlaceLogDifference_tail_integral_error_bound
#check realPlaceLogDifference_tail_tendstoUniformlyOn
#print axioms realPlaceLogDifference_tail_tendstoUniformlyOn

/-- Round 7: discharges assembly of the near-identity and tail integrability
premises for the actual scalar positive real-place difference density. -/
theorem realPlaceLog_full_integrable (N : ℝ) {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    MeasureTheory.IntegrableOn (realPlaceLogDifference N z w) (Set.Ioi (0 : ℝ)) ∧
    MeasureTheory.IntegrableOn (realPlaceLogLimit z w) (Set.Ioi (0 : ℝ)) := by
  have hu : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr (lt_of_not_ge h)
  obtain ⟨ha,hb⟩ := realPlaceLog_integrable N z w
  obtain ⟨hc,hd⟩ := realPlaceLog_tail_integrable N hσ hz hw
  exact ⟨hu ▸ MeasureTheory.IntegrableOn.union ha hc,
    hu ▸ MeasureTheory.IntegrableOn.union hb hd⟩

/-- Supplies the exact set-integral partition needed to combine the two
proved cutoff error estimates; absolute integrability is explicit. -/
theorem positiveIntegral_split (f : ℝ → ℂ)
    (hnear : MeasureTheory.IntegrableOn f (Set.Ioc (0 : ℝ) 1))
    (htail : MeasureTheory.IntegrableOn f (Set.Ioi (1 : ℝ))) :
    (∫ x in Set.Ioi (0 : ℝ), f x) =
      (∫ x in Set.Ioc (0 : ℝ) 1, f x) + (∫ x in Set.Ioi (1 : ℝ), f x) := by
  have hu : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi 1 = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx,h⟩
      · exact Or.inr (lt_of_not_ge h)
  have hd : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  rw [← hu]
  exact MeasureTheory.setIntegral_union hd measurableSet_Ioi hnear htail

/-- Discharges the full positive real-place cutoff-error premise on bounded
parameter sets with an independently specified half-plane margin. -/
theorem realPlaceLogDifference_full_error_bound (n : ℕ) {z w : ℂ} {R σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hzR : ‖z‖ ≤ R) (hwR : ‖w‖ ≤ R)
    (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    ‖(∫ x in Set.Ioi (0 : ℝ), realPlaceLogDifference (n+1) z w x) -
      (∫ x in Set.Ioi (0 : ℝ), realPlaceLogLimit z w x)‖ ≤
      cutoffErrorMass n * (Real.exp (1/2) * Real.exp R * (2*R)) + tailErrorMass σ n := by
  obtain ⟨ha,hb⟩ := realPlaceLog_integrable (n+1) z w
  obtain ⟨hc,hd⟩ := realPlaceLog_tail_integrable (n+1) hσ hz hw
  rw [positiveIntegral_split _ ha hc, positiveIntegral_split _ hb hd]
  have he := realPlaceLogDifference_integral_error_bound n hzR hwR
  have hf := realPlaceLogDifference_tail_integral_error_bound n hσ hz hw
  calc
    _ = ‖((∫ x in Set.Ioc (0 : ℝ) 1, realPlaceLogDifference (n+1) z w x) -
        (∫ x in Set.Ioc (0 : ℝ) 1, realPlaceLogLimit z w x)) +
        ((∫ x in Set.Ioi (1 : ℝ), realPlaceLogDifference (n+1) z w x) -
        (∫ x in Set.Ioi (1 : ℝ), realPlaceLogLimit z w x))‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hf)

/-- Round 7 export. Discharges uniform cutoff convergence of the WHOLE
positive real-place difference integral, on every bounded pair of parameter
sets with Re(z),Re(w)>=σ>-1/2. This does not assert holomorphy or a zero sum. -/
theorem realPlaceLogDifference_full_tendstoUniformlyOn (R : ℝ) {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℂ => ∫ x in Set.Ioi (0 : ℝ),
        realPlaceLogDifference (n+1) p.1 p.2 x)
      (fun p : ℂ × ℂ => ∫ x in Set.Ioi (0 : ℝ), realPlaceLogLimit p.1 p.2 x)
      Filter.atTop {p | (‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R) ∧ (σ ≤ p.1.re ∧ σ ≤ p.2.re)} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Filter.Tendsto
      (fun n => cutoffErrorMass n * (Real.exp (1/2) * Real.exp R * (2*R)) + tailErrorMass σ n)
      Filter.atTop (nhds 0) := by
    simpa using (cutoffErrorMass_tendsto.mul_const
      (Real.exp (1/2) * Real.exp R * (2*R))).add (tailErrorMass_tendsto hσ)
  filter_upwards [Filter.Tendsto.eventually_lt_const hε ht] with n hn
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (realPlaceLogDifference_full_error_bound n hσ hp.1.1 hp.1.2 hp.2.1 hp.2.2).trans_lt hn

#check realPlaceLog_full_integrable
#print axioms realPlaceLog_full_integrable
#check positiveIntegral_split
#print axioms positiveIntegral_split
#check realPlaceLogDifference_full_error_bound
#print axioms realPlaceLogDifference_full_error_bound
#check realPlaceLogDifference_full_tendstoUniformlyOn
#print axioms realPlaceLogDifference_full_tendstoUniformlyOn

/-- Round 8: the parameter derivative needed to justify differentiating the
positive real-place difference integral. This does not assert an integral
interchange or supply any spectral premise. -/
noncomputable def realPlaceLogDerivative (z : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) * (-(x : ℂ) * Complex.exp (-z * (x : ℂ))) /
    (Real.exp x - 1 : ℝ)

/-- Discharges the pointwise derivative premise left unproved by the failed
last r07 submission; totalized division also makes the formula valid at x=0. -/
theorem realPlaceLogLimit_hasDerivAt (z w : ℂ) (x : ℝ) :
    HasDerivAt (fun v : ℂ => realPlaceLogLimit v w x)
      (realPlaceLogDerivative z x) z := by
  unfold realPlaceLogLimit realPlaceLogDerivative
  have h := (((hasDerivAt_id z).neg.mul_const (x : ℂ)).cexp.sub_const
    (Complex.exp (-w * (x : ℂ)))).const_mul (Real.exp (x/2) : ℂ)
  simp only [Pi.neg_apply, id_eq] at h
  convert h.div_const (Real.exp x - 1 : ℝ) using 1
  ring

/-- Exact norm formula used only to discharge the derivative domination
premise of parameter differentiation for the same positive real-place density. -/
theorem realPlaceLogDerivative_norm (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖realPlaceLogDerivative z x‖ =
      Real.exp (x/2) * x * Real.exp (-z.re*x) / (Real.exp x - 1) := by
  have hd : 0 < Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  simp only [realPlaceLogDerivative, norm_div, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero,
    abs_of_pos hx, abs_of_pos (Real.exp_pos (x/2)), abs_of_pos hd]
  ring

/-- Discharges cutoff-independent derivative domination at norm one on
every bounded complex parameter set, without zero information. -/
theorem realPlaceLogDerivative_near_bound {z : ℂ} {R x : ℝ}
    (hz : ‖z‖ ≤ R) (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖realPlaceLogDerivative z x‖ ≤ Real.exp (1/2) * Real.exp R := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have hr : -z.re ≤ R := by
    simpa using (Complex.re_le_norm (-z)).trans (by simpa using hz)
  have he : Real.exp (-z.re*x) ≤ Real.exp R := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right hr hx.le).trans
      (mul_le_of_le_one_right hR hx1)
  have hf : Real.exp (x/2) ≤ Real.exp (1/2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hd : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  rw [realPlaceLogDerivative_norm z hx]
  apply (div_le_iff₀ (hx.trans_le hd)).2
  calc
    Real.exp (x/2) * x * Real.exp (-z.re*x) =
        (Real.exp (x/2) * Real.exp (-z.re*x)) * x := by ring
    _ ≤ (Real.exp (1/2) * Real.exp R) * x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hf he (Real.exp_pos _).le (Real.exp_pos _).le) hx.le
    _ ≤ (Real.exp (1/2) * Real.exp R) * (Real.exp x - 1) :=
      mul_le_mul_of_nonneg_left hd (by positivity)

/-- Discharges the derivative tail domination premise, uniformly on any
half-plane. The majorant is integrable when sigma > -1/2; its integral
interchange is not assumed by this pointwise estimate. -/
theorem realPlaceLogDerivative_tail_bound {z : ℂ} {σ x : ℝ}
    (hz : σ ≤ z.re) (hx : 1 ≤ x) :
    ‖realPlaceLogDerivative z x‖ ≤
      2*x*Real.exp (-(σ+1/2)*x) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have he : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hd : 0 < Real.exp x - 1 := by linarith
  have hn : Real.exp (-z.re*x) ≤ Real.exp (-σ*x) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [realPlaceLogDerivative_norm z hx0]
  apply (div_le_iff₀ hd).2
  calc
    Real.exp (x/2) * x * Real.exp (-z.re*x) ≤
        Real.exp (x/2) * x * Real.exp (-σ*x) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = x * Real.exp (x/2 + -σ*x) := by rw [Real.exp_add]; ring
    _ = x * Real.exp (-(σ+1/2)*x + x) := by congr 2; ring
    _ = (x * Real.exp (-(σ+1/2)*x)) * Real.exp x := by
      rw [Real.exp_add]; ring
    _ ≤ (x * Real.exp (-(σ+1/2)*x)) * (2 * (Real.exp x - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (2*x*Real.exp (-(σ+1/2)*x)) * (Real.exp x - 1) := by ring

#check realPlaceLogLimit_hasDerivAt
#print axioms realPlaceLogLimit_hasDerivAt
#check realPlaceLogDerivative_norm
#print axioms realPlaceLogDerivative_norm
#check realPlaceLogDerivative_near_bound
#print axioms realPlaceLogDerivative_near_bound
#check realPlaceLogDerivative_tail_bound
#print axioms realPlaceLogDerivative_tail_bound
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
open scoped Topology

/-- Round 9: an explicit integrable bound for the parameter derivative of
our actual positive real-place difference density. It discharges precisely
the domination premise for differentiation under the integral in §1.4.3. -/
noncomputable def realDerivativeMajorant (R σ x : ℝ) : ℝ :=
  (Real.exp (1/2) * Real.exp R * Real.exp 1) * Real.exp (-x) +
    (4 / (σ+1/2)) * Real.exp (-((σ+1/2)/2)*x)

/-- The derivative majorant is integrable without any spectral hypothesis. -/
theorem realDerivativeMajorant_integrable (R : ℝ) {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) :
    IntegrableOn (realDerivativeMajorant R σ) (Set.Ioi (0 : ℝ)) := by
  have h₁ : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi (0 : ℝ)) := by
    simpa using (integrableOn_exp_mul_Ioi (a := -(1 : ℝ)) (by norm_num) (0 : ℝ))
  have h₂ : IntegrableOn (fun x : ℝ => Real.exp (-((σ+1/2)/2)*x))
      (Set.Ioi (0 : ℝ)) := by
    apply integrableOn_exp_mul_Ioi
    linarith
  exact (h₁.const_mul _).add (h₂.const_mul _)

/-- Discharges the local uniform domination of the parameter derivative,
with explicit bounded-parameter and right-half-plane margins. -/
theorem realPlaceLogDerivative_majorized {R σ x : ℝ} {z : ℂ}
    (hσ : -(1/2 : ℝ) < σ) (hzR : ‖z‖ ≤ R) (hz : σ ≤ z.re) (hx : 0 < x) :
    ‖realPlaceLogDerivative z x‖ ≤ realDerivativeMajorant R σ x := by
  have hb : 0 < σ+1/2 := by linarith
  have ht : 0 ≤ (4 / (σ+1/2)) * Real.exp (-((σ+1/2)/2)*x) := by positivity
  have hn : 0 ≤ (Real.exp (1/2) * Real.exp R * Real.exp 1) * Real.exp (-x) := by positivity
  unfold realDerivativeMajorant
  by_cases hx1 : x ≤ 1
  · have he : 1 ≤ Real.exp 1 * Real.exp (-x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hh := realPlaceLogDerivative_near_bound hzR hx hx1
    calc
      _ ≤ Real.exp (1/2) * Real.exp R := hh
      _ ≤ (Real.exp (1/2) * Real.exp R * Real.exp 1) * Real.exp (-x) := by
        nlinarith [mul_le_mul_of_nonneg_left he
          (show 0 ≤ Real.exp (1/2) * Real.exp R by positivity)]
      _ ≤ _ := le_add_of_nonneg_right ht
  · have hh := realPlaceLogDerivative_tail_bound hz (le_of_not_ge hx1)
    have he : ((σ+1/2)/2)*x ≤ Real.exp (((σ+1/2)/2)*x) := by
      linarith [Real.add_one_le_exp (((σ+1/2)/2)*x)]
    have hc : 2*x ≤ (4/(σ+1/2)) * Real.exp (((σ+1/2)/2)*x) := by
      calc
        2*x ≤ (4 * Real.exp (((σ+1/2)/2)*x)) / (σ+1/2) :=
          (le_div_iff₀ hb).2 (by nlinarith)
        _ = _ := by ring
    have hd : 2*x*Real.exp (-(σ+1/2)*x) ≤
        (4/(σ+1/2))*Real.exp (-((σ+1/2)/2)*x) := by
      calc
        _ ≤ ((4/(σ+1/2))*Real.exp (((σ+1/2)/2)*x)) *
            Real.exp (-(σ+1/2)*x) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
        _ = _ := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
    exact hh.trans (hd.trans (le_add_of_nonneg_left hn))

#check realDerivativeMajorant_integrable
#print axioms realDerivativeMajorant_integrable
#check realPlaceLogDerivative_majorized
#print axioms realPlaceLogDerivative_majorized
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
open scoped Topology

/-- Supplies derivative measurability for the same parameter-integral
interchange; division is totalized at the excluded endpoint x=0. -/
theorem realPlaceLogDerivative_measurable (z : ℂ) :
    Measurable (realPlaceLogDerivative z) := by
  unfold realPlaceLogDerivative
  fun_prop

/-- Round 9 export: discharges differentiation under the WHOLE positive
real-place difference integral, on the exact half-plane Re(z)>-1/2,
with a fixed base parameter Re(w)>-1/2. All domination is derived above;
no trace formula, spectral sum, continuation or zero-free region is assumed. -/
theorem realPlaceLogIntegral_hasDerivAt {z w : ℂ}
    (hz : -(1/2 : ℝ) < z.re) (hw : -(1/2 : ℝ) < w.re) :
    IntegrableOn (realPlaceLogDerivative z) (Set.Ioi (0 : ℝ)) ∧
    HasDerivAt (fun v : ℂ => ∫ x in Set.Ioi (0 : ℝ), realPlaceLogLimit v w x)
      (∫ x in Set.Ioi (0 : ℝ), realPlaceLogDerivative z x) z := by
  obtain ⟨σ, hσ, hσm⟩ := exists_between (lt_min hz hw)
  have hσz : σ < z.re := hσm.trans_le (min_le_left _ _)
  have hσw : σ < w.re := hσm.trans_le (min_le_right _ _)
  let s : Set ℂ := {v | ‖v‖ < ‖z‖+1 ∧ σ < v.re}
  have hs : s ∈ 𝓝 z := by
    apply Filter.inter_mem
    · exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp; linarith)
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσz
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (bound := realDerivativeMajorant (‖z‖+1) σ) hs
  · exact Filter.Eventually.of_forall (fun v =>
      (realPlaceLogLimit_measurable v w).aestronglyMeasurable)
  · exact (realPlaceLog_full_integrable 1 hσ hσz.le hσw.le).2
  · exact (realPlaceLogDerivative_measurable z).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro v hv
    exact realPlaceLogDerivative_majorized hσ hv.1.le hv.2.le hx
  · exact realDerivativeMajorant_integrable _ hσ
  · exact Filter.Eventually.of_forall (fun x v _ => realPlaceLogLimit_hasDerivAt v w x)

/-- Discharges holomorphy of this scalar limiting local integral, the
positive-real branch only of the manuscript's archimedean premise. -/
theorem realPlaceLogIntegral_differentiableOn {w : ℂ}
    (hw : -(1/2 : ℝ) < w.re) :
    DifferentiableOn ℂ
      (fun v : ℂ => ∫ x in Set.Ioi (0 : ℝ), realPlaceLogLimit v w x)
      {z : ℂ | -(1/2 : ℝ) < z.re} := by
  intro z hz
  exact (realPlaceLogIntegral_hasDerivAt hz hw).2.differentiableAt.differentiableWithinAt

#check realPlaceLogDerivative_measurable
#print axioms realPlaceLogDerivative_measurable
#check realPlaceLogIntegral_hasDerivAt
#print axioms realPlaceLogIntegral_hasDerivAt
#check realPlaceLogIntegral_differentiableOn
#print axioms realPlaceLogIntegral_differentiableOn
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
open scoped Topology

/-! Round 10: the negative real-place branch u=-1 in §1.4.3, after
x=log(t)>0. The denominator is |1+t|=exp(x)+1. These are the actual
scalar difference densities; character factors and Haar constants still
require arithmetic attachment. Each lemma supplies the domination or
parameter-differentiation premise for this remaining real local branch. -/
noncomputable def realPlaceNegLogLimit (z w : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) *
    (Complex.exp (-z * (x : ℂ)) - Complex.exp (-w * (x : ℂ))) /
      (Real.exp x + 1 : ℝ)

noncomputable def realPlaceNegLogDerivative (z : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x/2) : ℂ) * (-(x : ℂ) * Complex.exp (-z * (x : ℂ))) /
    (Real.exp x + 1 : ℝ)

/-- Supplies domination of the negative-branch denominator by the already
checked positive branch, for exactly the integration domain x>0. -/
theorem realPlaceNeg_denominator_bound (a : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖a / ((Real.exp x + 1 : ℝ) : ℂ)‖ ≤
      ‖a / ((Real.exp x - 1 : ℝ) : ℂ)‖ := by
  have hm : 0 < Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  have hp : 0 < Real.exp x + 1 := by positivity
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hp, abs_of_pos hm]
  exact div_le_div_of_nonneg_left (norm_nonneg a) hm (by linarith)

/-- Supplies pointwise derivative, with the exact negative-branch density. -/
theorem realPlaceNegLogLimit_hasDerivAt (z w : ℂ) (x : ℝ) :
    HasDerivAt (fun v : ℂ => realPlaceNegLogLimit v w x)
      (realPlaceNegLogDerivative z x) z := by
  unfold realPlaceNegLogLimit realPlaceNegLogDerivative
  have h := (((hasDerivAt_id z).neg.mul_const (x : ℂ)).cexp.sub_const
    (Complex.exp (-w * (x : ℂ)))).const_mul (Real.exp (x/2) : ℂ)
  simp only [Pi.neg_apply, id_eq] at h
  convert h.div_const (Real.exp x + 1 : ℝ) using 1
  ring

/-- Supplies absolute integrability for the negative real-place branch;
no zero data, trace formula, or assumed summability enters. -/
theorem realPlaceNegLogLimit_integrable {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    IntegrableOn (realPlaceNegLogLimit z w) (Set.Ioi (0 : ℝ)) := by
  have hm : Measurable (realPlaceNegLogLimit z w) := by
    unfold realPlaceNegLogLimit
    fun_prop
  apply (realPlaceLog_full_integrable 1 hσ hz hw).2.norm.mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact realPlaceNeg_denominator_bound _ hx

/-- Supplies the same explicit integrable local uniform derivative bound
as the positive branch, uniformly for bounded parameters with a half-plane
margin sigma>-1/2. -/
theorem realPlaceNegLogDerivative_majorized {R σ x : ℝ} {z : ℂ}
    (hσ : -(1/2 : ℝ) < σ) (hzR : ‖z‖ ≤ R) (hz : σ ≤ z.re) (hx : 0 < x) :
    ‖realPlaceNegLogDerivative z x‖ ≤ realDerivativeMajorant R σ x := by
  exact (realPlaceNeg_denominator_bound _ hx).trans
    (realPlaceLogDerivative_majorized hσ hzR hz hx)

/-- Discharges differentiation under the full negative-real local integral.
The majorant is derived explicitly; the only hypotheses are the actual
scalar parameter inequalities Re(z),Re(w)>-1/2. -/
theorem realPlaceNegLogIntegral_hasDerivAt {z w : ℂ}
    (hz : -(1/2 : ℝ) < z.re) (hw : -(1/2 : ℝ) < w.re) :
    IntegrableOn (realPlaceNegLogDerivative z) (Set.Ioi (0 : ℝ)) ∧
    HasDerivAt (fun v : ℂ => ∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogLimit v w x)
      (∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogDerivative z x) z := by
  obtain ⟨σ, hσ, hσm⟩ := exists_between (lt_min hz hw)
  have hσz : σ < z.re := hσm.trans_le (min_le_left _ _)
  have hσw : σ < w.re := hσm.trans_le (min_le_right _ _)
  let s : Set ℂ := {v | ‖v‖ < ‖z‖+1 ∧ σ < v.re}
  have hs : s ∈ 𝓝 z := by
    apply Filter.inter_mem
    · exact (isOpen_lt continuous_norm continuous_const).mem_nhds (by dsimp; linarith)
    · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσz
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    (bound := realDerivativeMajorant (‖z‖+1) σ) hs
  · apply Filter.Eventually.of_forall
    intro v
    have hm : Measurable (realPlaceNegLogLimit v w) := by
      unfold realPlaceNegLogLimit
      fun_prop
    exact hm.aestronglyMeasurable
  · exact realPlaceNegLogLimit_integrable hσ hσz.le hσw.le
  · have hm : Measurable (realPlaceNegLogDerivative z) := by
      unfold realPlaceNegLogDerivative
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro v hv
    exact realPlaceNegLogDerivative_majorized hσ hv.1.le hv.2.le hx
  · exact realDerivativeMajorant_integrable _ hσ
  · exact Filter.Eventually.of_forall (fun x v _ => realPlaceNegLogLimit_hasDerivAt v w x)

/-- Round 10 export: supplies holomorphy of the limiting negative-real local
branch. Together with the reused positive branch this covers the two scalar
real denominators, but not their genuine character/Haar attachment. -/
theorem realPlaceNegLogIntegral_differentiableOn {w : ℂ}
    (hw : -(1/2 : ℝ) < w.re) :
    DifferentiableOn ℂ
      (fun v : ℂ => ∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogLimit v w x)
      {z : ℂ | -(1/2 : ℝ) < z.re} := by
  intro z hz
  exact (realPlaceNegLogIntegral_hasDerivAt hz hw).2.differentiableAt.differentiableWithinAt

#check realPlaceNeg_denominator_bound
#print axioms realPlaceNeg_denominator_bound
#check realPlaceNegLogLimit_hasDerivAt
#print axioms realPlaceNegLogLimit_hasDerivAt
#check realPlaceNegLogLimit_integrable
#print axioms realPlaceNegLogLimit_integrable
#check realPlaceNegLogDerivative_majorized
#print axioms realPlaceNegLogDerivative_majorized
#check realPlaceNegLogIntegral_hasDerivAt
#print axioms realPlaceNegLogIntegral_hasDerivAt
#check realPlaceNegLogIntegral_differentiableOn
#print axioms realPlaceNegLogIntegral_differentiableOn
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
open scoped Topology

/-- The same smooth one-sided test inserted in the u=-1 real-place branch. -/
noncomputable def realPlaceNegLogDifference (N : ℝ) (z w : ℂ) (x : ℝ) : ℂ :=
  (logCutoff N x : ℂ) * realPlaceNegLogLimit z w x

/-- Identifies the cutoff integrand with the actual scalar test logTest and
the negative-real trace denominator; this is not a substituted operator. -/
theorem realPlaceNegLogDifference_eq (N : ℝ) (z w : ℂ) (x : ℝ) :
    realPlaceNegLogDifference N z w x =
      (Real.exp (x/2) : ℂ) * logTest N z w x / (Real.exp x + 1 : ℝ) := by
  unfold realPlaceNegLogDifference realPlaceNegLogLimit logTest
  ring

/-- Supplies the measurable cutoff integrands required for dominated
convergence of this specific local trace branch. -/
theorem realPlaceNegLogDifference_measurable (N : ℝ) (z w : ℂ) :
    Measurable (realPlaceNegLogDifference N z w) := by
  have hh : Measurable (fun x : ℝ => (logCutoff N x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (logCutoff_smooth N).continuous.measurable
  have hl : Measurable (realPlaceNegLogLimit z w) := by
    unfold realPlaceNegLogLimit
    fun_prop
  exact hh.mul hl

/-- Discharges uniform-in-cutoff domination by the uncut integrable density. -/
theorem realPlaceNegLogDifference_norm_le (N : ℝ) (z w : ℂ) (x : ℝ) :
    ‖realPlaceNegLogDifference N z w x‖ ≤ ‖realPlaceNegLogLimit z w x‖ := by
  rw [realPlaceNegLogDifference, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (logCutoff_bounds N x).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (logCutoff_bounds N x).2

/-- Discharges absolute integrability of each finite negative-real trace
integrand. Its actual test has the previously proved smooth support. -/
theorem realPlaceNegLogDifference_integrable (N : ℝ) {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    IntegrableOn (realPlaceNegLogDifference N z w) (Set.Ioi (0 : ℝ)) := by
  apply (realPlaceNegLogLimit_integrable hσ hz hw).norm.mono'
    (realPlaceNegLogDifference_measurable N z w).aestronglyMeasurable
  exact Filter.Eventually.of_forall (realPlaceNegLogDifference_norm_le N z w)

/-- Round 10 second export: discharges the full negative-real cutoff/integral
limit for every fixed parameter pair Re(z),Re(w)>-1/2. This is full-sequence
convergence, not yet a locally uniform convergence theorem. -/
theorem realPlaceNegLogDifference_integral_tendsto {z w : ℂ}
    (hz : -(1/2 : ℝ) < z.re) (hw : -(1/2 : ℝ) < w.re) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x in Set.Ioi (0 : ℝ),
        realPlaceNegLogDifference (n+1) z w x)
      Filter.atTop
      (nhds (∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogLimit z w x)) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x => ‖realPlaceNegLogLimit z w x‖)
  · intro n
    exact (realPlaceNegLogDifference_measurable (n+1) z w).aestronglyMeasurable
  · exact (realPlaceNegLogLimit_integrable (lt_min hz hw)
      (min_le_left _ _) (min_le_right _ _)).norm
  · intro n
    exact Filter.Eventually.of_forall (realPlaceNegLogDifference_norm_le (n+1) z w)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [logCutoff_eventually_one hx] with n hn
    simp [realPlaceNegLogDifference, hn]

#check realPlaceNegLogDifference_eq
#print axioms realPlaceNegLogDifference_eq
#check realPlaceNegLogDifference_measurable
#print axioms realPlaceNegLogDifference_measurable
#check realPlaceNegLogDifference_norm_le
#print axioms realPlaceNegLogDifference_norm_le
#check realPlaceNegLogDifference_integrable
#print axioms realPlaceNegLogDifference_integrable
#check realPlaceNegLogDifference_integral_tendsto
#print axioms realPlaceNegLogDifference_integral_tendsto
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
open scoped Topology

/-- Round 11: discharges comparison of the actual negative-real cutoff
error with the already controlled positive-real error in §1.4.3. -/
theorem realPlaceNegLogDifference_error_le (N : ℝ) (z w : ℂ) {x : ℝ}
    (hx : 0 < x) :
    ‖realPlaceNegLogDifference N z w x - realPlaceNegLogLimit z w x‖ ≤
      ‖realPlaceLogDifference N z w x - realPlaceLogLimit z w x‖ := by
  have he : realPlaceNegLogDifference N z w x - realPlaceNegLogLimit z w x =
      ((logCutoff N x - 1 : ℝ) : ℂ) * realPlaceNegLogLimit z w x := by
    unfold realPlaceNegLogDifference
    push_cast
    ring
  rw [he, realPlaceLogDifference_error_factor, norm_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (realPlaceNeg_denominator_bound _ hx) (norm_nonneg _)

/-- Supplies absolute integrability on the two pieces used to control the
negative-real cutoff error; these hypotheses justify integral subtraction. -/
theorem realPlaceNegLog_integrable_pieces (N : ℝ) {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    (IntegrableOn (realPlaceNegLogDifference N z w) (Set.Ioc (0 : ℝ) 1) ∧
      IntegrableOn (realPlaceNegLogLimit z w) (Set.Ioc (0 : ℝ) 1)) ∧
    (IntegrableOn (realPlaceNegLogDifference N z w) (Set.Ioi (1 : ℝ)) ∧
      IntegrableOn (realPlaceNegLogLimit z w) (Set.Ioi (1 : ℝ))) := by
  have hi := realPlaceNegLogDifference_integrable N hσ hz hw
  have hj := realPlaceNegLogLimit_integrable hσ hz hw
  have hn : Set.Ioc (0 : ℝ) 1 ⊆ Set.Ioi 0 := fun _ hx => hx.1
  have ht : Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := by
    intro x hx
    change 1 < x at hx
    change 0 < x
    linarith
  exact ⟨⟨hi.mono_set hn, hj.mono_set hn⟩, ⟨hi.mono_set ht, hj.mono_set ht⟩⟩

/-- Discharges a uniform near-identity error bound for the negative-real
integral, with the same vanishing scalar error mass as the positive branch. -/
theorem realPlaceNegLogDifference_near_error_bound (n : ℕ) {z w : ℂ} {R σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hzR : ‖z‖ ≤ R) (hwR : ‖w‖ ≤ R)
    (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    ‖(∫ x in Set.Ioc (0 : ℝ) 1, realPlaceNegLogDifference (n+1) z w x) -
      (∫ x in Set.Ioc (0 : ℝ) 1, realPlaceNegLogLimit z w x)‖ ≤
      cutoffErrorMass n * (Real.exp (1/2) * Real.exp R * (2*R)) := by
  obtain ⟨⟨hi,hj⟩,_⟩ := realPlaceNegLog_integrable_pieces (n+1) hσ hz hw
  rw [← integral_sub hi hj]
  have h := norm_integral_le_of_norm_le
    ((logCutoff_error_integrable (n+1)).mul_const
      (Real.exp (1/2) * Real.exp R * (2*R))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact (realPlaceNegLogDifference_error_le (n+1) z w hx.1).trans
        (realPlaceLogDifference_error_bound (n+1) hzR hwR hx.1 hx.2))
  simpa only [integral_mul_const, cutoffErrorMass] using h

/-- Discharges the uniform negative-real tail error bound with a derived
integrable exponential majorant, independent of zero data. -/
theorem realPlaceNegLogDifference_tail_error_bound (n : ℕ) {z w : ℂ} {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    ‖(∫ x in Set.Ioi (1 : ℝ), realPlaceNegLogDifference (n+1) z w x) -
      (∫ x in Set.Ioi (1 : ℝ), realPlaceNegLogLimit z w x)‖ ≤ tailErrorMass σ n := by
  obtain ⟨_,⟨hi,hj⟩⟩ := realPlaceNegLog_integrable_pieces (n+1) hσ hz hw
  rw [← integral_sub hi hj]
  apply norm_integral_le_of_norm_le (tailError_integrable hσ (n+1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply (realPlaceNegLogDifference_error_le (n+1) z w (lt_trans zero_lt_one hx)).trans
  rw [realPlaceLogDifference_error_factor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (logCutoff_bounds (n+1) x).2)]
  simpa only [neg_sub] using mul_le_mul_of_nonneg_left
    (realPlaceLogLimit_tail_bound hz hw hx.le)
    (sub_nonneg.mpr (logCutoff_bounds (n+1) x).2)

/-- Discharges the full uniform cutoff-error estimate for the actual
negative-real scalar branch needed by the §1.4.3 limit argument. -/
theorem realPlaceNegLogDifference_full_error_bound (n : ℕ) {z w : ℂ} {R σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) (hzR : ‖z‖ ≤ R) (hwR : ‖w‖ ≤ R)
    (hz : σ ≤ z.re) (hw : σ ≤ w.re) :
    ‖(∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogDifference (n+1) z w x) -
      (∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogLimit z w x)‖ ≤
      cutoffErrorMass n * (Real.exp (1/2) * Real.exp R * (2*R)) + tailErrorMass σ n := by
  obtain ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ := realPlaceNegLog_integrable_pieces (n+1) hσ hz hw
  rw [positiveIntegral_split _ ha hc, positiveIntegral_split _ hb hd]
  have he := realPlaceNegLogDifference_near_error_bound n hσ hzR hwR hz hw
  have hf := realPlaceNegLogDifference_tail_error_bound n hσ hz hw
  calc
    _ = ‖((∫ x in Set.Ioc (0 : ℝ) 1, realPlaceNegLogDifference (n+1) z w x) -
        (∫ x in Set.Ioc (0 : ℝ) 1, realPlaceNegLogLimit z w x)) +
        ((∫ x in Set.Ioi (1 : ℝ), realPlaceNegLogDifference (n+1) z w x) -
        (∫ x in Set.Ioi (1 : ℝ), realPlaceNegLogLimit z w x))‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he hf)

/-- Round 11 export. Discharges full-sequence uniform convergence of the
negative-real difference integrals on every bounded pair of parameter sets
with Re(z),Re(w)>=sigma>-1/2. No trace identity, spectral sum or desired
zero-free region is assumed. Genuine character/Haar attachment is separate. -/
theorem realPlaceNegLogDifference_full_tendstoUniformlyOn (R : ℝ) {σ : ℝ}
    (hσ : -(1/2 : ℝ) < σ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℂ × ℂ => ∫ x in Set.Ioi (0 : ℝ),
        realPlaceNegLogDifference (n+1) p.1 p.2 x)
      (fun p : ℂ × ℂ => ∫ x in Set.Ioi (0 : ℝ), realPlaceNegLogLimit p.1 p.2 x)
      Filter.atTop {p | (‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R) ∧ (σ ≤ p.1.re ∧ σ ≤ p.2.re)} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Filter.Tendsto
      (fun n => cutoffErrorMass n * (Real.exp (1/2) * Real.exp R * (2*R)) + tailErrorMass σ n)
      Filter.atTop (nhds 0) := by
    simpa using (cutoffErrorMass_tendsto.mul_const
      (Real.exp (1/2) * Real.exp R * (2*R))).add (tailErrorMass_tendsto hσ)
  filter_upwards [Filter.Tendsto.eventually_lt_const hε ht] with n hn
  intro p hp
  rw [dist_comm, dist_eq_norm]
  exact (realPlaceNegLogDifference_full_error_bound n hσ hp.1.1 hp.1.2 hp.2.1 hp.2.2).trans_lt hn

#check realPlaceNegLogDifference_error_le
#print axioms realPlaceNegLogDifference_error_le
#check realPlaceNegLogDifference_full_error_bound
#print axioms realPlaceNegLogDifference_full_error_bound
#check realPlaceNegLogDifference_full_tendstoUniformlyOn
#print axioms realPlaceNegLogDifference_full_tendstoUniformlyOn
end CriticalLineAudit
