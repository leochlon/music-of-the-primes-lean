import Mathlib
set_option linter.unnecessarySeqFocus false

/-!
Round 184 D. The new arithmetic step in GLOBAL_ESTIMATE.md bounds the
archimedean logarithmic derivative uniformly in the ACTUAL character lattice.
This lemma is the real digamma-series tail estimate used there. It assumes
neither a zero sum nor nuclearity. The native resolvent-energy theorem is
reused from preserved/Checked182D.lean, not recompiled. The complete global
analytic derivation and its remaining native attachment are in the document.
-/
namespace Round184D

/-- For z = x + i*y with x >= 1, this bounds the real part of the
n-th digamma summand, with t = n+1. Summing beyond t > x+|y| gives a
uniform tail bound, leaving only a logarithmic harmonic head. -/
theorem digamma_real_tail_majorant (t x y : ℝ) (ht : 0 < t) (hx : 1 ≤ x) :
    1 / t - (t + x - 1) / ((t + x - 1)^2 + y^2) ≤
      (x - 1) / t^2 + y^2 / t^3 := by
  let d := t + x - 1
  have hd : t ≤ d := by dsimp [d]; linarith
  have hdp : 0 < d := lt_of_lt_of_le ht hd
  have hp : 0 < d^2 + y^2 := by positivity
  have hid : 1 / t - d / (d^2 + y^2) =
      (x - 1) / (t*d) + y^2 / (d*(d^2+y^2)) := by
    field_simp
    dsimp [d]
    ring
  change 1 / t - d / (d^2 + y^2) ≤ _
  rw [hid]
  apply add_le_add
  · apply div_le_div_of_nonneg_left (sub_nonneg.mpr hx) (sq_pos_of_pos ht)
    nlinarith
  · apply div_le_div_of_nonneg_left (sq_nonneg y) (pow_pos ht 3)
    calc
      t^3 = t * t^2 := by ring
      _ ≤ d * d^2 := by gcongr
      _ ≤ d * (d^2 + y^2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg y)) hdp.le

#check digamma_real_tail_majorant
#print axioms digamma_real_tail_majorant
end Round184D

/-! D187: the actual divided translation orbit used in the native
meromorphic resolvent has a derivative without assuming a differentiable
input orbit. This discharges the finite-interval generator-domain step. -/
noncomputable section
set_option linter.unusedSimpArgs false
open MeasureTheory
namespace Round187D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

def weightedPrimitive (f : ℝ → E) (z : ℂ) (t : ℝ) : E :=
  ∫ v in (0 : ℝ)..t, Complex.exp (-z * (v : ℂ)) • f v

theorem divided_orbit_hasDerivAt (f : ℝ → E) (hf : Continuous f)
    (z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (z * ((t+s : ℝ) : ℂ)) •
      (weightedPrimitive f z (t+s) - weightedPrimitive f z s))
      (z • (Complex.exp (z * (t : ℂ)) • weightedPrimitive f z t) +
        f t - Complex.exp (z * (t : ℂ)) • f 0) 0 := by
  let g : ℝ → E := fun v => Complex.exp (-z * (v : ℂ)) • f v
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hp (b : ℝ) : HasDerivAt (weightedPrimitive f z) (g b) b := by
    exact intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 b) hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have ht : HasDerivAt (fun s : ℝ => weightedPrimitive f z (t+s)) (g t) 0 := by
    have hp' : HasDerivAt (weightedPrimitive f z) (g t) (t + id (0 : ℝ)) := by simpa using hp t
    simpa using hp'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t)
  have hc : HasDerivAt (fun s : ℝ => Complex.exp (z * ((t+s : ℝ) : ℂ)))
      (Complex.exp (z * (t : ℂ)) * z) 0 := by
    simpa using (((Complex.ofRealCLM.hasDerivAt).scomp 0
      ((hasDerivAt_id (0 : ℝ)).const_add t)).const_mul z).cexp
  have hh := hc.smul (ht.sub (hp 0))
  convert hh using 1
  simp only [Pi.smul_apply, Pi.sub_apply, add_zero, weightedPrimitive, intervalIntegral.integral_same,
    sub_zero, g, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul]
  simp only [smul_sub, smul_smul, ← Complex.exp_add]
  have he : z * (t : ℂ) + -z * (t : ℂ) = 0 := by ring
  rw [he, Complex.exp_zero, one_smul]
  rw [mul_comm z (Complex.exp (z * (t : ℂ)))]
  abel

#check divided_orbit_hasDerivAt
#print axioms divided_orbit_hasDerivAt


omit [CompleteSpace E] in
theorem translated_divided_integral (f : ℝ → E) (hf : Continuous f)
    (z : ℂ) (t s : ℝ) :
    (∫ v in (0 : ℝ)..t, Complex.exp (z * ((t-v : ℝ) : ℂ)) • f (v+s)) =
    Complex.exp (z * ((t+s : ℝ) : ℂ)) •
      (weightedPrimitive f z (t+s) - weightedPrimitive f z s) := by
  let g : ℝ → E := fun v => Complex.exp (-z * (v : ℂ)) • f v
  have hg : Continuous g := by dsimp [g]; fun_prop
  calc
    _ = ∫ v in (0 : ℝ)..t, Complex.exp (z * ((t+s : ℝ) : ℂ)) • g (v+s) := by
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp [g]
      rw [smul_smul, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = Complex.exp (z * ((t+s : ℝ) : ℂ)) • (∫ v in (0 : ℝ)..t, g (v+s)) :=
      intervalIntegral.integral_smul _ _
    _ = Complex.exp (z * ((t+s : ℝ) : ℂ)) • (∫ v in s..t+s, g v) := by
      rw [intervalIntegral.integral_comp_add_right]
      simp only [zero_add]
    _ = _ := by
      change _ = Complex.exp (z * ((t+s : ℝ) : ℂ)) •
        ((∫ v in (0 : ℝ)..t+s, g v) - ∫ v in (0 : ℝ)..s, g v)
      rw [intervalIntegral.integral_interval_sub_left
        (hg.intervalIntegrable 0 (t+s)) (hg.intervalIntegrable 0 s)]

#check translated_divided_integral
#print axioms translated_divided_integral
end Round187D

/-! D188: discharge the actual group-orbit domain step, rather than
assuming the divided convolution is already in the generator domain. -/
namespace Round188D
open Round187D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

def dividedGroupOrbit (U : ℝ → E →L[ℂ] E) (z : ℂ) (t : ℝ) (x : E) : E :=
  ∫ v in (0 : ℝ)..t, Complex.exp (z * ((t-v : ℝ) : ℂ)) • U v x

theorem dividedGroupOrbit_generator_domain
    (U : ℝ → E →L[ℂ] E)
    (hzero : ∀ x, U 0 x = x)
    (hgroup : ∀ s v x, U s (U v x) = U (v+s) x)
    (hcont : ∀ x, Continuous (fun v => U v x))
    (z : ℂ) (t : ℝ) (x : E) :
    HasDerivAt (fun s : ℝ => U s (dividedGroupOrbit U z t x))
      (z • dividedGroupOrbit U z t x + U t x -
        Complex.exp (z * (t : ℂ)) • x) 0 := by
  have hi : IntervalIntegrable
      (fun v : ℝ => Complex.exp (z * ((t-v : ℝ) : ℂ)) • U v x)
      volume 0 t := by
    apply Continuous.intervalIntegrable
    exact (by fun_prop : Continuous (fun v : ℝ =>
      Complex.exp (z * ((t-v : ℝ) : ℂ)))).smul (hcont x)
  have he (s : ℝ) : U s (dividedGroupOrbit U z t x) =
      Complex.exp (z * ((t+s : ℝ) : ℂ)) •
        (weightedPrimitive (fun v => U v x) z (t+s) -
          weightedPrimitive (fun v => U v x) z s) := by
    unfold dividedGroupOrbit
    rw [← (U s).intervalIntegral_comp_comm hi]
    simp_rw [map_smul, hgroup]
    exact translated_divided_integral (fun v => U v x) (hcont x) z t s
  have hq : dividedGroupOrbit U z t x =
      Complex.exp (z * (t : ℂ)) •
        weightedPrimitive (fun v => U v x) z t := by
    simpa [hzero, weightedPrimitive] using he 0
  simpa only [← he, ← hq, hzero] using
    divided_orbit_hasDerivAt (fun v => U v x) (hcont x) z t

#check dividedGroupOrbit_generator_domain
#print axioms dividedGroupOrbit_generator_domain
end Round188D

/-! C191. The FULL seed average is in the generator domain. The two
integrability hypotheses concern actual seed vectors and their graph
components; GLOBAL_ESTIMATE.md derives both from native theta moments.
Neither spectral summability nor nuclearity is assumed. -/
namespace Round191C
open MeasureTheory Filter Round188D
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem integrated_seed_generator_domain
    (U : ℝ → E →L[ℂ] E)
    (hzero : ∀ x, U 0 x = x)
    (hgroup : ∀ s v x, U s (U v x) = U (v+s) x)
    (hcont : ∀ x, Continuous (fun v => U v x))
    (M : ℝ)
    (hloc : ∀ s : ℝ, |s| < 1 → ∀ v : E, ‖U s v‖ ≤ M * ‖v‖)
    (k : ℝ → ℂ) (z : ℂ) (x : E)
    (hV : Integrable (fun t : ℝ => k t • dividedGroupOrbit U z t x))
    (hY : Integrable (fun t : ℝ => k t •
      (z • dividedGroupOrbit U z t x + U t x -
        Complex.exp (z * (t : ℂ)) • x))) :
    HasDerivAt (fun s : ℝ => U s
      (∫ t : ℝ, k t • dividedGroupOrbit U z t x))
      (∫ t : ℝ, k t • (z • dividedGroupOrbit U z t x + U t x -
        Complex.exp (z * (t : ℂ)) • x)) 0 := by
  let V : ℝ → E := fun t => k t • dividedGroupOrbit U z t x
  let Y : ℝ → E := fun t => k t •
    (z • dividedGroupOrbit U z t x + U t x -
      Complex.exp (z * (t : ℂ)) • x)
  have hd0 (t : ℝ) : HasDerivAt (fun s : ℝ => U s (V t)) (Y t) 0 := by
    simpa only [V, Y, map_smul] using
      (dividedGroupOrbit_generator_domain U hzero hgroup hcont z t x).const_smul (k t)
  have hd (t s : ℝ) : HasDerivAt (fun r : ℝ => U r (V t)) (U s (Y t)) s := by
    have hh := ((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hd0 t)
    have hh' : HasDerivAt (fun r : ℝ => U s (U r (V t))) (U s (Y t)) (s-s) := by
      simpa using hh
    have hp := hh'.scomp (h := fun r : ℝ => r - s) s ((hasDerivAt_id s).sub_const s)
    simpa only [Function.comp_def, hgroup, sub_add_cancel, one_smul] using hp
  have hiV : Integrable V := hV
  have hiY : Integrable Y := hY
  have hm : ∀ᶠ s : ℝ in 𝓝 0, AEStronglyMeasurable (fun t => U s (V t)) := by
    exact Eventually.of_forall fun s => (U s).continuous.comp_aestronglyMeasurable hiV.aestronglyMeasurable
  have h0 : Integrable (fun t => U 0 (V t)) := by simpa only [hzero] using hiV
  have hmY : AEStronglyMeasurable (fun t => U 0 (Y t)) := by
    simpa only [hzero] using hiY.aestronglyMeasurable
  have hb : Integrable (fun t => M * ‖Y t‖) := hiY.norm.const_mul M
  have hs : Metric.ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hbound : ∀ᵐ t : ℝ, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖U s (Y t)‖ ≤ M * ‖Y t‖ := by
    exact Eventually.of_forall fun t s hs => hloc s (by simpa [Real.dist_eq] using hs) (Y t)
  have hdiff : ∀ᵐ t : ℝ, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => U r (V t)) (U s (Y t)) s :=
    Eventually.of_forall fun t s _ => hd t s
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hm h0 hmY hbound hb hdiff).2
  have he (s : ℝ) : (∫ t : ℝ, U s (V t)) = U s (∫ t : ℝ, V t) :=
    (U s).integral_comp_comm hiV
  simpa only [he, hzero, V, Y] using hh

#check integrated_seed_generator_domain
#print axioms integrated_seed_generator_domain
end Round191C

/-! F193. Quantitative native divided-orbit bound. This is the first
quantitative input needed to discharge hV and hY of C191 from the actual
theta seed moments, rather than postulating graph integrability. -/
namespace Round193F
set_option linter.unusedSectionVars false
open MeasureTheory Round188D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem divided_orbit_exponential_bound
    (U : ℝ → E →L[ℂ] E) (beta : ℝ) (hb : 0 ≤ beta)
    (hgrowth : ∀ t x, ‖U t x‖ ≤ Real.exp (beta * |t|) * ‖x‖)
    (z : ℂ) (t : ℝ) (x : E) :
    ‖dividedGroupOrbit U z t x‖ ≤
      |t| * Real.exp ((|z.re| + beta) * |t|) * ‖x‖ := by
  have hbnd (v : ℝ) (hv : v ∈ Set.uIoc 0 t) :
      |v| ≤ |t| ∧ |t-v| ≤ |t| := by
    rcases le_total 0 t with ht | ht
    · rw [Set.uIoc_of_le ht] at hv
      rcases hv with ⟨hv0, hvt⟩
      rw [abs_of_nonneg ht, abs_of_nonneg hv0.le,
        abs_of_nonneg (sub_nonneg.mpr hvt)]
      constructor <;> linarith
    · rw [Set.uIoc_of_ge ht] at hv
      rcases hv with ⟨hvt, hv0⟩
      rw [abs_of_nonpos ht, abs_of_nonpos hv0,
        abs_of_nonpos (sub_nonpos.mpr hvt.le)]
      constructor <;> linarith
  have hkernel (v : ℝ) (hv : v ∈ Set.uIoc 0 t) :
      ‖Complex.exp (z * ((t-v : ℝ) : ℂ)) • U v x‖ ≤
        Real.exp ((|z.re| + beta) * |t|) * ‖x‖ := by
    rw [norm_smul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    calc
      _ ≤ Real.exp (z.re * (t-v)) * (Real.exp (beta * |v|) * ‖x‖) := by
        gcongr
        exact hgrowth v x
      _ = Real.exp (z.re * (t-v) + beta * |v|) * ‖x‖ := by
        rw [Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply Real.exp_le_exp.mpr
        have hprod : z.re * (t-v) ≤ |z.re| * |t-v| := by
          simpa only [abs_mul] using le_abs_self (z.re * (t-v))
        have h1 := mul_le_mul_of_nonneg_left (hbnd v hv).2 (abs_nonneg z.re)
        have h2 := mul_le_mul_of_nonneg_left (hbnd v hv).1 hb
        nlinarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hkernel
  simpa only [dividedGroupOrbit, sub_zero] using hi.trans_eq (by ring)

#check divided_orbit_exponential_bound
#print axioms divided_orbit_exponential_bound

/-- Ordinary theta moments discharge BOTH integrability premises of C191.
The three measurability premises follow from the actual smooth seed and
strongly continuous native translation group. -/
theorem full_seed_graph_integrable
    (U : ℝ → E →L[ℂ] E) (beta : ℝ) (hb : 0 ≤ beta)
    (hgrowth : ∀ t x, ‖U t x‖ ≤ Real.exp (beta * |t|) * ‖x‖)
    (k : ℝ → ℂ) (z : ℂ) (x : E)
    (hm0 : Integrable (fun t : ℝ => ‖k t‖ * Real.exp ((|z.re|+beta)*|t|)))
    (hm1 : Integrable (fun t : ℝ => ‖k t‖ * |t| * Real.exp ((|z.re|+beta)*|t|)))
    (hVm : AEStronglyMeasurable (fun t : ℝ => k t • dividedGroupOrbit U z t x) volume)
    (hUm : AEStronglyMeasurable (fun t : ℝ => k t • U t x) volume)
    (hEm : AEStronglyMeasurable (fun t : ℝ =>
      (k t * Complex.exp (z * (t : ℂ))) • x) volume) :
    Integrable (fun t : ℝ => k t • dividedGroupOrbit U z t x) ∧
    Integrable (fun t : ℝ => k t • (z • dividedGroupOrbit U z t x + U t x -
      Complex.exp (z * (t : ℂ)) • x)) := by
  have hV : Integrable (fun t : ℝ => k t • dividedGroupOrbit U z t x) := by
    apply (hm1.mul_const ‖x‖).mono' hVm
    filter_upwards [] with t
    rw [norm_smul]
    calc
      _ ≤ ‖k t‖ * (|t| * Real.exp ((|z.re|+beta)*|t|) * ‖x‖) :=
        mul_le_mul_of_nonneg_left
          (divided_orbit_exponential_bound U beta hb hgrowth z t x) (norm_nonneg _)
      _ = _ := by ring
  have hU : Integrable (fun t : ℝ => k t • U t x) := by
    apply (hm0.mul_const ‖x‖).mono' hUm
    filter_upwards [] with t
    rw [norm_smul]
    have he : Real.exp (beta*|t|) ≤ Real.exp ((|z.re|+beta)*|t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (abs_nonneg z.re) (abs_nonneg t)]
    calc
      _ ≤ ‖k t‖ * (Real.exp (beta*|t|) * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hgrowth t x) (norm_nonneg _)
      _ ≤ _ := by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right he (norm_nonneg x)) (norm_nonneg (k t)))
  have hE : Integrable (fun t : ℝ => (k t * Complex.exp (z * (t : ℂ))) • x) := by
    apply (hm0.mul_const ‖x‖).mono' hEm
    filter_upwards [] with t
    rw [norm_smul, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg (k t))
    apply Real.exp_le_exp.mpr
    have hp : z.re * t ≤ |z.re| * |t| := by
      simpa only [abs_mul] using le_abs_self (z.re * t)
    nlinarith [mul_nonneg hb (abs_nonneg t)]
  refine ⟨hV, ?_⟩
  have hzV : Integrable (fun t : ℝ => z • (k t • dividedGroupOrbit U z t x)) := by
    apply (hV.norm.const_mul ‖z‖).mono'
    · exact (show Continuous (fun v : E => z • v) from continuous_const.smul continuous_id).comp_aestronglyMeasurable hVm
    · filter_upwards [] with t
      rw [norm_smul]
  have hi := (hzV.add hU).sub hE
  simpa only [smul_sub, smul_add, smul_smul, mul_comm] using hi

#check full_seed_graph_integrable
#print axioms full_seed_graph_integrable
end Round193F

/-! F194. The actual smooth theta seed and native C0 group discharge
all vector measurability hypotheses; only ordinary scalar moments remain.
The native construction giving those moments is displayed in GLOBAL_ESTIMATE.md.
This concludes a generator-domain statement, not assumed nuclearity. -/
namespace Round194F
open MeasureTheory Round187D Round188D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

theorem continuous_divided_orbit
    (U : ℝ → E →L[ℂ] E) (hcont : ∀ x, Continuous (fun t => U t x))
    (z : ℂ) (x : E) : Continuous (fun t => dividedGroupOrbit U z t x) := by
  let f : ℝ → E := fun t => U t x
  let g : ℝ → E := fun t => Complex.exp (-z * (t : ℂ)) • f t
  have hf : Continuous f := hcont x
  have hg : Continuous g := by
    exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ)))).smul hf
  have hp : Continuous (weightedPrimitive f z) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 t) hg.stronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt).continuousAt
  have he (t : ℝ) : dividedGroupOrbit U z t x =
      Complex.exp (z * (t : ℂ)) • weightedPrimitive f z t := by
    simpa [dividedGroupOrbit, weightedPrimitive, f] using
      translated_divided_integral f hf z t 0
  simp_rw [he]
  exact (by fun_prop : Continuous (fun t : ℝ => Complex.exp (z * (t : ℂ)))).smul hp

theorem continuous_theta_seed_generator_domain
    (U : ℝ → E →L[ℂ] E)
    (hzero : ∀ x, U 0 x = x)
    (hgroup : ∀ s v x, U s (U v x) = U (v+s) x)
    (hcont : ∀ x, Continuous (fun t => U t x))
    (beta : ℝ) (hb : 0 ≤ beta)
    (hgrowth : ∀ t x, ‖U t x‖ ≤ Real.exp (beta * |t|) * ‖x‖)
    (k : ℝ → ℂ) (hk : Continuous k) (z : ℂ) (x : E)
    (hm0 : Integrable (fun t : ℝ => ‖k t‖ * Real.exp ((|z.re|+beta)*|t|)))
    (hm1 : Integrable (fun t : ℝ => ‖k t‖ * |t| * Real.exp ((|z.re|+beta)*|t|))) :
    HasDerivAt (fun s : ℝ => U s
      (∫ t : ℝ, k t • dividedGroupOrbit U z t x))
      (∫ t : ℝ, k t • (z • dividedGroupOrbit U z t x + U t x -
        Complex.exp (z * (t : ℂ)) • x)) 0 := by
  have hVm : AEStronglyMeasurable (fun t => k t • dividedGroupOrbit U z t x) volume :=
    (hk.smul (continuous_divided_orbit U hcont z x)).aestronglyMeasurable
  have hUm : AEStronglyMeasurable (fun t => k t • U t x) volume :=
    (hk.smul (hcont x)).aestronglyMeasurable
  have hEc : Continuous (fun t : ℝ => (k t * Complex.exp (z * (t : ℂ))) • x) := by
    exact (hk.mul (by fun_prop)).smul continuous_const
  have hi := Round193F.full_seed_graph_integrable U beta hb hgrowth k z x
    hm0 hm1 hVm hUm hEc.aestronglyMeasurable
  apply Round191C.integrated_seed_generator_domain U hzero hgroup hcont
    (Real.exp beta) _ k z x hi.1 hi.2
  intro t ht v
  apply (hgrowth t v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
  apply Real.exp_le_exp.mpr
  nlinarith

#check continuous_divided_orbit
#print axioms continuous_divided_orbit
#check continuous_theta_seed_generator_domain
#print axioms continuous_theta_seed_generator_domain
end Round194F


/-! B194. The actual normalized compact-character averaging step in C189's
geometric seed. This proves its theta envelope with the Tate/native Haar
ratio retained. It supplies the seed moments in the global resolvent route;
it does not assert nuclearity or replace the original geometric space. -/
noncomputable section
set_option linter.unusedSimpArgs false
open MeasureTheory
namespace Round194B

def measuredThetaSeed {C : Type*} [MeasurableSpace C]
    (μ : Measure C) (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (t : ℝ) : ℂ :=
  (κ : ℂ) * (Real.exp (a * t) : ℂ) * ∫ y, Φ t y * χ y ∂μ

theorem native_normalized_theta_seed_bound
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a B P : ℝ) (hκ : 0 ≤ κ) (_hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hχ : ∀ y, ‖χ y‖ = 1)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P * Real.exp (-B * |t|))
    (t : ℝ) :
    ‖measuredThetaSeed μ κ a Φ χ t‖ ≤
      κ * P * Real.exp (-(B - |a|) * |t|) := by
  have havg : ‖∫ y, Φ t y * χ y ∂μ‖ ≤ P * Real.exp (-B * |t|) := by
    have hb : ∀ᵐ y ∂μ, ‖Φ t y * χ y‖ ≤ P * Real.exp (-B * |t|) :=
      Filter.Eventually.of_forall fun y => by
        simpa only [Pi.mul_apply, norm_mul, hχ y, mul_one] using hdecay t y
    simpa using norm_integral_le_of_norm_le_const hb
  have hat : a * t ≤ |a| * |t| := by
    calc
      a * t ≤ |a * t| := le_abs_self _
      _ = |a| * |t| := abs_mul _ _
  have hexp : Real.exp (a * t) ≤ Real.exp (|a| * |t|) := Real.exp_le_exp.mpr hat
  calc
    ‖measuredThetaSeed μ κ a Φ χ t‖ =
        κ * Real.exp (a * t) * ‖∫ y, Φ t y * χ y ∂μ‖ := by
      simp only [measuredThetaSeed, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hκ, abs_of_pos (Real.exp_pos _)]
    _ ≤ κ * Real.exp (|a| * |t|) * (P * Real.exp (-B * |t|)) := by
      gcongr
    _ = κ * P * Real.exp (-(B - |a|) * |t|) := by
      rw [show κ * Real.exp (|a| * |t|) * (P * Real.exp (-B * |t|)) =
        κ * P * (Real.exp (|a| * |t|) * Real.exp (-B * |t|)) by ring]
      rw [← Real.exp_add]
      congr 2
      ring

#check native_normalized_theta_seed_bound
#print axioms native_normalized_theta_seed_bound

/-- Both existence of the compact Bochner integral and its native seed
normalization. For the actual application the two measurability hypotheses
come from the continuous theta function and compact unitary character. -/
theorem native_seed_normalization
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a B P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : ∀ t, AEStronglyMeasurable (Φ t) μ)
    (hc : AEStronglyMeasurable χ μ)
    (hχ : ∀ y, ‖χ y‖ = 1)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P * Real.exp (-B * |t|)) :
    ∀ t, Integrable (fun y => Φ t y * χ y) μ ∧
      ‖measuredThetaSeed μ κ a Φ χ t‖ ≤
        κ * P * Real.exp (-(B - |a|) * |t|) := by
  intro t
  constructor
  · apply (integrable_const (P * Real.exp (-B * |t|))).mono' ((hΦ t).mul hc)
    exact Filter.Eventually.of_forall fun y => by
      simpa only [Pi.mul_apply, norm_mul, hχ y, mul_one] using hdecay t y
  · exact native_normalized_theta_seed_bound μ κ a B P hκ hP Φ χ hχ hdecay t

#check native_seed_normalization
#print axioms native_seed_normalization
end Round194B

namespace Round194D
open MeasureTheory

theorem native_theta_moment_majorants (k : ℝ → ℂ) (L A : ℝ)
    (hA : 0 ≤ A)
    (hdecay : ∀ t, ‖k t‖ ≤ A * Real.exp (-(L+2)*|t|)) (t : ℝ) :
    ‖k t‖ * Real.exp (L*|t|) ≤ A * Real.exp (-|t|) ∧
    ‖k t‖ * |t| * Real.exp (L*|t|) ≤ A * Real.exp (-|t|) := by
  have he : ‖k t‖ * Real.exp (L*|t|) ≤ A * Real.exp (-2*|t|) := by
    calc
      _ ≤ (A * Real.exp (-(L+2)*|t|)) * Real.exp (L*|t|) :=
        mul_le_mul_of_nonneg_right (hdecay t) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hab : |t| ≤ Real.exp (|t|) := by
    have hh := Real.add_one_le_exp (|t|)
    linarith
  constructor
  · exact he.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith [abs_nonneg t])) hA)
  · calc
      _ = (‖k t‖ * Real.exp (L*|t|)) * |t| := by ring
      _ ≤ (A * Real.exp (-2*|t|)) * |t| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg t)
      _ ≤ (A * Real.exp (-2*|t|)) * Real.exp (|t|) :=
        mul_le_mul_of_nonneg_left hab (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

#check native_theta_moment_majorants
#print axioms native_theta_moment_majorants
end Round194D

namespace Round195F
open MeasureTheory Round188D

/-- The scalar envelope used by the actual theta moment bounds is integrable
on the full signed log-norm coordinate, not merely on a compact interval. -/
theorem integrable_exp_neg_abs :
    Integrable (fun t : ℝ => Real.exp (-|t|)) := by
  have hlo : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Set.Iic 0) := by
    apply (integrableOn_exp_mul_Iic (a := 1) (by norm_num) 0).congr_fun _ measurableSet_Iic
    intro t ht
    simp [abs_of_nonpos (Set.mem_Iic.mp ht)]
  have hhi : IntegrableOn (fun t : ℝ => Real.exp (-|t|)) (Set.Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0).congr_fun _ measurableSet_Ioi
    intro t ht
    simp [abs_of_pos (Set.mem_Ioi.mp ht)]
  have hcover : Set.Iic (0 : ℝ) ∪ Set.Ioi 0 = Set.univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ, iff_true]
    exact le_or_gt t 0
  simpa only [hcover, integrableOn_univ] using hlo.union hhi

/-- Discharges precisely the two scalar moment assumptions of F194 and hence
C191's hV/hY. The remaining pointwise input is the theta-decay estimate. -/
theorem theta_moments_from_decay (k : ℝ → ℂ) (hk : Continuous k)
    (L A : ℝ) (hA : 0 ≤ A)
    (hdecay : ∀ t, ‖k t‖ ≤ A * Real.exp (-(L+2)*|t|)) :
    Integrable (fun t : ℝ => ‖k t‖ * Real.exp (L*|t|)) ∧
    Integrable (fun t : ℝ => ‖k t‖ * |t| * Real.exp (L*|t|)) := by
  have hm0 : Continuous (fun t : ℝ => ‖k t‖ * Real.exp (L*|t|)) := by fun_prop
  have hm1 : Continuous (fun t : ℝ => ‖k t‖ * |t| * Real.exp (L*|t|)) := by fun_prop
  constructor
  · apply (integrable_exp_neg_abs.const_mul A).mono' hm0.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Round194D.native_theta_moment_majorants k L A hA hdecay t).1
  · apply (integrable_exp_neg_abs.const_mul A).mono' hm1.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (Round194D.native_theta_moment_majorants k L A hA hdecay t).2

/-- The measured compact average is substituted explicitly. No scalar
integrability or spectral summability is a premise. Actual adelic theta decay
must still instantiate hdecay, and actual smoothness must instantiate hk. -/
theorem measured_theta_seed_moments
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a L P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hk : Continuous (Round194B.measuredThetaSeed μ κ a Φ χ))
    (hχ : ∀ y, ‖χ y‖ = 1)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P * Real.exp (-(|a|+L+2)*|t|)) :
    Integrable (fun t : ℝ => ‖Round194B.measuredThetaSeed μ κ a Φ χ t‖ *
      Real.exp (L*|t|)) ∧
    Integrable (fun t : ℝ => ‖Round194B.measuredThetaSeed μ κ a Φ χ t‖ *
      |t| * Real.exp (L*|t|)) := by
  apply theta_moments_from_decay _ hk L (κ*P) (mul_nonneg hκ hP)
  intro t
  convert Round194B.native_normalized_theta_seed_bound μ κ a (|a|+L+2) P
    hκ hP Φ χ hχ hdecay t using 1 <;> congr 2 <;> ring

#check integrable_exp_neg_abs
#print axioms integrable_exp_neg_abs
#check theta_moments_from_decay
#print axioms theta_moments_from_decay
#check measured_theta_seed_moments
#print axioms measured_theta_seed_moments
end Round195F

set_option linter.unnecessarySeqFocus false

/-! C194. NATIVE_TRANSLATION_GROWTH in the original logarithmic coordinate.
The density is exactly the reciprocal manuscript weight, written using exp/log.
The final theorem controls the actual weighted L2 mass, not spectral coefficients.
This supplies the growth premise of the seed-generator attachment; it is not
itself a full nuclearity theorem. -/
noncomputable section
namespace Round194C
open MeasureTheory

def nativeDualWeight (u v s x : ℝ) : ℝ :=
  Real.exp (-2 * max (u*x) (v*x) - (s/2)*Real.log (1+x^2))

theorem log_one_sq_lipschitz (x y : ℝ) :
    |Real.log (1+y^2)-Real.log (1+x^2)| ≤ |y-x| := by
  have hd (t : ℝ) : HasDerivAt (fun z : ℝ => Real.log (1+z^2))
      (2*t/(1+t^2)) t := by
    convert (((hasDerivAt_id t).pow 2).const_add 1).log
      (ne_of_gt (by positivity : (0:ℝ)<1+t^2)) using 1 <;> dsimp <;> ring
  have hb (t : ℝ) : ‖2*t/(1+t^2)‖ ≤ (1:ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2),
      abs_of_pos (by positivity : (0:ℝ)<1+t^2)]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<1+t^2)).2
    nlinarith [sq_nonneg (|t|-1), sq_abs t]
  simpa only [Real.norm_eq_abs, one_mul] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hd t).hasDerivWithinAt) (fun t _ => hb t)
      (Set.mem_univ x) (Set.mem_univ y)

theorem native_weight_translate (u v s x t : ℝ) (hs : 0 ≤ s) :
    nativeDualWeight u v s (x-t) ≤
      Real.exp (2*(max |u| |v|+s/4)*|t|) * nativeDualWeight u v s x := by
  have hm : max (u*x) (v*x) - max (u*(x-t)) (v*(x-t)) ≤
      max |u| |v| * |t| := by
    apply (max_sub_max_le_max _ _ _ _).trans
    apply max_le
    · calc
        u*x-u*(x-t) = u*t := by ring
        _ ≤ |u| * |t| := by simpa only [abs_mul] using le_abs_self (u*t)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg t)
    · calc
        v*x-v*(x-t) = v*t := by ring
        _ ≤ |v| * |t| := by simpa only [abs_mul] using le_abs_self (v*t)
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg t)
  have hl : Real.log (1+x^2)-Real.log (1+(x-t)^2) ≤ |t| := by
    have hh := log_one_sq_lipschitz (x-t) x
    have hx : x-(x-t)=t := by ring
    rw [hx] at hh
    exact (le_abs_self _).trans hh
  unfold nativeDualWeight
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ s/2)
  nlinarith

/-- Actual weighted L2 mass of translation; taking square roots gives exactly
exp((max |u| |v| + s/4)*|t|). No operator-growth hypothesis is used. -/
theorem native_translation_l2_mass_le (u v s t : ℝ) (hs : 0 ≤ s)
    (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ x : ℝ, ENNReal.ofReal (‖f (x+t)‖^2) *
        ENNReal.ofReal (nativeDualWeight u v s x)) ≤
      ENNReal.ofReal (Real.exp (2*(max |u| |v|+s/4)*|t|)) *
        ∫⁻ x : ℝ, ENNReal.ofReal (‖f x‖^2) *
          ENNReal.ofReal (nativeDualWeight u v s x) := by
  let C := Real.exp (2*(max |u| |v|+s/4)*|t|)
  let F : ℝ → ENNReal := fun x => ENNReal.ofReal (‖f x‖^2) *
    ENNReal.ofReal (nativeDualWeight u v s x)
  have hF : Measurable F := by dsimp [F, nativeDualWeight]; fun_prop
  have hw (x : ℝ) : ENNReal.ofReal (nativeDualWeight u v s x) ≤
      ENNReal.ofReal C * ENNReal.ofReal (nativeDualWeight u v s (x+t)) := by
    have hh := native_weight_translate u v s (x+t) t hs
    rw [add_sub_cancel_right] at hh
    have hh' := ENNReal.ofReal_le_ofReal hh
    simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le] using hh'
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal C * F (x+t) := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ ENNReal.ofReal (‖f (x+t)‖^2) *
            (ENNReal.ofReal C * ENNReal.ofReal (nativeDualWeight u v s (x+t))) :=
          mul_le_mul' le_rfl (hw x)
        _ = _ := by dsimp [F]; ac_rfl
    _ = ENNReal.ofReal C * ∫⁻ x : ℝ, F (x+t) :=
      lintegral_const_mul _ (hF.comp (measurable_id.add_const t))
    _ = _ := by rw [lintegral_add_right_eq_self F t]

#check native_weight_translate
#print axioms native_weight_translate
#check native_translation_l2_mass_le
#print axioms native_translation_l2_mass_le
end Round194C

namespace Round195D
open MeasureTheory Round194C

def nativeDualMeasure (u v s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (nativeDualWeight u v s x))

abbrev NativeDualFiber (u v s : ℝ) := Lp ℂ 2 (nativeDualMeasure u v s)
end Round195D

/-! C195 assembly. The actual reciprocal-weight Lp carrier and the measured
compact average are explicit. The scalar moment, measurability and local
bound premises of C191 are discharged by the copied B/D/F declarations.
This interface remains conditional on constructing the native translation U
and the actual adelic theta function satisfying the displayed decay. It is
not the requested fully instantiated native theorem or a nuclear bound. -/
namespace Round195C
open MeasureTheory Round188D Round195D

theorem normalized_seed_domain_on_native_fiber
    (u v s : ℝ) (hs : 0 ≤ s)
    (U : ℝ → NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s)
    (hzero : ∀ x, U 0 x = x)
    (hgroup : ∀ t r x, U t (U r x) = U (r+t) x)
    (hcont : ∀ x, Continuous (fun t => U t x))
    (hgrowth : ∀ t x, ‖U t x‖ ≤
      Real.exp ((max |u| |v| + s/4) * |t|) * ‖x‖)
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hk : Continuous (Round194B.measuredThetaSeed μ κ a Φ χ))
    (hχ : ∀ y, ‖χ y‖ = 1)
    (z : ℂ) (x : NativeDualFiber u v s)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P *
      Real.exp (-(|a|+(|z.re| + (max |u| |v| + s/4))+2)*|t|)) :
    HasDerivAt (fun r : ℝ => U r
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit U z t x))
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit U z t x + U t x -
          Complex.exp (z * (t : ℂ)) • x)) 0 := by
  have hb : 0 ≤ max |u| |v| + s/4 := by positivity
  have hm := Round195F.measured_theta_seed_moments μ κ a
    (|z.re| + (max |u| |v| + s/4)) P hκ hP Φ χ hk hχ hdecay
  exact Round194F.continuous_theta_seed_generator_domain
    U hzero hgroup hcont (max |u| |v| + s/4) hb hgrowth
    (Round194B.measuredThetaSeed μ κ a Φ χ) hk z x hm.1 hm.2

#check normalized_seed_domain_on_native_fiber
#print axioms normalized_seed_domain_on_native_fiber
end Round195C

namespace Round195B
open Round194B

/-- Changing only the auxiliary theta Haar by r multiplies its seed by r;
this identity does not rescale the original convolution operator. -/
theorem measuredThetaSeed_haar_rescale
    {C : Type*} [MeasurableSpace C] (μ : Measure C) (r : NNReal)
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ) (t : ℝ) :
    measuredThetaSeed ((r : ENNReal) • μ) κ a Φ χ t =
      measuredThetaSeed μ ((r : ℝ) * κ) a Φ χ t := by
  simp only [measuredThetaSeed, integral_smul_measure, ENNReal.coe_toReal,
    Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The native real tilt changes the Mellin coordinate by a, with the
Tate/native scalar retained outside the whole transform. -/
theorem measuredThetaSeed_mellin_shift
    {C : Type*} [MeasurableSpace C] (μ : Measure C)
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ) (z : ℂ) :
    (∫ t : ℝ, measuredThetaSeed μ κ a Φ χ t * Complex.exp (z * (t : ℂ))) =
      (κ : ℂ) * ∫ t : ℝ, (∫ y, Φ t y * χ y ∂μ) *
        Complex.exp (((a : ℂ) + z) * (t : ℂ)) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only [measuredThetaSeed]
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
    calc
      _ = (κ : ℂ) * (∫ y, Φ t y * χ y ∂μ) *
          (Complex.exp ((a : ℂ) * (t : ℂ)) * Complex.exp (z * (t : ℂ))) := by ring
      _ = _ := by rw [← Complex.exp_add, ← add_mul]; ring

/-- Measurability of the measured seed is derived from the actual joint
measurability input, not from a default value of a Bochner integral. -/
theorem measuredThetaSeed_stronglyMeasurable
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [SFinite μ]
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hχ : StronglyMeasurable χ) :
    StronglyMeasurable (measuredThetaSeed μ κ a Φ χ) := by
  have hpair : StronglyMeasurable
      (Function.uncurry (fun t y => Φ t y * χ y)) :=
    hΦ.mul (hχ.comp_measurable measurable_snd)
  have havg := hpair.integral_prod_right (ν := μ)
  have he : StronglyMeasurable (fun t : ℝ => (Real.exp (a*t) : ℂ)) :=
    (by fun_prop : Continuous (fun t : ℝ => (Real.exp (a*t) : ℂ))).stronglyMeasurable
  exact (stronglyMeasurable_const.mul he).mul havg

#check measuredThetaSeed_haar_rescale
#print axioms measuredThetaSeed_haar_rescale
#check measuredThetaSeed_mellin_shift
#print axioms measuredThetaSeed_mellin_shift
#check measuredThetaSeed_stronglyMeasurable
#print axioms measuredThetaSeed_stronglyMeasurable
end Round195B

namespace Round195C
open MeasureTheory Round188D Round195D

/-- Direct C191 application on the weighted Lp fiber. Joint theta measurability
suffices: seed continuity, scalar moments and graph integrability are derived.
Native translation laws and the actual adelic theta realization remain open. -/
theorem measurable_normalized_seed_domain_on_native_fiber
    (u v s : ℝ) (hs : 0 ≤ s)
    (U : ℝ → NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s)
    (hzero : ∀ x, U 0 x = x)
    (hgroup : ∀ t r x, U t (U r x) = U (r+t) x)
    (hcont : ∀ x, Continuous (fun t => U t x))
    (hgrowth : ∀ t x, ‖U t x‖ ≤
      Real.exp ((max |u| |v| + s/4) * |t|) * ‖x‖)
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hχm : StronglyMeasurable χ) (hχ : ∀ y, ‖χ y‖ = 1)
    (z : ℂ) (x : NativeDualFiber u v s)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P *
      Real.exp (-(|a|+(|z.re| + (max |u| |v| + s/4))+2)*|t|)) :
    HasDerivAt (fun r : ℝ => U r
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit U z t x))
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit U z t x + U t x -
          Complex.exp (z * (t : ℂ)) • x)) 0 := by
  let k := Round194B.measuredThetaSeed μ κ a Φ χ
  let beta := max |u| |v| + s/4
  let L := |z.re| + beta
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hkm : StronglyMeasurable k :=
    Round195B.measuredThetaSeed_stronglyMeasurable μ κ a Φ χ hΦ hχm
  have hbound (t : ℝ) : ‖k t‖ ≤ (κ*P) * Real.exp (-(L+2)*|t|) := by
    have he : |a| + L + 2 - |a| = L+2 := by ring
    simpa only [he] using Round194B.native_normalized_theta_seed_bound μ κ a
      (|a|+L+2) P hκ hP Φ χ hχ hdecay t
  have hexp : StronglyMeasurable (fun t : ℝ => Real.exp (L*|t|)) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (L*|t|))).stronglyMeasurable
  have hm0 : Integrable (fun t : ℝ => ‖k t‖ * Real.exp (L*|t|)) := by
    apply (Round195F.integrable_exp_neg_abs.const_mul (κ*P)).mono'
      (hkm.norm.mul hexp).aestronglyMeasurable
    filter_upwards [] with t
    change ‖‖k t‖ * Real.exp (L*|t|)‖ ≤ (κ*P) * Real.exp (-|t|)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)]
    exact (Round194D.native_theta_moment_majorants k L (κ*P)
      (mul_nonneg hκ hP) hbound t).1
  have hm1 : Integrable (fun t : ℝ => ‖k t‖ * |t| * Real.exp (L*|t|)) := by
    apply (Round195F.integrable_exp_neg_abs.const_mul (κ*P)).mono'
      ((hkm.norm.mul continuous_abs.stronglyMeasurable).mul hexp).aestronglyMeasurable
    filter_upwards [] with t
    change ‖‖k t‖ * |t| * Real.exp (L*|t|)‖ ≤ (κ*P) * Real.exp (-|t|)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le)]
    exact (Round194D.native_theta_moment_majorants k L (κ*P)
      (mul_nonneg hκ hP) hbound t).2
  have hVm : AEStronglyMeasurable (fun t : ℝ => k t • dividedGroupOrbit U z t x) volume := hkm.aestronglyMeasurable.smul
    (Round194F.continuous_divided_orbit U hcont z x).aestronglyMeasurable
  have hUm : AEStronglyMeasurable (fun t : ℝ => k t • U t x) volume := hkm.aestronglyMeasurable.smul (hcont x).aestronglyMeasurable
  have hc : Continuous (fun t : ℝ => Complex.exp (z * (t : ℂ))) := by fun_prop
  have hEm : AEStronglyMeasurable
      (fun t : ℝ => (k t * Complex.exp (z * (t : ℂ))) • x) volume :=
    ((hkm.mul hc.stronglyMeasurable).smul stronglyMeasurable_const).aestronglyMeasurable
  have hi := Round193F.full_seed_graph_integrable U beta hb hgrowth k z x
    hm0 hm1 hVm hUm hEm
  apply Round191C.integrated_seed_generator_domain U hzero hgroup hcont
    (Real.exp beta) _ k z x hi.1 hi.2
  intro t ht y
  apply (hgrowth t y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  apply Real.exp_le_exp.mpr
  change beta * |t| ≤ beta
  nlinarith

#check measurable_normalized_seed_domain_on_native_fiber
#print axioms measurable_normalized_seed_domain_on_native_fiber
end Round195C

namespace Round195D
open MeasureTheory Round194C
theorem native_dual_density_measurable (u v s : ℝ) :
    Measurable (fun x => ENNReal.ofReal (nativeDualWeight u v s x)) := by
  unfold nativeDualWeight
  fun_prop

#check nativeDualMeasure
#check NativeDualFiber
#check native_dual_density_measurable
#print axioms native_dual_density_measurable

/-- Convert the already proved native quadratic estimate into a measure bound,
so it applies to all L2 equivalence classes, not only continuous representatives. -/
theorem native_indicator_mass (u v s : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ x : ℝ, ENNReal.ofReal (‖S.indicator (fun _ => (1 : ℂ)) x‖^2) *
      ENNReal.ofReal (nativeDualWeight u v s x)) = nativeDualMeasure u v s S := by
  rw [nativeDualMeasure, withDensity_apply _ hS, ← lintegral_indicator hS]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ S <;> simp [Set.indicator, hx]

theorem native_translation_measure_le (u v s t : ℝ) (hs : 0 ≤ s) :
    Measure.map (fun x : ℝ => x+t) (nativeDualMeasure u v s) ≤
      ENNReal.ofReal (Real.exp (2*(max |u| |v|+s/4)*|t|)) • nativeDualMeasure u v s := by
  apply Measure.le_iff.mpr
  intro S hS
  have h := native_translation_l2_mass_le u v s t hs
    (S.indicator (fun _ => (1 : ℂ))) (measurable_const.indicator hS)
  have he : (fun x : ℝ => S.indicator (fun _ => (1 : ℂ)) (x+t)) =
      ((fun x : ℝ => x+t) ⁻¹' S).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x+t ∈ S <;> simp [Set.indicator, hx]
  have he' (x : ℝ) := congrFun he x
  simp_rw [he'] at h
  have hpre : MeasurableSet ((fun x : ℝ => x+t) ⁻¹' S) :=
    (measurable_id.add_const t) hS
  rw [native_indicator_mass u v s ((fun x : ℝ => x+t) ⁻¹' S) hpre,
    native_indicator_mass u v s S hS] at h
  have hmeas : Measurable (fun x : ℝ => x+t) := measurable_id.add_const t
  rw [Measure.map_apply hmeas hS]
  simpa only [Measure.smul_apply, smul_eq_mul] using h

/-- Translation is defined on every vector of the actual weighted L2 fiber. -/
theorem native_translation_memLp (u v s t : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    MemLp (fun x : ℝ => f (x+t)) 2 (nativeDualMeasure u v s) := by
  have hf := (Lp.memLp f).of_measure_le_smul (by simp)
    (native_translation_measure_le u v s t hs)
  exact hf.comp_of_map (measurable_id.add_const t).aemeasurable

def nativeTranslationVector (u v s t : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) : NativeDualFiber u v s :=
  (native_translation_memLp u v s t hs f).toLp (fun x => f (x+t))

#check native_translation_measure_le
#print axioms native_translation_measure_le
#check native_translation_memLp
#print axioms native_translation_memLp
#check nativeTranslationVector
#print axioms nativeTranslationVector

theorem native_translation_norm_le (u v s t : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    ‖nativeTranslationVector u v s t hs f‖ ≤
      Real.exp ((max |u| |v|+s/4)*|t|) * ‖f‖ := by
  let C := ENNReal.ofReal (Real.exp (2*(max |u| |v|+s/4)*|t|))
  have hm : Measurable (fun x : ℝ => x+t) := measurable_id.add_const t
  have hmap := (Lp.memLp f).of_measure_le_smul (by simp)
    (native_translation_measure_le u v s t hs)
  have hscaled : MemLp (fun x : ℝ => f x) 2 (C • nativeDualMeasure u v s) :=
    (Lp.memLp f).smul_measure (by simp [C])
  have hle : eLpNorm (fun x : ℝ => f (x+t)) 2 (nativeDualMeasure u v s) ≤
      eLpNorm (fun x : ℝ => f x) 2 (C • nativeDualMeasure u v s) := by
    have he : eLpNorm (fun x : ℝ => f (x+t)) 2 (nativeDualMeasure u v s) =
        eLpNorm (fun x : ℝ => f x) 2
          (Measure.map (fun x : ℝ => x+t) (nativeDualMeasure u v s)) := by
      simpa only [Function.comp_def] using
        (eLpNorm_map_measure (p := 2) hmap.aestronglyMeasurable hm.aemeasurable).symm
    exact he.trans_le (eLpNorm_mono_measure _ (native_translation_measure_le u v s t hs))
  have hb := ENNReal.toReal_mono hscaled.2.ne hle
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤),
    smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hb
  have hc : C.toReal ^ (1 / (2 : ENNReal)).toReal =
      Real.exp ((max |u| |v|+s/4)*|t|) := by
    dsimp [C]
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    norm_num
    ring
  rw [hc] at hb
  unfold nativeTranslationVector
  rw [Lp.norm_toLp, Lp.norm_def]
  exact hb

#check native_translation_norm_le
#print axioms native_translation_norm_le

theorem native_translation_zero (u v s : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) : nativeTranslationVector u v s 0 hs f = f := by
  apply Lp.ext
  simpa only [nativeTranslationVector, add_zero] using
    (native_translation_memLp u v s 0 hs f).coeFn_toLp

#check native_translation_zero
#print axioms native_translation_zero
end Round195D

namespace Round196D
open MeasureTheory Round195D

/-- Almost-everywhere identities survive translation for the actual weighted measure. -/
theorem native_translation_ae (u v s t : ℝ) (hs : 0 ≤ s)
    {P : ℝ → Prop} (hP : ∀ᵐ x ∂nativeDualMeasure u v s, P x) :
    ∀ᵐ x ∂nativeDualMeasure u v s, P (x+t) := by
  have hc : (ENNReal.ofReal (Real.exp (2*(max |u| |v|+s/4)*|t|)) •
      nativeDualMeasure u v s) ≪ nativeDualMeasure u v s := by
    intro S hS
    simp [Measure.smul_apply, hS]
  have ha := (Measure.absolutelyContinuous_of_le
    (native_translation_measure_le u v s t hs)).trans hc
  exact ae_of_ae_map (measurable_id.add_const t).aemeasurable (ha.ae_le hP)

theorem native_translation_coe (u v s t : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    (fun x => nativeTranslationVector u v s t hs f x) =ᵐ[nativeDualMeasure u v s]
      (fun x => f (x+t)) :=
  (native_translation_memLp u v s t hs f).coeFn_toLp

theorem native_translation_add (u v s t : ℝ) (hs : 0 ≤ s)
    (f g : NativeDualFiber u v s) :
    nativeTranslationVector u v s t hs (f+g) =
      nativeTranslationVector u v s t hs f + nativeTranslationVector u v s t hs g := by
  apply Lp.ext
  filter_upwards [native_translation_coe u v s t hs (f+g),
    Lp.coeFn_add (nativeTranslationVector u v s t hs f) (nativeTranslationVector u v s t hs g),
    native_translation_coe u v s t hs f, native_translation_coe u v s t hs g,
    native_translation_ae u v s t hs (Lp.coeFn_add f g)] with x hfg hsum hf hg htrans
  simp only [Pi.add_apply] at hsum htrans
  rw [hfg, htrans, hsum, hf, hg]

theorem native_translation_smul (u v s t : ℝ) (hs : 0 ≤ s)
    (c : ℂ) (f : NativeDualFiber u v s) :
    nativeTranslationVector u v s t hs (c • f) =
      c • nativeTranslationVector u v s t hs f := by
  apply Lp.ext
  filter_upwards [native_translation_coe u v s t hs (c • f),
    Lp.coeFn_smul c (nativeTranslationVector u v s t hs f),
    native_translation_coe u v s t hs f,
    native_translation_ae u v s t hs (Lp.coeFn_smul c f)] with x hcf hsmul hf htrans
  simp only [Pi.smul_apply] at hsmul htrans
  rw [hcf, htrans, hsmul, hf]

/-- The actual weighted translation continuous linear map. -/
def nativeTranslation (u v s : ℝ) (hs : 0 ≤ s) (t : ℝ) :
    NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s :=
  LinearMap.mkContinuous
    { toFun := nativeTranslationVector u v s t hs
      map_add' := native_translation_add u v s t hs
      map_smul' := native_translation_smul u v s t hs }
    (Real.exp ((max |u| |v|+s/4)*|t|)) (native_translation_norm_le u v s t hs)

@[simp] theorem nativeTranslation_apply (u v s : ℝ) (hs : 0 ≤ s) (t : ℝ)
    (f : NativeDualFiber u v s) :
    nativeTranslation u v s hs t f = nativeTranslationVector u v s t hs f := rfl

theorem nativeTranslation_zero (u v s : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) : nativeTranslation u v s hs 0 f = f :=
  native_translation_zero u v s hs f

theorem nativeTranslation_bound (u v s t : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    ‖nativeTranslation u v s hs t f‖ ≤
      Real.exp ((max |u| |v|+s/4)*|t|)*‖f‖ :=
  native_translation_norm_le u v s t hs f

theorem nativeTranslation_group (u v s t r : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    nativeTranslation u v s hs t (nativeTranslation u v s hs r f) =
      nativeTranslation u v s hs (r+t) f := by
  apply Lp.ext
  filter_upwards [native_translation_coe u v s t hs (nativeTranslation u v s hs r f),
    native_translation_ae u v s t hs (native_translation_coe u v s r hs f),
    native_translation_coe u v s (r+t) hs f] with x houter hinner htotal
  change nativeTranslationVector u v s t hs (nativeTranslation u v s hs r f) x =
    nativeTranslationVector u v s (r+t) hs f x
  rw [houter, nativeTranslation_apply, hinner, htotal]
  congr 1
  ring

#check nativeTranslation
#print axioms nativeTranslation
#check nativeTranslation_zero
#print axioms nativeTranslation_zero
#check nativeTranslation_group
#print axioms nativeTranslation_group
#check nativeTranslation_bound
#print axioms nativeTranslation_bound
end Round196D

namespace Round196C
open MeasureTheory Round188D Round195D Round196D

/-- C191 instantiated with the actual weighted translation CLM and its proved
zero, group and growth laws. Strong continuity and the actual theta realization
are the remaining native premises; no scalar moments or graph integrability
are assumed. -/
theorem native_normalized_seed_generator_domain
    (u v s : ℝ) (hs : 0 ≤ s)
    (hcont : ∀ x : NativeDualFiber u v s,
      Continuous (fun t => nativeTranslation u v s hs t x))
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hχm : StronglyMeasurable χ) (hχ : ∀ y, ‖χ y‖ = 1)
    (z : ℂ) (x : NativeDualFiber u v s)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P *
      Real.exp (-(|a|+(|z.re|+(max |u| |v|+s/4))+2)*|t|)) :
    HasDerivAt (fun r : ℝ => nativeTranslation u v s hs r
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit (nativeTranslation u v s hs) z t x))
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit (nativeTranslation u v s hs) z t x +
          nativeTranslation u v s hs t x -
          Complex.exp (z * (t : ℂ)) • x)) 0 := by
  exact Round195C.measurable_normalized_seed_domain_on_native_fiber u v s hs
    (nativeTranslation u v s hs)
    (nativeTranslation_zero u v s hs)
    (fun t r y => nativeTranslation_group u v s t r hs y)
    hcont (fun t y => nativeTranslation_bound u v s t hs y)
    μ κ a P hκ hP Φ χ hΦ hχm hχ z x hdecay

#check native_normalized_seed_generator_domain
#print axioms native_normalized_seed_generator_domain
end Round196C


namespace Round196D
open MeasureTheory Round195D

open scoped ContDiff

instance nativeDualMeasure_locallyFinite (u v s : ℝ) :
    IsLocallyFiniteMeasure (nativeDualMeasure u v s) := by
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  unfold Round194C.nativeDualWeight
  have hl : Continuous (fun x : ℝ => Real.log (1+x^2)) :=
    (continuous_const.add (continuous_id.pow 2)).log (fun x => ne_of_gt (by positivity))
  fun_prop

/-- A genuine dense smooth compact core in the actual weighted completion. -/
theorem native_smooth_compact_core_dense (u v s : ℝ) :
    Dense {f : NativeDualFiber u v s | ∃ g : ℝ → ℂ,
      (fun x => f x) =ᵐ[nativeDualMeasure u v s] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num)

#check native_smooth_compact_core_dense
#print axioms native_smooth_compact_core_dense
end Round196D

namespace Round196D
open MeasureTheory Round195D

/-- Strong continuity at zero on the actual dense compact continuous core. -/
theorem nativeTranslation_continuousAt_zero_of_core (u v s : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) (g : ℝ → ℂ)
    (hfg : (fun x => f x) =ᵐ[nativeDualMeasure u v s] g)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ContinuousAt (fun t => nativeTranslation u v s hs t f) 0 := by
  obtain ⟨R, hR, hsupport⟩ := hgs.exists_pos_le_norm
  let S := Metric.closedBall (0 : ℝ) (R+1)
  have hS : MeasurableSet S := measurableSet_closedBall
  have hμS : nativeDualMeasure u v s S ≠ ⊤ :=
    (isCompact_closedBall (0 : ℝ) (R+1)).measure_lt_top.ne
  have hq := memLp_indicator_const (μ := nativeDualMeasure u v s) (2 : ENNReal)
    hS (1 : ℂ) (Or.inr hμS)
  let q : NativeDualFiber u v s := hq.toLp (S.indicator (fun _ => (1 : ℂ)))
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let η := ε / (‖q‖+1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro t ht
  have htδ : ‖t‖ < δ := by simpa using (lt_min_iff.mp ht).1
  have ht1 : ‖t‖ < 1 := by simpa using (lt_min_iff.mp ht).2
  have hb : ‖nativeTranslation u v s hs t f - f‖ ≤ η*‖q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul (g := q)
    have htcoe : (fun x => nativeTranslation u v s hs t f x) =ᵐ[nativeDualMeasure u v s]
        (fun x => f (x+t)) := native_translation_coe u v s t hs f
    filter_upwards [Lp.coeFn_sub (nativeTranslation u v s hs t f) f,
      htcoe, native_translation_ae u v s t hs hfg, hfg, hq.coeFn_toLp]
      with x hsub htrans hshift hx hqx
    simp only [Pi.sub_apply] at hsub
    change ‖(nativeTranslation u v s hs t f - f) x‖ ≤ η * ‖q x‖
    rw [hsub, htrans, hshift, hx]
    change ‖g (x+t)-g x‖ ≤ η * ‖hq.toLp _ x‖
    rw [hqx]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS, norm_one, mul_one]
      have hd : dist (x+t) x < δ := by simpa [dist_eq_norm] using htδ
      have hsmall : ‖g (x+t)-g x‖ < η := by
        simpa only [dist_eq_norm] using hmod hd
      exact hsmall.le
    · have hxnorm : R+1 < ‖x‖ := by
        simpa only [S, Metric.mem_closedBall, dist_zero_right, not_le] using hxS
      have htri : ‖x‖ ≤ ‖x+t‖+‖t‖ := by
        simpa only [add_sub_cancel_right] using norm_sub_le (x+t) t
      have hz1 := hsupport x (by linarith : R ≤ ‖x‖)
      have hz2 := hsupport (x+t) (by linarith : R ≤ ‖x+t‖)
      simp [hz1, hz2, Set.indicator_of_notMem hxS]
  rw [nativeTranslation_zero, dist_eq_norm]
  apply hb.trans_lt
  have heq : η * (‖q‖+1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

#check nativeTranslation_continuousAt_zero_of_core
#print axioms nativeTranslation_continuousAt_zero_of_core
end Round196D


namespace Round196C
open MeasureTheory Round195D Round196D Filter
open scoped Topology

/-- Density extension for the exact remaining native group-continuity premise.
D still owes continuity at zero on compact smooth representatives. -/
theorem native_translation_tendsto_zero_of_dense
    (u v s : ℝ) (hs : 0 ≤ s)
    (S : Set (NativeDualFiber u v s)) (hS : Dense S)
    (hcore : ∀ g ∈ S, Tendsto (fun t : ℝ => nativeTranslation u v s hs t g)
      (𝓝 0) (𝓝 g)) (f : NativeDualFiber u v s) :
    Tendsto (fun t : ℝ => nativeTranslation u v s hs t f) (𝓝 0) (𝓝 f) := by
  let beta := max |u| |v|+s/4
  let M := Real.exp beta
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hM : 0 < M := Real.exp_pos _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hS f) δ hδ
  have hc := Metric.tendsto_nhds.mp (hcore g hg) (ε/2) (by positivity)
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
    simpa only [Metric.ball, Set.mem_setOf_eq, Real.dist_eq, sub_zero] using
      (Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1))
  filter_upwards [hc, ht] with t htg ht
  have hlocal : ‖nativeTranslation u v s hs t (f-g)‖ ≤ M*‖f-g‖ := by
    apply (nativeTranslation_bound u v s t hs (f-g)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    change beta*|t| ≤ beta
    nlinarith
  have hnorm : ‖f-g‖ < δ := by simpa only [dist_eq_norm] using hfg
  have hgf : ‖g-f‖ < δ := by simpa only [norm_sub_rev] using hnorm
  have hstep : ‖nativeTranslation u v s hs t f - f‖ ≤
      M*‖f-g‖ + ‖nativeTranslation u v s hs t g-g‖ + ‖g-f‖ := by
    calc
      _ = ‖nativeTranslation u v s hs t (f-g) +
          (nativeTranslation u v s hs t g-g) + (g-f)‖ := by
        congr 1
        rw [map_sub]
        abel
      _ ≤ ‖nativeTranslation u v s hs t (f-g)‖ +
          ‖nativeTranslation u v s hs t g-g‖ + ‖g-f‖ := norm_add₃_le
      _ ≤ _ := by linarith [hlocal]
  have hd : (M+1)*δ = ε/2 := by
    dsimp [δ]
    field_simp [ne_of_gt (show 0 < M+1 by positivity)]
    <;> ring
  rw [dist_eq_norm] at htg ⊢
  have hmul : M*‖f-g‖ < M*δ := mul_lt_mul_of_pos_left hnorm hM
  nlinarith

#check native_translation_tendsto_zero_of_dense
#print axioms native_translation_tendsto_zero_of_dense
end Round196C

namespace Round196C
open MeasureTheory Round195D Round196D Filter
open scoped Topology ContDiff

theorem native_translation_continuous_of_smooth_core
    (u v s : ℝ) (hs : 0 ≤ s)
    (hcore : ∀ (f : NativeDualFiber u v s) (g : ℝ → ℂ),
      (fun x => f x) =ᵐ[nativeDualMeasure u v s] g →
      HasCompactSupport g → ContDiff ℝ ∞ g →
      Tendsto (fun t : ℝ => nativeTranslation u v s hs t f) (𝓝 0) (𝓝 f))
    (f : NativeDualFiber u v s) :
    Continuous (fun t : ℝ => nativeTranslation u v s hs t f) := by
  have hzero := native_translation_tendsto_zero_of_dense u v s hs
    _ (native_smooth_compact_core_dense u v s)
    (fun g hg => by
      obtain ⟨k, heq, hcomp, hdiff⟩ := hg
      exact hcore g k heq hcomp hdiff) f
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have ht : Tendsto (fun t : ℝ => t-t₀) (𝓝 t₀) (𝓝 0) := by
    simpa only [sub_self] using
      (show Continuous (fun t : ℝ => t-t₀) from continuous_id.sub continuous_const).tendsto t₀
  have hh := ((nativeTranslation u v s hs t₀).continuous.tendsto f).comp
    (hzero.comp ht)
  simpa only [Function.comp_def, nativeTranslation_group, sub_add_cancel] using hh

#check native_translation_continuous_of_smooth_core
#print axioms native_translation_continuous_of_smooth_core
end Round196C

namespace Round196D
open MeasureTheory Round195D

theorem nativeTranslation_continuous (u v s : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    Continuous (fun t : ℝ => nativeTranslation u v s hs t f) := by
  apply Round196C.native_translation_continuous_of_smooth_core u v s hs _ f
  intro f g hfg hcomp hdiff
  simpa only [ContinuousAt, nativeTranslation_zero] using
    nativeTranslation_continuousAt_zero_of_core u v s hs f g hfg hdiff.continuous hcomp

#check nativeTranslation_continuous
#print axioms nativeTranslation_continuous
end Round196D

namespace Round196F
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem schwartz_coercive_term_bound (f : SchwartzMap E ℂ) (n : ℕ)
    (x z : E) (r : ℝ) (hr : 0 < r) (hz : z ≠ 0)
    (hscale : r * ‖z‖ ≤ ‖x‖) :
    ‖f x‖ ≤ (SchwartzMap.seminorm ℝ n 0 f) * r⁻¹ ^ n * ‖z‖⁻¹ ^ n := by
  have hbase : 0 < r * ‖z‖ := mul_pos hr (norm_pos_iff.mpr hz)
  have hpow : (r * ‖z‖)^n * ‖f x‖ ≤ SchwartzMap.seminorm ℝ n 0 f :=
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hbase.le hscale n) (norm_nonneg _)).trans
      (SchwartzMap.norm_pow_mul_le_seminorm ℝ f n x)
  calc
    ‖f x‖ ≤ SchwartzMap.seminorm ℝ n 0 f / (r * ‖z‖)^n :=
      (le_div_iff₀ (pow_pos hbase n)).mpr (by nlinarith [hpow])
    _ = _ := by simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow]; ring

/-- Actual infinite Schwartz lattice sum, with summability derived from
ZLattice.summable_norm_pow_inv. The input hscale is geometric coercivity,
not a theta bound, scalar moment, or spectral summability assumption. -/
theorem schwartz_lattice_norm_sum_decay
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (n : ℕ) (hn : Module.finrank ℤ L < n)
    {C : Type*} (T : ℝ → C → E → E) (c delta B : ℝ) (hc : 0 < c)
    (hB : B ≤ (n : ℝ) * delta)
    (hscale : ∀ t, 0 ≤ t → ∀ y (x : L),
      c * Real.exp (delta*t) * ‖x‖ ≤ ‖T t y x‖) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t, 0 ≤ t → ∀ y,
      Summable (fun x : {x : L // x ≠ 0} => ‖f (T t y x.1)‖) ∧
      (∑' x : {x : L // x ≠ 0}, ‖f (T t y x.1)‖) ≤
        P * Real.exp (-B*t) := by
  let S := SchwartzMap.seminorm ℝ n 0 f
  let w : {x : L // x ≠ 0} → ℝ := fun x => ‖x.1‖⁻¹ ^ n
  have hw : Summable w :=
    (ZLattice.summable_norm_pow_inv L n hn).subtype {x : L | x ≠ 0}
  have hw0 : ∀ x, 0 ≤ w x := by intro x; positivity
  have hS : 0 ≤ S := (mul_nonneg (pow_nonneg (norm_nonneg (0 : E)) n)
    (norm_nonneg (f 0))).trans (SchwartzMap.norm_pow_mul_le_seminorm ℝ f n 0)
  refine ⟨S * c⁻¹^n * ∑' x, w x, by positivity, ?_⟩
  intro t ht y
  have hterm (x : {x : L // x ≠ 0}) :
      ‖f (T t y x.1)‖ ≤ (S * c⁻¹^n * Real.exp (-B*t)) * w x := by
    have hx : (x.1 : E) ≠ 0 := by
      intro he
      apply x.2
      exact Subtype.ext he
    have hp := schwartz_coercive_term_bound f n (T t y x.1) x.1
      (c * Real.exp (delta*t)) (mul_pos hc (Real.exp_pos _)) hx (hscale t ht y x.1)
    have he : Real.exp (-((n : ℝ)*delta)*t) ≤ Real.exp (-B*t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc
      ‖f (T t y x.1)‖ ≤ S * (c * Real.exp (delta*t))⁻¹^n * ‖(x.1 : E)‖⁻¹^n := hp
      _ = (S * c⁻¹^n * Real.exp (-((n : ℝ)*delta)*t)) * w x := by
        change S * (c * Real.exp (delta*t))⁻¹^n * ‖(x.1 : E)‖⁻¹^n =
          (S * c⁻¹^n * Real.exp (-((n : ℝ)*delta)*t)) * ‖(x.1 : E)‖⁻¹^n
        rw [mul_inv_rev, mul_pow, ← Real.exp_neg, ← Real.exp_nat_mul]
        have heq : (n : ℝ) * -(delta*t) = -((n : ℝ)*delta)*t := by ring
        rw [heq]
        ring
      _ ≤ (S * c⁻¹^n * Real.exp (-B*t)) * w x := by gcongr
  have hmajor : Summable (fun x => (S * c⁻¹^n * Real.exp (-B*t)) * w x) :=
    hw.mul_left _
  have hs : Summable (fun x : {x : L // x ≠ 0} => ‖f (T t y x.1)‖) :=
    hmajor.of_norm_bounded (fun x => by simpa only [norm_norm] using hterm x)
  refine ⟨hs, ?_⟩
  calc
    ∑' x : {x : L // x ≠ 0}, ‖f (T t y x.1)‖ ≤
        ∑' x, (S * c⁻¹^n * Real.exp (-B*t)) * w x :=
      hs.tsum_le_tsum hterm hmajor
    _ = (S * c⁻¹^n * ∑' x, w x) * Real.exp (-B*t) := by
      rw [tsum_mul_left]
      ring

theorem schwartz_lattice_theta_decay
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (n : ℕ) (hn : Module.finrank ℤ L < n)
    {C : Type*} (T : ℝ → C → E → E) (c delta B : ℝ) (hc : 0 < c)
    (hB : B ≤ (n : ℝ) * delta)
    (hscale : ∀ t, 0 ≤ t → ∀ y (x : L),
      c * Real.exp (delta*t) * ‖x‖ ≤ ‖T t y x‖) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t, 0 ≤ t → ∀ y,
      Summable (fun x : {x : L // x ≠ 0} => ‖f (T t y x.1)‖) ∧
      ‖∑' x : {x : L // x ≠ 0}, f (T t y x.1)‖ ≤
        P * Real.exp (-B*t) := by
  obtain ⟨P, hP, hp⟩ := schwartz_lattice_norm_sum_decay L f n hn T c delta B hc hB hscale
  refine ⟨P, hP, ?_⟩
  intro t ht y
  exact ⟨(hp t ht y).1, (norm_tsum_le_tsum_norm (hp t ht y).1).trans (hp t ht y).2⟩

#check schwartz_coercive_term_bound
#print axioms schwartz_coercive_term_bound
#check schwartz_lattice_theta_decay
#print axioms schwartz_lattice_theta_decay
end Round196F

namespace Round196F
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Combines two proved Schwartz lattice estimates with the zero-mass Poisson
identity. This produces F195/C195's theta-envelope argument rather than taking
that envelope as input. Native adelic lattice and Poisson identities remain
explicit realization obligations. -/
theorem theta_decay_of_lattice_poisson
    (L Ldual : Submodule ℤ E) [DiscreteTopology L] [DiscreteTopology Ldual]
    (f fdual : SchwartzMap E ℂ) (n m : ℕ)
    (hn : Module.finrank ℤ L < n) (hm : Module.finrank ℤ Ldual < m)
    {C : Type*} (T Tdual : ℝ → C → E → E) (invC : C → C)
    (c d delta epsilon B : ℝ) (hc : 0 < c) (hd : 0 < d)
    (hB : B ≤ (n : ℝ)*delta) (hBdual : B+1 ≤ (m : ℝ)*epsilon)
    (hscale : ∀ t, 0 ≤ t → ∀ y (x : L),
      c * Real.exp (delta*t) * ‖x‖ ≤ ‖T t y x‖)
    (hscaleDual : ∀ t, 0 ≤ t → ∀ y (x : Ldual),
      d * Real.exp (epsilon*t) * ‖x‖ ≤ ‖Tdual t y x‖)
    (Φ : ℝ → C → ℂ)
    (hpos : ∀ t, 0 ≤ t → ∀ y,
      Φ t y = ∑' x : {x : L // x ≠ 0}, f (T t y x.1))
    (hpoisson : ∀ t, t < 0 → ∀ y,
      Φ t y = (Real.exp (-t) : ℂ) *
        ∑' x : {x : Ldual // x ≠ 0}, fdual (Tdual (-t) (invC y) x.1)) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t y, ‖Φ t y‖ ≤ P * Real.exp (-B*|t|) := by
  obtain ⟨P, hP, hp⟩ := schwartz_lattice_theta_decay L f n hn T c delta B hc hB hscale
  obtain ⟨Q, hQ, hq⟩ := schwartz_lattice_theta_decay Ldual fdual m hm Tdual d epsilon
    (B+1) hd hBdual hscaleDual
  refine ⟨P+Q, add_nonneg hP hQ, ?_⟩
  intro t y
  by_cases ht : 0 ≤ t
  · rw [hpos t ht y, abs_of_nonneg ht]
    exact ((hp t ht y).2).trans (by gcongr; linarith)
  · have ht0 : t < 0 := lt_of_not_ge ht
    have ht1 : 0 ≤ -t := neg_nonneg.mpr ht0.le
    rw [hpoisson t ht0 y, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_neg ht0]
    calc
      Real.exp (-t) * ‖∑' x : {x : Ldual // x ≠ 0},
          fdual (Tdual (-t) (invC y) x.1)‖ ≤
          Real.exp (-t) * (Q * Real.exp (-(B+1)*(-t))) := by
        exact mul_le_mul_of_nonneg_left (hq (-t) ht1 (invC y)).2 (Real.exp_pos _).le
      _ = Q * Real.exp (-B*(-t)) := by
        rw [show Real.exp (-t) * (Q * Real.exp (-(B+1)*(-t))) =
          Q * (Real.exp (-t) * Real.exp (-(B+1)*(-t))) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ (P+Q) * Real.exp (-B*(-t)) := by gcongr; linarith

#check theta_decay_of_lattice_poisson
#print axioms theta_decay_of_lattice_poisson
end Round196F

namespace Round196F
/-- Exact anisotropic expansion of a finite product of archimedean normed
spaces. The slowest place exponent is retained explicitly. -/
theorem diagonal_section_coercive
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (q : ι → ℝ) (delta t : ℝ) (ht : 0 ≤ t) (hq : ∀ i, delta ≤ q i)
    (x : ∀ i, F i) :
    Real.exp (delta*t) * ‖x‖ ≤ ‖fun i => Real.exp (q i*t) • x i‖ := by
  have heq : Real.exp (delta*t) * ‖x‖ = ‖Real.exp (delta*t) • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [heq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  calc
    ‖(Real.exp (delta*t) • x) i‖ = Real.exp (delta*t) * ‖x i‖ := by
      simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (q i*t) * ‖x i‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hq i) ht)
    _ = ‖Real.exp (q i*t) • x i‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ ‖fun j => Real.exp (q j*t) • x j‖ :=
      norm_le_pi_norm (G := F) (fun j => Real.exp (q j*t) • x j) i
#check diagonal_section_coercive
#print axioms diagonal_section_coercive
end Round196F

namespace Round196F
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The finite adelic factors may vary over lattice points. Their uniform
bound is retained, so the analytic estimate does not require an unramified
constant finite factor or a single unweighted theta equality. -/
theorem weighted_schwartz_lattice_theta_decay
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (n : ℕ) (hn : Module.finrank ℤ L < n)
    {C : Type*} (T : ℝ → C → E → E) (c delta B V : ℝ) (hc : 0 < c) (hV : 0 ≤ V)
    (hB : B ≤ (n : ℝ) * delta)
    (hscale : ∀ t, 0 ≤ t → ∀ y (x : L),
      c * Real.exp (delta*t) * ‖x‖ ≤ ‖T t y x‖)
    (q : ℝ → C → L → ℂ) (hq : ∀ t y x, ‖q t y x‖ ≤ V) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t, 0 ≤ t → ∀ y,
      ‖∑' x : {x : L // x ≠ 0}, q t y x.1 * f (T t y x.1)‖ ≤
        P * Real.exp (-B*t) := by
  obtain ⟨P, hP, hp⟩ := schwartz_lattice_norm_sum_decay L f n hn T c delta B hc hB hscale
  refine ⟨V*P, mul_nonneg hV hP, ?_⟩
  intro t ht y
  have hmajor := (hp t ht y).1.mul_left V
  have hb (x : {x : L // x ≠ 0}) :
      ‖q t y x.1 * f (T t y x.1)‖ ≤ V * ‖f (T t y x.1)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hq t y x.1) (norm_nonneg _)
  have hs : Summable (fun x : {x : L // x ≠ 0} => ‖q t y x.1 * f (T t y x.1)‖) :=
    hmajor.of_norm_bounded (fun x => by simpa only [norm_norm] using hb x)
  apply (norm_tsum_le_tsum_norm hs).trans
  calc
    _ ≤ ∑' x : {x : L // x ≠ 0}, V * ‖f (T t y x.1)‖ := hs.tsum_le_tsum hb hmajor
    _ = V * ∑' x : {x : L // x ≠ 0}, ‖f (T t y x.1)‖ := tsum_mul_left
    _ ≤ V * (P * Real.exp (-B*t)) := mul_le_mul_of_nonneg_left (hp t ht y).2 hV
    _ = _ := by ring

#check schwartz_lattice_norm_sum_decay
#print axioms schwartz_lattice_norm_sum_decay
#check weighted_schwartz_lattice_theta_decay
#print axioms weighted_schwartz_lattice_theta_decay
end Round196F


namespace Round197C
open MeasureTheory Round188D Round195D Round196D

/-- The exact native domain application with all translation hypotheses proved. -/
theorem native_seed_generator_domain
    (u v s : ℝ) (hs : 0 ≤ s)
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a P : ℝ) (hκ : 0 ≤ κ) (hP : 0 ≤ P)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hχm : StronglyMeasurable χ) (hχ : ∀ y, ‖χ y‖ = 1)
    (z : ℂ) (x : NativeDualFiber u v s)
    (hdecay : ∀ t y, ‖Φ t y‖ ≤ P *
      Real.exp (-(|a|+(|z.re|+(max |u| |v|+s/4))+2)*|t|)) :
    HasDerivAt (fun r : ℝ => nativeTranslation u v s hs r
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit (nativeTranslation u v s hs) z t x))
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit (nativeTranslation u v s hs) z t x +
          nativeTranslation u v s hs t x -
          Complex.exp (z * (t : ℂ)) • x)) 0 := by
  exact Round196C.native_normalized_seed_generator_domain u v s hs
    (nativeTranslation_continuous u v s hs)
    μ κ a P hκ hP Φ χ hΦ hχm hχ z x hdecay

#check native_seed_generator_domain
#print axioms native_seed_generator_domain

/-- Join F's proved envelope to the actual weighted translation domain theorem.
The adelic realization arguments remain explicit; no theta decay, moment,
graph integrability, strong continuity or nuclearity hypothesis is supplied. -/
theorem lattice_poisson_seed_generator_domain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (u v s : ℝ) (hs : 0 ≤ s)
    {C : Type*} [MeasurableSpace C] (μ : Measure C) [IsProbabilityMeasure μ]
    (κ a : ℝ) (hκ : 0 ≤ κ)
    (L Ldual : Submodule ℤ E) [DiscreteTopology L] [DiscreteTopology Ldual]
    (f fdual : SchwartzMap E ℂ) (n m : ℕ)
    (hn : Module.finrank ℤ L < n) (hm : Module.finrank ℤ Ldual < m)
    (T Tdual : ℝ → C → E → E) (invC : C → C)
    (c d delta epsilon : ℝ) (hc : 0 < c) (hd : 0 < d)
    (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : StronglyMeasurable (Function.uncurry Φ))
    (hχm : StronglyMeasurable χ) (hχ : ∀ y, ‖χ y‖ = 1)
    (z : ℂ) (x : NativeDualFiber u v s)
    (hB : |a|+(|z.re|+(max |u| |v|+s/4))+2 ≤ (n : ℝ)*delta)
    (hBdual : (|a|+(|z.re|+(max |u| |v|+s/4))+2)+1 ≤ (m : ℝ)*epsilon)
    (hscale : ∀ t, 0 ≤ t → ∀ y (x : L),
      c * Real.exp (delta*t) * ‖x‖ ≤ ‖T t y x‖)
    (hscaleDual : ∀ t, 0 ≤ t → ∀ y (x : Ldual),
      d * Real.exp (epsilon*t) * ‖x‖ ≤ ‖Tdual t y x‖)
    (hpos : ∀ t, 0 ≤ t → ∀ y,
      Φ t y = ∑' x : {x : L // x ≠ 0}, f (T t y x.1))
    (hpoisson : ∀ t, t < 0 → ∀ y,
      Φ t y = (Real.exp (-t) : ℂ) *
        ∑' x : {x : Ldual // x ≠ 0}, fdual (Tdual (-t) (invC y) x.1)) :
    HasDerivAt (fun r : ℝ => nativeTranslation u v s hs r
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit (nativeTranslation u v s hs) z t x))
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit (nativeTranslation u v s hs) z t x +
          nativeTranslation u v s hs t x -
          Complex.exp (z * (t : ℂ)) • x)) 0 := by
  obtain ⟨P, hP, hdecay⟩ := Round196F.theta_decay_of_lattice_poisson
    L Ldual f fdual n m hn hm T Tdual invC c d delta epsilon
    (|a|+(|z.re|+(max |u| |v|+s/4))+2) hc hd hB hBdual
    hscale hscaleDual Φ hpos hpoisson
  exact native_seed_generator_domain u v s hs μ κ a P hκ hP
    Φ χ hΦ hχm hχ z x hdecay

#check lattice_poisson_seed_generator_domain
#print axioms lattice_poisson_seed_generator_domain
end Round197C
