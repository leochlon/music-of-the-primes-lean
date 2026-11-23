import Mathlib

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


namespace Round194A
set_option linter.unusedSectionVars false
open MeasureTheory Filter Round188D
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- Ordinary measured seed moments imply integrability of the complete
native divided-orbit vector and graph vector. No spectral sums occur. -/
theorem seed_graph_integrable
    (k : ℝ → ℂ) (V Ux Ex : ℝ → E) (z : ℂ)
    (b d : ℝ → ℝ)
    (hV : AEStronglyMeasurable (fun t => k t • V t))
    (hU : AEStronglyMeasurable (fun t => k t • Ux t))
    (hE : AEStronglyMeasurable (fun t => k t • Ex t))
    (hb : Integrable b) (hd : Integrable d)
    (hVb : ∀ t, ‖k t‖ * ‖V t‖ ≤ b t)
    (hUb : ∀ t, ‖k t‖ * ‖Ux t‖ ≤ d t)
    (hEb : ∀ t, ‖k t‖ * ‖Ex t‖ ≤ d t) :
    Integrable (fun t => k t • V t) ∧
    Integrable (fun t => k t • (z • V t + Ux t - Ex t)) := by
  have hiV : Integrable (fun t => k t • V t) :=
    hb.mono' hV (Eventually.of_forall fun t => by simpa only [norm_smul] using hVb t)
  have hiU : Integrable (fun t => k t • Ux t) :=
    hd.mono' hU (Eventually.of_forall fun t => by simpa only [norm_smul] using hUb t)
  have hiE : Integrable (fun t => k t • Ex t) :=
    hd.mono' hE (Eventually.of_forall fun t => by simpa only [norm_smul] using hEb t)
  refine ⟨hiV, ?_⟩
  convert ((hiV.smul z).add hiU).sub hiE using 1
  ext t
  simp only [smul_sub, smul_add, smul_comm (k t) z, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]

#check seed_graph_integrable
#print axioms seed_graph_integrable

/-- The divided orbit has an explicit native growth envelope. The only
operator estimate is the weighted translation bound, not a spectral bound. -/
theorem divided_orbit_native_envelope
    (U : ℝ → E →L[ℂ] E) (β : ℝ) (hβ : 0 ≤ β)
    (hU : ∀ t x, ‖U t x‖ ≤ Real.exp (β * |t|) * ‖x‖)
    (z : ℂ) (t : ℝ) (x : E) :
    ‖dividedGroupOrbit U z t x‖ ≤
      |t| * Real.exp ((β + ‖z‖) * |t|) * ‖x‖ := by
  unfold dividedGroupOrbit
  have hb : ∀ v ∈ Set.uIoc (0 : ℝ) t,
      ‖Complex.exp (z * ((t-v : ℝ) : ℂ)) • U v x‖ ≤
        Real.exp ((β + ‖z‖) * |t|) * ‖x‖ := by
    intro v hv
    change min (0 : ℝ) t < v ∧ v ≤ max (0 : ℝ) t at hv
    have hvabs : |v| ≤ |t| := by
      rcases le_total 0 t with ht | ht
      · rw [min_eq_left ht, max_eq_right ht] at hv
        simpa [abs_of_nonneg (le_of_lt hv.1), abs_of_nonneg ht] using hv.2
      · rw [min_eq_right ht, max_eq_left ht] at hv
        rw [abs_of_nonpos hv.2, abs_of_nonpos ht]
        linarith [hv.1]
    have htabs : |t-v| ≤ |t| := by
      rcases le_total 0 t with ht | ht
      · rw [min_eq_left ht, max_eq_right ht] at hv
        rw [abs_of_nonneg (sub_nonneg.mpr hv.2), abs_of_nonneg ht]
        linarith [hv.1]
      · rw [min_eq_right ht, max_eq_left ht] at hv
        rw [abs_of_nonpos (by linarith [hv.1]), abs_of_nonpos ht]
        linarith [hv.2]
    have hz : (z * ((t-v : ℝ) : ℂ)).re ≤ ‖z‖ * |t| := by
      calc
        _ ≤ ‖z * ((t-v : ℝ) : ℂ)‖ := Complex.re_le_norm _
        _ = ‖z‖ * |t-v| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ * |t| := mul_le_mul_of_nonneg_left htabs (norm_nonneg z)
    calc
      _ = Real.exp ((z * ((t-v : ℝ) : ℂ)).re) * ‖U v x‖ := by
        rw [norm_smul, Complex.norm_exp]
      _ ≤ Real.exp (‖z‖ * |t|) * (Real.exp (β * |v|) * ‖x‖) := by
        gcongr
        exact hU v x
      _ ≤ Real.exp (‖z‖ * |t|) * (Real.exp (β * |t|) * ‖x‖) := by
        gcongr
      _ = Real.exp ((β + ‖z‖) * |t|) * ‖x‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa only [sub_zero, mul_assoc, mul_left_comm, mul_comm] using hi

#check divided_orbit_native_envelope
#print axioms divided_orbit_native_envelope
end Round194A


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


namespace Round193C

theorem completed_zero_tail_shift (x T t : ℝ)
    (hx : 0 < x) (hT : 0 < T) (ht : T ^ 2 ≤ t ^ 2) :
    x / (x ^ 2 + t ^ 2) ≤
      (3 * x / T) * ((x + T) / ((x + T) ^ 2 + t ^ 2)) := by
  have hA : 0 < x ^ 2 + t ^ 2 := by positivity
  have hB : 0 < (x + T) ^ 2 + t ^ 2 := by positivity
  have hshape : (x + T) ^ 2 + t ^ 2 ≤ 3 * (x ^ 2 + t ^ 2) := by
    nlinarith [sq_nonneg (x - T), sq_nonneg x]
  have hcomp : T * ((x + T) ^ 2 + t ^ 2) ≤
      3 * (x + T) * (x ^ 2 + t ^ 2) := by
    calc
      _ ≤ T * (3 * (x ^ 2 + t ^ 2)) := mul_le_mul_of_nonneg_left hshape hT.le
      _ ≤ 3 * (x + T) * (x ^ 2 + t ^ 2) := by nlinarith
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hA (mul_pos hT hB)).2
  nlinarith [mul_le_mul_of_nonneg_left hcomp hx.le]

#check completed_zero_tail_shift
#print axioms completed_zero_tail_shift
end Round193C



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

/-! Round 193 E: the exact native logarithmic-weight quadratic form.
This certifies the coefficient bound in the native integration-by-parts
numerical-range argument; it is not itself a nuclearity theorem. -/
namespace Round193E
set_option linter.unnecessarySeqFocus false
open MeasureTheory

def branchWeight (b s x : ℝ) : ℝ :=
  Real.exp (-2*b*x - (s/2)*Real.log (1+x^2))

def nativeWeight (u v s x : ℝ) : ℝ :=
  if x < 0 then branchWeight u s x else branchWeight v s x

def nativeEnergyCoefficient (u v s x : ℝ) : ℝ :=
  (if x < 0 then u else v) + s*x/(2*(1+x^2))

theorem native_weight_eq_log_formula (u v s x : ℝ) (huv : u ≤ v) :
    nativeWeight u v s x =
      Real.exp (-2*max (u*x) (v*x) - (s/2)*Real.log (1+x^2)) := by
  by_cases hx : x < 0
  · have hh : v*x ≤ u*x := mul_le_mul_of_nonpos_right huv hx.le
    simp [nativeWeight, branchWeight, hx, max_eq_left hh, mul_assoc]
  · have hh : u*x ≤ v*x := mul_le_mul_of_nonneg_right huv (le_of_not_gt hx)
    simp [nativeWeight, branchWeight, hx, max_eq_right hh, mul_assoc]

theorem branch_weight_hasDerivAt (b s x : ℝ) :
    HasDerivAt (branchWeight b s)
      ((-2*b-s*x/(1+x^2))*branchWeight b s x) x := by
  have hp : (0 : ℝ) < 1+x^2 := by positivity
  have hl := (((hasDerivAt_id x).pow 2).const_add 1).log (ne_of_gt hp)
  have he := (((hasDerivAt_id x).const_mul (-2*b)).sub (hl.const_mul (s/2))).exp
  convert he using 1 <;> dsimp [branchWeight] <;> ring

theorem native_coefficient_bound (u v s x : ℝ) (hs : 0 ≤ s) :
    |nativeEnergyCoefficient u v s x| ≤ max |u| |v| + s/4 := by
  have hd : (0 : ℝ) < 1+x^2 := by positivity
  have hx : |x| ≤ (1+x^2)/2 := by
    have h1 := sq_nonneg (|x|-1)
    nlinarith [sq_abs x]
  have hp : |s*x/(2*(1+x^2))| ≤ s/4 := by
    rw [abs_div, abs_mul, abs_of_nonneg hs, abs_of_pos (by positivity : (0:ℝ)<2*(1+x^2))]
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2*(1+x^2))).2
    nlinarith [mul_le_mul_of_nonneg_left hx hs]
  have hb : |(if x < 0 then u else v)| ≤ max |u| |v| := by
    split_ifs <;> simp only [le_max_left, le_max_right]
  exact (abs_add_le _ _).trans (add_le_add hb hp)

theorem native_weight_energy_bound (u v s : ℝ) (hs : 0 ≤ s)
    (f : ℝ → ℂ) (hf : Measurable f)
    (hi : Integrable (fun x : ℝ => ‖f x‖^2 * nativeWeight u v s x)) :
    |∫ x : ℝ, nativeEnergyCoefficient u v s x *
        (‖f x‖^2 * nativeWeight u v s x)| ≤
      (max |u| |v| + s/4) *
        ∫ x : ℝ, ‖f x‖^2 * nativeWeight u v s x := by
  let B := max |u| |v| + s/4
  let d : ℝ → ℝ := fun x => ‖f x‖^2 * nativeWeight u v s x
  have hd (x : ℝ) : 0 ≤ d x := by
    dsimp [d, nativeWeight, branchWeight]
    split_ifs <;> positivity
  have hm : Measurable (fun x : ℝ => nativeEnergyCoefficient u v s x * d x) := by
    have hbranch (b : ℝ) : Measurable (fun x : ℝ =>
        (b+s*x/(2*(1+x^2))) * (‖f x‖^2 * branchWeight b s x)) := by
      dsimp [branchWeight]
      fun_prop
    have hh : Measurable (fun x : ℝ => if x < 0 then
        (u+s*x/(2*(1+x^2))) * (‖f x‖^2 * branchWeight u s x) else
        (v+s*x/(2*(1+x^2))) * (‖f x‖^2 * branchWeight v s x)) := by
      apply Measurable.ite
      all_goals first | exact measurableSet_Iio | exact hbranch u | exact hbranch v
    convert hh using 1
    ext x
    dsimp [nativeEnergyCoefficient, d, nativeWeight]
    split_ifs <;> rfl
  have hb (x : ℝ) : ‖nativeEnergyCoefficient u v s x * d x‖ ≤ B*d x := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hd x)]
    exact mul_le_mul_of_nonneg_right (native_coefficient_bound u v s x hs) (hd x)
  have hib : Integrable (fun x : ℝ => B*d x) := hi.const_mul B
  have hie : Integrable (fun x : ℝ => nativeEnergyCoefficient u v s x * d x) :=
    hib.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  calc
    _ = ‖∫ x : ℝ, nativeEnergyCoefficient u v s x * d x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x : ℝ, ‖nativeEnergyCoefficient u v s x * d x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, B*d x := integral_mono hie.norm hib hb
    _ = _ := integral_const_mul B d

#check native_weight_eq_log_formula
#print axioms native_weight_eq_log_formula
#check branch_weight_hasDerivAt
#print axioms branch_weight_hasDerivAt
#check native_coefficient_bound
#print axioms native_coefficient_bound
#check native_weight_energy_bound
#print axioms native_weight_energy_bound
end Round193E

/-! E194: exact native integration by parts. The two endpoints at zero
cancel because the ACTUAL branch weights both equal one. This supplies the
numerical-range equality needed by D182, under explicit regularity and
ordinary boundary-flux hypotheses, not spectral summability. -/
namespace Round194E
set_option linter.unnecessarySeqFocus false
open MeasureTheory Filter Set Round193E
open scoped Topology

def density (p r : ℝ → ℝ) (x : ℝ) : ℝ := (p x)^2 + (r x)^2

def cross (p r p' r' : ℝ → ℝ) (x : ℝ) : ℝ := p x*p' x+r x*r' x

theorem branch_density_derivative (b s : ℝ) (p r p' r' : ℝ → ℝ)
    (x : ℝ) (hp : HasDerivAt p (p' x) x) (hr : HasDerivAt r (r' x) x) :
    HasDerivAt (fun y => density p r y * branchWeight b s y)
      (2 * (cross p r p' r' x -
        (b+s*x/(2*(1+x^2)))*density p r x) * branchWeight b s x) x := by
  have hd := ((hp.pow 2).add (hr.pow 2)).mul (branch_weight_hasDerivAt b s x)
  convert hd using 1 <;> dsimp [density, cross] <;> field_simp <;> ring

theorem native_weight_integration_by_parts
    (u v s : ℝ) (p r p' r' : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (p' x) x)
    (hr : ∀ x, HasDerivAt r (r' x) x)
    (hc : Integrable (fun x => cross p r p' r' x * nativeWeight u v s x))
    (he : Integrable (fun x => nativeEnergyCoefficient u v s x *
      density p r x * nativeWeight u v s x))
    (hleft : Tendsto (fun x => density p r x * branchWeight u s x)
      atBot (𝓝 0))
    (hright : Tendsto (fun x => density p r x * branchWeight v s x)
      atTop (𝓝 0)) :
    (∫ x : ℝ, cross p r p' r' x * nativeWeight u v s x) =
      ∫ x : ℝ, nativeEnergyCoefficient u v s x *
        density p r x * nativeWeight u v s x := by
  let J : ℝ → ℝ := fun x => 2 * (cross p r p' r' x * nativeWeight u v s x -
    nativeEnergyCoefficient u v s x * density p r x * nativeWeight u v s x)
  have hi : Integrable J := (hc.sub he).const_mul 2
  have hpc : Continuous p := continuous_iff_continuousAt.mpr (fun x => (hp x).continuousAt)
  have hrc : Continuous r := continuous_iff_continuousAt.mpr (fun x => (hr x).continuousAt)
  have hbc (b : ℝ) : Continuous (fun x => density p r x * branchWeight b s x) := by
    have hweight : Continuous (branchWeight b s) :=
      continuous_iff_continuousAt.mpr (fun x => (branch_weight_hasDerivAt b s x).continuousAt)
    exact ((hpc.pow 2).add (hrc.pow 2)).mul hweight
  have hdl (x : ℝ) (hx : x ∈ Iio (0 : ℝ)) :
      HasDerivAt (fun y => density p r y * branchWeight u s y) (J x) x := by
    have hx' : x < 0 := hx
    convert branch_density_derivative u s p r p' r' x (hp x) (hr x) using 1 <;>
      simp [J, nativeWeight, nativeEnergyCoefficient, hx'] <;> ring
  have hdr (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun y => density p r y * branchWeight v s y) (J x) x := by
    have hx' : ¬x < 0 := not_lt.mpr (le_of_lt hx)
    convert branch_density_derivative v s p r p' r' x (hp x) (hr x) using 1 <;>
      simp [J, nativeWeight, nativeEnergyCoefficient, hx'] <;> ring
  have hl := integral_Iic_of_hasDerivAt_of_tendsto
    (hbc u).continuousAt.continuousWithinAt hdl hi.integrableOn hleft
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto
    (hbc v).continuousAt.continuousWithinAt hdr hi.integrableOn hright
  have hz : (∫ x : ℝ, J x) = 0 := by
    have hu := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hi
    rw [compl_Iic] at hu
    rw [← hu, hl, hh]
    simp [branchWeight]
  dsimp [J] at hz
  rw [integral_const_mul, integral_sub hc he] at hz
  linarith

#check branch_density_derivative
#print axioms branch_density_derivative
#check native_weight_integration_by_parts
#print axioms native_weight_integration_by_parts
end Round194E



/-! Round 194 H: actual native weight transport. This is an input to the
native translation-group realization feeding C191's integrated seed-domain
lemma. It is not a theorem of global nuclearity. -/
noncomputable section
open MeasureTheory
namespace Round194H

def nativeWeight (u v s x : ℝ) : ℝ :=
  max (Real.exp (2*u*x)) (Real.exp (2*v*x)) * (1+x^2)^(s/2)

def translationCost (u v s t : ℝ) : ℝ :=
  Real.exp (2 * max |u| |v| * |t|) * ((1+|t|)^2)^(s/2)

theorem polynomial_native_shift (x t : ℝ) :
    1+(x+t)^2 ≤ (1+|t|)^2*(1+x^2) := by
  have hxt : x*t ≤ |x| *|t| := by simpa [abs_mul] using le_abs_self (x*t)
  have hx : 2*|x| ≤ 1+x^2 := by nlinarith [sq_nonneg (|x|-1), sq_abs x]
  have ht := abs_nonneg t
  have hp := mul_le_mul_of_nonneg_right hx ht
  nlinarith [sq_abs t, sq_nonneg (x*t)]

theorem native_weight_translation (u v s x t : ℝ) (hs : 0 ≤ s) :
    nativeWeight u v s (x+t) ≤ translationCost u v s t * nativeWeight u v s x := by
  let r := max |u| |v|
  have hu : u*t ≤ r*|t| := by
    calc
      u*t ≤ |u*t| := le_abs_self _
      _ = |u| *|t| := abs_mul _ _
      _ ≤ r*|t| := mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
  have hv : v*t ≤ r*|t| := by
    calc
      v*t ≤ |v*t| := le_abs_self _
      _ = |v| *|t| := abs_mul _ _
      _ ≤ r*|t| := mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)
  have he (b : ℝ) (hb : b*t ≤ r*|t|) :
      Real.exp (2*b*(x+t)) ≤ Real.exp (2*r*|t|)*Real.exp (2*b*x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hem : max (Real.exp (2*u*(x+t))) (Real.exp (2*v*(x+t))) ≤
      Real.exp (2*r*|t|) * max (Real.exp (2*u*x)) (Real.exp (2*v*x)) := by
    apply max_le
    · exact (he u hu).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le)
    · exact (he v hv).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le)
  have hp : (1+(x+t)^2)^(s/2) ≤ ((1+|t|)^2)^(s/2)*(1+x^2)^(s/2) := by
    calc
      _ ≤ ((1+|t|)^2*(1+x^2))^(s/2) :=
        Real.rpow_le_rpow (by positivity) (polynomial_native_shift x t) (by positivity)
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have h := mul_le_mul hem hp (by positivity : 0 ≤ (1+(x+t)^2)^(s/2))
    (by positivity : 0 ≤ Real.exp (2*r*|t|)*max (Real.exp (2*u*x)) (Real.exp (2*v*x)))
  dsimp [nativeWeight, translationCost]
  dsimp [r] at h
  nlinarith only [h]

theorem native_weight_pos (u v s x : ℝ) : 0 < nativeWeight u v s x := by
  unfold nativeWeight
  exact mul_pos (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _))
    (Real.rpow_pos_of_pos (by positivity) _)

theorem native_dual_weight_translation (u v s x t : ℝ) (hs : 0 ≤ s) :
    1 / nativeWeight u v s (x-t) ≤ translationCost u v s t / nativeWeight u v s x := by
  rw [div_le_div_iff₀ (native_weight_pos u v s (x-t)) (native_weight_pos u v s x)]
  simpa only [sub_add_cancel, one_mul] using native_weight_translation u v s (x-t) t hs

/-- The actual weighted quadratic norm under translation, with the original
Lebesgue log-Haar measure. Applied on each compact character fiber, whose
compact Haar mass is one, this extends U(t) to the native dual completion. -/
theorem native_dual_translation_integral
    (u v s t : ℝ) (hs : 0 ≤ s) (f : ℝ → ℂ) (hc : Continuous f)
    (hf : Integrable (fun x : ℝ => ‖f x‖^2 / nativeWeight u v s x)) :
    Integrable (fun x : ℝ => ‖f (x+t)‖^2 / nativeWeight u v s x) ∧
    (∫ x : ℝ, ‖f (x+t)‖^2 / nativeWeight u v s x) ≤
      translationCost u v s t * (∫ x : ℝ, ‖f x‖^2 / nativeWeight u v s x) := by
  let g : ℝ → ℝ := fun x => ‖f x‖^2 / nativeWeight u v s (x-t)
  have hfm : Measurable f := hc.measurable
  have hgm : AEStronglyMeasurable g := by
    apply Measurable.aestronglyMeasurable
    dsimp [g, nativeWeight]
    fun_prop
  have hb (x : ℝ) : g x ≤ translationCost u v s t * (‖f x‖^2 / nativeWeight u v s x) := by
    have h := mul_le_mul_of_nonneg_left (native_dual_weight_translation u v s x t hs)
      (sq_nonneg ‖f x‖)
    dsimp [g]
    convert h using 1 <;> ring
  have hg : Integrable g := by
    apply (hf.const_mul (translationCost u v s t)).mono' hgm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [g]; exact div_nonneg (sq_nonneg _) (native_weight_pos u v s (x-t)).le)]
    exact hb x
  constructor
  · simpa only [g, add_sub_cancel_right] using hg.comp_add_right t
  · have he : (∫ x : ℝ, ‖f (x+t)‖^2 / nativeWeight u v s x) = ∫ x : ℝ, g x := by
      simpa only [g, add_sub_cancel_right] using integral_add_right_eq_self g t
    rw [he]
    calc
      _ ≤ ∫ x : ℝ, translationCost u v s t * (‖f x‖^2 / nativeWeight u v s x) :=
        integral_mono hg (hf.const_mul _) hb
      _ = _ := integral_const_mul _ _

#check native_weight_translation
#print axioms native_weight_translation
#check native_dual_weight_translation
#print axioms native_dual_weight_translation
#check native_dual_translation_integral
#print axioms native_dual_translation_integral
end Round194H

/-! A195 assembly. This identifies the EXACT E/H native densities so E's
energy coefficient is usable on D's withDensity carrier. This discharges
NATIVE_WEIGHT_COMPATIBILITY, not the nuclear bound. The full target and
absent native definitions are recorded in INTEGRATION.md. -/
namespace Round195A
open MeasureTheory

/-- E's branch/log density is exactly the reciprocal manuscript weight
used by H's native translation norm. -/
theorem native_dual_weight_eq_reciprocal (u v s x : ℝ) (huv : u ≤ v) :
    Round193E.nativeWeight u v s x = 1 / Round194H.nativeWeight u v s x := by
  have hmax : max (Real.exp (2*u*x)) (Real.exp (2*v*x)) =
      Real.exp (2 * max (u*x) (v*x)) := by
    rcases le_total (u*x) (v*x) with h | h
    · have h2 : 2*u*x ≤ 2*v*x := by nlinarith
      rw [max_eq_right h, max_eq_right (Real.exp_le_exp.mpr h2)]
      congr 1
      ring
    · have h2 : 2*v*x ≤ 2*u*x := by nlinarith
      rw [max_eq_left h, max_eq_left (Real.exp_le_exp.mpr h2)]
      congr 1
      ring
  rw [Round193E.native_weight_eq_log_formula u v s x huv]
  unfold Round194H.nativeWeight
  rw [hmax, Real.rpow_def_of_pos (by positivity : (0:ℝ) < 1+x^2),
    ← Real.exp_add, one_div, ← Real.exp_neg]
  congr 1
  ring

/-- Concrete application of E193 to the original reciprocal weighted
norm in H194/D195. No unknown generator or spectral premise is assumed. -/
theorem native_energy_on_original_density (u v s : ℝ) (huv : u ≤ v)
    (hs : 0 ≤ s) (f : ℝ → ℂ) (hf : Measurable f)
    (hi : Integrable (fun x : ℝ => ‖f x‖^2 / Round194H.nativeWeight u v s x)) :
    |∫ x : ℝ, Round193E.nativeEnergyCoefficient u v s x *
        (‖f x‖^2 / Round194H.nativeWeight u v s x)| ≤
      (max |u| |v| + s/4) *
        ∫ x : ℝ, ‖f x‖^2 / Round194H.nativeWeight u v s x := by
  have he (x : ℝ) : ‖f x‖^2 * Round193E.nativeWeight u v s x =
      ‖f x‖^2 / Round194H.nativeWeight u v s x := by
    rw [native_dual_weight_eq_reciprocal u v s x huv]
    ring
  have hi' : Integrable (fun x : ℝ => ‖f x‖^2 * Round193E.nativeWeight u v s x) := by
    simpa only [he] using hi
  simpa only [he] using Round193E.native_weight_energy_bound u v s hs f hf hi'

#check native_dual_weight_eq_reciprocal
#print axioms native_dual_weight_eq_reciprocal
#check native_energy_on_original_density
#print axioms native_energy_on_original_density
end Round195A

/-
ACTUAL JOINED TARGET (specification only; these native definitions have not
been supplied, so this is deliberately not an axiom or an assumed theorem):

theorem actual_projected_nuclear_bound
    (K : Type*) [Field K] [NumberField K]
    (I : NativeInterval) (s a : ℝ) (phi : AdmissibleClassTest K)
    (hp : OriginalParameterRange K I s a) :
    ∀ h ∈ ({sharp phi, sharp (pointwiseEll phi)} : Set (ClassTest K)),
      ∃ C : ℝ, 0 ≤ C ∧
        nuclearNorm ((Pspec K I s a).comp (classConvolution K I s h)) ≤
          ENNReal.ofReal C

Absent: original class/native carrier and operator definitions; actual
seed and group realization; native contour/residue exhaustion; actual
completed-Hecke character/zero sum; infinite nuclear-series assembly.
No target-equivalent assumptions have been introduced.
-/



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


namespace Round195E
set_option linter.unusedSimpArgs false
open MeasureTheory Filter Set Round193E Round194E
open scoped Topology
set_option linter.unnecessarySeqFocus false

private theorem compact_support_of_vanish_outside
    (q : ℝ → ℝ) (R : ℝ) (hq : ∀ x, R < |x| → q x = 0) :
    HasCompactSupport q := by
  apply (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hab : |x| ≤ R := by
    by_contra h
    exact hx (hq x (lt_of_not_ge h))
  exact abs_le.mp hab

theorem native_core_energy_bound
    (u v s : ℝ) (huv : u ≤ v) (hs : 0 ≤ s)
    (p r p' r' : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (p' x) x)
    (hr : ∀ x, HasDerivAt r (r' x) x)
    (hp' : Continuous p') (hr' : Continuous r')
    (R : ℝ) (hps : ∀ x, R < |x| → p x = 0)
    (hrs : ∀ x, R < |x| → r x = 0) :
    |∫ x : ℝ, cross p r p' r' x * nativeWeight u v s x| ≤
      (max |u| |v| + s/4) *
        ∫ x : ℝ, density p r x * nativeWeight u v s x := by
  let w := nativeWeight u v s
  let d := density p r
  let B := max |u| |v| + s/4
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun x => (hp x).continuousAt
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun x => (hr x).continuousAt
  have hw : Continuous w := by
    have he : w = fun x => Real.exp
        (-2*max (u*x) (v*x) - (s/2)*Real.log (1+x^2)) := by
      funext x
      exact native_weight_eq_log_formula u v s x huv
    rw [he]
    have hl : Continuous (fun x : ℝ => Real.log (1+x^2)) :=
      (continuous_const.add (continuous_id.pow 2)).log
        (fun x => ne_of_gt (by positivity : (0:ℝ) < 1+x^2))
    have hm : Continuous (fun x : ℝ => max (u*x) (v*x)) :=
      (continuous_const.mul continuous_id).max (continuous_const.mul continuous_id)
    exact Real.continuous_exp.comp ((continuous_const.mul hm).sub (continuous_const.mul hl))
  have hd : Continuous d := (hpc.pow 2).add (hrc.pow 2)
  have hdn (x : ℝ) : 0 ≤ d x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hwn (x : ℝ) : 0 ≤ w x := by
    dsimp [w, nativeWeight, branchWeight]
    split_ifs <;> positivity
  have hdw : Integrable (fun x => d x * w x) := by
    apply (hd.mul hw).integrable_of_hasCompactSupport
    apply compact_support_of_vanish_outside _ R
    intro x hx
    simp [d, density, hps x hx, hrs x hx]
  have hc : Integrable (fun x => cross p r p' r' x * w x) := by
    apply (((hpc.mul hp').add (hrc.mul hr')).mul hw).integrable_of_hasCompactSupport
    apply compact_support_of_vanish_outside _ R
    intro x hx
    simp [cross, hps x hx, hrs x hx]
  have hm : Measurable (fun x => nativeEnergyCoefficient u v s x * (d x*w x)) := by
    have he : Measurable (nativeEnergyCoefficient u v s) := by
      unfold nativeEnergyCoefficient
      have hi : Measurable (fun x : ℝ => if x < 0 then u else v) := by
        apply Measurable.ite
        all_goals first | exact measurableSet_Iio | exact measurable_const
      exact hi.add (by fun_prop)
    exact he.mul (hd.measurable.mul hw.measurable)
  have hb (x : ℝ) : ‖nativeEnergyCoefficient u v s x * (d x*w x)‖ ≤ B*(d x*w x) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hdn x) (hwn x))]
    exact mul_le_mul_of_nonneg_right
      (native_coefficient_bound u v s x hs) (mul_nonneg (hdn x) (hwn x))
  have he : Integrable (fun x => nativeEnergyCoefficient u v s x * d x * w x) := by
    simpa only [mul_assoc] using
      (hdw.const_mul B).mono' hm.aestronglyMeasurable (Eventually.of_forall hb)
  have hleft : Tendsto (fun x => density p r x * branchWeight u s x) atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (-R)] with x hx
    have hR : R < |x| := by linarith [neg_le_abs x]
    simp [density, hps x hR, hrs x hR]
  have hright : Tendsto (fun x => density p r x * branchWeight v s x) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop R] with x hx
    have hR : R < |x| := lt_of_lt_of_le hx (le_abs_self x)
    simp [density, hps x hR, hrs x hR]
  rw [native_weight_integration_by_parts u v s p r p' r' hp hr hc he hleft hright]
  let f : ℝ → ℂ := fun x => ⟨p x, r x⟩
  have hf : Measurable f := by
    have he : f = fun x => (p x : ℂ) + Complex.I * (r x : ℂ) := by
      funext x
      apply Complex.ext <;> simp [f]
    rw [he]
    fun_prop
  have hfd (x : ℝ) : ‖f x‖^2 = density p r x := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [f, density]
    ring
  have hfi : Integrable (fun x => ‖f x‖^2 * nativeWeight u v s x) := by
    simpa only [hfd] using hdw
  simpa only [hfd, mul_assoc] using native_weight_energy_bound u v s hs f hf hfi

#check native_core_energy_bound
#print axioms native_core_energy_bound
end Round195E


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
open MeasureTheory
open Round194C

/-- Reciprocal of the original log-coordinate weight, with original Lebesgue log-Haar. -/
def nativeDualMeasure (u v s : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (nativeDualWeight u v s x))

/-- The actual weighted dual log-coordinate Hilbert fiber, not yet the full character sum. -/
abbrev NativeDualFiber (u v s : ℝ) := Lp ℂ 2 (nativeDualMeasure u v s)

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
end Round195D


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
    hκ hP Φ χ hχ hdecay t using 1
  congr 2
  ring

#check integrable_exp_neg_abs
#print axioms integrable_exp_neg_abs
#check theta_moments_from_decay
#print axioms theta_moments_from_decay
#check measured_theta_seed_moments
#print axioms measured_theta_seed_moments
end Round195F



noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Round191H

theorem adaptive_native_contour_exponent
    (R H K : ℝ) (hR : 0 < R) (hH : 1 ≤ H)
    (hsmall : 4 * H ≤ R ^ 2) (hK : K ≤ H) :
    K - (Real.sqrt H / R) * R ^ 2 ≤ -(R * Real.sqrt H) / 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hs0 : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hs2 : (Real.sqrt H) ^ 2 = H := Real.sq_sqrt hH0
  have hsR : 2 * Real.sqrt H ≤ R := by nlinarith
  have hmul := mul_nonneg hs0 (sub_nonneg.mpr hsR)
  have hid : (Real.sqrt H / R) * R ^ 2 = R * Real.sqrt H := by
    field_simp
  rw [hid]
  nlinarith

#check adaptive_native_contour_exponent
#print axioms adaptive_native_contour_exponent
end Round191H


/-! G195: the horizontal boundary term in native Gaussian contour exhaustion.
The unresolved native premise is the resolvent bound hR at chosen heights.
No density, jet completeness, nuclearity, or summability is assumed here. -/
namespace Round195G
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

def horizontalContour (ε b T : ℝ) (R : ℂ → E) : E :=
  ∫ x in (-b)..b,
    Complex.exp ((ε : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I)^2) •
      R ((x : ℂ) + (T : ℂ) * Complex.I)

theorem horizontal_contour_gaussian_bound
    (R : ℂ → E) (ε b T M K : ℝ) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hR : ∀ x ∈ Set.Icc (-b) b,
      ‖R ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤ M * Real.exp K) :
    ‖horizontalContour ε b T R‖ ≤
      (2*b*M) * Real.exp (ε*b^2 + K - ε*T^2) := by
  have hn (x : ℝ) (hx : x ∈ Set.uIoc (-b) b) :
      ‖Complex.exp ((ε : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I)^2) •
        R ((x : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        M * Real.exp (ε*b^2 + K - ε*T^2) := by
    have hx' : x ∈ Set.Icc (-b) b := by
      rw [Set.uIoc_of_le (by linarith : -b ≤ b)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hsq : x^2 ≤ b^2 := by nlinarith [hx'.1, hx'.2]
    have hre : (((ε : ℂ) * ((x : ℂ) + (T : ℂ) * Complex.I)^2).re) =
        ε*(x^2-T^2) := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
    rw [norm_smul, Complex.norm_exp, hre]
    calc
      _ ≤ Real.exp (ε*(x^2-T^2)) * (M * Real.exp K) := by
        exact mul_le_mul_of_nonneg_left (hR x hx') (le_of_lt (Real.exp_pos _))
      _ = M * Real.exp (ε*x^2 + K - ε*T^2) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ M * Real.exp (ε*b^2 + K - ε*T^2) := by
        have hM : 0 ≤ M := by
          have hh := (norm_nonneg _).trans (hR x hx')
          exact nonneg_of_mul_nonneg_left hh (Real.exp_pos K)
        gcongr
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hn
  have habs : |b - -b| = 2*b := by rw [abs_of_nonneg (by linarith)]; ring
  dsimp [horizontalContour]
  calc
    _ ≤ (M * Real.exp (ε*b^2 + K - ε*T^2)) * |b - -b| := hi
    _ = _ := by rw [habs]; ring

/-- Joins the checked H191 exponent estimate to the actual vector integral.
It applies equally in the native carrier and in its closed graph norm. -/
theorem horizontal_contour_adaptive_bound
    (R : ℂ → E) (b T t H M K : ℝ) (hb : 0 ≤ b) (hT : 0 < T)
    (ht : t^2 = T^2)
    (hH : 1 ≤ H) (hsmall : 4*H ≤ T^2) (hK : K ≤ H) (hM : 0 ≤ M)
    (hR : ∀ x ∈ Set.Icc (-b) b,
      ‖R ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * Real.exp K) :
    ‖horizontalContour (Real.sqrt H / T) b t R‖ ≤
      (2*b*M) * Real.exp (b^2 - T/2) := by
  have hH0 : 0 ≤ H := by linarith
  have hs0 := Real.sqrt_nonneg H
  have hs2 := Real.sq_sqrt hH0
  have hs1 : 1 ≤ Real.sqrt H := by nlinarith
  have hst : Real.sqrt H ≤ T := by nlinarith
  have heps : Real.sqrt H / T ≤ 1 := (div_le_one hT).2 hst
  have hh := Round191H.adaptive_native_contour_exponent T H K hT hH hsmall hK
  have hbase := horizontal_contour_gaussian_bound R (Real.sqrt H / T) b t M K
    (div_nonneg hs0 hT.le) hb hR
  rw [ht] at hbase
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hbb := mul_le_mul_of_nonneg_right heps (sq_nonneg b)
  have ht := mul_le_mul_of_nonneg_left hs1 hT.le
  nlinarith

#check horizontalContour
#check horizontal_contour_gaussian_bound
#print axioms horizontal_contour_gaussian_bound
#check horizontal_contour_adaptive_bound
#print axioms horizontal_contour_adaptive_bound
end Round195G



/-! H195: the infinite rank-one series in the reviewed R W R factorization.
This is the requested trace-ideal interface, not the native spectral bound.
The two square-column estimates must be derived on the actual annihilator.
No nuclearity or rank-one summability is assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
namespace Round195H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

/-- A concrete nuclear-series certificate with quantitative total cost. -/
def HasNuclearCost (T : E →L[ℂ] E) (C : ℝ) : Prop :=
  ∃ (v : ι → E) (f : ι → E →L[ℂ] ℂ),
    (∀ x, HasSum (fun i => f i x • v i) (T x)) ∧
    Summable (fun i => ‖f i‖ * ‖v i‖) ∧
    (∑' i, ‖f i‖ * ‖v i‖) ≤ C

/-- Square-column control yields the actual infinite R S expansion, with
S = W R in the reviewed native application. The cost is derived by Young's
inequality; no target rank-one summability is a premise. -/
theorem factorization_has_nuclear_cost
    (b : HilbertBasis ι ℂ E) (R S : E →L[ℂ] E)
    (hr : Summable (fun i => ‖R (b i)‖^2))
    (hs : Summable (fun i => ‖(innerSL ℂ (b i)).comp S‖^2)) :
    HasNuclearCost (ι := ι) (R.comp S)
      (((∑' i, ‖R (b i)‖^2) +
        (∑' i, ‖(innerSL ℂ (b i)).comp S‖^2))/2) := by
  let f : ι → E →L[ℂ] ℂ := fun i => (innerSL ℂ (b i)).comp S
  let v : ι → E := fun i => R (b i)
  have hm : Summable (fun i => (‖v i‖^2 + ‖f i‖^2)/2) :=
    (hr.add hs).div_const 2
  have hp (i : ι) : ‖f i‖ * ‖v i‖ ≤ (‖v i‖^2 + ‖f i‖^2)/2 := by
    nlinarith [sq_nonneg (‖v i‖ - ‖f i‖)]
  have hc : Summable (fun i => ‖f i‖ * ‖v i‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hp hm
  refine ⟨v, f, ?_, hc, ?_⟩
  · intro x
    have hh := R.hasSum (b.hasSum_repr (S x))
    simpa only [f, v, map_smul, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hh
  · calc
      _ ≤ ∑' i, (‖v i‖^2 + ‖f i‖^2)/2 := hc.tsum_le_tsum hp hm
      _ = _ := by rw [tsum_div_const, hr.tsum_add hs]

#check factorization_has_nuclear_cost
#print axioms factorization_has_nuclear_cost

/-- The exact infinite-series slot in the reviewed estimate. W is the
smoothed convolution; in the native application W commutes with R, so
R R W = R W R. Both hypotheses are finite energy estimates, not nuclear
summability. The native spectral/character bounds must discharge them. -/
theorem resolvent_factorization_nuclear_bound
    (b : HilbertBasis ι ℂ E) (R W : E →L[ℂ] E) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset ι, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (hrow : ∀ J : Finset ι, ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z) :
    HasNuclearCost (ι := ι) (R.comp (R.comp W)) (B*Z) := by
  let f : ι → E →L[ℂ] ℂ := fun i => ((innerSL ℂ (b i)).comp R).comp W
  let v : ι → E := fun i => R (b i)
  have hB : 0 ≤ B := (norm_nonneg W).trans hW
  have hp (i : ι) : ‖f i‖ * ‖v i‖ ≤
      B * ((‖R (b i)‖^2 + ‖(innerSL ℂ (b i)).comp R‖^2)/2) := by
    have hf : ‖f i‖ ≤ ‖(innerSL ℂ (b i)).comp R‖ * B := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hW (norm_nonneg _))
    have hh := mul_le_mul_of_nonneg_right hf (norm_nonneg (v i))
    have hy := sq_nonneg (‖R (b i)‖ - ‖(innerSL ℂ (b i)).comp R‖)
    have hz := mul_nonneg hB hy
    dsimp [v] at hh
    nlinarith
  have hfin (J : Finset ι) : ∑ i ∈ J, ‖f i‖ * ‖v i‖ ≤ B*Z := by
    calc
      _ ≤ ∑ i ∈ J, B * ((‖R (b i)‖^2 + ‖(innerSL ℂ (b i)).comp R‖^2)/2) :=
        Finset.sum_le_sum fun i _ => hp i
      _ = B * (((∑ i ∈ J, ‖R (b i)‖^2) +
          (∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2))/2) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ B*Z := mul_le_mul_of_nonneg_left (by linarith [hcol J, hrow J]) hB
  have hc : Summable (fun i => ‖f i‖ * ‖v i‖) :=
    summable_of_sum_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfin
  refine ⟨v, f, ?_, hc, ?_⟩
  · intro x
    have hh := R.hasSum (b.hasSum_repr (R (W x)))
    simpa only [v, f, map_smul, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hh
  · exact le_of_tendsto hc.hasSum (Filter.Eventually.of_forall hfin)

#check resolvent_factorization_nuclear_bound
#print axioms resolvent_factorization_nuclear_bound
end Round195H

namespace Round195H
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Nuclear norm defined by absolutely summable rank-one representations.
An arbitrary summation type is allowed; summability forces countable
nonzero cost. This is a definition, not an assumed trace-class interface. -/
def nuclearNorm (T : H →L[ℂ] H) : ENNReal :=
  sInf {c | ∃ (κ : Type u) (C : ℝ), HasNuclearCost (ι := κ) T C ∧
    c = ENNReal.ofReal C}

theorem nuclearNorm_le_of_cost {κ : Type u} {T : H →L[ℂ] H} {C : ℝ}
    (h : HasNuclearCost (ι := κ) T C) : nuclearNorm T ≤ ENNReal.ofReal C := by
  exact sInf_le ⟨κ, C, h, rfl⟩

/-- Quantitative norm form of the infinite assembly requested by A. All
native finite energy and identification obligations remain explicit. -/
theorem resolvent_nuclearNorm_le [CompleteSpace H]
    {κ : Type u} (b : HilbertBasis κ ℂ H) (R W : H →L[ℂ] H) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset κ, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (hrow : ∀ J : Finset κ, ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z) :
    nuclearNorm (R.comp (R.comp W)) ≤ ENNReal.ofReal (B*Z) :=
  nuclearNorm_le_of_cost (resolvent_factorization_nuclear_bound b R W B Z hW hcol hrow)

#check nuclearNorm
#check resolvent_nuclearNorm_le
#print axioms resolvent_nuclearNorm_le
end Round195H

namespace Round195A
open MeasureTheory

/-- D's Lp carrier uses exactly the reciprocal manuscript density. -/
theorem native_measure_eq_original (u v s : ℝ) (huv : u ≤ v) :
    Round195D.nativeDualMeasure u v s =
      volume.withDensity (fun x => ENNReal.ofReal (1 / Round194H.nativeWeight u v s x)) := by
  unfold Round195D.nativeDualMeasure
  congr 1
  funext x
  apply congrArg ENNReal.ofReal
  exact (Round193E.native_weight_eq_log_formula u v s x huv).symm.trans
    (native_dual_weight_eq_reciprocal u v s x huv)

/-- E's complete smooth-core estimate, instantiated on the density defining
D's actual Lp fiber. Core-to-generator closure is still not asserted. -/
theorem native_core_energy_on_carrier_density
    (u v s : ℝ) (huv : u ≤ v) (hs : 0 ≤ s)
    (p r p' r' : ℝ → ℝ)
    (hp : ∀ x, HasDerivAt p (p' x) x)
    (hr : ∀ x, HasDerivAt r (r' x) x)
    (hp' : Continuous p') (hr' : Continuous r')
    (R : ℝ) (hps : ∀ x, R < |x| → p x = 0)
    (hrs : ∀ x, R < |x| → r x = 0) :
    |∫ x : ℝ, Round194E.cross p r p' r' x * Round194C.nativeDualWeight u v s x| ≤
      (max |u| |v| + s/4) *
        ∫ x : ℝ, Round194E.density p r x * Round194C.nativeDualWeight u v s x := by
  have he (x : ℝ) : Round193E.nativeWeight u v s x = Round194C.nativeDualWeight u v s x :=
    Round193E.native_weight_eq_log_formula u v s x huv
  simpa only [he] using Round195E.native_core_energy_bound u v s huv hs
    p r p' r' hp hr hp' hr' R hps hrs

#check native_measure_eq_original
#print axioms native_measure_eq_original
#check native_core_energy_on_carrier_density
#print axioms native_core_energy_on_carrier_density
#check Round195F.measured_theta_seed_moments
#check Round195G.horizontal_contour_adaptive_bound
#check Round195H.resolvent_nuclearNorm_le
end Round195A

/- Copied from final checked r195 B, lines 134-299. -/

/-! Round 193 G: the ACTUAL archimedean pole-clearing Tate seeds.
This discharges finite-interval additive-mass identities within
LOCAL_TO_NATIVE_SEED of GLOBAL_ESTIMATE.md. It does not assert global
nuclearity or presume a spectral sum. -/
noncomputable section
open MeasureTheory
namespace Round193G

def realSeed (A x : ℝ) : ℝ :=
  (4*A^2*x^4-6*A*x^2)*Real.exp (-A*x^2)
def realPrimitive (A x : ℝ) : ℝ :=
  (-2*A)*x^3*Real.exp (-A*x^2)
def complexRadialSeed (A r : ℝ) : ℝ :=
  (A^2*r^5-2*A*r^3)*Real.exp (-A*r^2)
def complexPrimitive (A r : ℝ) : ℝ :=
  (-A/2)*r^4*Real.exp (-A*r^2)

theorem real_seed_derivative (A x : ℝ) :
    HasDerivAt (realPrimitive A) (realSeed A x) x := by
  unfold realPrimitive realSeed
  convert (((hasDerivAt_id x).pow 3).const_mul (-2*A)).mul
    ((((hasDerivAt_id x).pow 2).const_mul (-A)).exp) using 1
  simp only [Pi.pow_apply, id_eq]
  ring

theorem complex_seed_radial_derivative (A r : ℝ) :
    HasDerivAt (complexPrimitive A) (complexRadialSeed A r) r := by
  unfold complexPrimitive complexRadialSeed
  convert (((hasDerivAt_id r).pow 4).const_mul (-A/2)).mul
    ((((hasDerivAt_id r).pow 2).const_mul (-A)).exp) using 1
  simp only [Pi.pow_apply, id_eq]
  ring

/-- These are the real additive integral and the complex additive polar
integral of the actual local seeds. No moment identity is a hypothesis. -/
theorem archimedean_seed_boundary_integrals (A a b : ℝ) :
    (∫ x in a..b, realSeed A x) = realPrimitive A b - realPrimitive A a ∧
    (∫ r in a..b, complexRadialSeed A r) =
      complexPrimitive A b - complexPrimitive A a := by
  constructor
  · apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => real_seed_derivative A x)
    exact (by unfold realSeed; fun_prop : Continuous (realSeed A)).intervalIntegrable a b
  · apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => complex_seed_radial_derivative A r)
    exact (by unfold complexRadialSeed; fun_prop : Continuous (complexRadialSeed A)).intervalIntegrable a b

#check real_seed_derivative
#print axioms real_seed_derivative
#check complex_seed_radial_derivative
#print axioms complex_seed_radial_derivative
#check archimedean_seed_boundary_integrals
#print axioms archimedean_seed_boundary_integrals
end Round193G

namespace Round194G
open Round193G
/-- Origin conditions of the actual local pole-clearing seeds. -/
theorem archimedean_seed_origin_values (A : ℝ) :
    realSeed A 0 = 0 ∧ complexRadialSeed A 0 = 0 := by
  simp [realSeed, complexRadialSeed]
#check archimedean_seed_origin_values
#print axioms archimedean_seed_origin_values
end Round194G

namespace Round194G
open Round193G Filter
open scoped Topology

theorem actual_seed_integrable (A : ℝ) (hA : 0 < A) :
    Integrable (realSeed A) ∧ Integrable (complexRadialSeed A) := by
  have h (n : ℕ) : Integrable (fun x : ℝ => x^n * Real.exp (-A*x^2)) := by
    simpa only [Real.rpow_natCast] using
      integrable_rpow_mul_exp_neg_mul_sq hA (s := (n : ℝ)) (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
  constructor
  · convert ((h 4).const_mul (4*A^2)).sub ((h 2).const_mul (6*A)) using 1
    ext x
    dsimp only [realSeed, Pi.sub_apply]
    ring
  · convert ((h 5).const_mul (A^2)).sub ((h 3).const_mul (2*A)) using 1
    ext x
    dsimp only [complexRadialSeed, Pi.sub_apply]
    ring

theorem actual_seed_zero_masses (A : ℝ) (hA : 0 < A) :
    (∫ x : ℝ, realSeed A x) = 0 ∧
    (∫ r : ℝ in Set.Ioi 0, complexRadialSeed A r) = 0 := by
  have hlim (n : ℕ) : Tendsto
      (fun x : ℝ => x^n * Real.exp (-A*x^2)) (cocompact ℝ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos (Real.exp_pos _)] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact hA (n : ℝ)
  have hr : Tendsto (realPrimitive A) (cocompact ℝ) (𝓝 0) := by
    change Tendsto (fun x : ℝ => (-2*A)*x^3*Real.exp (-A*x^2)) _ _
    simpa only [mul_assoc, mul_zero] using (hlim 3).const_mul (-2*A)
  have hc : Tendsto (complexPrimitive A) (cocompact ℝ) (𝓝 0) := by
    change Tendsto (fun x : ℝ => (-A/2)*x^4*Real.exp (-A*x^2)) _ _
    simpa only [mul_assoc, mul_zero] using (hlim 4).const_mul (-A/2)
  constructor
  · have hi := integral_of_hasDerivAt_of_tendsto
      (real_seed_derivative A) (actual_seed_integrable A hA).1
      (hr.mono_left atBot_le_cocompact) (hr.mono_left atTop_le_cocompact)
    simpa using hi
  · have hi := integral_Ioi_of_hasDerivAt_of_tendsto
      (f := complexPrimitive A) (a := 0)
      (by unfold complexPrimitive; fun_prop)
      (fun x _ => complex_seed_radial_derivative A x)
      (actual_seed_integrable A hA).2.integrableOn
      (hc.mono_left atTop_le_cocompact)
    simpa [complexPrimitive] using hi

#check actual_seed_integrable
#print axioms actual_seed_integrable
#check actual_seed_zero_masses
#print axioms actual_seed_zero_masses
end Round194G

namespace Round195B
open Round194B

/-- This supplies F194's continuous scalar-seed premise from continuity
of the compact theta family and the compact character. -/
theorem measuredThetaSeed_continuous
    {C : Type*} [TopologicalSpace C] [MeasurableSpace C]
    [BorelSpace C] [CompactSpace C]
    (μ : Measure C) [IsFiniteMeasure μ]
    (κ a : ℝ) (Φ : ℝ → C → ℂ) (χ : C → ℂ)
    (hΦ : Continuous (Function.uncurry Φ)) (hχ : Continuous χ) :
    Continuous (measuredThetaSeed μ κ a Φ χ) := by
  have hp : Continuous (Function.uncurry (fun t y => Φ t y * χ y)) :=
    hΦ.mul (hχ.comp continuous_snd)
  have havg : Continuous (fun t : ℝ => ∫ y, Φ t y * χ y ∂μ) := by
    simpa using continuous_parametric_integral_of_continuous hp
      (s := Set.univ) isCompact_univ
  have he : Continuous (fun t : ℝ => (Real.exp (a*t) : ℂ)) := by fun_prop
  exact (continuous_const.mul he).mul havg

#check measuredThetaSeed_continuous
#print axioms measuredThetaSeed_continuous
end Round195B

namespace Round195B
/-- Left translation of the primal compact character average has the inverse
character, as required by the manuscript's bilinear dual convention. -/
theorem character_average_inverse_isotype
    {C : Type*} [Group C] [MeasurableSpace C] [MeasurableMul C]
    (μ : Measure C) [μ.IsMulLeftInvariant]
    (χ : C →* ℂˣ) (f : C → ℂ) (x : C) :
    (∫ y, f (x*y) * (χ y : ℂ) ∂μ) =
      (χ x : ℂ)⁻¹ * ∫ y, f y * (χ y : ℂ) ∂μ := by
  apply mul_left_cancel₀ (Units.ne_zero (χ x))
  rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (χ x)), one_mul,
    ← integral_const_mul]
  calc
    _ = ∫ y, f (x*y) * (χ (x*y) : ℂ) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [map_mul, Units.val_mul]
        ring
    _ = _ := integral_mul_left_eq_self (fun y => f y * (χ y : ℂ)) x

#check character_average_inverse_isotype
#print axioms character_average_inverse_isotype
end Round195B

/- Copied from final checked r195 D, lines 167-212. -/
namespace Round195D
open MeasureTheory
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

/- Copied from final checked r195 C, lines 698-732. -/
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

/- Copied from final checked r195 C, lines 790-866. -/
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

/- Copied from final checked r195 E, lines 373-519. -/
/-! Direct domain attachment: C191's strong derivative and D's actual
translation norm bound imply the numerical range on the full generator
domain. This avoids requiring an additional smooth-core density theorem.
The actual U and its native growth must still be supplied by D. -/
namespace Round195E
open Filter Set
open scoped Topology InnerProductSpace
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]

private theorem orbit_numerical_range_upper
    (f : ℝ → H) (x y : H) (beta : ℝ) (hzero : f 0 = x)
    (hd : HasDerivAt f y 0)
    (hgrowth : ∀ t : ℝ, 0 < t → ‖f t‖ ≤ Real.exp (beta*t) * ‖x‖) :
    (inner ℂ x y).re ≤ beta * ‖x‖^2 := by
  let L : H →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ x).restrictScalars ℝ)
  have hh := L.hasFDerivAt.comp_hasDerivAt 0 hd
  have hh' : HasDerivAt (fun t => (inner ℂ x (f t)).re) (inner ℂ x y).re 0 := hh
  have he : HasDerivAt (fun t : ℝ => Real.exp (beta*t) * ‖x‖^2)
      (beta * ‖x‖^2) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).const_mul beta).exp).mul_const (‖x‖^2)
  apply le_of_tendsto_of_tendsto hh'.tendsto_slope_zero_right he.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hb : (inner ℂ x (f t)).re ≤ Real.exp (beta*t) * ‖x‖^2 := by
    calc
      _ ≤ ‖inner ℂ x (f t)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖f t‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (Real.exp (beta*t)*‖x‖) :=
        mul_le_mul_of_nonneg_left (hgrowth t ht') (norm_nonneg x)
      _ = _ := by ring
  have hxself : (inner ℂ x x).re = ‖x‖^2 := by
    rw [inner_self_eq_norm_sq_to_K, pow_two]
    change (((‖x‖ : ℂ) * (‖x‖ : ℂ)).re) = ‖x‖^2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  simpa only [zero_add, hzero, hxself, mul_zero, Real.exp_zero,
    one_mul, smul_eq_mul] using
    mul_le_mul_of_nonneg_left (sub_le_sub_right hb (‖x‖^2)) (inv_nonneg.mpr ht'.le)

theorem native_generator_numerical_range
    (U : ℝ → H →L[ℂ] H) (beta : ℝ)
    (hzero : ∀ x, U 0 x = x)
    (hgrowth : ∀ t x, ‖U t x‖ ≤ Real.exp (beta*|t|) * ‖x‖)
    (x y : H) (hd : HasDerivAt (fun t => U t x) y 0) :
    |(inner ℂ x y).re| ≤ beta * ‖x‖^2 := by
  have hu : (inner ℂ x y).re ≤ beta * ‖x‖^2 := by
    apply orbit_numerical_range_upper (fun t => U t x) x y beta (hzero x) hd
    intro t ht
    simpa only [abs_of_pos ht] using hgrowth t x
  have hn : HasDerivAt (fun t : ℝ => U (-t) x) (-y) 0 := by
    have hd0 : HasDerivAt (fun t => U t x) y (-id (0:ℝ)) := by simpa using hd
    simpa using hd0.scomp (0:ℝ) ((hasDerivAt_id (0:ℝ)).neg)
  have hl : (inner ℂ x (-y)).re ≤ beta * ‖x‖^2 := by
    apply orbit_numerical_range_upper (fun t => U (-t) x) x (-y) beta (by simpa using hzero x) hn
    intro t ht
    simpa only [abs_neg, abs_of_pos ht] using hgrowth (-t) x
  rw [inner_neg_right, Complex.neg_re] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

#check native_generator_numerical_range
#print axioms native_generator_numerical_range
end Round195E


/-!
Round 182 D. First new premise in GLOBAL_ESTIMATE.md:
NATIVE_RESOLVENT_COERCIVITY_TO_HILBERT_SCHMIDT.
The native logarithmic weight gives the numerical-range hypothesis with
c = alpha + s/4. This lemma turns that bound into a resolvent column-square
bound, retaining the real trace instead of inverse jet/Gram norms.
The native attachment, zero counting and global contour sum are not
formalized here and no nuclearity conclusion is asserted.
-/
noncomputable section
set_option linter.unusedSimpArgs false
open scoped InnerProductSpace
namespace Round182D

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem resolvent_column_coercivity
    (D R : H →L[ℂ] H) (c : ℝ) (z : ℂ)
    (hnum : ∀ v : H, (inner ℂ v (D v)).re ≤ c * ‖v‖ ^ 2)
    (hres : ∀ x : H, z • R x - D (R x) = x) (x : H) :
    (z.re - c) * ‖R x‖ ^ 2 ≤ (inner ℂ (R x) x).re := by
  have hid : (inner ℂ (R x) x).re =
      z.re * ‖R x‖ ^ 2 - (inner ℂ (R x) (D (R x))).re := by
    calc
      _ = (inner ℂ (R x) (z • R x - D (R x))).re :=
        congrArg (fun y : H => (inner ℂ (R x) y).re) (hres x).symm
      _ = _ := by
        simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
          Complex.mul_re, ← Complex.ofReal_pow]
  rw [hid]
  nlinarith [hnum (R x)]

/-- For an orthonormal basis the numerator is Re(trace R) and the left
side is the squared Hilbert-Schmidt norm. No eigenvector conditioning
or nuclear/summability hypothesis is present. -/
theorem resolvent_column_square_sum_le
    {ι : Type*} (J : Finset ι) (e : ι → H)
    (D R : H →L[ℂ] H) (c : ℝ) (z : ℂ) (hz : c < z.re)
    (hnum : ∀ v : H, (inner ℂ v (D v)).re ≤ c * ‖v‖ ^ 2)
    (hres : ∀ x : H, z • R x - D (R x) = x) :
    (∑ j ∈ J, ‖R (e j)‖ ^ 2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) / (z.re - c) := by
  apply (le_div_iff₀ (sub_pos.mpr hz)).2
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    resolvent_column_coercivity D R c z hnum hres (e j)

#check resolvent_column_coercivity
#print axioms resolvent_column_coercivity
#check resolvent_column_square_sum_le
#print axioms resolvent_column_square_sum_le
end Round182D

namespace Round195E
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]

/-- Joined application of the new domain numerical range to the preserved
resolvent energy theorem. On a native invariant finite window, D is the
bounded generator restriction. Actual window/group/resolvent construction
is still required; no numerical-range inequality is assumed here. -/
theorem native_resolvent_column_square_sum_le
    {ι : Type*} (J : Finset ι) (e : ι → H)
    (U : ℝ → H →L[ℂ] H) (D R : H →L[ℂ] H)
    (beta : ℝ) (z : ℂ) (hz : beta < z.re)
    (hzero : ∀ x, U 0 x = x)
    (hgrowth : ∀ t x, ‖U t x‖ ≤ Real.exp (beta*|t|) * ‖x‖)
    (hgen : ∀ v : H, HasDerivAt (fun t => U t v) (D v) 0)
    (hres : ∀ x : H, z • R x - D (R x) = x) :
    (∑ j ∈ J, ‖R (e j)‖^2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) / (z.re-beta) := by
  apply Round182D.resolvent_column_square_sum_le J e D R beta z hz _ hres
  intro v
  exact (le_abs_self _).trans
    (native_generator_numerical_range U beta hzero hgrowth v (D v) (hgen v))

#check native_resolvent_column_square_sum_le
#print axioms native_resolvent_column_square_sum_le
end Round195E

/- Copied from final checked r195 G, lines 111-165. -/
namespace Round195G
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]

/-- Both oriented horizontal edges of the rectangle. No sum of individual
residue norms is taken. The resolvent may take values in a closed graph. -/
theorem horizontal_contour_pair_bound
    (R : ℂ → E) (b T H M K : ℝ) (hb : 0 ≤ b) (hT : 0 < T)
    (hH : 1 ≤ H) (hsmall : 4*H ≤ T^2) (hK : K ≤ H) (hM : 0 ≤ M)
    (hR : ∀ t : ℝ, t^2 = T^2 → ∀ x ∈ Set.Icc (-b) b,
      ‖R ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * Real.exp K) :
    ‖horizontalContour (Real.sqrt H / T) b T R -
      horizontalContour (Real.sqrt H / T) b (-T) R‖ ≤
      (4*b*M) * Real.exp (b^2-T/2) := by
  have hp := horizontal_contour_adaptive_bound R b T T H M K hb hT rfl
    hH hsmall hK hM (hR T rfl)
  have hn := horizontal_contour_adaptive_bound R b T (-T) H M K hb hT (by ring)
    hH hsmall hK hM (hR (-T) (by ring))
  calc
    _ ≤ ‖horizontalContour (Real.sqrt H / T) b T R‖ +
        ‖horizontalContour (Real.sqrt H / T) b (-T) R‖ := norm_sub_le _ _
    _ ≤ (2*b*M) * Real.exp (b^2-T/2) +
        (2*b*M) * Real.exp (b^2-T/2) := add_le_add hp hn
    _ = _ := by ring

/-- Horizontal boundary terms vanish in the chosen norm. Instantiating
E with the native closed graph retains the generator component as well. -/
theorem horizontal_contour_pair_vanishes
    (R : ℂ → E) (b M : ℝ) (T H K : ℕ → ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hT : ∀ n, 0 < T n)
    (hH : ∀ n, 1 ≤ H n) (hsmall : ∀ n, 4*H n ≤ (T n)^2)
    (hK : ∀ n, K n ≤ H n) (hTinf : Tendsto T atTop atTop)
    (hR : ∀ n (t : ℝ), t^2 = (T n)^2 → ∀ x ∈ Set.Icc (-b) b,
      ‖R ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * Real.exp (K n)) :
    Tendsto (fun n =>
      horizontalContour (Real.sqrt (H n) / T n) b (T n) R -
      horizontalContour (Real.sqrt (H n) / T n) b (-T n) R)
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n =>
    horizontal_contour_pair_bound R b (T n) (H n) M (K n) hb (hT n)
      (hH n) (hsmall n) (hK n) hM (hR n))
  have hh : Tendsto (fun n => T n / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2) hTinf
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hh).const_mul
    ((4*b*M)*Real.exp (b^2))
  have heq (n : ℕ) : (4*b*M)*Real.exp (b^2-T n/2) =
      ((4*b*M)*Real.exp (b^2))*Real.exp (-(T n/2)) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  simpa only [heq, mul_zero, Function.comp_def] using he

#check horizontal_contour_pair_bound
#print axioms horizontal_contour_pair_bound
#check horizontal_contour_pair_vanishes
#print axioms horizontal_contour_pair_vanishes
end Round195G

/- Copied from final checked r195 H, lines 125-188. -/
namespace Round195H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem basis_hasSum_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  have hh := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner x x)
  have he (i : ι) : (inner ℂ x (b i) * inner ℂ (b i) x).re =
      ‖inner ℂ (b i) x‖^2 := by
    rw [← inner_conj_symm (b i) x, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    rw [← Complex.sq_norm, norm_inner_symm]
    simp only [Complex.sq_norm]
    rw [inner_conj_symm]
  have hx : (inner ℂ x x).re = ‖x‖^2 := by
    rw [inner_self_eq_norm_sq_to_K]
    change (((‖x‖ : ℝ) : ℂ)^2).re = ‖x‖^2
    simp [pow_two]
  simpa only [Complex.reCLM_apply, he, hx] using hh

/-- The row estimate is discharged from the column estimate, rather than
passed back to the native spectral proof as an extra hypothesis. -/
theorem finite_rows_le_of_columns
    (b : HilbertBasis ι ℂ E) (R : E →L[ℂ] E) (Z : ℝ)
    (hcol : ∀ J : Finset ι, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (J : Finset ι) :
    ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z := by
  classical
  have hsum (i : ι) :
      HasSum (fun j => ‖inner ℂ (b i) (R (b j))‖^2)
        (‖(innerSL ℂ (b i)).comp R‖^2) := by
    have hh := basis_hasSum_sq b (R.adjoint (b i))
    simpa only [ContinuousLinearMap.innerSL_apply_comp, innerSL_apply_norm,
      ContinuousLinearMap.adjoint_inner_right, norm_inner_symm] using hh
  have hall : HasSum (fun j => ∑ i ∈ J, ‖inner ℂ (b i) (R (b j))‖^2)
      (∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2) := by
    exact hasSum_sum fun i _ => hsum i
  apply le_of_tendsto hall
  apply Filter.Eventually.of_forall
  intro S
  calc
    _ ≤ ∑ j ∈ S, ‖R (b j)‖^2 := Finset.sum_le_sum fun j _ =>
      b.orthonormal.sum_inner_products_le (R (b j))
    _ ≤ Z := hcol S

#check finite_rows_le_of_columns
#print axioms finite_rows_le_of_columns
end Round195H

namespace Round195H
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_nuclearNorm_le_of_columns
    {κ : Type u} (b : HilbertBasis κ ℂ H) (R W : H →L[ℂ] H) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset κ, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z) :
    nuclearNorm (R.comp (R.comp W)) ≤ ENNReal.ofReal (B*Z) := by
  exact resolvent_nuclearNorm_le b R W B Z hW hcol
    (finite_rows_le_of_columns b R Z hcol)

#check resolvent_nuclearNorm_le_of_columns
#print axioms resolvent_nuclearNorm_le_of_columns
end Round195H

namespace Round196A
open MeasureTheory Round188D Round195D
open scoped InnerProductSpace

/-- The concrete domain-to-energy application at the measured theta-seed
vector in the actual reciprocal-weight Lp fiber. This discharges the derivative
premise of E195 at C195's vector. Native U and adelic theta realization are
still required; this is not a nuclear-bound theorem. -/
theorem measured_seed_generator_energy
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
    |(inner ℂ
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit U z t x)
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit U z t x + U t x -
          Complex.exp (z * (t : ℂ)) • x))).re| ≤
      (max |u| |v| + s/4) *
      ‖∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit U z t x‖^2 := by
  exact Round195E.native_generator_numerical_range U (max |u| |v| + s/4)
    hzero hgrowth _ _
    (Round195C.measurable_normalized_seed_domain_on_native_fiber
      u v s hs U hzero hgroup hcont hgrowth μ κ a P hκ hP Φ χ hΦ hχm hχ z x hdecay)

#check measured_seed_generator_energy
#print axioms measured_seed_generator_energy
#check Round195H.resolvent_nuclearNorm_le_of_columns
#print axioms Round195H.resolvent_nuclearNorm_le_of_columns
end Round196A

/- Joined from pinned, hash-matched current round196 D source. -/
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

/- Joined from pinned, hash-matched current round196 E source. -/
namespace Round196E
open Round195D
open scoped InnerProductSpace

theorem native_translation_generator_numerical_range
    (u v s : ℝ) (hs : 0 ≤ s)
    (x y : NativeDualFiber u v s)
    (hd : HasDerivAt (fun t => nativeTranslationVector u v s t hs x) y 0) :
    |(inner ℂ x y).re| ≤ (max |u| |v| + s/4) * ‖x‖^2 := by
  let beta := max |u| |v| + s/4
  change |(inner ℂ x y).re| ≤ beta * ‖x‖^2
  have hu : (inner ℂ x y).re ≤ beta * ‖x‖^2 := by
    apply Round195E.orbit_numerical_range_upper
      (fun t => nativeTranslationVector u v s t hs x) x y beta
      (native_translation_zero u v s hs x) hd
    intro t ht
    simpa only [abs_of_pos ht] using native_translation_norm_le u v s t hs x
  have hn : HasDerivAt (fun t : ℝ => nativeTranslationVector u v s (-t) hs x)
      (-y) 0 := by
    have hd0 : HasDerivAt (fun t => nativeTranslationVector u v s t hs x) y
        (-id (0:ℝ)) := by simpa using hd
    simpa using hd0.scomp (0:ℝ) ((hasDerivAt_id (0:ℝ)).neg)
  have hl : (inner ℂ x (-y)).re ≤ beta * ‖x‖^2 := by
    apply Round195E.orbit_numerical_range_upper
      (fun t => nativeTranslationVector u v s (-t) hs x) x (-y) beta
      (by simpa using native_translation_zero u v s hs x) hn
    intro t ht
    simpa only [abs_neg, abs_of_pos ht] using native_translation_norm_le u v s (-t) hs x
  rw [inner_neg_right, Complex.neg_re] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

/-- Numerical range is evaluated only on the genuine resolvent range.
There is no bounded whole-space generator and no assumed numerical range. -/
theorem native_fiber_resolvent_coercivity
    (u v s : ℝ) (hs : 0 ≤ s)
    (R : NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s) (z : ℂ)
    (hres : ∀ x : NativeDualFiber u v s,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x))
        (z • R x - x) 0)
    (x : NativeDualFiber u v s) :
    (z.re - (max |u| |v| + s/4)) * ‖R x‖^2 ≤ (inner ℂ (R x) x).re := by
  have hn := (le_abs_self _).trans
    (native_translation_generator_numerical_range u v s hs (R x) (z • R x - x) (hres x))
  have hid : (inner ℂ (R x) (z • R x - x)).re =
      z.re * ‖R x‖^2 - (inner ℂ (R x) x).re := by
    simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      Complex.mul_re, ← Complex.ofReal_pow]
  rw [hid] at hn
  nlinarith

/-- Direct native column-energy input to H195's infinite nuclear assembly.
Its residual hres is the actual generator-resolvent identity, not a trace or
summability assumption. The finite real trace must still be bounded. -/
theorem native_fiber_resolvent_column_square_sum_le
    (u v s : ℝ) (hs : 0 ≤ s)
    {ι : Type*} (J : Finset ι) (e : ι → NativeDualFiber u v s)
    (R : NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s)
    (z : ℂ) (hz : max |u| |v| + s/4 < z.re)
    (hres : ∀ x : NativeDualFiber u v s,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x))
        (z • R x - x) 0) :
    (∑ j ∈ J, ‖R (e j)‖^2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) /
        (z.re - (max |u| |v| + s/4)) := by
  apply (le_div_iff₀ (sub_pos.mpr hz)).2
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    native_fiber_resolvent_coercivity u v s hs R z hres (e j)

#check native_translation_generator_numerical_range
#print axioms native_translation_generator_numerical_range
#check native_fiber_resolvent_coercivity
#print axioms native_fiber_resolvent_coercivity
#check native_fiber_resolvent_column_square_sum_le
#print axioms native_fiber_resolvent_column_square_sum_le
end Round196E

namespace Round196E
open Round195D
open scoped InnerProductSpace

/-- The actual fiber estimate restricts to any native subspace. In the joined
proof V must be the actual geometric annihilator; no identity of V with a jet
span or full native character space is assumed by this energy lemma. -/
theorem native_subspace_resolvent_coercivity
    (u v s : ℝ) (hs : 0 ≤ s) (V : Submodule ℂ (NativeDualFiber u v s))
    (R : V →L[ℂ] V) (z : ℂ)
    (hres : ∀ x : V,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x : NativeDualFiber u v s))
        ((z • R x - x : V) : NativeDualFiber u v s) 0)
    (x : V) :
    (z.re - (max |u| |v| + s/4)) * ‖R x‖^2 ≤ (inner ℂ (R x) x).re := by
  have hn := (le_abs_self _).trans
    (native_translation_generator_numerical_range u v s hs
      (R x : NativeDualFiber u v s) ((z • R x - x : V) : NativeDualFiber u v s) (hres x))
  change (inner ℂ (R x) (z • R x - x)).re ≤
    (max |u| |v| + s/4) * ‖R x‖^2 at hn
  have hid : (inner ℂ (R x) (z • R x - x)).re =
      z.re * ‖R x‖^2 - (inner ℂ (R x) x).re := by
    simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      Complex.mul_re, ← Complex.ofReal_pow]
  rw [hid] at hn
  nlinarith

theorem native_subspace_resolvent_column_square_sum_le
    (u v s : ℝ) (hs : 0 ≤ s) (V : Submodule ℂ (NativeDualFiber u v s))
    {ι : Type*} (J : Finset ι) (e : ι → V)
    (R : V →L[ℂ] V) (z : ℂ) (hz : max |u| |v| + s/4 < z.re)
    (hres : ∀ x : V,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x : NativeDualFiber u v s))
        ((z • R x - x : V) : NativeDualFiber u v s) 0) :
    (∑ j ∈ J, ‖R (e j)‖^2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) /
        (z.re - (max |u| |v| + s/4)) := by
  apply (le_div_iff₀ (sub_pos.mpr hz)).2
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    native_subspace_resolvent_coercivity u v s hs V R z hres (e j)

#check native_subspace_resolvent_coercivity
#print axioms native_subspace_resolvent_coercivity
#check native_subspace_resolvent_column_square_sum_le
#print axioms native_subspace_resolvent_column_square_sum_le
end Round196E

/- Joined from pinned, hash-matched current round196 C source. -/
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

/- Joined from pinned, hash-matched current round196 G source. -/
namespace Round191D


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussian_translation_limit
    (U : ℝ → E →L[ℝ] E) (x : E)
    (hzero : U 0 x = x) (hcont : Continuous (fun t => U t x))
    (β : ℝ) (hβ : 0 ≤ β)
    (hgrowth : ∀ t, ‖U t x‖ ≤ Real.exp (β * |t|) * ‖x‖)
    (r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t : ℝ,
      Real.exp (-(t^2)) • (U (r n * t) x - x)) atTop (𝓝 0) := by
  let bound : ℝ → ℝ := fun t =>
    ((Real.exp (β^2 / 2) + 1) * ‖x‖) * Real.exp (-(1/2 : ℝ) * t^2)
  have hb : Integrable bound := by
    exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).const_mul _
  have hnorm (n : ℕ) (t : ℝ) :
      ‖Real.exp (-(t^2)) • (U (r n * t) x - x)‖ ≤ bound t := by
    have ht : |r n * t| ≤ |t| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right (hr n) (abs_nonneg t)
    have hU : ‖U (r n * t) x - x‖ ≤
        (Real.exp (β * |t|) + 1) * ‖x‖ := by
      calc
        _ ≤ ‖U (r n * t) x‖ + ‖x‖ := norm_sub_le _ _
        _ ≤ Real.exp (β * |r n * t|) * ‖x‖ + ‖x‖ := by gcongr; exact hgrowth _
        _ ≤ (Real.exp (β * |t|) + 1) * ‖x‖ := by
          rw [add_mul, one_mul]
          gcongr
    have h1 : Real.exp (-(t^2)) * Real.exp (β * |t|) ≤
        Real.exp (β^2 / 2) * Real.exp (-(1/2 : ℝ) * t^2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (|t| - β), sq_abs t]
    have h2 : Real.exp (-(t^2)) ≤ Real.exp (-(1/2 : ℝ) * t^2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg t]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(t^2)) * ((Real.exp (β * |t|) + 1) * ‖x‖) := by gcongr
      _ = (Real.exp (-(t^2)) * Real.exp (β * |t|) + Real.exp (-(t^2))) * ‖x‖ := by ring
      _ ≤ (Real.exp (β^2 / 2) * Real.exp (-(1/2 : ℝ) * t^2) +
          Real.exp (-(1/2 : ℝ) * t^2)) * ‖x‖ := by gcongr
      _ = bound t := by dsimp [bound]; ring
  have hlim (t : ℝ) : Tendsto (fun n =>
      Real.exp (-(t^2)) • (U (r n * t) x - x)) atTop (𝓝 (0 : E)) := by
    have hrt : Tendsto (fun n => r n * t) atTop (𝓝 0) := by
      simpa using hr0.mul_const t
    have hux : Tendsto (fun n => U (r n * t) x) atTop (𝓝 x) := by
      simpa [hzero] using hcont.continuousAt.tendsto.comp hrt
    simpa using (hux.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))).const_smul (Real.exp (-(t^2)))
  have h := tendsto_integral_of_dominated_convergence bound
    (fun n => (show Continuous (fun t : ℝ =>
      Real.exp (-(t^2)) • (U (r n * t) x - x)) by
        exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(t^2)))).smul
          ((hcont.comp (by fun_prop)).sub continuous_const)).aestronglyMeasurable)
    hb (fun n => Filter.Eventually.of_forall (hnorm n))
    (Filter.Eventually.of_forall hlim)
  simpa using h

#check gaussian_translation_limit
#print axioms gaussian_translation_limit
/-- Quantitative Gaussian error for a generator-controlled orbit.  In the
native application f(t)=U(t)R(c)x or U(t)T_h x; the displayed increment
bound is derived from the actual weighted generator, not assumed totality. -/
theorem gaussian_generator_error_bound
    (f : ℝ → E) (β M r : ℝ) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hr : |r| ≤ 1)
    (hinc : ∀ t, ‖f t - f 0‖ ≤ |t| * Real.exp (β * |t|) * M) :
    ‖∫ t : ℝ, Real.exp (-(t^2)) • (f (r*t) - f 0)‖ ≤
      (|r| * Real.exp (β^2/2) * M) *
        ∫ t : ℝ, Real.exp (-(1/4 : ℝ) * t^2) := by
  let bound : ℝ → ℝ := fun t =>
    (|r| * Real.exp (β^2/2) * M) * Real.exp (-(1/4 : ℝ) * t^2)
  have hb : Integrable bound :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/4)).const_mul _
  have hn (t : ℝ) :
      ‖Real.exp (-(t^2)) • (f (r*t) - f 0)‖ ≤ bound t := by
    have ht : |r*t| ≤ |t| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right hr (abs_nonneg t)
    have he : Real.exp (-(t^2)) * Real.exp (β * |r*t|) ≤
        Real.exp (β^2/2) * Real.exp (-(1/2 : ℝ) * t^2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left ht hβ
      nlinarith [sq_nonneg (|t|-β), sq_abs t]
    have ha : |t| ≤ Real.exp (t^2/4) := by
      have hsq := sq_nonneg (|t|-2)
      have hab := sq_abs t
      have hex := Real.add_one_le_exp (t^2/4)
      nlinarith
    have hp : |t| * Real.exp (-(1/2 : ℝ)*t^2) ≤
        Real.exp (-(1/4 : ℝ)*t^2) := by
      calc
        _ ≤ Real.exp (t^2/4) * Real.exp (-(1/2 : ℝ)*t^2) := by gcongr
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(t^2)) * (|r*t| * Real.exp (β*|r*t|) * M) := by
        gcongr; exact hinc _
      _ = (|r| *M) * |t| * (Real.exp (-(t^2))*Real.exp (β*|r*t|)) := by
        rw [abs_mul]; ring
      _ ≤ (|r| *M) * |t| * (Real.exp (β^2/2)*Real.exp (-(1/2 : ℝ)*t^2)) := by
        gcongr
      _ = (|r| *Real.exp (β^2/2)*M) * (|t| *Real.exp (-(1/2 : ℝ)*t^2)) := by ring
      _ ≤ bound t := by dsimp [bound]; gcongr
  have hh := norm_integral_le_of_norm_le hb (Filter.Eventually.of_forall hn)
  simpa only [bound, integral_const_mul] using hh

#check gaussian_generator_error_bound
#print axioms gaussian_generator_error_bound
end Round191D

/-! G196: joins the shrinking adaptive Gaussian with the checked horizontal
boundary term. These are the two approximation errors in the native contour
exhaustion. The actual graph-resolvent/residue identity is still required. -/
namespace Round196G
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem gaussian_translation_limit_of_nonneg_width
    (U : ℝ → E →L[ℝ] E) (x : E)
    (hzero : U 0 x = x) (hcont : Continuous (fun t => U t x))
    (β : ℝ) (hβ : 0 ≤ β)
    (hgrowth : ∀ t, ‖U t x‖ ≤ Real.exp (β * |t|) * ‖x‖)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t : ℝ,
      Real.exp (-(t^2)) • (U (r n * t) x - x)) atTop (𝓝 0) := by
  let rc : ℕ → ℝ := fun n => min 1 (r n)
  have hrc (n : ℕ) : |rc n| ≤ 1 := by
    rw [abs_of_nonneg (le_min (by norm_num) (hr n))]
    exact min_le_left _ _
  have hrc0 : Tendsto rc atTop (𝓝 0) := by
    simpa [rc] using (tendsto_const_nhds.min hr0 :
      Tendsto (fun n => min (1 : ℝ) (r n)) atTop (𝓝 (min 1 0)))
  have heq : rc =ᶠ[atTop] r := by
    have hh := (tendsto_order.1 hr0).2 1 (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hh] with n hn
    exact min_eq_right hn.le
  have h := Round191D.gaussian_translation_limit U x hzero hcont β hβ
    hgrowth rc hrc hrc0
  apply h.congr'
  filter_upwards [heq] with n hn
  simp only [hn]

variable [NormedSpace ℂ E]

theorem adaptive_gaussian_contour_error_vanishes
    (U : ℝ → E →L[ℝ] E) (x : E)
    (hzero : U 0 x = x) (hcont : Continuous (fun t => U t x))
    (β : ℝ) (hβ : 0 ≤ β)
    (hgrowth : ∀ t, ‖U t x‖ ≤ Real.exp (β * |t|) * ‖x‖)
    (R : ℂ → E) (b M : ℝ) (T H K : ℕ → ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hT : ∀ n, 0 < T n)
    (hH : ∀ n, 1 ≤ H n) (hsmall : ∀ n, 4*H n ≤ (T n)^2)
    (hK : ∀ n, K n ≤ H n) (hTinf : Tendsto T atTop atTop)
    (hsubquadratic : Tendsto (fun n => H n / (T n)^2) atTop (𝓝 0))
    (hR : ∀ n (t : ℝ), t^2 = (T n)^2 → ∀ y ∈ Set.Icc (-b) b,
      ‖R ((y : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * Real.exp (K n)) :
    Tendsto (fun n =>
      (Real.sqrt Real.pi)⁻¹ • (∫ t : ℝ, Real.exp (-(t^2)) •
        (U ((2 * Real.sqrt (Real.sqrt (H n) / T n)) * t) x - x)) +
      (Round195G.horizontalContour (Real.sqrt (H n) / T n) b (T n) R -
       Round195G.horizontalContour (Real.sqrt (H n) / T n) b (-T n) R))
      atTop (𝓝 0) := by
  have heps : Tendsto (fun n => Real.sqrt (H n) / T n) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsubquadratic
    have heq (n : ℕ) : Real.sqrt (H n / (T n)^2) = Real.sqrt (H n) / T n := by
      rw [Real.sqrt_div (le_trans (by norm_num) (hH n)), Real.sqrt_sq_eq_abs, abs_of_pos (hT n)]
    simpa only [Function.comp_def, heq, Real.sqrt_zero] using h
  have hwidth : Tendsto (fun n => 2 * Real.sqrt (Real.sqrt (H n) / T n))
      atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp heps).const_mul 2
  have hgaussian := gaussian_translation_limit_of_nonneg_width U x hzero hcont β hβ
    hgrowth (fun n => 2 * Real.sqrt (Real.sqrt (H n) / T n))
    (fun n => mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hwidth
  have hhorizontal := Round195G.horizontal_contour_pair_vanishes R b M T H K
    hb hM hT hH hsmall hK hTinf hR
  simpa using (hgaussian.const_smul ((Real.sqrt Real.pi)⁻¹)).add hhorizontal

#check gaussian_translation_limit_of_nonneg_width
#print axioms gaussian_translation_limit_of_nonneg_width
#check adaptive_gaussian_contour_error_vanishes
#print axioms adaptive_gaussian_contour_error_vanishes
end Round196G

/- Joined from pinned, hash-matched current round196 H source. -/
namespace Round196H
open scoped BigOperators

def integerWeight (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ (-2 : ℝ)

theorem integerWeight_nonneg (n : ℤ) : 0 ≤ integerWeight n :=
  Real.rpow_nonneg (by positivity) _

theorem integerWeight_summable : Summable integerWeight := by
  have h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hp
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [integerWeight, abs_of_nonneg, add_comm] using h

def latticeWeight (d : ℕ) (k : Fin d → ℤ) : ℝ :=
  ∏ i, integerWeight (k i)

def latticeMass : ℝ := ∑' n : ℤ, integerWeight n

def latticeConsEquiv (d : ℕ) : (ℤ × (Fin d → ℤ)) ≃ (Fin (d+1) → ℤ) where
  toFun p := Fin.cons p.1 p.2
  invFun k := (k 0, fun i => k i.succ)
  left_inv := by intro p; simp
  right_inv := by
    intro k
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem latticeWeight_nonneg (d : ℕ) (k : Fin d → ℤ) :
    0 ≤ latticeWeight d k := Finset.prod_nonneg fun _ _ => integerWeight_nonneg _

theorem latticeWeight_hasSum (d : ℕ) :
    HasSum (latticeWeight d) (latticeMass ^ d) := by
  induction d with
  | zero =>
      letI : Unique (Fin 0 → ℤ) :=
        { default := fun i => Fin.elim0 i
          uniq := fun f => by funext i; exact Fin.elim0 i }
      simpa [latticeWeight] using (hasSum_fintype (latticeWeight 0))
  | succ d ih =>
      have hp := integerWeight_summable.mul_of_nonneg ih.summable
        integerWeight_nonneg (latticeWeight_nonneg d)
      have hh := integerWeight_summable.hasSum.mul ih hp
      apply (latticeConsEquiv d).hasSum_iff.mp
      simpa [Function.comp_def, latticeConsEquiv, latticeWeight,
        Fin.prod_univ_succ, latticeMass, pow_succ, mul_comm] using hh

/-- The full concrete F × Z^d majorant, including d=0. -/
theorem finite_level_character_majorant {F : Type*} [Fintype F] (d : ℕ) :
    HasSum (fun p : F × (Fin d → ℤ) => latticeWeight d p.2)
      ((Fintype.card F : ℝ) * latticeMass ^ d) := by
  have hf := hasSum_fintype (fun _ : F => (1 : ℝ))
  have hl := latticeWeight_hasSum d
  have hp := hf.summable.mul_of_nonneg hl.summable (by intro; norm_num)
    (latticeWeight_nonneg d)
  simpa using hf.mul hl hp

#check finite_level_character_majorant
#print axioms finite_level_character_majorant
end Round196H

namespace Round196A
open MeasureTheory Round188D Round195D Round196D
open scoped InnerProductSpace

/-- C196 and E196 joined at the concrete weighted translation and integrated
measured theta seed. No U/group/growth or derivative premise remains.
Strong continuity and actual adelic theta/envelope remain explicit. -/
theorem native_measured_seed_generator_energy
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
    |(inner ℂ
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit (nativeTranslation u v s hs) z t x)
      (∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        (z • dividedGroupOrbit (nativeTranslation u v s hs) z t x +
          nativeTranslation u v s hs t x -
          Complex.exp (z * (t : ℂ)) • x))).re| ≤
      (max |u| |v|+s/4) *
      ‖∫ t : ℝ, Round194B.measuredThetaSeed μ κ a Φ χ t •
        dividedGroupOrbit (nativeTranslation u v s hs) z t x‖^2 := by
  apply Round196E.native_translation_generator_numerical_range u v s hs
  exact Round196C.native_normalized_seed_generator_domain u v s hs hcont
    μ κ a P hκ hP Φ χ hΦ hχm hχ z x hdecay

#check native_measured_seed_generator_energy
#print axioms native_measured_seed_generator_energy
#check Round196D.nativeTranslation_group
#print axioms Round196D.nativeTranslation_group
#check Round196E.native_subspace_resolvent_column_square_sum_le
#print axioms Round196E.native_subspace_resolvent_column_square_sum_le
#check Round196G.adaptive_gaussian_contour_error_vanishes
#print axioms Round196G.adaptive_gaussian_contour_error_vanishes
#check Round196H.finite_level_character_majorant
#print axioms Round196H.finite_level_character_majorant
end Round196A
