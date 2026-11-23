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

/-! F196: the missing theta-envelope step is reduced to actual discrete lattice
geometry and Schwartz seminorms. No theta decay or lattice summability is an
input. The coercivity premise retains the true norm-section exponent. -/
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
