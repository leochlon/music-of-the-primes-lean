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
    have hp : z.re*t ≤ |z.re| * |t| := by
      simpa only [abs_mul] using le_abs_self (z.re*t)
    have he : Real.exp (z.re*t) ≤ Real.exp ((|z.re|+beta)*|t|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hb (abs_nonneg t)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (norm_nonneg (k t))) (norm_nonneg x)
  refine ⟨hV, ?_⟩
  have hZ : Integrable (fun t : ℝ => z • (k t • dividedGroupOrbit U z t x)) := by
    apply (hV.norm.const_mul ‖z‖).mono'
      ((z • ContinuousLinearMap.id ℂ E).continuous.comp_aestronglyMeasurable
        hV.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun t => le_of_eq (norm_smul z _))
  have hi := (hZ.add hU).sub hE
  simpa only [smul_sub, smul_add, smul_smul, mul_comm] using hi

#check full_seed_graph_integrable
#print axioms full_seed_graph_integrable
end Round193F

/-! D194: quantitative moments of the actual rapidly decaying theta seed.
The measured native application takes L=beta+|Re z|. No spectral sum
or nuclearity hypothesis occurs. Both envelopes integrate to 2*A. -/
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
