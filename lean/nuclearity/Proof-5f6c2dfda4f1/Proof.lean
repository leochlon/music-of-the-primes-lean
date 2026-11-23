import Mathlib

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

namespace Round195F
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


end Round195F

namespace Round196G
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

def verticalTailIntegrand (ε b T : ℝ) (R : ℂ → E) (t : ℝ) : E :=
  ({y : ℝ | T ≤ |y|} : Set ℝ).indicator
    (fun y => Complex.exp ((ε : ℂ) * ((b : ℂ) + (y : ℂ) * Complex.I)^2) •
      R ((b : ℂ) + (y : ℂ) * Complex.I)) t

def verticalTail (ε b T : ℝ) (R : ℂ → E) : E :=
  ∫ t : ℝ, verticalTailIntegrand ε b T R t

/-- Both infinite ends of a vertical contour vanish together at the adaptive
width. The native application supplies the exterior Laplace-resolvent bound. -/
theorem adaptive_vertical_tail_vanishes
    (R : ℂ → E) (b M : ℝ) (T H : ℕ → ℝ)
    (hM : 0 ≤ M) (hT : ∀ n, 0 < T n) (hH : ∀ n, 1 ≤ H n)
    (hsmall : ∀ n, 4*H n ≤ (T n)^2)
    (hTinf : Tendsto T atTop atTop)
    (hcont : Continuous (fun t : ℝ => R ((b : ℂ) + (t : ℂ) * Complex.I)))
    (hR : ∀ t : ℝ, ‖R ((b : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M) :
    Tendsto (fun n => verticalTail (Real.sqrt (H n) / T n) b (T n) R)
      atTop (𝓝 0) := by
  let bound : ℝ → ℝ := fun t => (M * Real.exp (b^2)) * Real.exp (-|t|)
  have hb : Integrable bound := Round195F.integrable_exp_neg_abs.const_mul _
  have hn (n : ℕ) (t : ℝ) :
      ‖verticalTailIntegrand (Real.sqrt (H n) / T n) b (T n) R t‖ ≤ bound t := by
    by_cases ht : T n ≤ |t|
    · unfold verticalTailIntegrand
      rw [Set.indicator_of_mem (show t ∈ {y : ℝ | T n ≤ |y|} from ht)]
      have hs0 := Real.sqrt_nonneg (H n)
      have hs2 := Real.sq_sqrt (le_trans (by norm_num) (hH n))
      have hs1 : 1 ≤ Real.sqrt (H n) := by nlinarith [hH n]
      have hsT : Real.sqrt (H n) ≤ T n := by nlinarith [hsmall n, hT n]
      have heps0 : 0 ≤ Real.sqrt (H n) / T n := div_nonneg hs0 (hT n).le
      have heps1 : Real.sqrt (H n) / T n ≤ 1 := (div_le_one (hT n)).2 hsT
      have hepsT : (Real.sqrt (H n) / T n) * T n = Real.sqrt (H n) := by
        exact div_mul_cancel₀ _ (ne_of_gt (hT n))
      have hl : |t| ≤ (Real.sqrt (H n) / T n) * t^2 := by
        have h1 := mul_le_mul_of_nonneg_right hs1 (abs_nonneg t)
        have h2 := mul_le_mul_of_nonneg_left ht heps0
        have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg t)
        rw [hepsT] at h3
        nlinarith [sq_abs t]
      have hre : (((Real.sqrt (H n) / T n : ℝ) : ℂ) *
          ((b : ℂ) + (t : ℂ) * Complex.I)^2).re =
          (Real.sqrt (H n) / T n)*(b^2-t^2) := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
      rw [norm_smul, Complex.norm_exp, hre]
      calc
        _ ≤ Real.exp ((Real.sqrt (H n) / T n)*(b^2-t^2)) * M := by
          gcongr; exact hR t
        _ ≤ Real.exp (b^2-|t|) * M := by
          gcongr
          have hh := mul_le_mul_of_nonneg_right heps1 (sq_nonneg b)
          nlinarith
        _ = bound t := by
          dsimp [bound]
          rw [sub_eq_add_neg, Real.exp_add]
          ring
    · simp only [verticalTailIntegrand, Set.indicator_of_notMem (show t ∉ {y : ℝ | T n ≤ |y|} from ht), norm_zero]
      exact mul_nonneg (mul_nonneg hM (Real.exp_pos _).le) (Real.exp_pos _).le
  have hm (n : ℕ) : AEStronglyMeasurable
      (verticalTailIntegrand (Real.sqrt (H n) / T n) b (T n) R) := by
    have hcs : Continuous (fun t : ℝ =>
        Complex.exp (((Real.sqrt (H n) / T n : ℝ) : ℂ) *
          ((b : ℂ) + (t : ℂ) * Complex.I)^2)) := by fun_prop
    have hc := hcs.smul hcont
    exact hc.aestronglyMeasurable.indicator
      ((isClosed_le continuous_const continuous_abs).measurableSet)
  have hlim (t : ℝ) : Tendsto (fun n =>
      verticalTailIntegrand (Real.sqrt (H n) / T n) b (T n) R t)
      atTop (𝓝 (0 : E)) := by
    have hh : ∀ᶠ n in atTop, |t| < T n :=
      hTinf.eventually (eventually_gt_atTop _)
    apply tendsto_const_nhds.congr'
    filter_upwards [hh] with n hn
    simp [verticalTailIntegrand, not_le.mpr hn]
  have hh := tendsto_integral_of_dominated_convergence bound hm hb
    (fun n => Filter.Eventually.of_forall (hn n)) (Filter.Eventually.of_forall hlim)
  simpa only [verticalTail, integral_zero] using hh

#check adaptive_vertical_tail_vanishes
#print axioms adaptive_vertical_tail_vanishes
end Round196G



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

namespace Round196G
open Round195D Round196D

/-- A genuine generator-domain vector has a continuous orbit under the actual
weighted translation. Global strong continuity is not a premise here. -/
theorem native_domain_orbit_continuous
    (u v s : ℝ) (hs : 0 ≤ s) (x y : NativeDualFiber u v s)
    (hd : HasDerivAt (fun t => nativeTranslation u v s hs t x) y 0) :
    Continuous (fun t => nativeTranslation u v s hs t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hshift : Tendsto (fun r : ℝ => r-t) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self] using (tendsto_id.sub_const t :
      Tendsto (fun r : ℝ => r-t) (𝓝 t) (𝓝 (t-t)))
  have h0 := hd.continuousAt.tendsto.comp hshift
  have hc := (nativeTranslation u v s hs t).continuous.continuousAt.tendsto.comp h0
  have heq (r : ℝ) : nativeTranslation u v s hs t
      (nativeTranslation u v s hs (r-t) x) = nativeTranslation u v s hs r x := by
    rw [nativeTranslation_group]
    congr 2
    ring
  simpa only [Function.comp_def, heq, nativeTranslation_zero] using hc

/-- Native-fiber application of the Gaussian/horizontal contour limit.
No abstract translation group, group law, growth or orbit-continuity premise
remains. The derivative is the genuine generator-domain witness. -/
theorem native_domain_contour_error_vanishes
    (u v s : ℝ) (hs : 0 ≤ s) (x y : NativeDualFiber u v s)
    (hd : HasDerivAt (fun t => nativeTranslation u v s hs t x) y 0)
    (R : ℂ → NativeDualFiber u v s) (b M : ℝ) (T H K : ℕ → ℝ)
    (hb : 0 ≤ b) (hM : 0 ≤ M) (hT : ∀ n, 0 < T n)
    (hH : ∀ n, 1 ≤ H n) (hsmall : ∀ n, 4*H n ≤ (T n)^2)
    (hK : ∀ n, K n ≤ H n) (hTinf : Tendsto T atTop atTop)
    (hsubquadratic : Tendsto (fun n => H n / (T n)^2) atTop (𝓝 0))
    (hR : ∀ n (t : ℝ), t^2 = (T n)^2 → ∀ r ∈ Set.Icc (-b) b,
      ‖R ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * Real.exp (K n)) :
    Tendsto (fun n =>
      (Real.sqrt Real.pi)⁻¹ • (∫ t : ℝ, Real.exp (-(t^2)) •
        (nativeTranslation u v s hs
          ((2 * Real.sqrt (Real.sqrt (H n) / T n)) * t) x - x)) +
      (Round195G.horizontalContour (Real.sqrt (H n) / T n) b (T n) R -
       Round195G.horizontalContour (Real.sqrt (H n) / T n) b (-T n) R))
      atTop (𝓝 0) := by
  exact adaptive_gaussian_contour_error_vanishes
    (fun t => (nativeTranslation u v s hs t).restrictScalars ℝ) x
    (nativeTranslation_zero u v s hs x)
    (native_domain_orbit_continuous u v s hs x y hd)
    (max |u| |v|+s/4) (by positivity)
    (fun t => nativeTranslation_bound u v s t hs x)
    R b M T H K hb hM hT hH hsmall hK hTinf hsubquadratic hR

#check native_domain_orbit_continuous
#print axioms native_domain_orbit_continuous
#check native_domain_contour_error_vanishes
#print axioms native_domain_contour_error_vanishes
end Round196G
