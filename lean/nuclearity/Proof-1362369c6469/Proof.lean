import Mathlib

private theorem generic_group_cancellation {G : Type*} [Group G] (x y z : G) :
    (x*z⁻¹)⁻¹*(x*y⁻¹) = z*y⁻¹ := by
  rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

/-! Round 90 B: exact convolution correction for the actual idele-class group.
This is the manuscript weight at alpha=0, s=2. It controls the difference
between ordinary and weight-conjugated convolution, an explicit source of
leakage for A(phi) P. Nuclear summability and the Hilbert adjoint identification
are not asserted. -/
open scoped NumberField NNReal ENNReal
open MeasureTheory

namespace NuclearBoundB90

variable (K : Type*) [Field K] [NumberField K]
abbrev Adeles := NumberField.AdeleRing (𝓞 K) K
abbrev Ideles := (Adeles K)ˣ
noncomputable def principalIdele : Kˣ →* Ideles K :=
  Units.map (algebraMap K (Adeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (Ideles K) :=
  (principalIdele K).range
abbrev Classes := Ideles K ⧸ principalIdeles K
noncomputable instance : MeasurableSpace (Classes K) := borel (Classes K)

noncomputable def convolution (μ : Measure (Classes K))
    (φ f : Classes K → ℂ) (x : Classes K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

/-- At alpha=0,s=2, this is w^-1 A(phi) w, with w(x)=1+ell(x)^2.
For reflected conjugate phi it is the formal weighted Hilbert adjoint. -/
noncomputable def weightConjugatedConvolution (μ : Measure (Classes K))
    (ell : Classes K → ℝ) (φ f : Classes K → ℂ) (x : Classes K) : ℂ :=
  ∫ g, (((1 + ell (g⁻¹ * x) ^ 2) / (1 + ell x ^ 2) : ℝ) : ℂ) *
    (φ g * f (g⁻¹ * x)) ∂μ

/-- Exact algebraic correction; no uniform lift or spectral bound is used. -/
theorem polynomial_weight_correction (t h : ℝ) :
    1 - (1 + (t-h)^2) / (1+t^2) =
      (2*t/(1+t^2))*h - (1/(1+t^2))*h^2 := by
  have hw : (1+t^2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- This coefficient tends to zero in the output tail for compact log support. -/
theorem polynomial_weight_correction_bound (t h R : ℝ)
    (hR : |h| ≤ R) :
    |1 - (1 + (t-h)^2)/(1+t^2)| ≤
      (2*|t| *R + R^2)/(1+t^2) := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hR
  have hden : 0 < 1+t^2 := by positivity
  have hid : 1 - (1+(t-h)^2)/(1+t^2) = (2*t*h-h^2)/(1+t^2) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hden]
  apply div_le_div_of_nonneg_right _ hden.le
  calc
    |2*t*h-h^2| ≤ |2*t*h| + |h^2| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (2*t*h) (h^2)
    _ = 2*|t| *|h| + |h|^2 := by rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), abs_pow]
    _ ≤ 2*|t| *R + R^2 := by nlinarith [abs_nonneg t, abs_nonneg h]

/-- Exact correction of authentic convolution, retaining the multiplier in x.
The log-coordinate cocycle and all integral hypotheses remain explicit. -/
theorem genuine_convolution_weight_correction
    (μ : Measure (Classes K)) (ell : Classes K → ℝ)
    (φ f : Classes K → ℂ) (x : Classes K)
    (hlog : ∀ g, ell (g⁻¹*x) = ell x - ell g)
    (h0 : Integrable (fun g => φ g * f (g⁻¹*x)) μ)
    (h1 : Integrable (fun g => (ell g : ℂ) * (φ g * f (g⁻¹*x))) μ)
    (h2 : Integrable (fun g => ((ell g)^2 : ℝ) * (φ g * f (g⁻¹*x))) μ) :
    convolution K μ φ f x - weightConjugatedConvolution K μ ell φ f x =
      ((2*ell x/(1+ell x^2) : ℝ) : ℂ) *
        convolution K μ (fun g => (ell g : ℂ) * φ g) f x -
      ((1/(1+ell x^2) : ℝ) : ℂ) *
        convolution K μ (fun g => (((ell g)^2 : ℝ) : ℂ) * φ g) f x := by
  let a : ℂ := ((2*ell x/(1+ell x^2) : ℝ) : ℂ)
  let b : ℂ := ((1/(1+ell x^2) : ℝ) : ℂ)
  have hp (g : Classes K) :
      (((1+ell (g⁻¹*x)^2)/(1+ell x^2) : ℝ) : ℂ) * (φ g * f (g⁻¹*x)) =
      φ g * f (g⁻¹*x) -
        (a*((ell g : ℂ)*(φ g*f (g⁻¹*x))) -
         b*((((ell g)^2 : ℝ) : ℂ)*(φ g*f (g⁻¹*x)))) := by
    rw [hlog g]
    have hc := polynomial_weight_correction (ell x) (ell g)
    have hc' := congrArg (fun r : ℝ => (r : ℂ)) hc
    push_cast at hc'
    dsimp [a,b]
    push_cast
    linear_combination -(φ g * f (g⁻¹*x))*hc'
  unfold convolution weightConjugatedConvolution
  simp_rw [hp]
  have hcint : Integrable (fun g =>
      a*((ell g : ℂ)*(φ g*f (g⁻¹*x))) -
      b*((((ell g)^2 : ℝ) : ℂ)*(φ g*f (g⁻¹*x)))) μ :=
    (h1.const_mul a).sub (h2.const_mul b)
  have hi := integral_sub h0 hcint
  rw [hi]
  have hi2 := integral_sub (h1.const_mul a) (h2.const_mul b)
  rw [hi2, integral_const_mul, integral_const_mul]
  simp only [mul_assoc]
  dsimp [a,b]
  ring

/-- A direct bound for the correction acting on each actual lifted function. -/
theorem genuine_convolution_weight_correction_norm
    (μ : Measure (Classes K)) (ell : Classes K → ℝ)
    (φ f : Classes K → ℂ) (x : Classes K)
    (hlog : ∀ g, ell (g⁻¹*x) = ell x - ell g)
    (h0 : Integrable (fun g => φ g * f (g⁻¹*x)) μ)
    (h1 : Integrable (fun g => (ell g : ℂ) * (φ g * f (g⁻¹*x))) μ)
    (h2 : Integrable (fun g => ((ell g)^2 : ℝ) * (φ g * f (g⁻¹*x))) μ) :
    ‖convolution K μ φ f x - weightConjugatedConvolution K μ ell φ f x‖ ≤
      |2*ell x/(1+ell x^2)| *
        ‖convolution K μ (fun g => (ell g : ℂ) * φ g) f x‖ +
      |1/(1+ell x^2)| *
        ‖convolution K μ (fun g => (((ell g)^2 : ℝ) : ℂ) * φ g) f x‖ := by
  rw [genuine_convolution_weight_correction K μ ell φ f x hlog h0 h1 h2]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ = _ := by simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Uniform smallness of the first correction multiplier in the output tail. -/
theorem first_correction_tail (t T : ℝ) (hT : 0 < T) (ht : T ≤ |t|) :
    |2*t/(1+t^2)| ≤ 2/T := by
  have hden : 0 < 1+t^2 := by positivity
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), abs_of_pos hden]
  apply (div_le_div_iff₀ hden hT).mpr
  have hab : |t|^2 = t^2 := sq_abs t
  have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg t)
  nlinarith

/-- Uniform smallness of the second correction multiplier in the output tail. -/
theorem second_correction_tail (t T : ℝ) (hT : 0 < T) (ht : T ≤ |t|) :
    |1/(1+t^2)| ≤ 1/T^2 := by
  have hden : 0 < 1+t^2 := by positivity
  rw [abs_of_pos (div_pos zero_lt_one hden)]
  apply (div_le_div_iff₀ hden (sq_pos_of_pos hT)).mpr
  have hab : |t|^2 = t^2 := sq_abs t
  nlinarith [abs_nonneg t]

end NuclearBoundB90

namespace NuclearBoundB91
open NuclearBoundB90
variable (K : Type*) [Field K] [NumberField K]

/-- Direct square-kernel estimate for genuine convolution after a cutoff.
The weight is the Hilbert density. No nuclear estimate is assumed. -/
theorem genuine_cutoff_kernel_energy_bound
    (μ : Measure (Classes K)) (ρ φ : Classes K → ℂ) (w : Classes K → ℝ)
    (hw : ∀ x, 1 ≤ w x)
    (hρ : Measurable (fun x => ENNReal.ofReal (‖ρ x‖^2 * w x)))
    (hφ : Measurable (fun g => ENNReal.ofReal (‖φ g‖^2)))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) μ μ) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal
      ((‖ρ x‖^2 * w x) * ‖φ (x*y⁻¹)‖^2 / w y) ∂μ ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (‖ρ x‖^2 * w x) ∂μ) *
      (∫⁻ g, ENNReal.ofReal (‖φ g‖^2) ∂μ) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖ρ x‖^2 * w x) *
        (∫⁻ g, ENNReal.ofReal (‖φ g‖^2) ∂μ) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (‖ρ x‖^2 * w x) *
            ENNReal.ofReal (‖φ (x*y⁻¹)‖^2) ∂μ := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (by have := hw x; positivity : 0 ≤ ‖ρ x‖^2 * w x)]
          apply ENNReal.ofReal_le_ofReal
          exact div_le_self (by have := hw x; positivity) (hw y)
        _ = _ := by
          have hm : Measurable (fun y : Classes K =>
              ENNReal.ofReal (‖φ (x*y⁻¹)‖^2)) := hφ.comp (hpres x).measurable
          rw [lintegral_const_mul _ hm, (hpres x).lintegral_comp hφ]
    _ = _ := lintegral_mul_const _ hρ

/-- Finite square-kernel energy from finite cutoff weight mass and L2 test mass. -/
theorem genuine_cutoff_kernel_energy_finite
    (μ : Measure (Classes K)) (ρ φ : Classes K → ℂ) (w : Classes K → ℝ)
    (hw : ∀ x, 1 ≤ w x)
    (hρ : Measurable (fun x => ENNReal.ofReal (‖ρ x‖^2 * w x)))
    (hφ : Measurable (fun g => ENNReal.ofReal (‖φ g‖^2)))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) μ μ)
    (hρfin : (∫⁻ x, ENNReal.ofReal (‖ρ x‖^2 * w x) ∂μ) ≠ ⊤)
    (hφfin : (∫⁻ g, ENNReal.ofReal (‖φ g‖^2) ∂μ) ≠ ⊤) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal
      ((‖ρ x‖^2 * w x) * ‖φ (x*y⁻¹)‖^2 / w y) ∂μ ∂μ) < ⊤ := by
  exact lt_of_le_of_lt
    (genuine_cutoff_kernel_energy_bound K μ ρ φ w hw hρ hφ hpres)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hρfin hφfin))

/-- The actual manuscript weight meets the needed bound for all alpha,s>=0. -/
theorem manuscript_weight_ge_one (α s t : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    1 ≤ Real.exp (2*α*|t|) * (1+t^2) ^ (s/2) := by
  have he : 1 ≤ Real.exp (2*α*|t|) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : 1 ≤ (1+t^2) ^ (s/2) := Real.one_le_rpow (by nlinarith) (by positivity)
  nlinarith


/-- Kernel of M_rho A_phi after the weighted-to-unweighted L2 conjugation. -/
noncomputable def transportedCutoffKernel
    (ρ φ : Classes K → ℂ) (w : Classes K → ℝ) (x y : Classes K) : ℂ :=
  ρ x * φ (x*y⁻¹) * (Real.sqrt (w x / w y) : ℂ)

theorem transportedCutoffKernel_norm_sq
    (ρ φ : Classes K → ℂ) (w : Classes K → ℝ)
    (hw : ∀ x, 1 ≤ w x) (x y : Classes K) :
    ‖transportedCutoffKernel K ρ φ w x y‖^2 =
      (‖ρ x‖^2 * w x) * ‖φ (x*y⁻¹)‖^2 / w y := by
  have hdiv : 0 ≤ w x / w y := div_nonneg
    (le_trans zero_le_one (hw x)) (le_trans zero_le_one (hw y))
  simp only [transportedCutoffKernel, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hdiv]
  ring

/-- Product-measure form of the actual weighted convolution kernel bound. -/
theorem genuine_cutoff_kernel_product_bound
    (μ : Measure (Classes K)) [SFinite μ]
    (ρ φ : Classes K → ℂ) (w : Classes K → ℝ)
    (hw : ∀ x, 1 ≤ w x)
    (hρ : Measurable (fun x => ENNReal.ofReal (‖ρ x‖^2 * w x)))
    (hφ : Measurable (fun g => ENNReal.ofReal (‖φ g‖^2)))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) μ μ)
    (hk : AEMeasurable (fun z : Classes K × Classes K =>
      ENNReal.ofReal (‖transportedCutoffKernel K ρ φ w z.1 z.2‖^2)) (μ.prod μ)) :
    (∫⁻ z : Classes K × Classes K,
      ENNReal.ofReal (‖transportedCutoffKernel K ρ φ w z.1 z.2‖^2) ∂μ.prod μ) ≤
      (∫⁻ x, ENNReal.ofReal (‖ρ x‖^2 * w x) ∂μ) *
      (∫⁻ g, ENNReal.ofReal (‖φ g‖^2) ∂μ) := by
  rw [lintegral_prod _ hk]
  simp_rw [transportedCutoffKernel_norm_sq K ρ φ w hw]
  exact genuine_cutoff_kernel_energy_bound K μ ρ φ w hw hρ hφ hpres


/-- Exact intermediate-cutoff insertion needed for a product of two
compact-output convolution factors. This controls the genuine integrand. -/
theorem genuine_compact_output_cutoff_insertion
    (ell : Classes K → ℝ) (ρ φ σ f : Classes K → ℂ) (T R : ℝ)
    (hρ : ∀ x, ρ x ≠ 0 → |ell x| ≤ T)
    (hφ : ∀ g, φ g ≠ 0 → |ell g| ≤ R)
    (hσ : ∀ y, |ell y| ≤ T+R → σ y = 1)
    (x g : Classes K) (hlog : ell (g⁻¹*x) = ell x - ell g) :
    ρ x * (φ g * f (g⁻¹*x)) =
      ρ x * (φ g * (σ (g⁻¹*x) * f (g⁻¹*x))) := by
  by_cases hx : ρ x = 0
  · simp [hx]
  by_cases hg : φ g = 0
  · simp [hg]
  have hl : |ell (g⁻¹*x)| ≤ T+R := by
    rw [hlog]
    exact (abs_sub (ell x) (ell g)).trans (add_le_add (hρ x hx) (hφ g hg))
  rw [hσ _ hl, one_mul]

end NuclearBoundB91

namespace Round93A
noncomputable section
open MeasureTheory NuclearBoundB90 NuclearBoundB91

def stripWeight (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (1 + u ^ 2) ^ (s / 2)

/-- A corrected translation estimate, valid for every nonnegative strip width
    and real Sobolev parameter; unlike (9.3.1.6), it does not vanish at identity. -/
theorem stripWeight_translate_bound (alpha s u v : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    stripWeight alpha s (u + v) ≤
      (Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)) *
        stripWeight alpha s v := by
  have hp : 1 + (u + v) ^ 2 ≤ (2 * (1 + u ^ 2)) * (1 + v ^ 2) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u * v)]
  have he : Real.exp (2 * alpha * |u + v|) ≤
      Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_add_le u v]
  have hw : (1 + (u + v) ^ 2) ^ (s / 2) ≤
      (2 * (1 + u ^ 2)) ^ (s / 2) * (1 + v ^ 2) ^ (s / 2) := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ 2 * (1 + u ^ 2))
      (by positivity : 0 ≤ 1 + v ^ 2)]
    exact Real.rpow_le_rpow (by positivity) hp (by positivity)
  unfold stripWeight
  calc
    _ ≤ (Real.exp (2 * alpha * |u|) * Real.exp (2 * alpha * |v|)) *
        ((2 * (1 + u ^ 2)) ^ (s / 2) * (1 + v ^ 2) ^ (s / 2)) :=
      mul_le_mul he hw (by positivity) (by positivity)
    _ = _ := by ring

noncomputable def translationCost (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (2 * (1 + u ^ 2)) ^ (s / 2)

theorem stripWeight_pos (alpha s u : ℝ) : 0 < stripWeight alpha s u := by
  unfold stripWeight
  positivity

theorem translationCost_nonneg (alpha s u : ℝ) :
    0 ≤ translationCost alpha s u := by
  unfold translationCost
  positivity

theorem stripWeight_ratio (alpha s u v : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) :
    stripWeight alpha s (u+v) / stripWeight alpha s v ≤
      translationCost alpha s u := by
  apply (div_le_iff₀ (stripWeight_pos alpha s v)).mpr
  exact stripWeight_translate_bound alpha s u v ha hs

variable (K : Type*) [Field K] [NumberField K]

/-- Pointwise actual convolution kernel bound with displacement cost. -/
theorem genuine_kernel_displacement_bound
    (ell : Classes K → ℝ) (rho phi : Classes K → ℂ)
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (x y : Classes K) (hlog : ell x = ell (x*y⁻¹) + ell y) :
    ‖transportedCutoffKernel K rho phi (fun z => stripWeight alpha s (ell z)) x y‖^2 ≤
      ‖rho x‖^2 * (‖phi (x*y⁻¹)‖^2 * translationCost alpha s (ell (x*y⁻¹))) := by
  rw [transportedCutoffKernel_norm_sq K rho phi (fun z => stripWeight alpha s (ell z))
    (fun z => manuscript_weight_ge_one alpha s (ell z) ha hs)]
  have hr : stripWeight alpha s (ell x) / stripWeight alpha s (ell y) ≤
      translationCost alpha s (ell (x*y⁻¹)) := by
    rw [hlog]
    exact stripWeight_ratio alpha s _ _ ha hs
  calc
    _ = (‖rho x‖^2 * ‖phi (x*y⁻¹)‖^2) *
        (stripWeight alpha s (ell x) / stripWeight alpha s (ell y)) := by ring
    _ ≤ (‖rho x‖^2 * ‖phi (x*y⁻¹)‖^2) *
        translationCost alpha s (ell (x*y⁻¹)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

/-- Actual-group kernel energy with unweighted output L2 mass.
This is an input to an HS factorization, not an S1 assertion. -/
theorem genuine_kernel_unweighted_cutoff_energy
    (mu : Measure (Classes K)) [SFinite mu]
    (ell : Classes K → ℝ) (rho phi : Classes K → ℂ)
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hrho : Measurable (fun x => ENNReal.ofReal (‖rho x‖^2)))
    (hphi : Measurable (fun g => ENNReal.ofReal
      (‖phi g‖^2 * translationCost alpha s (ell g))))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hk : AEMeasurable (fun z : Classes K × Classes K =>
      ENNReal.ofReal (‖transportedCutoffKernel K rho phi
        (fun q => stripWeight alpha s (ell q)) z.1 z.2‖^2)) (mu.prod mu)) :
    (∫⁻ z : Classes K × Classes K, ENNReal.ofReal
      (‖transportedCutoffKernel K rho phi
        (fun q => stripWeight alpha s (ell q)) z.1 z.2‖^2) ∂mu.prod mu) ≤
      (∫⁻ x, ENNReal.ofReal (‖rho x‖^2) ∂mu) *
      (∫⁻ g, ENNReal.ofReal (‖phi g‖^2 * translationCost alpha s (ell g)) ∂mu) := by
  rw [lintegral_prod _ hk]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (‖rho x‖^2) *
        (∫⁻ g, ENNReal.ofReal (‖phi g‖^2 * translationCost alpha s (ell g)) ∂mu) ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (‖rho x‖^2) * ENNReal.ofReal
            (‖phi (x*y⁻¹)‖^2 * translationCost alpha s (ell (x*y⁻¹))) ∂mu := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (sq_nonneg ‖rho x‖)]
          exact ENNReal.ofReal_le_ofReal
            (genuine_kernel_displacement_bound K ell rho phi alpha s ha hs x y (hlog x y))
        _ = _ := by
          have hm : Measurable (fun y : Classes K => ENNReal.ofReal
              (‖phi (x*y⁻¹)‖^2 * translationCost alpha s (ell (x*y⁻¹)))) :=
            hphi.comp (hpres x).measurable
          rw [lintegral_const_mul _ hm, (hpres x).lintegral_comp hphi]
    _ = _ := lintegral_mul_const _ hrho


/-- Uniform displacement cost on the support of one fixed test. -/
theorem translationCost_support_bound (alpha s u R : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (hR : |u| ≤ R) :
    translationCost alpha s u ≤ translationCost alpha s R := by
  have hR0 : 0 ≤ R := (abs_nonneg u).trans hR
  unfold translationCost
  rw [abs_of_nonneg hR0]
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    nlinarith
  · apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    nlinarith [sq_abs u, abs_nonneg u]
  · positivity
  · positivity

/-- The weighted test mass is bounded by a finite support constant times
its ordinary L2 mass; there is no cutoff parameter in this constant. -/
theorem genuine_weighted_test_mass_bound
    (mu : Measure (Classes K)) (ell : Classes K → ℝ) (phi : Classes K → ℂ)
    (alpha s R : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hsupp : ∀ g, phi g ≠ 0 → |ell g| ≤ R)
    (hphi : Measurable (fun g => ENNReal.ofReal (‖phi g‖^2))) :
    (∫⁻ g, ENNReal.ofReal (‖phi g‖^2 * translationCost alpha s (ell g)) ∂mu) ≤
      (∫⁻ g, ENNReal.ofReal (‖phi g‖^2) ∂mu) *
        ENNReal.ofReal (translationCost alpha s R) := by
  calc
    _ ≤ ∫⁻ g, ENNReal.ofReal (‖phi g‖^2) *
        ENNReal.ofReal (translationCost alpha s R) ∂mu := by
      apply lintegral_mono
      intro g
      dsimp only
      rw [← ENNReal.ofReal_mul (sq_nonneg ‖phi g‖)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : phi g = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left
          (translationCost_support_bound alpha s (ell g) R ha hs (hsupp g hz))
          (sq_nonneg ‖phi g‖)
    _ = _ := lintegral_mul_const _ hphi

/-- Finite energy follows from ordinary L2 masses and test support.
It still requires the genuine kernel/Hilbert-operator bridge before use as
an HS norm, and two factors before an S1 norm can be concluded. -/
theorem genuine_supported_kernel_energy_finite
    (mu : Measure (Classes K)) [SFinite mu]
    (ell : Classes K → ℝ) (rho phi : Classes K → ℂ)
    (alpha s R : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hrho : Measurable (fun x => ENNReal.ofReal (‖rho x‖^2)))
    (hphi : Measurable (fun g => ENNReal.ofReal (‖phi g‖^2)))
    (hcost : Measurable (fun g => ENNReal.ofReal
      (‖phi g‖^2 * translationCost alpha s (ell g))))
    (hsupp : ∀ g, phi g ≠ 0 → |ell g| ≤ R)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hk : AEMeasurable (fun z : Classes K × Classes K =>
      ENNReal.ofReal (‖transportedCutoffKernel K rho phi
        (fun q => stripWeight alpha s (ell q)) z.1 z.2‖^2)) (mu.prod mu))
    (hrhofin : (∫⁻ x, ENNReal.ofReal (‖rho x‖^2) ∂mu) ≠ ⊤)
    (hphifin : (∫⁻ g, ENNReal.ofReal (‖phi g‖^2) ∂mu) ≠ ⊤) :
    (∫⁻ z : Classes K × Classes K, ENNReal.ofReal
      (‖transportedCutoffKernel K rho phi
        (fun q => stripWeight alpha s (ell q)) z.1 z.2‖^2) ∂mu.prod mu) < ⊤ := by
  have hcostfin : (∫⁻ g, ENNReal.ofReal
      (‖phi g‖^2 * translationCost alpha s (ell g)) ∂mu) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hphifin ENNReal.ofReal_ne_top)
    exact genuine_weighted_test_mass_bound K mu ell phi alpha s R ha hs hsupp hphi
  exact lt_of_le_of_lt
    (genuine_kernel_unweighted_cutoff_energy K mu ell rho phi alpha s ha hs
      hlog hrho hcost hpres hk)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hrhofin hcostfin))


/-- Exact squared multiplier cost in the proposed global second-correction
factorization; unlike a fixed cutoff, its output profile is integrable. -/
theorem second_correction_split_cost (x y h : ℝ) (hxy : x = h+y) :
    (1+y^2)/(1+x^2)^2 ≤ (2*(1+h^2))/(1+x^2) := by
  have hx : 0 < 1+x^2 := by positivity
  have hy : y = x-h := by linarith
  have hp : 1+y^2 ≤ 2*(1+h^2)*(1+x^2) := by
    rw [hy]
    nlinarith [sq_nonneg (x+h), sq_nonneg (x*h)]
  calc
    _ = ((1+y^2)/(1+x^2))/(1+x^2) := by simp only [div_div, pow_two]
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_iff₀ hx).mpr hp) hx.le

/-- Direct control of the first noncompact factor's genuine kernel energy.
Hilbert-kernel realization and test factorization are still required. -/
theorem genuine_second_correction_factor_integrand
    (ell : Classes K → ℝ) (phi : Classes K → ℂ)
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (x y : Classes K) (hlog : ell x = ell (x*y⁻¹) + ell y) :
    ((1+ell y^2)/(1+ell x^2)^2) *
      ‖transportedCutoffKernel K (fun _ => 1) phi
        (fun z => stripWeight alpha s (ell z)) x y‖^2 ≤
      (2*(1+ell (x*y⁻¹)^2) * translationCost alpha s (ell (x*y⁻¹))) *
        ‖phi (x*y⁻¹)‖^2 / (1+ell x^2) := by
  have hm := second_correction_split_cost (ell x) (ell y) (ell (x*y⁻¹)) hlog
  have hk := genuine_kernel_displacement_bound K ell (fun _ => 1) phi
    alpha s ha hs x y hlog
  simp only [norm_one, one_pow, one_mul] at hk
  calc
    _ ≤ ((2*(1+ell (x*y⁻¹)^2))/(1+ell x^2)) *
        (‖phi (x*y⁻¹)‖^2 * translationCost alpha s (ell (x*y⁻¹))) :=
      mul_le_mul hm hk (by positivity) (by positivity)
    _ = _ := by ring


end
end Round93A

namespace Round94A
open NuclearBoundB90 NuclearBoundB91 Round93A
variable (K : Type*) [Field K] [NumberField K]

/-- Integrated noncompact first-factor energy in the second-correction
factorization. Its output profile is independent of every cutoff. -/
theorem genuine_second_correction_factor_energy
    (mu : Measure (Classes K))
    (ell : Classes K → ℝ) (phi : Classes K → ℂ)
    (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (htest : Measurable (fun g => ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖phi g‖^2)))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal
      (((1+ell y^2)/(1+ell x^2)^2) *
        ‖transportedCutoffKernel K (fun _ => 1) phi
          (fun z => stripWeight alpha s (ell z)) x y‖^2) ∂mu ∂mu) ≤
      (∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) ∂mu) *
      (∫⁻ g, ENNReal.ofReal
        (2*(1+ell g^2)*translationCost alpha s (ell g)*‖phi g‖^2) ∂mu) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) *
        (∫⁻ g, ENNReal.ofReal
          (2*(1+ell g^2)*translationCost alpha s (ell g)*‖phi g‖^2) ∂mu) ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (1/(1+ell x^2)) * ENNReal.ofReal
            (2*(1+ell (x*y⁻¹)^2)*translationCost alpha s (ell (x*y⁻¹))*
              ‖phi (x*y⁻¹)‖^2) ∂mu := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(1+ell x^2))]
          apply ENNReal.ofReal_le_ofReal
          convert genuine_second_correction_factor_integrand K ell phi alpha s
            ha hs x y (hlog x y) using 1
          ring
        _ = _ := by
          have hm : Measurable (fun y : Classes K => ENNReal.ofReal
              (2*(1+ell (x*y⁻¹)^2)*translationCost alpha s (ell (x*y⁻¹))*
                ‖phi (x*y⁻¹)‖^2)) := htest.comp (hpres x).measurable
          rw [lintegral_const_mul _ hm, (hpres x).lintegral_comp htest]
    _ = _ := lintegral_mul_const _ hout

/-- The first factor test cost has no output cutoff dependence. -/
theorem genuine_second_correction_test_mass
    (mu : Measure (Classes K)) (ell : Classes K → ℝ) (phi : Classes K → ℂ)
    (alpha s R : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hsupp : ∀ g, phi g ≠ 0 → |ell g| ≤ R)
    (hphi : Measurable (fun g => ENNReal.ofReal (‖phi g‖^2))) :
    (∫⁻ g, ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖phi g‖^2) ∂mu) ≤
      (∫⁻ g, ENNReal.ofReal (‖phi g‖^2) ∂mu) *
        ENNReal.ofReal (2*(1+R^2)*translationCost alpha s R) := by
  calc
    _ ≤ ∫⁻ g, ENNReal.ofReal (‖phi g‖^2) *
        ENNReal.ofReal (2*(1+R^2)*translationCost alpha s R) ∂mu := by
      apply lintegral_mono
      intro g
      dsimp only
      rw [← ENNReal.ofReal_mul (sq_nonneg ‖phi g‖)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : phi g = 0
      · simp [hz]
      · have hg := hsupp g hz
        have hR : 0 ≤ R := (abs_nonneg _).trans hg
        have hp : 2*(1+ell g^2) ≤ 2*(1+R^2) := by
          nlinarith [sq_abs (ell g), abs_nonneg (ell g)]
        have hc := translationCost_support_bound alpha s (ell g) R ha hs hg
        have hh := mul_le_mul hp hc (translationCost_nonneg _ _ _) (by positivity)
        calc
          _ ≤ (2*(1+R^2)*translationCost alpha s R)*‖phi g‖^2 :=
            mul_le_mul_of_nonneg_right hh (sq_nonneg _)
          _ = _ := by ring
    _ = _ := lintegral_mul_const _ hphi

end Round94A

namespace Round94A
open NuclearBoundB90 NuclearBoundB91 Round93A
variable (K : Type*) [Field K] [NumberField K]

/-- Finite actual output mass from the already checked logarithmic Haar
pushforward. This premise is measure normalization, not a nuclear bound. -/
theorem genuine_profile_finite_of_log_pushforward
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (hell : Measurable ell) (V : ℝ≥0)
    (hpush : Measure.map ell mu = (V : ℝ≥0∞) • volume) :
    (∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) ∂mu) < ⊤ := by
  have hg : Continuous (fun t : ℝ => (1+t^2)⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t; positivity
  have hi : Integrable (fun t : ℝ => (1+t^2)⁻¹) (Measure.map ell mu) := by
    rw [hpush]
    exact integrable_inv_one_add_sq.smul_measure (by simp)
  have hj : Integrable (fun x => (1+ell x^2)⁻¹) mu :=
    (integrable_map_measure hg.aestronglyMeasurable hell.aemeasurable).mp hi
  have hn : 0 ≤ᵐ[mu] (fun x => (1+ell x^2)⁻¹) := by
    filter_upwards with x
    positivity
  simp only [one_div]
  rw [← ofReal_integral_eq_lintegral_ofReal hj hn]
  exact ENNReal.ofReal_lt_top

/-- Genuine noncompact first-factor energy is finite. No output-profile
integrability or kernel-energy finiteness is assumed. -/
theorem genuine_second_correction_factor_finite
    (mu : Measure (Classes K))
    (ell : Classes K → ℝ) (phi : Classes K → ℂ)
    (alpha s R : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hell : Measurable ell) (V : ℝ≥0)
    (hpush : Measure.map ell mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (htest : Measurable (fun g => ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖phi g‖^2)))
    (hphi : Measurable (fun g => ENNReal.ofReal (‖phi g‖^2)))
    (hsupp : ∀ g, phi g ≠ 0 → |ell g| ≤ R)
    (hphifin : (∫⁻ g, ENNReal.ofReal (‖phi g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal
      (((1+ell y^2)/(1+ell x^2)^2) *
        ‖transportedCutoffKernel K (fun _ => 1) phi
          (fun z => stripWeight alpha s (ell z)) x y‖^2) ∂mu ∂mu) < ⊤ := by
  have hJ := genuine_profile_finite_of_log_pushforward K mu ell hell V hpush
  have hD : (∫⁻ g, ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖phi g‖^2) ∂mu) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hphifin ENNReal.ofReal_ne_top)
      (genuine_second_correction_test_mass K mu ell phi alpha s R ha hs hsupp hphi)
  exact lt_of_le_of_lt
    (genuine_second_correction_factor_energy K mu ell phi alpha s ha hs
      hlog hout htest hpres)
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hJ.ne hD))

end Round94A

namespace Round95A
noncomputable section
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A
variable (K : Type*) [Field K] [NumberField K]

/-- Squared kernel densities for the proposed two-factor realization of
M_(1/(1+ell^2)) A(psi) A(theta), without any output cutoff. -/
def leftDensity (ell : Classes K → ℝ) (alpha s : ℝ)
    (psi : Classes K → ℂ) (x y : Classes K) : ℝ≥0∞ :=
  ENNReal.ofReal (((1+ell y^2)/(1+ell x^2)^2) *
    ‖transportedCutoffKernel K (fun _ => 1) psi
      (fun z => stripWeight alpha s (ell z)) x y‖^2)

def rightDensity (ell : Classes K → ℝ) (alpha s : ℝ)
    (theta : Classes K → ℂ) (x y : Classes K) : ℝ≥0∞ :=
  ENNReal.ofReal ((1/(1+ell x^2)) *
    ‖transportedCutoffKernel K (fun _ => 1) theta
      (fun z => stripWeight alpha s (ell z)) x y‖^2)

def profileMass (mu : Measure (Classes K)) (ell : Classes K → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) ∂mu

def testMass (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (alpha s : ℝ) (theta : Classes K → ℂ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal (‖theta g‖^2 * translationCost alpha s (ell g)) ∂mu

def leftTestMass (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (alpha s : ℝ) (psi : Classes K → ℂ) : ℝ≥0∞ :=
  ∫⁻ g, ENNReal.ofReal
    (2*(1+ell g^2)*translationCost alpha s (ell g)*‖psi g‖^2) ∂mu

theorem genuine_right_factor_energy
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (theta : Classes K → ℂ) (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (htest : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2 * translationCost alpha s (ell g))))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu) :
    (∫⁻ x, ∫⁻ y, rightDensity K ell alpha s theta x y ∂mu ∂mu) ≤
      profileMass K mu ell * testMass K mu ell alpha s theta := by
  unfold rightDensity profileMass testMass
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) *
        (∫⁻ g, ENNReal.ofReal (‖theta g‖^2 * translationCost alpha s (ell g)) ∂mu) ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (1/(1+ell x^2)) * ENNReal.ofReal
            (‖theta (x*y⁻¹)‖^2 * translationCost alpha s (ell (x*y⁻¹))) ∂mu := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(1+ell x^2))]
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simpa only [norm_one, one_pow, one_mul] using
            genuine_kernel_displacement_bound K ell (fun _ => 1) theta alpha s ha hs x y (hlog x y)
        _ = _ := by
          have hm : Measurable (fun y : Classes K => ENNReal.ofReal
              (‖theta (x*y⁻¹)‖^2 * translationCost alpha s (ell (x*y⁻¹)))) :=
            htest.comp (hpres x).measurable
          rw [lintegral_const_mul _ hm, (hpres x).lintegral_comp htest]
    _ = _ := lintegral_mul_const _ hout

/-- Continuous rank-one majorant for the noncompact second correction.
The two factor costs are proved from the actual convolution kernel. -/
theorem genuine_noncompact_rankOneCost_bound
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (psi theta : Classes K → ℂ) (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s (ell g))))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hl : AEMeasurable (fun z : Classes K × Classes K =>
      leftDensity K ell alpha s psi z.1 z.2) (mu.prod mu))
    (hr : AEMeasurable (fun z : Classes K × Classes K =>
      rightDensity K ell alpha s theta z.1 z.2) (mu.prod mu)) :
    (∫⁻ z, (∫⁻ x, leftDensity K ell alpha s psi x z ∂mu) ^ (1/2 : ℝ) *
      (∫⁻ y, rightDensity K ell alpha s theta z y ∂mu) ^ (1/2 : ℝ) ∂mu) ≤
      (profileMass K mu ell * leftTestMass K mu ell alpha s psi) ^ (1/2 : ℝ) *
      (profileMass K mu ell * testMass K mu ell alpha s theta) ^ (1/2 : ℝ) := by
  let a : Classes K → ℝ≥0∞ := fun z => ∫⁻ x, leftDensity K ell alpha s psi x z ∂mu
  let b : Classes K → ℝ≥0∞ := fun z => ∫⁻ y, rightDensity K ell alpha s theta z y ∂mu
  have ham : AEMeasurable a mu := hl.lintegral_prod_left
  have hbm : AEMeasurable b mu := hr.lintegral_prod_right
  have hah : AEMeasurable (fun z => a z ^ (1/2 : ℝ)) mu := by fun_prop
  have hbh : AEMeasurable (fun z => b z ^ (1/2 : ℝ)) mu := by fun_prop
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two hah hbh
  have hp (t : ℝ≥0∞) : (t ^ (1/2 : ℝ)) ^ (2 : ℝ) = t := by
    rw [← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, hp] at hh
  have hea : (∫⁻ z, a z ∂mu) ≤ profileMass K mu ell * leftTestMass K mu ell alpha s psi := by
    dsimp only [a]
    rw [← lintegral_lintegral_swap hl]
    exact genuine_second_correction_factor_energy K mu ell psi alpha s ha hs hlog hout hpsi hpres
  have heb := genuine_right_factor_energy K mu ell theta alpha s ha hs hlog hout htheta hpres
  exact hh.trans (mul_le_mul'
    (ENNReal.rpow_le_rpow hea (by norm_num))
    (ENNReal.rpow_le_rpow heb (by norm_num)))

end
end Round95A

namespace Round95A
noncomputable section
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A
variable (K : Type*) [Field K] [NumberField K]

/-- Finiteness of the actual noncompact continuous rank-one majorant.
Neither factor energy nor majorant summability is a premise. -/
theorem genuine_noncompact_rankOneCost_finite
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hell : Measurable ell) (V : ℝ≥0)
    (hpush : Measure.map ell mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s (ell g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |ell g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |ell g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hl : AEMeasurable (fun z : Classes K × Classes K =>
      leftDensity K ell alpha s psi z.1 z.2) (mu.prod mu))
    (hr : AEMeasurable (fun z : Classes K × Classes K =>
      rightDensity K ell alpha s theta z.1 z.2) (mu.prod mu)) :
    (∫⁻ z, (∫⁻ x, leftDensity K ell alpha s psi x z ∂mu) ^ (1/2 : ℝ) *
      (∫⁻ y, rightDensity K ell alpha s theta z y ∂mu) ^ (1/2 : ℝ) ∂mu) < ⊤ := by
  have hJ : profileMass K mu ell ≠ ⊤ :=
    (genuine_profile_finite_of_log_pushforward K mu ell hell V hpush).ne
  have hD : leftTestMass K mu ell alpha s psi ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hpf ENNReal.ofReal_ne_top)
      (genuine_second_correction_test_mass K mu ell psi alpha s R ha hs hpsupp hpsi0)
  have hE : testMass K mu ell alpha s theta ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top htf ENNReal.ofReal_ne_top)
      (genuine_weighted_test_mass_bound K mu ell theta alpha s S ha hs htsupp htheta0)
  exact lt_of_le_of_lt
    (genuine_noncompact_rankOneCost_bound K mu ell psi theta alpha s ha hs hlog
      hout hpsi htheta hpres hl hr)
    (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hJ hD))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.mul_ne_top hJ hE)))

end
end Round95A

namespace Round95A
noncomputable section
open NuclearBoundB90 NuclearBoundB91 Round93A
variable (K : Type*) [Field K] [NumberField K]

def leftKernel (ell : Classes K → ℝ) (alpha s : ℝ)
    (psi : Classes K → ℂ) (x y : Classes K) : ℂ :=
  ((Real.sqrt (1+ell y^2) / (1+ell x^2) : ℝ) : ℂ) *
    transportedCutoffKernel K (fun _ => 1) psi
      (fun z => stripWeight alpha s (ell z)) x y

def rightKernel (ell : Classes K → ℝ) (alpha s : ℝ)
    (theta : Classes K → ℂ) (x y : Classes K) : ℂ :=
  (((Real.sqrt (1+ell x^2))⁻¹ : ℝ) : ℂ) *
    transportedCutoffKernel K (fun _ => 1) theta
      (fun z => stripWeight alpha s (ell z)) x y

theorem genuine_leftKernel_density (ell : Classes K → ℝ) (alpha s : ℝ)
    (psi : Classes K → ℂ) (x y : Classes K) :
    ENNReal.ofReal (‖leftKernel K ell alpha s psi x y‖^2) =
      leftDensity K ell alpha s psi x y := by
  unfold leftKernel leftDensity
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_pow, div_pow,
    Real.sq_sqrt (by positivity)]

theorem genuine_rightKernel_density (ell : Classes K → ℝ) (alpha s : ℝ)
    (theta : Classes K → ℂ) (x y : Classes K) :
    ENNReal.ofReal (‖rightKernel K ell alpha s theta x y‖^2) =
      rightDensity K ell alpha s theta x y := by
  unfold rightKernel rightDensity
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_pow, inv_pow,
    Real.sq_sqrt (by positivity), one_div]

theorem correction_split_cancellation (x z : ℝ) :
    (Real.sqrt (1+z^2)/(1+x^2)) * (Real.sqrt (1+z^2))⁻¹ = 1/(1+x^2) := by
  have hz : Real.sqrt (1+z^2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- The exact integrand has the order M_q A(psi) A(theta).
No cyclic permutation or global spectral identification is used. -/
theorem genuine_factor_kernel_cancellation (ell : Classes K → ℝ) (alpha s : ℝ)
    (psi theta : Classes K → ℂ) (x z y : Classes K) :
    leftKernel K ell alpha s psi x z * rightKernel K ell alpha s theta z y =
      ((1/(1+ell x^2) : ℝ) : ℂ) *
        (transportedCutoffKernel K (fun _ => 1) psi
          (fun q => stripWeight alpha s (ell q)) x z *
         transportedCutoffKernel K (fun _ => 1) theta
          (fun q => stripWeight alpha s (ell q)) z y) := by
  unfold leftKernel rightKernel
  calc
    _ = (((Real.sqrt (1+ell z^2)/(1+ell x^2)) *
        (Real.sqrt (1+ell z^2))⁻¹ : ℝ) : ℂ) *
        (transportedCutoffKernel K (fun _ => 1) psi
          (fun q => stripWeight alpha s (ell q)) x z *
         transportedCutoffKernel K (fun _ => 1) theta
          (fun q => stripWeight alpha s (ell q)) z y) := by push_cast; ring
    _ = _ := by rw [correction_split_cancellation]

end
end Round95A

namespace Round96A
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine noncompact correction factors are square-integrable kernels.
Their energies are derived from compact logarithmic test support, ordinary L2
masses, and the logarithmic Haar formula; no factor energy is assumed. -/
theorem genuine_noncompact_factors_memLp_two
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹) + ell y)
    (hell : Measurable ell) (V : ℝ≥0)
    (hpush : Measure.map ell mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+ell g^2)*translationCost alpha s (ell g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s (ell g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |ell g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |ell g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K ell alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K ell alpha s theta z.1 z.2) (mu.prod mu)) :
    MemLp (fun z : Classes K × Classes K =>
      leftKernel K ell alpha s psi z.1 z.2) 2 (mu.prod mu) ∧
    MemLp (fun z : Classes K × Classes K =>
      rightKernel K ell alpha s theta z.1 z.2) 2 (mu.prod mu) := by
  have hl := ENNReal.measurable_ofReal.comp_aemeasurable
    (hlm.norm.pow 2).aemeasurable
  have hr := ENNReal.measurable_ofReal.comp_aemeasurable
    (hrm.norm.pow 2).aemeasurable
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖leftKernel K ell alpha s psi z.1 z.2‖^2)) (mu.prod mu) at hl
  simp_rw [genuine_leftKernel_density] at hl
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖rightKernel K ell alpha s theta z.1 z.2‖^2)) (mu.prod mu) at hr
  simp_rw [genuine_rightKernel_density] at hr
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hlm).mpr
    refine ⟨hlm.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    simp_rw [genuine_leftKernel_density]
    rw [lintegral_prod _ hl]
    exact genuine_second_correction_factor_finite K mu ell psi alpha s R ha hs
      hlog hell V hpush hout hpsi hpsi0 hpsupp hpf hpres
  · apply (memLp_two_iff_integrable_sq_norm hrm).mpr
    refine ⟨hrm.norm.pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    simp_rw [genuine_rightKernel_density]
    rw [lintegral_prod _ hr]
    have hJ : profileMass K mu ell ≠ ⊤ :=
      (genuine_profile_finite_of_log_pushforward K mu ell hell V hpush).ne
    have hE : testMass K mu ell alpha s theta ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top htf ENNReal.ofReal_ne_top)
        (genuine_weighted_test_mass_bound K mu ell theta alpha s S ha hs htsupp htheta0)
    exact lt_of_le_of_lt
      (genuine_right_factor_energy K mu ell theta alpha s ha hs hlog hout htheta hpres)
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hJ hE))

end Round96A

namespace Round96A
open NuclearBoundB90 NuclearBoundB91 Round93A Round95A
variable (K : Type*) [Field K] [NumberField K]

/-- The square-integrable factors discharge Fubini for almost every output
and every L2 input. The preceding theorem supplies both kernel L2 premises. -/
theorem genuine_noncompact_fubini_ae
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (psi theta f : Classes K → ℂ) (alpha s : ℝ)
    (hl : MemLp (fun z : Classes K × Classes K =>
      leftKernel K ell alpha s psi z.1 z.2) 2 (mu.prod mu))
    (hr : MemLp (fun z : Classes K × Classes K =>
      rightKernel K ell alpha s theta z.1 z.2) 2 (mu.prod mu))
    (hf : MemLp f 2 mu) :
    ∀ᵐ x ∂mu, Integrable (fun p : Classes K × Classes K =>
      (leftKernel K ell alpha s psi x p.1 *
        rightKernel K ell alpha s theta p.1 p.2) * f p.2) (mu.prod mu) := by
  filter_upwards [hl.aestronglyMeasurable.prodMk_left,
    (hl.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with x hm hi
  have ha : MemLp (leftKernel K ell alpha s psi x) 2 mu :=
    (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have hm2 : AEStronglyMeasurable (fun p : Classes K × Classes K =>
      leftKernel K ell alpha s psi x p.1 * f p.2) (mu.prod mu) :=
    ha.aestronglyMeasurable.comp_fst.mul hf.aestronglyMeasurable.comp_snd
  have hp : MemLp (fun p : Classes K × Classes K =>
      leftKernel K ell alpha s psi x p.1 * f p.2) 2 (mu.prod mu) := by
    apply (memLp_two_iff_integrable_sq_norm hm2).mpr
    simpa only [norm_mul, mul_pow] using
      (ha.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
        (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  apply (hp.integrable_mul hr).congr
  filter_upwards [] with p
  change (leftKernel K ell alpha s psi x p.1 * f p.2) *
    rightKernel K ell alpha s theta p.1 p.2 = _
  ring

end Round96A

namespace Round96A
open NuclearBoundB90 NuclearBoundB91 Round93A Round95A
variable (K : Type*) [Field K] [NumberField K]

/-- The noncompact factors compose in the order M_q A(psi * theta).
This is an exact kernel identity on the genuine idele-class quotient. -/
theorem genuine_noncompact_kernel_composition
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (psi theta : Classes K → ℂ) (alpha s : ℝ)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (x y : Classes K) :
    (∫ z, leftKernel K ell alpha s psi x z *
      rightKernel K ell alpha s theta z y ∂mu) =
    transportedCutoffKernel K (fun a => ((1/(1+ell a^2) : ℝ) : ℂ))
      (convolution K mu psi theta) (fun a => stripWeight alpha s (ell a)) x y := by
  let w := fun a : Classes K => stripWeight alpha s (ell a)
  have hw (a : Classes K) : 0 < w a := stripWeight_pos alpha s (ell a)
  have htel (z : Classes K) :
      (Real.sqrt (w x / w z) : ℂ) * (Real.sqrt (w z / w y) : ℂ) =
        (Real.sqrt (w x / w y) : ℂ) := by
    have hh : Real.sqrt (w x / w z) * Real.sqrt (w z / w y) =
        Real.sqrt (w x / w y) := by
      rw [← Real.sqrt_mul (div_nonneg (hw x).le (hw z).le)]
      congr 1
      field_simp [ne_of_gt (hw z), ne_of_gt (hw y)]
    exact_mod_cast hh
  have hid : (∫ z, leftKernel K ell alpha s psi x z *
      rightKernel K ell alpha s theta z y ∂mu) =
      (((1/(1+ell x^2) : ℝ) : ℂ) * (Real.sqrt (w x / w y) : ℂ)) *
        (∫ z, psi (x*z⁻¹) * theta (z*y⁻¹) ∂mu) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [genuine_factor_kernel_cancellation]
    unfold transportedCutoffKernel
    change _ = (((1/(1+ell x^2) : ℝ) : ℂ) * (Real.sqrt (w x / w y) : ℂ)) * _
    calc
      _ = (((1/(1+ell x^2) : ℝ) : ℂ) * psi (x*z⁻¹) * theta (z*y⁻¹)) *
        ((Real.sqrt (w x / w z) : ℂ) * (Real.sqrt (w z / w y) : ℂ)) := by
          dsimp [w]; ring
      _ = _ := by rw [htel]; ring
  have hgroup (z : Classes K) : (x*z⁻¹)⁻¹*(x*y⁻¹) = z*y⁻¹ := by
    exact generic_group_cancellation x y z
  have hc := (hpres x).integral_comp (hemb x)
    (fun g => psi g * theta (g⁻¹*(x*y⁻¹)))
  simp only [hgroup] at hc
  rw [hid, hc]
  unfold transportedCutoffKernel NuclearBoundB90.convolution
  dsimp only [w]
  ring

/-- The composition identity acts on every L2 input, with Fubini discharged
by the genuine factor estimates through genuine_noncompact_factors_memLp_two. -/
theorem genuine_noncompact_action_composition_ae
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (psi theta f : Classes K → ℂ) (alpha s : ℝ)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hl : MemLp (fun z : Classes K × Classes K =>
      leftKernel K ell alpha s psi z.1 z.2) 2 (mu.prod mu))
    (hr : MemLp (fun z : Classes K × Classes K =>
      rightKernel K ell alpha s theta z.1 z.2) 2 (mu.prod mu))
    (hf : MemLp f 2 mu) :
    ∀ᵐ x ∂mu,
      (∫ z, leftKernel K ell alpha s psi x z *
        (∫ y, rightKernel K ell alpha s theta z y * f y ∂mu) ∂mu) =
      ∫ y, transportedCutoffKernel K (fun a => ((1/(1+ell a^2) : ℝ) : ℂ))
        (convolution K mu psi theta) (fun a => stripWeight alpha s (ell a)) x y * f y ∂mu := by
  filter_upwards [genuine_noncompact_fubini_ae K mu ell psi theta f alpha s hl hr hf]
    with x hF
  calc
    _ = ∫ z, ∫ y, (leftKernel K ell alpha s psi x z *
        rightKernel K ell alpha s theta z y) * f y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ y, ∫ z, (leftKernel K ell alpha s psi x z *
        rightKernel K ell alpha s theta z y) * f y ∂mu ∂mu :=
      integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_mul_const]
      rw [genuine_noncompact_kernel_composition K mu ell psi theta alpha s hpres hemb]

end Round96A

/- Exact checked arithmetic definitions extracted without rebuilding topology. -/
open scoped NumberField Valued WithZero ENNReal NNReal
open NumberField MeasureTheory
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
noncomputable instance classCommGroup : CommGroup (HeckeIdeleClasses K) := inferInstance
noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem genuineIdeleModulus_principal (a : Kˣ) :
    genuineIdeleModulus K (principalIdele K a) = 1 := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(principalIdele K a).val.1 w‖ = w (a : K) := by
    exact NumberField.InfinitePlace.Completion.norm_coe w
      ((WithAbs.equiv _).symm (a : K))
  have hf (v : NumberField.FinitePlace K) :
      ‖(principalIdele K a).val.2 v.maximalIdeal‖ = v (a : K) := by
    exact NumberField.FinitePlace.norm_embedding_eq v (a : K)
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  exact NumberField.prod_abs_eq_one (K := K) a.ne_zero
/-- Outside finitely many finite places, an actual idele has local norm one. -/
theorem genuineIdele_finite_norm_support (a : HeckeIdeles K) :
    (Function.mulSupport (fun v : NumberField.FinitePlace K =>
      ‖a.val.2 v.maximalIdeal‖)).Finite := by
  have he : ∀ᶠ v in Filter.cofinite, ‖a.val.2 v‖ = 1 := by
    filter_upwards [RestrictedProduct.eventually _ _ a.val.2,
      RestrictedProduct.eventually _ _ (a⁻¹).val.2] with v hv hi
    change Valued.v (a.val.2 v) ≤ 1 at hv
    change Valued.v ((a⁻¹).val.2 v) ≤ 1 at hi
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 := by
      have h := congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
      exact h
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm hv
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right hi _
        _ = Valued.v (a.val.2 v) := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  exact (Filter.eventually_cofinite.mp he).preimage
    NumberField.FinitePlace.maximalIdeal_injective.injOn
theorem genuineIdeleModulus_mul (a b : HeckeIdeles K) :
    genuineIdeleModulus K (a * b) = genuineIdeleModulus K a * genuineIdeleModulus K b := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(a * b).val.1 w‖ ^ w.mult =
        ‖a.val.1 w‖ ^ w.mult * ‖b.val.1 w‖ ^ w.mult := by
    change ‖a.val.1 w * b.val.1 w‖ ^ w.mult = _
    rw [norm_mul, mul_pow]
  have hf (v : NumberField.FinitePlace K) :
      ‖(a * b).val.2 v.maximalIdeal‖ =
        ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ := by
    change ‖a.val.2 v.maximalIdeal * b.val.2 v.maximalIdeal‖ = _
    exact norm_mul _ _
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib
    (genuineIdele_finite_norm_support K a) (genuineIdele_finite_norm_support K b)]
  ring

theorem genuineIdeleModulus_ne_zero (a : HeckeIdeles K) :
    genuineIdeleModulus K a ≠ 0 := by
  have h1 : genuineIdeleModulus K 1 = 1 := by
    simpa only [map_one] using genuineIdeleModulus_principal K 1
  have hp := genuineIdeleModulus_mul K a a⁻¹
  rw [mul_inv_cancel, h1] at hp
  intro hz
  rw [hz, zero_mul] at hp
  exact one_ne_zero hp


open MeasureTheory Topology Filter
open NumberField.InfinitePlace.Completion
open scoped ENNReal NNReal
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)

instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩

instance classMeasurableInv : MeasurableInv (HeckeIdeleClasses K) := by
  infer_instance
instance classMeasurableMul : MeasurableMul (HeckeIdeleClasses K) := by
  infer_instance

noncomputable def genuineIdeleLog (a : HeckeIdeles K) : ℂ :=
  (Real.log (genuineIdeleModulus K a) : ℂ)
/-- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]

/-- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
local-norm logarithm. This is not supplied by an abstract replacement norm. -/
noncomputable def genuineLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeles K →* Multiplicative ℂ where
  toFun a := Multiplicative.ofAdd (genuineIdeleLog K a)
  map_one' := by
    change genuineIdeleLog K 1 = 0
    simpa only [map_one] using genuineIdeleLog_principal K 1
  map_mul' a b := hadd a b

noncomputable def genuineClassLogHom
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b) :
    HeckeIdeleClasses K →* Multiplicative ℂ :=
  QuotientGroup.lift (principalIdeles K) (genuineLogHom K hadd) (by
    rintro x ⟨a, rfl⟩
    exact genuineIdeleLog_principal K a)

noncomputable def genuineClassLog
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (x : HeckeIdeleClasses K) : ℂ :=
  Multiplicative.toAdd (genuineClassLogHom K hadd x)

theorem genuineClassLog_mk
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (a : HeckeIdeles K) :
    genuineClassLog K hadd (QuotientGroup.mk a) = genuineIdeleLog K a := rfl

theorem genuineClassLog_translate
    (hadd : ∀ a b : HeckeIdeles K,
      genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b)
    (g x : HeckeIdeleClasses K) :
    genuineClassLog K hadd (g⁻¹ * x) =
      genuineClassLog K hadd x - genuineClassLog K hadd g := by
  unfold genuineClassLog
  rw [map_mul, map_inv]
  change -Multiplicative.toAdd (genuineClassLogHom K hadd g) +
    Multiplicative.toAdd (genuineClassLogHom K hadd x) = _
  abel


noncomputable def genuineRealClassLog (x : HeckeIdeleClasses K) : ℝ :=
  (genuineClassLog K (genuineIdeleLog_add K) x).re

theorem genuineRealClassLog_mul (x y : HeckeIdeleClasses K) :
    genuineRealClassLog K (x*y) = genuineRealClassLog K x + genuineRealClassLog K y := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_mul]
  rfl

theorem genuineRealClassLog_inv (x : HeckeIdeleClasses K) :
    genuineRealClassLog K x⁻¹ = -genuineRealClassLog K x := by
  unfold genuineRealClassLog genuineClassLog
  rw [map_inv]
  rfl

end MasulloGRH

namespace Round97A
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A
variable (K : Type*) [Field K] [NumberField K]
noncomputable abbrev actualLog : Classes K → ℝ := MasulloGRH.genuineRealClassLog K

/-- The continuous rank-one cost is finite and its kernel acts as the actual
arithmetic rational correction. No kernel L2 energy or Fubini hypothesis is
assumed: they follow from compact log support and ordinary test L2 masses.
This is not yet a Schatten operator realization or the full projected bound. -/
theorem genuine_arithmetic_correction_cost_and_action
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta f : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hf : MemLp f 2 mu)
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu)) :
    ((∫⁻ z, (∫⁻ x, leftDensity K (actualLog K) alpha s psi x z ∂mu) ^ (1/2 : ℝ) *
      (∫⁻ y, rightDensity K (actualLog K) alpha s theta z y ∂mu) ^ (1/2 : ℝ) ∂mu) < ⊤) ∧
    (∀ᵐ x ∂mu,
      (∫ z, leftKernel K (actualLog K) alpha s psi x z *
        (∫ y, rightKernel K (actualLog K) alpha s theta z y * f y ∂mu) ∂mu) =
      ∫ y, transportedCutoffKernel K (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
        (NuclearBoundB90.convolution K mu psi theta)
        (fun a => stripWeight alpha s (actualLog K a)) x y * f y ∂mu) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hlhr := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  have hl := ENNReal.measurable_ofReal.comp_aemeasurable (hlm.norm.pow 2).aemeasurable
  have hr := ENNReal.measurable_ofReal.comp_aemeasurable (hrm.norm.pow 2).aemeasurable
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖leftKernel K ell alpha s psi z.1 z.2‖^2)) (mu.prod mu) at hl
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖rightKernel K ell alpha s theta z.1 z.2‖^2)) (mu.prod mu) at hr
  simp_rw [genuine_leftKernel_density] at hl
  simp_rw [genuine_rightKernel_density] at hr
  constructor
  · exact genuine_noncompact_rankOneCost_finite K mu ell psi theta alpha s R S ha hs
      hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hl hr
  · exact genuine_noncompact_action_composition_ae K mu ell psi theta f alpha s
      hpres hemb hlhr.1 hlhr.2 hf

end Round97A

/-! Reuse B97 Hilbert norm and row-functional construction exactly. -/
namespace Round97B
theorem toLp_energy {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (g : X → ℂ) (hg : MemLp g 2 mu) :
    ‖hg.toLp g‖^2 = ∫ x, ‖g x‖^2 ∂mu := by
  let v := hg.toLp g
  have hi := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hin : Integrable (fun x => inner ℂ (v x) (v x)) mu := by
    apply hi.ofReal.congr
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  change ‖v‖^2 = _
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re hin]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

/-- Exact dual norm of the constructed kernel-row functional. -/
theorem kernel_row_functional {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (g : X → ℂ) (hg : MemLp g 2 mu) :
    ∃ L : Lp ℂ 2 mu →L[ℂ] ℂ,
      (∀ F, L F = ∫ x, g x * F x ∂mu) ∧
      ‖L‖^2 = ∫ x, ‖g x‖^2 ∂mu := by
  have hstar : MemLp (fun x => star (g x)) 2 mu :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable.star).mpr
      (by simpa using hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  let v := hstar.toLp (fun x => star (g x))
  refine ⟨innerSL ℂ v, ?_, ?_⟩
  · intro F
    rw [innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hstar.coeFn_toLp] with x hx
    change inner ℂ ((hstar.toLp (fun x => star (g x))) x) (F x) = _
    rw [hx]
    change F x * star (star (g x)) = g x * F x
    rw [star_star, mul_comm]
  · rw [innerSL_apply_norm]
    simpa [v] using toLp_energy mu (fun x => star (g x)) hstar

end Round97B

namespace Round98B
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
variable (K : Type*) [Field K] [NumberField K]

/-- Construct the actual noncompact rational-correction Hilbert columns and
row functionals, deriving their L2 membership from supported ordinary L2 tests.
No factor-energy, lift or nuclear bound is assumed. AE factor construction
does not yet supply their strong measurability or the S1 integral. -/
theorem genuine_arithmetic_correction_hilbert_factors
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu)) :
    ∀ᵐ z ∂mu, ∃ v : Lp ℂ 2 mu, ∃ L : Lp ℂ 2 mu →L[ℂ] ℂ,
      (∀ᵐ x ∂mu, v x = leftKernel K (actualLog K) alpha s psi x z) ∧
      (∀ F, L F = ∫ y, rightKernel K (actualLog K) alpha s theta z y * F y ∂mu) ∧
      ‖v‖^2 = (∫ x, ‖leftKernel K (actualLog K) alpha s psi x z‖^2 ∂mu) ∧
      ‖L‖^2 = (∫ y, ‖rightKernel K (actualLog K) alpha s theta z y‖^2 ∂mu) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  have hAi := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hBi := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  filter_upwards [hlm.prodMk_right, hrm.prodMk_left,
    hAi.prod_left_ae, hBi.prod_right_ae] with z ham hbm hai hbi
  have haL := (memLp_two_iff_integrable_sq_norm ham).mpr hai
  have hbL := (memLp_two_iff_integrable_sq_norm hbm).mpr hbi
  obtain ⟨L, hL, hLn⟩ := Round97B.kernel_row_functional mu _ hbL
  refine ⟨haL.toLp _, L, haL.coeFn_toLp, hL, ?_, hLn⟩
  exact Round97B.toLp_energy mu _ haL

end Round98B

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace Round99G

theorem toLp_energy {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (g : X → ℂ) (hg : MemLp g 2 mu) :
    ‖hg.toLp g‖^2 = ∫ x, ‖g x‖^2 ∂mu := by
  let v := hg.toLp g
  have hi := hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hin : Integrable (fun x => inner ℂ (v x) (v x)) mu := by
    apply hi.ofReal.congr
    filter_upwards [hg.coeFn_toLp] with x hx
    simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  change ‖v‖^2 = _
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re hin]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp [v, hx, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem kernel_row_bessel {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) (g : X → ℂ) (hg : MemLp g 2 mu)
    (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) (J : Finset ι) :
    ∑ i ∈ J, ‖∫ y, g y * e i y ∂mu‖^2 ≤ ∫ y, ‖g y‖^2 ∂mu := by
  have hstar : MemLp (fun x => star (g x)) 2 mu :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable.star).mpr
      (by simpa using hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  let v := hstar.toLp (fun x => star (g x))
  have hinner (i : ι) : inner ℂ v (e i) = ∫ y, g y * e i y ∂mu := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hstar.coeFn_toLp] with x hx
    change inner ℂ ((hstar.toLp (fun x => star (g x))) x) (e i x) = _
    rw [hx]
    change e i x * star (star (g x)) = g x * e i x
    rw [star_star, mul_comm]
  calc
    _ = ∑ i ∈ J, ‖inner ℂ (e i) v‖^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← hinner, norm_inner_symm]
    _ ≤ ‖v‖^2 := he.sum_inner_products_le v
    _ = _ := by simpa [v] using toLp_energy mu (fun x => star (g x)) hstar


/-- Actual integral outputs, their L2 membership and uniform finite Bessel bound
are derived from the product kernel energy, not assumed. -/
theorem kernel_orthonormal_energy {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (k : X → X → ℂ)
    (hk : MemLp (fun p : X × X => k p.1 p.2) 2 (mu.prod mu))
    (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) :
    ∃ v : ι → Lp ℂ 2 mu,
      (∀ i, ∀ᵐ x ∂mu, v i x = ∫ y, k x y * e i y ∂mu) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖v i‖^2 ≤
        ∫ p : X × X, ‖k p.1 p.2‖^2 ∂(mu.prod mu)) := by
  have hi := hk.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hrows : ∀ᵐ x ∂mu, MemLp (k x) 2 mu := by
    filter_upwards [hk.aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with x hm hx
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hx
  let F : ι → X → ℂ := fun i x => ∫ y, k x y * e i y ∂mu
  have hm (i : ι) : AEStronglyMeasurable (F i) mu :=
    (hk.aestronglyMeasurable.mul (Lp.memLp (e i)).aestronglyMeasurable.comp_snd).integral_prod_right'
  have hfi (i : ι) : Integrable (fun x => ‖F i x‖^2) mu := by
    apply hi.integral_prod_left.mono' ((hm i).norm.pow 2)
    filter_upwards [hrows] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [F] using kernel_row_bessel mu (k x) hx e he ({i} : Finset ι)
  have hmem (i : ι) : MemLp (F i) 2 mu :=
    (memLp_two_iff_integrable_sq_norm (hm i)).mpr (hfi i)
  refine ⟨fun i => (hmem i).toLp (F i), fun i => (hmem i).coeFn_toLp, ?_⟩
  intro J
  simp_rw [toLp_energy]
  rw [← integral_finset_sum J (fun i _ => hfi i)]
  rw [integral_prod _ hi]
  apply integral_mono_ae (integrable_finset_sum J (fun i _ => hfi i)) hi.integral_prod_left
  filter_upwards [hrows] with x hx
  exact kernel_row_bessel mu (k x) hx e he J

end Round99G

namespace Round99G
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
variable (K : Type*) [Field K] [NumberField K]

/-- The actual rational correction factors map every orthonormal family into
L2, with every finite sum of squared output norms bounded by the kernel energy.
All factor L2 estimates are derived from supported test data. This is a direct
Hilbert-Schmidt component, not yet a nuclear realization of the full AP. -/
theorem genuine_arithmetic_correction_orthonormal_energy
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    {ι : Type*} (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) :
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ i, ∀ᵐ x ∂mu, u i x = ∫ y, leftKernel K (actualLog K) alpha s psi x y * e i y ∂mu) ∧
      (∀ i, ∀ᵐ x ∂mu, v i x = ∫ y, rightKernel K (actualLog K) alpha s theta x y * e i y ∂mu) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖^2 ≤
        ∫ p : Classes K × Classes K, ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖v i‖^2 ≤
        ∫ p : Classes K × Classes K, ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  obtain ⟨u, hu, huN⟩ := kernel_orthonormal_energy mu (leftKernel K ell alpha s psi) hA e he
  obtain ⟨v, hv, hvN⟩ := kernel_orthonormal_energy mu (rightKernel K ell alpha s theta) hB e he
  exact ⟨u, v, hu, hv, huN, hvN⟩

end Round99G

namespace Round100E
open MeasureTheory
open scoped BigOperators

/-- The right factor is conjugate-transposed, so the rank-one family is
oriented for B C, rather than B C*. -/
theorem kernel_pair_nuclear_cost {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (B C : X → X → ℂ)
    (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu))
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) :
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ i, ∀ᵐ x ∂mu, u i x = ∫ y, B x y * e i y ∂mu) ∧
      (∀ i, ∀ᵐ x ∂mu, v i x = ∫ y, star (C y x) * e i y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        ((∫ p : X × X, ‖B p.1 p.2‖^2 ∂(mu.prod mu)) +
         (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu))) / 2) := by
  have hCt : MemLp (fun p : X × X => star (C p.2 p.1)) 2 (mu.prod mu) := by
    simpa only [Function.comp_def, Pi.star_apply] using
      (hC.comp_measurePreserving Measure.measurePreserving_swap).star
  obtain ⟨u, hu, huN⟩ := Round99G.kernel_orthonormal_energy mu B hB e he
  obtain ⟨v, hv, hvN⟩ := Round99G.kernel_orthonormal_energy mu
    (fun x y => star (C y x)) hCt e he
  have hswap : (∫ p : X × X, ‖star (C p.2 p.1)‖^2 ∂(mu.prod mu)) =
      ∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu) := by
    simpa using integral_prod_swap (μ := mu) (ν := mu)
      (fun p : X × X => ‖C p.1 p.2‖^2)
  have hcost (J : Finset ι) : ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
      ((∫ p : X × X, ‖B p.1 p.2‖^2 ∂(mu.prod mu)) +
       (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu))) / 2 := by
    calc
      _ ≤ ∑ i ∈ J, (‖u i‖^2 + ‖v i‖^2) / 2 := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]
      _ = ((∑ i ∈ J, ‖u i‖^2) + (∑ i ∈ J, ‖v i‖^2)) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ _ := by
        have hu' := huN J
        have hv' := hvN J
        rw [hswap] at hv'
        linarith
  exact ⟨u, v, hu, hv,
    summable_of_sum_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcost,
    hcost⟩


/-- The displayed Hilbert rank-one operators form a norm-convergent series
when their derived nuclear costs are summable. This helper does not identify
its sum with a manuscript operator. -/
theorem rankOne_series_of_cost {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u v : ι → H) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun i => ‖(innerSL ℂ (v i)).smulRight (u i)‖) ∧
    Summable (fun i => (innerSL ℂ (v i)).smulRight (u i)) := by
  have hb (i : ι) : ‖(innerSL ℂ (v i)).smulRight (u i)‖ ≤ ‖u i‖ * ‖v i‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro f
    have h := mul_le_mul_of_nonneg_right ((innerSL ℂ (v i)).le_opNorm f) (norm_nonneg (u i))
    simpa [ContinuousLinearMap.smulRight_apply, norm_smul, innerSL_apply_norm,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hn : Summable (fun i => ‖(innerSL ℂ (v i)).smulRight (u i)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb hc
  exact ⟨hn, hn.of_norm⟩

end Round100E

namespace Round100E
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
variable (K : Type*) [Field K] [NumberField K]

/-- Derived summable nuclear cost for the authentic rational-correction
factor family, retaining only the supported test and measure inputs.
The rank-one series has not yet been reconstructed as the full AP. -/
theorem genuine_arithmetic_correction_summable_rankOne
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    {ι : Type*} (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) :
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ i, ∀ᵐ x ∂mu, u i x = ∫ y,
        leftKernel K (actualLog K) alpha s psi x y * e i y ∂mu) ∧
      (∀ i, ∀ᵐ x ∂mu, v i x = ∫ y,
        star (rightKernel K (actualLog K) alpha s theta y x) * e i y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        ((∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) +
         (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) / 2) ∧
      Summable (fun i => ‖(innerSL ℂ (v i)).smulRight (u i)‖) ∧
      Summable (fun i => (innerSL ℂ (v i)).smulRight (u i)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  obtain ⟨u, v, hu, hv, hc, hN⟩ := kernel_pair_nuclear_cost mu
    (leftKernel K ell alpha s psi) (rightKernel K ell alpha s theta) hA hB e he
  obtain ⟨hn, ht⟩ := rankOne_series_of_cost u v hc
  exact ⟨u, v, hu, hv, hc, hN, hn, ht⟩

end Round100E

namespace Round99B
/-- Row Cauchy-Schwarz, integrated on the actual product measure. -/
theorem kernel_action_energy {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (k : X × X → ℂ)
    (hk : MemLp k 2 (mu.prod mu)) (F : Lp ℂ 2 mu) :
    MemLp (fun x => ∫ y, k (x,y) * F y ∂mu) 2 mu ∧
    (∫ x, ‖∫ y, k (x,y) * F y ∂mu‖^2 ∂mu) ≤
      (∫ p, ‖k p‖^2 ∂(mu.prod mu)) * ‖F‖^2 := by
  have hki := hk.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hm := (hk.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable F).comp_snd).integral_prod_right'
  have hb : ∀ᵐ x ∂mu, ‖∫ y, k (x,y) * F y ∂mu‖^2 ≤
      (∫ y, ‖k (x,y)‖^2 ∂mu) * ‖F‖^2 := by
    filter_upwards [hk.aestronglyMeasurable.prodMk_left, hki.prod_right_ae]
      with x hxm hxi
    have hx := (memLp_two_iff_integrable_sq_norm hxm).mpr hxi
    obtain ⟨L, hL, hn⟩ := Round97B.kernel_row_functional mu _ hx
    have hp := pow_le_pow_left₀ (norm_nonneg (L F)) (L.le_opNorm F) 2
    simpa only [hL F, mul_pow, hn] using hp
  have hd := hki.integral_prod_left.mul_const (‖F‖^2)
  have hi : Integrable (fun x => ‖∫ y, k (x,y) * F y ∂mu‖^2) mu := by
    apply hd.mono' (hm.norm.pow 2)
    simpa only [Pi.pow_apply, Pi.mul_apply, Real.norm_eq_abs, abs_pow, abs_norm] using hb
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hi, ?_⟩
  calc
    _ ≤ ∫ x, (∫ y, ‖k (x,y)‖^2 ∂mu) * ‖F‖^2 ∂mu := integral_mono_ae hi hd hb
    _ = _ := by rw [integral_mul_const, integral_integral hki]
end Round99B

namespace Round100H
open MeasureTheory
/-- Realize an actual square-integrable kernel as a bounded operator.
This is the operator-realization step, not an assertion of nuclearity. -/
theorem kernel_bounded_operator {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (k : X × X → ℂ)
    (hk : MemLp k 2 (mu.prod mu)) :
    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, T F x = ∫ y, k (x,y) * F y ∂mu) ∧
      ‖T‖ ≤ Real.sqrt (∫ p, ‖k p‖^2 ∂(mu.prod mu)) := by
  let out (F : Lp ℂ 2 mu) :=
    (Round99B.kernel_action_energy mu k hk F).1.toLp
      (fun x => ∫ y, k (x,y) * F y ∂mu)
  have hout (F : Lp ℂ 2 mu) :
      ∀ᵐ x ∂mu, out F x = ∫ y, k (x,y) * F y ∂mu :=
    (Round99B.kernel_action_energy mu k hk F).1.coeFn_toLp
  have hrows : ∀ᵐ x ∂mu, MemLp (fun y => k (x,y)) 2 mu := by
    have hi := hk.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    filter_upwards [hk.aestronglyMeasurable.prodMk_left, hi.prod_right_ae]
      with x hm hi
    exact (memLp_two_iff_integrable_sq_norm hm).mpr hi
  let A : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu :=
    { toFun := out
      map_add' := by
        intro F G
        apply Lp.ext
        filter_upwards [hout (F+G), hout F, hout G,
          Lp.coeFn_add (out F) (out G), hrows] with x hfg hf hg hadd hx
        obtain ⟨L, hL, hn⟩ := Round97B.kernel_row_functional mu _ hx
        rw [hfg, hadd]
        simp only [Pi.add_apply]
        rw [hf, hg, ← hL (F+G), ← hL F, ← hL G, map_add]
      map_smul' := by
        intro c F
        apply Lp.ext
        filter_upwards [hout (c • F), hout F,
          Lp.coeFn_smul c (out F), hrows] with x hcf hf hsmul hx
        obtain ⟨L, hL, hn⟩ := Round97B.kernel_row_functional mu _ hx
        change out (c • F) x = (c • out F) x
        rw [hcf, hsmul]
        simp only [Pi.smul_apply]
        rw [hf, ← hL (c • F), ← hL F, map_smul] }
  let E : ℝ := ∫ p, ‖k p‖^2 ∂(mu.prod mu)
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  have hbound (F : Lp ℂ 2 mu) : ‖A F‖ ≤ Real.sqrt E * ‖F‖ := by
    have he := (Round99B.kernel_action_energy mu k hk F).2
    have hn := Round97B.toLp_energy mu _ (Round99B.kernel_action_energy mu k hk F).1
    change ‖A F‖^2 = _ at hn
    rw [← hn] at he
    have hs := Real.sq_sqrt hE
    have hr := Real.sqrt_nonneg E
    change ‖A F‖^2 ≤ E * ‖F‖^2 at he
    have he2 : ‖A F‖^2 ≤ (Real.sqrt E * ‖F‖)^2 := by
      rw [mul_pow, hs]
      exact he
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _))).mp he2
  let T := A.mkContinuous (Real.sqrt E) hbound
  refine ⟨T, ?_, ?_⟩
  · exact hout
  · exact LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg E) _
end Round100H


namespace Round101H
open MeasureTheory

/-- Absolute Fubini pairing for the actual conjugate-transposed kernel. -/
theorem kernel_transpose_pairing {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (C : X → X → ℂ)
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (e F v out : Lp ℂ 2 mu)
    (hv : ∀ᵐ y ∂mu, v y = ∫ z, star (C z y) * e z ∂mu)
    (hout : ∀ᵐ z ∂mu, out z = ∫ y, C z y * F y ∂mu) :
    inner ℂ v F = inner ℂ e out := by
  have he := (Lp.memLp e).star
  have hf := Lp.memLp F
  have hm : AEStronglyMeasurable (fun p : X × X => star (e p.1) * F p.2) (mu.prod mu) :=
    he.aestronglyMeasurable.comp_fst.mul hf.aestronglyMeasurable.comp_snd
  have hp : MemLp (fun p : X × X => star (e p.1) * F p.2) 2 (mu.prod mu) := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    simpa only [norm_mul, mul_pow] using
      (he.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
        (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hi := hp.integrable_mul hC
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ y, ∫ z, (star (e z) * F y) * C z y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [hv] with y hy
      change F y * star (v y) = _
      rw [hy]
      change F y * (starRingEnd ℂ) (∫ z, star (C z y) * e z ∂mu) = _
      rw [← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      simp [mul_comm, mul_left_comm]
    _ = ∫ z, ∫ y, (star (e z) * F y) * C z y ∂mu ∂mu :=
      (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hout] with z hz
      change _ = out z * star (e z)
      rw [hz, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      ring


/-- The complete-basis series reconstructs the correctly ordered kernel product. -/
theorem kernel_basis_reconstruction {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (C : X → X → ℂ)
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (A B : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (hB : ∀ F, ∀ᵐ z ∂mu, B F z = ∫ y, C z y * F y ∂mu)
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (v : ι → Lp ℂ 2 mu)
    (hv : ∀ i, ∀ᵐ y ∂mu, v i y = ∫ z, star (C z y) * e i z ∂mu)
    (F : Lp ℂ 2 mu) :
    HasSum (fun i => inner ℂ (v i) F • A (e i)) ((A.comp B) F) := by
  have hp (i) : inner ℂ (v i) F = inner ℂ (e i) (B F) :=
    kernel_transpose_pairing mu C hC (e i) F (v i) (B F) (hv i) (hB F)
  simpa only [map_smul, HilbertBasis.repr_apply_apply, ← hp,
    ContinuousLinearMap.comp_apply] using A.hasSum (e.hasSum_repr (B F))

end Round101H

namespace Round101H
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_arithmetic_correction_nuclear_representation
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (NuclearBoundB90.convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        ((∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) +
         (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) / 2) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  obtain ⟨A, hAa, hAn⟩ := Round100H.kernel_bounded_operator mu _ hA
  obtain ⟨B, hBa, hBn⟩ := Round100H.kernel_bounded_operator mu _ hB
  obtain ⟨u, v, hu, hv, hc, hN⟩ := Round100E.kernel_pair_nuclear_cost mu
    (leftKernel K ell alpha s psi) (rightKernel K ell alpha s theta) hA hB e e.orthonormal
  have huA (i) : u i = A (e i) := by
    apply Lp.ext
    filter_upwards [hu i, hAa (e i)] with x hx hy
    exact hx.trans hy.symm
  refine ⟨A.comp B, u, v, ?_, hc, hN, ?_⟩
  · intro F
    have hf : MemLp (fun x => F x) 2 mu := Lp.memLp F
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb hf hlm hrm).2
    filter_upwards [hAa (B F), hact] with x hx hact
    change A (B F) x = _
    rw [hx, ← hact]
    apply integral_congr_ae
    filter_upwards [hBa F] with z hz
    rw [hz]
  · intro F
    simpa only [huA] using kernel_basis_reconstruction mu
      (rightKernel K ell alpha s theta) hB A B hBa e v hv F

end Round101H

namespace Round130C
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round99G
open scoped BigOperators
theorem bounded_multiplier_energy {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f c : X → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hf : MemLp f 2 mu) (hc : AEStronglyMeasurable c mu)
    (hb : ∀ x, ‖c x‖ ≤ C) :
    MemLp (fun x => c x*f x) 2 mu ∧
    Real.sqrt (∫ x, ‖c x*f x‖^2 ∂mu) ≤
      C*Real.sqrt (∫ x, ‖f x‖^2 ∂mu) := by
  have hi := hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hm := hc.mul hf.aestronglyMeasurable
  have hpoint (x : X) : ‖c x*f x‖^2 ≤ C^2*‖f x‖^2 := by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2)
      (sq_nonneg _)
  have hnew : Integrable (fun x => ‖c x*f x‖^2) mu := by
    apply (hi.const_mul (C^2)).mono' (hm.norm.pow 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint x
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hnew, ?_⟩
  have he : (∫ x, ‖c x*f x‖^2 ∂mu) ≤ C^2*(∫ x, ‖f x‖^2 ∂mu) := by
    rw [← integral_const_mul]
    exact integral_mono_ae hnew (hi.const_mul (C^2)) (Filter.Eventually.of_forall hpoint)
  have hh := Real.sqrt_le_sqrt he
  rwa [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at hh

theorem kernel_rankOne_cost_sharp {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (B C : X → X → ℂ)
    (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu))
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) :
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ i, ∀ᵐ x ∂mu, u i x = ∫ y, B x y * e i y ∂mu) ∧
      (∀ i, ∀ᵐ y ∂mu, v i y = ∫ z, star (C z y) * e i z ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖innerSL ℂ (v i)‖ ≤
        Real.sqrt (∫ p : X × X, ‖B p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu))) := by
  have hCs : MemLp (fun p : X × X => star (C p.2 p.1)) 2 (mu.prod mu) := by
    simpa [Function.comp_def] using (hC.comp_measurePreserving Measure.measurePreserving_swap).star
  obtain ⟨u, hu, huN⟩ := kernel_orthonormal_energy mu B hB e he
  obtain ⟨v, hv, hvN⟩ := kernel_orthonormal_energy mu (fun y z => star (C z y)) hCs e he
  have hswap : (∫ p : X × X, ‖star (C p.2 p.1)‖^2 ∂(mu.prod mu)) =
      ∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu) := by
    simpa using integral_prod_swap (μ := mu) (ν := mu) (fun p : X × X => ‖C p.1 p.2‖^2)
  have hbound (J : Finset ι) : ∑ i ∈ J, ‖u i‖ * ‖innerSL ℂ (v i)‖ ≤
      Real.sqrt (∫ p : X × X, ‖B p.1 p.2‖^2 ∂(mu.prod mu)) *
      Real.sqrt (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu)) := by
    simp_rw [innerSL_apply_norm]
    calc
      _ ≤ Real.sqrt (∑ i ∈ J, ‖u i‖^2) * Real.sqrt (∑ i ∈ J, ‖v i‖^2) :=
        Real.sum_mul_le_sqrt_mul_sqrt J (fun i => ‖u i‖) (fun i => ‖v i‖)
      _ ≤ _ := by
        apply mul_le_mul (Real.sqrt_le_sqrt (huN J)) _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        apply Real.sqrt_le_sqrt
        have hvJ := hvN J
        rw [hswap] at hvJ
        exact hvJ
  exact ⟨u, v, hu, hv, summable_of_sum_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound, hbound⟩

variable (K : Type*) [Field K] [NumberField K]
theorem genuine_compact_output_nuclear_representation
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    (c : Classes K → ℂ) (L : ℝ)
    (hcb : ∀ x, ‖c x‖ ≤ 1)
    (hcsupp : ∀ x, c x ≠ 0 → |actualLog K x| ≤ L)
    (hcm : AEStronglyMeasurable (fun p : Classes K × Classes K =>
      (((1+(actualLog K p.1)^2 : ℝ) : ℂ) * c p.1)) (mu.prod mu))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K
          c
          (NuclearBoundB90.convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖innerSL ℂ (v i)‖ ≤
        (1+L^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  let d (x : Classes K) : ℂ := ((1+ell x^2 : ℝ) : ℂ) * c x
  have hd (x) : ‖d x‖ ≤ 1+L^2 := by
    by_cases hz : c x = 0
    · simp [d, hz]; positivity
    have ht := pow_le_pow_left₀ (abs_nonneg (ell x)) (hcsupp x hz) 2
    have ht' : ell x^2 ≤ L^2 := by simpa [sq_abs] using ht
    dsimp [d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1+ell x^2)]
    calc
      _ ≤ (1+ell x^2)*1 := mul_le_mul_of_nonneg_left (hcb x) (by positivity)
      _ ≤ 1+L^2 := by nlinarith
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  let left (x y : Classes K) := d x * leftKernel K ell alpha s psi x y
  obtain ⟨hD, hDE⟩ := bounded_multiplier_energy (mu.prod mu)
    (fun p : Classes K × Classes K => leftKernel K ell alpha s psi p.1 p.2)
    (fun p : Classes K × Classes K => d p.1) (1+L^2) (by positivity)
    hA hcm (fun p => hd p.1)
  obtain ⟨A, hAa, hAn⟩ := Round100H.kernel_bounded_operator mu _ hD
  obtain ⟨B, hBa, hBn⟩ := Round100H.kernel_bounded_operator mu _ hB
  obtain ⟨u, v, hu, hv, hc, hN⟩ := kernel_rankOne_cost_sharp mu
    left (rightKernel K ell alpha s theta) hD hB e e.orthonormal
  have huA (i) : u i = A (e i) := by
    apply Lp.ext
    filter_upwards [hu i, hAa (e i)] with x hx hy
    exact hx.trans hy.symm
  refine ⟨A.comp B, u, v, ?_, hc, ?_, ?_⟩
  · intro F
    have hf : MemLp (fun x => F x) 2 mu := Lp.memLp F
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb hf hlm hrm).2
    filter_upwards [hAa (B F), hact] with x hx hact
    change A (B F) x = _
    rw [hx]
    calc
      _ = d x * (∫ z, leftKernel K ell alpha s psi x z *
          (∫ y, rightKernel K ell alpha s theta z y * F y ∂mu) ∂mu) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hBa F] with z hz
        rw [hz]
        ring
      _ = _ := by
        rw [hact, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [d, transportedCutoffKernel]
        have hq : (1+ell x^2 : ℝ) ≠ 0 := by positivity
        have hqc : ((1+ell x^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
        push_cast at hqc ⊢
        dsimp [ell] at hqc ⊢
        field_simp [hqc]
  · intro J
    exact (hN J).trans (mul_le_mul_of_nonneg_right hDE (Real.sqrt_nonneg _))
  · intro F
    simpa only [huA] using Round101H.kernel_basis_reconstruction mu
      (rightKernel K ell alpha s theta) hB A B hBa e v hv F

#check genuine_compact_output_nuclear_representation
#print axioms genuine_compact_output_nuclear_representation
end Round130C

namespace Round130C
open MasulloGRH MeasureTheory
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
local notation "G" => HeckeIdeleClasses K
local notation "ell" => genuineRealClassLog K

/-- The compact output part of the actual weighted-adjoint kernel has
compact input support enlarged only by the test support radius. -/
theorem genuine_compact_kernel_input_support
    (phi c : G → ℂ) (R L : ℝ)
    (hphi : ∀ g, phi g ≠ 0 → |ell g| ≤ R)
    (hc : ∀ x, c x ≠ 0 → |ell x| ≤ L)
    (x y : G) (hne : c x * phi (x*y⁻¹) ≠ 0) :
    |ell y| ≤ L+R := by
  have hx : c x ≠ 0 := fun hz => hne (by simp [hz])
  have hp : phi (x*y⁻¹) ≠ 0 := fun hz => hne (by simp [hz])
  have hl : ell y = ell x - ell (x*y⁻¹) := by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv]
    ring
  calc
    |ell y| = |ell x - ell (x*y⁻¹)| := congrArg abs hl
    _ ≤ |ell x| + |ell (x*y⁻¹)| := abs_sub _ _
    _ ≤ L+R := add_le_add (hc x hx) (hphi (x*y⁻¹) hp)

/-- Literal insertion of the enlarged input cutoff; the coefficient can
include either orientation of the native weight ratio. -/
theorem genuine_compact_kernel_cutoff_insertion
    (phi c : G → ℂ) (W : G → G → ℂ) (R L : ℝ)
    (hphi : ∀ g, phi g ≠ 0 → |ell g| ≤ R)
    (hc : ∀ x, c x ≠ 0 → |ell x| ≤ L) (x y : G) :
    c x * phi (x*y⁻¹) * W x y =
      c x * phi (x*y⁻¹) * W x y *
        (if |ell y| ≤ L+R then 1 else 0) := by
  by_cases hz : c x * phi (x*y⁻¹) = 0
  · simp [hz]
  · rw [if_pos (genuine_compact_kernel_input_support K phi c R L hphi hc x y hz), mul_one]

#check genuine_compact_kernel_cutoff_insertion
#print axioms genuine_compact_kernel_cutoff_insertion
end
end Round130C

namespace Round130Sign
open MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
local notation "G" => HeckeIdeleClasses K
local notation "ell" => genuineRealClassLog K

def positiveHalf (x : G) : ℂ := if 0 ≤ ell x then 1 else 0

/-- The sign-cutoff commutator is confined to the test's fixed log slab. -/
theorem genuine_sign_commutator_support (phi : G → ℂ) (R : ℝ)
    (hsupp : ∀ g, phi g ≠ 0 → |ell g| ≤ R) (x y : G)
    (hne : (positiveHalf K x - positiveHalf K y) * phi (x*y⁻¹) ≠ 0) :
    |ell x| ≤ R ∧ |ell y| ≤ R := by
  have hp : phi (x*y⁻¹) ≠ 0 := fun hz => hne (by simp [hz])
  have hg := abs_le.mp (hsupp (x*y⁻¹) hp)
  rw [genuineRealClassLog_mul, genuineRealClassLog_inv] at hg
  by_cases hx : 0 ≤ ell x <;> by_cases hy : 0 ≤ ell y
  · simp [positiveHalf, hx, hy] at hne
  · rw [abs_of_nonneg hx, abs_of_neg (lt_of_not_ge hy)]
    constructor <;> linarith
  · rw [abs_of_neg (lt_of_not_ge hx), abs_of_nonneg hy]
    constructor <;> linarith
  · simp [positiveHalf, hx, hy] at hne

#check genuine_sign_commutator_support
#print axioms genuine_sign_commutator_support
end
end Round130Sign

namespace Round131C
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round99G Round130C
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
/-- Actual compact-output kernel with a contractive input multiplier.
The cost is derived from genuine convolution factors, unchanged by b. -/
theorem genuine_compact_input_output_nuclear_representation
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    (c : Classes K → ℂ) (L : ℝ)
    (hcb : ∀ x, ‖c x‖ ≤ 1)
    (hcsupp : ∀ x, c x ≠ 0 → |actualLog K x| ≤ L)
    (hcm : AEStronglyMeasurable (fun p : Classes K × Classes K =>
      (((1+(actualLog K p.1)^2 : ℝ) : ℂ) * c p.1)) (mu.prod mu))
    (b : Classes K → ℂ) (hbb : ∀ x, ‖b x‖ ≤ 1)
    (hbm : AEStronglyMeasurable b mu)
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K
          c
          (NuclearBoundB90.convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * (b y * F y) ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖innerSL ℂ (v i)‖ ≤
        (1+L^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  let d (x : Classes K) : ℂ := ((1+ell x^2 : ℝ) : ℂ) * c x
  have hd (x) : ‖d x‖ ≤ 1+L^2 := by
    by_cases hz : c x = 0
    · simp [d, hz]; positivity
    have ht := pow_le_pow_left₀ (abs_nonneg (ell x)) (hcsupp x hz) 2
    have ht' : ell x^2 ≤ L^2 := by simpa [sq_abs] using ht
    dsimp [d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1+ell x^2)]
    calc
      _ ≤ (1+ell x^2)*1 := mul_le_mul_of_nonneg_left (hcb x) (by positivity)
      _ ≤ 1+L^2 := by nlinarith
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  let left (x y : Classes K) := d x * leftKernel K ell alpha s psi x y
  obtain ⟨hD, hDE⟩ := bounded_multiplier_energy (mu.prod mu)
    (fun p : Classes K × Classes K => leftKernel K ell alpha s psi p.1 p.2)
    (fun p : Classes K × Classes K => d p.1) (1+L^2) (by positivity)
    hA hcm (fun p => hd p.1)
  obtain ⟨A, hAa, hAn⟩ := Round100H.kernel_bounded_operator mu _ hD
  let right (x y : Classes K) := b y * rightKernel K ell alpha s theta x y
  obtain ⟨hE, hEE⟩ := bounded_multiplier_energy (mu.prod mu)
    (fun p : Classes K × Classes K => rightKernel K ell alpha s theta p.1 p.2)
    (fun p : Classes K × Classes K => b p.2) 1 zero_le_one hB
    hbm.comp_snd (fun p => hbb p.2)
  simp only [one_mul] at hEE
  obtain ⟨B, hBa, hBn⟩ := Round100H.kernel_bounded_operator mu _ hE
  obtain ⟨u, v, hu, hv, hc, hN⟩ := kernel_rankOne_cost_sharp mu
    left right hD hE e e.orthonormal
  have huA (i) : u i = A (e i) := by
    apply Lp.ext
    filter_upwards [hu i, hAa (e i)] with x hx hy
    exact hx.trans hy.symm
  refine ⟨A.comp B, u, v, ?_, hc, ?_, ?_⟩
  · intro F
    have hf : MemLp (fun x => b x * F x) 2 mu :=
      (bounded_multiplier_energy mu (fun x => F x) b 1 zero_le_one
        (Lp.memLp F) hbm hbb).1
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => b x * F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb hf hlm hrm).2
    filter_upwards [hAa (B F), hact] with x hx hact
    change A (B F) x = _
    rw [hx]
    calc
      _ = d x * (∫ z, leftKernel K ell alpha s psi x z *
          (∫ y, rightKernel K ell alpha s theta z y * (b y * F y) ∂mu) ∂mu) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hBa F] with z hz
        have hz' : B F z = ∫ y, rightKernel K ell alpha s theta z y * (b y * F y) ∂mu := by
          rw [hz]
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        rw [hz']
        ring
      _ = _ := by
        rw [hact, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with y
        dsimp [d, transportedCutoffKernel]
        have hq : (1+ell x^2 : ℝ) ≠ 0 := by positivity
        have hqc : ((1+ell x^2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq
        push_cast at hqc ⊢
        dsimp [ell] at hqc ⊢
        field_simp [hqc]
  · intro J
    exact (hN J).trans (mul_le_mul hDE hEE
      (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
  · intro F
    simpa only [huA] using Round101H.kernel_basis_reconstruction mu
      right hE A B hBa e v hv F


#check genuine_compact_input_output_nuclear_representation
#print axioms genuine_compact_input_output_nuclear_representation
end Round131C

namespace Round131C
open MasulloGRH Round130Sign
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
local notation "G" => HeckeIdeleClasses K
local notation "ell" => genuineRealClassLog K

def slab (R : ℝ) (x : G) : ℂ := if |ell x| ≤ R then 1 else 0

/-- The two bounded multipliers in the compact-output nuclear construction
recover the sign commutator exactly, at the fixed test-support radius. -/
theorem genuine_sign_commutator_decomposition (phi : G → ℂ) (R : ℝ)
    (hsupp : ∀ g, phi g ≠ 0 → |ell g| ≤ R) (x y : G) :
    (positiveHalf K x - positiveHalf K y) * phi (x*y⁻¹) =
      (slab K R x * positiveHalf K x) * phi (x*y⁻¹) -
      slab K R x * phi (x*y⁻¹) * positiveHalf K y := by
  by_cases hz : (positiveHalf K x - positiveHalf K y) * phi (x*y⁻¹) = 0
  · calc
      _ = slab K R x * ((positiveHalf K x - positiveHalf K y) * phi (x*y⁻¹)) := by rw [hz, mul_zero]
      _ = _ := by ring
  · have hx := (genuine_sign_commutator_support K phi R hsupp x y hz).1
    simp only [slab, if_pos hx, one_mul]
    ring

theorem slab_bound (R : ℝ) (x : G) : ‖slab K R x‖ ≤ 1 := by
  unfold slab
  split <;> simp

theorem sign_slab_bound (R : ℝ) (x : G) :
    ‖slab K R x * positiveHalf K x‖ ≤ 1 := by
  unfold slab positiveHalf
  split <;> split <;> simp

theorem sign_slab_support (R : ℝ) (x : G)
    (hx : slab K R x * positiveHalf K x ≠ 0) : |ell x| ≤ R := by
  by_contra h
  simp [slab, h] at hx

#check genuine_sign_commutator_decomposition
#print axioms genuine_sign_commutator_decomposition
end
end Round131C

open Filter Topology
namespace Round102B

theorem lp_energy {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (u : Lp ℂ 2 mu) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂mu := by
  have hi := (Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hin : Integrable (fun x => inner ℂ (u x) (u x)) mu := by
    apply hi.ofReal.congr
    filter_upwards [] with x
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re hin]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

noncomputable def cutoffSize {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : X → ℂ) (u : Lp ℂ 2 mu) : ℝ :=
  Real.sqrt (∫ x, ‖(rho x - 1) * u x‖^2 ∂mu)

theorem cutoff_density_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : X → ℂ) (u : Lp ℂ 2 mu)
    (hr : ∀ x, ‖rho x‖ ≤ 1) (x : X) :
    ‖‖(rho x - 1) * u x‖^2‖ ≤ 4 * ‖u x‖^2 := by
  have hb : ‖rho x - 1‖ ≤ 2 := by
    have ht := norm_sub_le (rho x) (1 : ℂ)
    simp only [norm_one] at ht
    linarith [hr x]
  have hs : ‖rho x - 1‖^2 ≤ (4 : ℝ) := by
    nlinarith [norm_nonneg (rho x - 1)]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)

theorem cutoffSize_le {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : X → ℂ) (u : Lp ℂ 2 mu)
    (hr : ∀ x, ‖rho x‖ ≤ 1) (hm : AEStronglyMeasurable rho mu) :
    cutoffSize mu rho u ≤ 2 * ‖u‖ := by
  have hi := (Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hme := ((hm.sub (aestronglyMeasurable_const (b := (1 : ℂ)))).mul (Lp.aestronglyMeasurable u)).norm.pow 2
  have hd : ∀ᵐ x ∂mu, ‖‖(rho x - 1) * u x‖^2‖ ≤ 4 * ‖u x‖^2 :=
    Filter.Eventually.of_forall (cutoff_density_bound mu rho u hr)
  have hie : Integrable (fun x => ‖(rho x - 1) * u x‖^2) mu :=
    (hi.const_mul 4).mono' hme hd
  have hb : (∫ x, ‖(rho x - 1) * u x‖^2 ∂mu) ≤ 4 * ‖u‖^2 := by
    rw [lp_energy mu u, ← integral_const_mul]
    apply integral_mono_ae hie (hi.const_mul 4)
    filter_upwards [hd] with x hx
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hx)
  unfold cutoffSize
  have hn : 0 ≤ ∫ x, ‖(rho x - 1) * u x‖^2 ∂mu := integral_nonneg (fun _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have hp := Real.sqrt_nonneg (∫ x, ‖(rho x - 1) * u x‖^2 ∂mu)
  nlinarith [norm_nonneg u]

theorem cutoffSize_tendsto_zero {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : ℕ → X → ℂ) (u : Lp ℂ 2 mu)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    Tendsto (fun n => cutoffSize mu (rho n) u) atTop (𝓝 0) := by
  have hi := (Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hme (n) : AEStronglyMeasurable (fun x => ‖(rho n x - 1) * u x‖^2) mu :=
    (((hm n).sub (aestronglyMeasurable_const (b := (1 : ℂ)))).mul (Lp.aestronglyMeasurable u)).norm.pow 2
  have hd (n) : ∀ᵐ x ∂mu, ‖‖(rho n x - 1) * u x‖^2‖ ≤ 4 * ‖u x‖^2 :=
    Filter.Eventually.of_forall (cutoff_density_bound mu (rho n) u (hr n))
  have hp : ∀ᵐ x ∂mu, Tendsto (fun n => ‖(rho n x - 1) * u x‖^2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hl] with x hx
    simpa using (((hx.sub_const 1).mul_const (u x)).norm.pow 2)
  have he := tendsto_integral_of_dominated_convergence
    (fun x => 4 * ‖u x‖^2) hme (hi.const_mul 4) hd hp
  have he0 : Tendsto (fun n => ∫ x, ‖(rho n x - 1) * u x‖^2 ∂mu) atTop (𝓝 0) := by
    simpa using he
  simpa [cutoffSize] using (Real.continuous_sqrt.tendsto (0 : ℝ)).comp he0

theorem cutoff_cost_summable {X I : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : X → ℂ) (u v : I → Lp ℂ 2 mu)
    (hr : ∀ x, ‖rho x‖ ≤ 1) (hm : AEStronglyMeasurable rho mu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun i => cutoffSize mu rho (u i) * ‖v i‖) := by
  apply Summable.of_nonneg_of_le
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fun i => ?_) (hc.mul_left 2)
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (cutoffSize_le mu rho (u i) hr hm) (norm_nonneg (v i))

theorem cutoff_cost_tendsto_zero {X I : Type*} [MeasurableSpace X]
    (mu : Measure X) (rho : ℕ → X → ℂ) (u v : I → Lp ℂ 2 mu)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1))
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Tendsto (fun n => ∑' i, cutoffSize mu (rho n) (u i) * ‖v i‖) atTop (𝓝 0) := by
  have hp (i) : Tendsto (fun n => cutoffSize mu (rho n) (u i) * ‖v i‖)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (cutoffSize_tendsto_zero mu rho (u i) hr hm hl).mul_const (‖v i‖)
  have hb : ∀ᶠ n in atTop, ∀ i, ‖cutoffSize mu (rho n) (u i) * ‖v i‖‖ ≤
      2 * (‖u i‖ * ‖v i‖) := by
    apply Filter.Eventually.of_forall
    intro n i
    have hn : 0 ≤ cutoffSize mu (rho n) (u i) := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hn (norm_nonneg (v i)))]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (cutoffSize_le mu (rho n) (u i) (hr n) (hm n))
        (norm_nonneg (v i))
  simpa using tendsto_tsum_of_dominated_convergence (hc.mul_left 2) hp hb

end Round102B

namespace Round131C
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round99G Round130C
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_compact_input_output_nuclear_and_cutoff
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    (c : Classes K → ℂ) (L : ℝ)
    (hcb : ∀ x, ‖c x‖ ≤ 1)
    (hcsupp : ∀ x, c x ≠ 0 → |actualLog K x| ≤ L)
    (hcm : AEStronglyMeasurable (fun p : Classes K × Classes K =>
      (((1+(actualLog K p.1)^2 : ℝ) : ℂ) * c p.1)) (mu.prod mu))
    (b : Classes K → ℂ) (hbb : ∀ x, ‖b x‖ ≤ 1)
    (hbm : AEStronglyMeasurable b mu)
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K
          c
          (NuclearBoundB90.convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * (b y * F y) ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖innerSL ℂ (v i)‖ ≤
        (1+L^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) ∧
      (∀ (rho : ℕ → Classes K → ℂ),
        (∀ n x, ‖rho n x‖ ≤ 1) →
        (∀ n, AEStronglyMeasurable (rho n) mu) →
        (∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) →
        (∀ n, Summable (fun i => Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖)) ∧
        Tendsto (fun n => ∑' i, Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖)
          atTop (𝓝 0)) := by
  obtain ⟨T, u, v, hT, hc, hN, hsum⟩ :=
    genuine_compact_input_output_nuclear_representation K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm c L hcb hcsupp hcm b hbb hbm e
  refine ⟨T, u, v, hT, hc, hN, hsum, ?_⟩
  intro rho hr hm hl
  have hc' : Summable (fun i => ‖u i‖ * ‖v i‖) := by
    simpa only [innerSL_apply_norm] using hc
  exact ⟨fun n => Round102B.cutoff_cost_summable mu (rho n) u v (hr n) (hm n) hc',
    Round102B.cutoff_cost_tendsto_zero mu rho u v hr hm hl hc'⟩

#check genuine_compact_input_output_nuclear_and_cutoff
#print axioms genuine_compact_input_output_nuclear_and_cutoff
end Round131C

namespace Round132C
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round95A Round97A
open Round130Sign Round131C
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The actual supported-test convolution has the sum of its support radii. -/
theorem genuine_convolution_log_support
    (mu : Measure (Classes K)) (psi theta : Classes K → ℂ) (R S : ℝ)
    (hp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (ht : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S) :
    ∀ x, convolution K mu psi theta x ≠ 0 → |actualLog K x| ≤ R+S := by
  intro x hx
  by_contra h
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with g
  by_cases hpg : psi g = 0
  · simp [hpg]
  have htg : theta (g⁻¹*x) = 0 := by
    by_contra ht0
    have hg := hp g hpg
    have hh := ht (g⁻¹*x) ht0
    have he : actualLog K x = actualLog K g + actualLog K (g⁻¹*x) := by
      change MasulloGRH.genuineRealClassLog K x =
        MasulloGRH.genuineRealClassLog K g + MasulloGRH.genuineRealClassLog K (g⁻¹*x)
      rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
      ring
    have ha := abs_add_le (actualLog K g) (actualLog K (g⁻¹*x))
    rw [← he] at ha
    exact h (ha.trans (add_le_add hg hh))
  simp [htg]

/-- One summable nuclear representation for the two actual sign-commutator
pieces, at the FIXED test-support radius. No required summability is assumed. -/
theorem genuine_sign_commutator_nuclear_and_cutoff
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ Tplus Tminus : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : (ι ⊕ ι) → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, Tplus F x = ∫ y,
        transportedCutoffKernel K
          (fun a => slab K (R+S) a * positiveHalf K a)
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      (∀ F, ∀ᵐ x ∂mu, Tminus F x = ∫ y,
        transportedCutoffKernel K (slab K (R+S))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y *
            (positiveHalf K y * F y) ∂mu) ∧
      (∀ x y, (positiveHalf K x - positiveHalf K y) *
          convolution K mu psi theta (x*y⁻¹) =
        (slab K (R+S) x * positiveHalf K x) *
          convolution K mu psi theta (x*y⁻¹) -
        slab K (R+S) x * convolution K mu psi theta (x*y⁻¹) * positiveHalf K y) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∑' i, ‖u i‖ * ‖v i‖) ≤
        2*(1+(R+S)^2) * Real.sqrt (∫ z : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi z.1 z.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ z : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta z.1 z.2‖^2 ∂(mu.prod mu)) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) ((Tplus-Tminus) F)) ∧
      (∀ (rho : ℕ → Classes K → ℂ),
        (∀ n x, ‖rho n x‖ ≤ 1) →
        (∀ n, AEStronglyMeasurable (rho n) mu) →
        (∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) →
        (∀ n, Summable (fun i => Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖)) ∧
        Tendsto (fun n => ∑' i,
          Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖) atTop (𝓝 0)) := by
  have hH : Measurable (positiveHalf K) := by
    unfold positiveHalf
    exact Measurable.ite (measurableSet_le measurable_const hell) measurable_const measurable_const
  have hchi : Measurable (slab K (R+S)) := by
    unfold slab
    exact Measurable.ite (measurableSet_le hell.abs measurable_const) measurable_const measurable_const
  have hHb (x : Classes K) : ‖positiveHalf K x‖ ≤ 1 := by
    unfold positiveHalf
    split <;> simp
  have hchis (x : Classes K) (hx : slab K (R+S) x ≠ 0) : |actualLog K x| ≤ R+S := by
    by_contra h
    simp [slab, h] at hx
  have hmplus : AEStronglyMeasurable
      (fun p : Classes K × Classes K =>
        (((1+actualLog K p.1^2 : ℝ) : ℂ) *
          (slab K (R+S) p.1 * positiveHalf K p.1))) (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmminus : AEStronglyMeasurable
      (fun p : Classes K × Classes K =>
        (((1+actualLog K p.1^2 : ℝ) : ℂ) * slab K (R+S) p.1)) (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  obtain ⟨Tp, up, vp, hap, hcp, hNp, hrp⟩ :=
    genuine_compact_input_output_nuclear_representation K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm (fun x => slab K (R+S) x * positiveHalf K x) (R+S)
      (sign_slab_bound K (R+S)) (sign_slab_support K (R+S)) hmplus
      (fun _ => 1) (fun _ => by simp) aestronglyMeasurable_const e
  obtain ⟨Tm, um, vm, ham, hcm, hNm, hrm'⟩ :=
    genuine_compact_input_output_nuclear_representation K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm (slab K (R+S)) (R+S)
      (slab_bound K (R+S)) hchis hmminus (positiveHalf K) hHb hH.aestronglyMeasurable e
  simp only [innerSL_apply_norm] at hcp hcm hNp hNm
  let u : (ι ⊕ ι) → Lp ℂ 2 mu := Sum.elim up (fun i => -um i)
  let v : (ι ⊕ ι) → Lp ℂ 2 mu := Sum.elim vp vm
  have hcost : HasSum (fun i => ‖u i‖ * ‖v i‖)
      ((∑' i, ‖up i‖ * ‖vp i‖) + ∑' i, ‖um i‖ * ‖vm i‖) := by
    apply HasSum.sum
    · simpa [u, v, Function.comp_def] using hcp.hasSum
    · simpa [u, v, Function.comp_def] using hcm.hasSum
  refine ⟨Tp, Tm, u, v, ?_, ham, ?_, hcost.summable, ?_, ?_, ?_⟩
  · simpa only [one_mul] using hap
  · exact genuine_sign_commutator_decomposition K _ (R+S)
      (genuine_convolution_log_support K mu psi theta R S hpsupp htsupp)
  · rw [hcost.tsum_eq]
    calc
      _ ≤ _ := add_le_add (hcp.tsum_le_of_sum_le hNp) (hcm.tsum_le_of_sum_le hNm)
      _ = _ := by ring
  · intro F
    have hh : HasSum (fun i => inner ℂ (v i) F • u i) (Tp F + -(Tm F)) := by
      apply HasSum.sum
      · simpa [u, v, Function.comp_def] using hrp F
      · simpa [u, v, Function.comp_def] using (hrm' F).neg
    simpa only [ContinuousLinearMap.sub_apply, sub_eq_add_neg] using hh
  · intro rho hr hm hl
    exact ⟨fun n => Round102B.cutoff_cost_summable mu (rho n) u v
      (hr n) (hm n) hcost.summable,
      Round102B.cutoff_cost_tendsto_zero mu rho u v hr hm hl hcost.summable⟩

#check genuine_convolution_log_support
#print axioms genuine_convolution_log_support
#check genuine_sign_commutator_nuclear_and_cutoff
#print axioms genuine_sign_commutator_nuclear_and_cutoff
end
end Round132C

namespace Round133C
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round95A Round96A Round97A
open Round130C Round130Sign Round131C Round132C
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Integrability of each actual convolution row, derived from the two
square-integrable factor kernels. The output multiplier is arbitrary. -/
theorem genuine_convolution_row_integrable
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (psi theta f : Classes K → ℂ) (alpha s : ℝ)
    (c : Classes K → ℂ)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hl : MemLp (fun z : Classes K × Classes K =>
      leftKernel K ell alpha s psi z.1 z.2) 2 (mu.prod mu))
    (hr : MemLp (fun z : Classes K × Classes K =>
      rightKernel K ell alpha s theta z.1 z.2) 2 (mu.prod mu))
    (hf : MemLp f 2 mu) :
    ∀ᵐ x ∂mu, Integrable (fun y =>
      transportedCutoffKernel K c (convolution K mu psi theta)
        (fun a => stripWeight alpha s (ell a)) x y * f y) mu := by
  filter_upwards [genuine_noncompact_fubini_ae K mu ell psi theta f alpha s hl hr hf]
    with x hx
  apply (hx.integral_prod_right.const_mul
    ((((1+ell x^2 : ℝ) : ℂ)) * c x)).congr
  filter_upwards [] with y
  change (((1+ell x^2 : ℝ) : ℂ) * c x) *
    (∫ z, (leftKernel K ell alpha s psi x z *
      rightKernel K ell alpha s theta z y) * f y ∂mu) = _
  rw [integral_mul_const,
    genuine_noncompact_kernel_composition K mu ell psi theta alpha s hpres hemb]
  have hq : ((1+ell x^2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1+ell x^2))
  dsimp only [transportedCutoffKernel]
  push_cast at hq ⊢
  field_simp [hq]

set_option maxHeartbeats 1600000 in
theorem genuine_sign_commutator_nuclear_integral
    (mu : Measure (Classes K)) [SFinite mu]
    (psi theta : Classes K → ℂ) (alpha s R S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (hell : Measurable (actualLog K)) (V : ℝ≥0)
    (hpush : Measure.map (actualLog K) mu = (V : ℝ≥0∞) • volume)
    (hout : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K) x^2))))
    (hpsi : Measurable (fun g => ENNReal.ofReal
      (2*(1+(actualLog K) g^2)*translationCost alpha s ((actualLog K) g)*‖psi g‖^2)))
    (htheta : Measurable (fun g => ENNReal.ofReal
      (‖theta g‖^2*translationCost alpha s ((actualLog K) g))))
    (hpsi0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (htheta0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |(actualLog K) g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |(actualLog K) g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hlm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      leftKernel K (actualLog K) alpha s psi z.1 z.2) (mu.prod mu))
    (hrm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      rightKernel K (actualLog K) alpha s theta z.1 z.2) (mu.prod mu))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ Tplus Tminus : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : (ι ⊕ ι) → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, Tplus F x = ∫ y,
        transportedCutoffKernel K
          (fun a => slab K (R+S) a * positiveHalf K a)
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      (∀ F, ∀ᵐ x ∂mu, Tminus F x = ∫ y,
        transportedCutoffKernel K (slab K (R+S))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y *
            (positiveHalf K y * F y) ∂mu) ∧
      (∀ x y, (positiveHalf K x - positiveHalf K y) *
          convolution K mu psi theta (x*y⁻¹) =
        (slab K (R+S) x * positiveHalf K x) *
          convolution K mu psi theta (x*y⁻¹) -
        slab K (R+S) x * convolution K mu psi theta (x*y⁻¹) * positiveHalf K y) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∑' i, ‖u i‖ * ‖v i‖) ≤
        2*(1+(R+S)^2) * Real.sqrt (∫ z : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi z.1 z.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ z : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta z.1 z.2‖^2 ∂(mu.prod mu)) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) ((Tplus-Tminus) F)) ∧
      (∀ (rho : ℕ → Classes K → ℂ),
        (∀ n x, ‖rho n x‖ ≤ 1) →
        (∀ n, AEStronglyMeasurable (rho n) mu) →
        (∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) →
        (∀ n, Summable (fun i => Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖)) ∧
        Tendsto (fun n => ∑' i,
          Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖) atTop (𝓝 0)) ∧
      (∀ F, ∀ᵐ x ∂mu, (Tplus-Tminus) F x = ∫ y,
        (positiveHalf K x - positiveHalf K y) * convolution K mu psi theta (x*y⁻¹) *
          (Real.sqrt (stripWeight alpha s (actualLog K x) /
            stripWeight alpha s (actualLog K y)) : ℂ) * F y ∂mu) ∧
      (∀ F, ∀ᵐ x ∂mu, R+S < |actualLog K x| → (Tplus-Tminus) F x = 0) := by
  have hH : Measurable (positiveHalf K) := by
    unfold positiveHalf
    exact Measurable.ite (measurableSet_le measurable_const hell) measurable_const measurable_const
  have hchi : Measurable (slab K (R+S)) := by
    unfold slab
    exact Measurable.ite (measurableSet_le hell.abs measurable_const) measurable_const measurable_const
  have hHb (x : Classes K) : ‖positiveHalf K x‖ ≤ 1 := by
    unfold positiveHalf
    split <;> simp
  have hchis (x : Classes K) (hx : slab K (R+S) x ≠ 0) : |actualLog K x| ≤ R+S := by
    by_contra h
    simp [slab, h] at hx
  have hmplus : AEStronglyMeasurable
      (fun p : Classes K × Classes K =>
        (((1+actualLog K p.1^2 : ℝ) : ℂ) *
          (slab K (R+S) p.1 * positiveHalf K p.1))) (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  have hmminus : AEStronglyMeasurable
      (fun p : Classes K × Classes K =>
        (((1+actualLog K p.1^2 : ℝ) : ℂ) * slab K (R+S) p.1)) (mu.prod mu) := by
    apply Measurable.aestronglyMeasurable
    fun_prop
  obtain ⟨Tp, up, vp, hap, hcp, hNp, hrp⟩ :=
    genuine_compact_input_output_nuclear_representation K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm (fun x => slab K (R+S) x * positiveHalf K x) (R+S)
      (sign_slab_bound K (R+S)) (sign_slab_support K (R+S)) hmplus
      (fun _ => 1) (fun _ => by simp) aestronglyMeasurable_const e
  obtain ⟨Tm, um, vm, ham, hcm, hNm, hrm'⟩ :=
    genuine_compact_input_output_nuclear_representation K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm (slab K (R+S)) (R+S)
      (slab_bound K (R+S)) hchis hmminus (positiveHalf K) hHb hH.aestronglyMeasurable e
  simp only [innerSL_apply_norm] at hcp hcm hNp hNm
  let u : (ι ⊕ ι) → Lp ℂ 2 mu := Sum.elim up (fun i => -um i)
  let v : (ι ⊕ ι) → Lp ℂ 2 mu := Sum.elim vp vm
  have hcost : HasSum (fun i => ‖u i‖ * ‖v i‖)
      ((∑' i, ‖up i‖ * ‖vp i‖) + ∑' i, ‖um i‖ * ‖vm i‖) := by
    apply HasSum.sum
    · simpa [u, v, Function.comp_def] using hcp.hasSum
    · simpa [u, v, Function.comp_def] using hcm.hasSum
  refine ⟨Tp, Tm, u, v, ?_, ham, ?_, hcost.summable, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [one_mul] using hap
  · exact genuine_sign_commutator_decomposition K _ (R+S)
      (genuine_convolution_log_support K mu psi theta R S hpsupp htsupp)
  · rw [hcost.tsum_eq]
    calc
      _ ≤ _ := add_le_add (hcp.tsum_le_of_sum_le hNp) (hcm.tsum_le_of_sum_le hNm)
      _ = _ := by ring
  · intro F
    have hh : HasSum (fun i => inner ℂ (v i) F • u i) (Tp F + -(Tm F)) := by
      apply HasSum.sum
      · simpa [u, v, Function.comp_def] using hrp F
      · simpa [u, v, Function.comp_def] using (hrm' F).neg
    simpa only [ContinuousLinearMap.sub_apply, sub_eq_add_neg] using hh
  · intro rho hr hm hl
    exact ⟨fun n => Round102B.cutoff_cost_summable mu (rho n) u v
      (hr n) (hm n) hcost.summable,
      Round102B.cutoff_cost_tendsto_zero mu rho u v hr hm hl hcost.summable⟩

  · intro F
    have hlog (x y : Classes K) : actualLog K x =
        actualLog K (x*y⁻¹) + actualLog K y := by
      change MasulloGRH.genuineRealClassLog K x =
        MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
      rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
      ring
    obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu (actualLog K)
      psi theta alpha s R S ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hlm hrm
    have hfH : MemLp (fun y => positiveHalf K y * F y) 2 mu :=
      (bounded_multiplier_energy mu (fun y => F y) (positiveHalf K) 1 zero_le_one
        (Lp.memLp F) hH.aestronglyMeasurable hHb).1
    have hpint := genuine_convolution_row_integrable K mu (actualLog K) psi theta
      (fun y => F y) alpha s (fun a => slab K (R+S) a * positiveHalf K a)
      hpres hemb hA hB (Lp.memLp F)
    have hmint := genuine_convolution_row_integrable K mu (actualLog K) psi theta
      (fun y => positiveHalf K y * F y) alpha s (slab K (R+S))
      hpres hemb hA hB hfH
    filter_upwards [hap F, ham F, hpint, hmint, Lp.coeFn_sub (Tp F) (Tm F)]
      with x hx hy hpx hmx hsub
    change (Tp F - Tm F) x = _
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hx, hy]
    simp only [one_mul]
    rw [← integral_sub hpx hmx]
    apply integral_congr_ae
    filter_upwards [] with y
    have hid := genuine_sign_commutator_decomposition K
      (convolution K mu psi theta) (R+S)
      (genuine_convolution_log_support K mu psi theta R S hpsupp htsupp) x y
    dsimp only [transportedCutoffKernel]
    rw [hid]
    ring
  · intro F
    filter_upwards [hap F, ham F, Lp.coeFn_sub (Tp F) (Tm F)] with x hx hy hsub
    intro houtside
    have hcx : slab K (R+S) x = 0 := by
      exact if_neg (not_le.mpr houtside)
    change (Tp F - Tm F) x = 0
    simp only [Pi.sub_apply] at hsub
    rw [hsub, hx, hy]
    simp only [transportedCutoffKernel, hcx, zero_mul, integral_zero, sub_self]

#check genuine_convolution_row_integrable
#print axioms genuine_convolution_row_integrable
#check genuine_sign_commutator_nuclear_integral
#print axioms genuine_sign_commutator_nuclear_integral
end
end Round133C

namespace Round133Cutoff
open MeasureTheory NuclearBoundB90 Round93A Round97A Round130Sign Round132C
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Physical output cutoffs equal to one on the fixed test slab leave the
literal genuine sign-commutator action unchanged, exactly. -/
theorem genuine_sign_commutator_cutoff_exact
    (mu : Measure (Classes K)) (psi theta f rho : Classes K → ℂ)
    (alpha s R S : ℝ)
    (hp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (ht : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hrho : ∀ x, |actualLog K x| ≤ R+S → rho x = 1) (x : Classes K) :
    rho x * (∫ y,
      (positiveHalf K x - positiveHalf K y) * convolution K mu psi theta (x*y⁻¹) *
        (Real.sqrt (stripWeight alpha s (actualLog K x) /
          stripWeight alpha s (actualLog K y)) : ℂ) * f y ∂mu) =
    (∫ y,
      (positiveHalf K x - positiveHalf K y) * convolution K mu psi theta (x*y⁻¹) *
        (Real.sqrt (stripWeight alpha s (actualLog K x) /
          stripWeight alpha s (actualLog K y)) : ℂ) * f y ∂mu) := by
  by_cases hx : |actualLog K x| ≤ R+S
  · rw [hrho x hx, one_mul]
  have hz (y : Classes K) :
      (positiveHalf K x - positiveHalf K y) * convolution K mu psi theta (x*y⁻¹) = 0 := by
    by_contra hne
    exact hx (genuine_sign_commutator_support K (convolution K mu psi theta) (R+S)
      (genuine_convolution_log_support K mu psi theta R S hp ht) x y hne).1
  simp only [hz, zero_mul, integral_zero, mul_zero]

#check genuine_sign_commutator_cutoff_exact
#print axioms genuine_sign_commutator_cutoff_exact
end
end Round133Cutoff
