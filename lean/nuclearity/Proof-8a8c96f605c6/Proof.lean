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

open MeasureTheory Filter
open scoped Topology
noncomputable section
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


namespace Round102B
open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_arithmetic_correction_cutoff_cost
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
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu))
    (rho : ℕ → Classes K → ℂ)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Filter.Tendsto (fun n => rho n x) Filter.atTop (nhds 1)) :
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
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) ∧
      (∀ n, Summable (fun i => cutoffSize mu (rho n) (u i) * ‖v i‖)) ∧
      Filter.Tendsto (fun n => ∑' i, cutoffSize mu (rho n) (u i) * ‖v i‖)
        Filter.atTop (nhds 0) := by
  obtain ⟨T, u, v, hT, hc, hN, hs⟩ :=
    Round101H.genuine_arithmetic_correction_nuclear_representation K mu psi theta
      alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb hlm hrm e
  exact ⟨T, u, v, hT, hc, hN, hs,
    fun n => cutoff_cost_summable mu (rho n) u v (hr n) (hm n) hc,
    cutoff_cost_tendsto_zero mu rho u v hr hm hl hc⟩

end Round102B


noncomputable section
namespace Round103B

def powerRemainder : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n+1, r => r * powerRemainder n r + n

theorem powerRemainder_nonneg (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ powerRemainder d r := by
  induction d with
  | zero => simp [powerRemainder]
  | succ d hd => simpa [powerRemainder] using add_nonneg (mul_nonneg hr hd) (Nat.cast_nonneg d)

theorem powerRemainder_mono (d : ℕ) (r M : ℝ) (hr : 0 ≤ r) (hrM : r ≤ M) :
    powerRemainder d r ≤ powerRemainder d M := by
  induction d with
  | zero => simp [powerRemainder]
  | succ d hd =>
    simp only [powerRemainder]
    exact add_le_add (mul_le_mul hrM hd (powerRemainder_nonneg d r hr) (hr.trans hrM)) le_rfl

theorem powerRemainder_identity (d : ℕ) (r : ℝ) :
    r^d = 1 + (d : ℝ)*(r-1) + (r-1)^2 * powerRemainder d r := by
  induction d with
  | zero => simp [powerRemainder]
  | succ d hd => rw [pow_succ, hd]; simp only [powerRemainder, Nat.cast_add, Nat.cast_one]; ring

def remainderConstant (d : ℕ) (R : ℝ) : ℝ :=
  (d : ℝ)*R^2 + (8*R^2 + 2*R^4)*powerRemainder d (2*(1+R^2))

def polynomialAdjointRemainder (d : ℕ) (t h : ℝ) : ℝ :=
  ((1+(t-h)^2)/(1+t^2))^d - 1 + (d : ℝ)*(2*t/(1+t^2))*h

/-- Uniform inverse-quadratic envelope after removing the first correction,
for every polynomial weight (1+t^2)^d and displacement |h| <= R. -/
theorem polynomial_adjoint_remainder_bound (d : ℕ) (t h R : ℝ)
    (hR : |h| ≤ R) :
    |polynomialAdjointRemainder d t h| ≤ remainderConstant d R / (1+t^2) := by
  have hR0 : 0 ≤ R := (abs_nonneg h).trans hR
  have hq : 0 < 1+t^2 := by positivity
  have hh : h^2 ≤ R^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) (add_nonneg hR0 (abs_nonneg h)), sq_abs h]
  have hh4 : h^4 ≤ R^4 := by nlinarith [sq_nonneg h, sq_nonneg R]
  let r := (1+(t-h)^2)/(1+t^2)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrM : r ≤ 2*(1+R^2) := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [sq_nonneg (t+h), mul_nonneg (sq_nonneg t) (sq_nonneg R)]
  have hid : r-1 = (h^2-2*t*h)/(1+t^2) := by dsimp [r]; field_simp; ring
  have hnum : (h^2-2*t*h)^2 ≤ (8*R^2+2*R^4)*(1+t^2) := by
    have ha : (h^2-2*t*h)^2 ≤ 8*t^2*h^2+2*h^4 := by nlinarith [sq_nonneg (h^2+2*t*h)]
    have hb : 8*t^2*h^2 ≤ 8*t^2*R^2 := mul_le_mul_of_nonneg_left hh (by positivity)
    nlinarith [mul_nonneg (sq_nonneg t) (pow_nonneg hR0 4)]
  have hd : (r-1)^2 ≤ (8*R^2+2*R^4)/(1+t^2) := by
    rw [hid, div_pow]
    calc
      _ ≤ ((8*R^2+2*R^4)*(1+t^2))/(1+t^2)^2 :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ = _ := by field_simp
  have he : polynomialAdjointRemainder d t h =
      (d : ℝ)*h^2/(1+t^2) + (r-1)^2*powerRemainder d r := by
    unfold polynomialAdjointRemainder
    change r^d - 1 + (d : ℝ)*(2*t/(1+t^2))*h = _
    rw [powerRemainder_identity]
    rw [hid]
    ring
  have hQr := powerRemainder_nonneg d r hr
  rw [he, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (d : ℝ)*R^2/(1+t^2) +
        ((8*R^2+2*R^4)/(1+t^2))*powerRemainder d (2*(1+R^2)) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg d)) hq.le
      · exact mul_le_mul hd (powerRemainder_mono d r _ hr hrM)
          (powerRemainder_nonneg d r hr) (by positivity)
    _ = _ := by unfold remainderConstant; ring

end Round103B

namespace Round103B
open NuclearBoundB90 Round97A
variable (K : Type*) [Field K] [NumberField K]

/-- This is the actual arithmetic weight-conjugation residual kernel,
with weight (1+ell^2)^d. The estimate is uniform in the output point. -/
theorem genuine_polynomial_adjoint_remainder_kernel_bound
    (d : ℕ) (phi : Classes K → ℂ) (R : ℝ)
    (hsupp : ∀ g, phi g ≠ 0 → |actualLog K g| ≤ R)
    (x g : Classes K) :
    ‖(((((1+(actualLog K (g⁻¹*x))^2)^d /
          (1+(actualLog K x)^2)^d) - 1 +
          (d : ℝ)*(2*actualLog K x/(1+(actualLog K x)^2))*actualLog K g : ℝ) : ℂ) * phi g)‖ ≤
      (remainderConstant d R/(1+(actualLog K x)^2))*‖phi g‖ := by
  by_cases hp : phi g = 0
  · simp [hp]
  have hlog : actualLog K (g⁻¹*x) = actualLog K x - actualLog K g := by
    change MasulloGRH.genuineRealClassLog K (g⁻¹*x) =
      MasulloGRH.genuineRealClassLog K x - MasulloGRH.genuineRealClassLog K g
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hlog, ← div_pow]
  exact mul_le_mul_of_nonneg_right
    (polynomial_adjoint_remainder_bound d (actualLog K x) (actualLog K g) R (hsupp g hp))
    (norm_nonneg _)

end Round103B

namespace Round104G
open MeasureTheory NuclearBoundB90 Round97A
open scoped BigOperators
noncomputable section

/-- Actual logarithmic test modification used by the two signed residuals. -/
def logModified {X : Type*} (ell : X → ℝ) (n : ℕ) (f : X → ℂ) : X → ℂ :=
  fun x => (ell x : ℂ)^n * f x

theorem logModified_norm_le {X : Type*} (ell : X → ℝ) (n : ℕ)
    (f : X → ℂ) (R : ℝ) (hsupp : ∀ x, f x ≠ 0 → |ell x| ≤ R) (x : X) :
    ‖logModified ell n f x‖ ≤ R^n * ‖f x‖ := by
  by_cases hz : f x = 0
  · simp [logModified, hz]
  · rw [logModified, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (hsupp x hz) n) (norm_nonneg _)

theorem logModified_support {X : Type*} (ell : X → ℝ) (n : ℕ)
    (f : X → ℂ) (R : ℝ) (hsupp : ∀ x, f x ≠ 0 → |ell x| ≤ R) :
    ∀ x, logModified ell n f x ≠ 0 → |ell x| ≤ R := by
  intro x hx
  apply hsupp x
  intro hz
  apply hx
  simp [logModified, hz]

theorem logModified_memLp {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (ell : X → ℝ) (hell : Measurable ell) (n : ℕ)
    (f : X → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x, f x ≠ 0 → |ell x| ≤ R) (hf : MemLp f 2 mu) :
    MemLp (logModified ell n f) 2 mu := by
  have hm0 : Measurable (fun x => (ell x : ℂ)^n) := by fun_prop
  have hm : AEStronglyMeasurable (logModified ell n f) mu :=
    hm0.aestronglyMeasurable.mul hf.aestronglyMeasurable
  apply (hf.const_mul ((R^n : ℝ) : ℂ)).mono hm
  filter_upwards [] with x
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hR n)] using logModified_norm_le ell n f R hsupp x

/-- Quantitative ordinary L2 mass, with unchanged logarithmic support.
The supported-test residual factor estimates can use these same radii. -/
theorem logModified_energy_le {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (ell : X → ℝ) (hell : Measurable ell) (n : ℕ)
    (f : X → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x, f x ≠ 0 → |ell x| ≤ R) (hf : MemLp f 2 mu) :
    (∫ x, ‖logModified ell n f x‖^2 ∂mu) ≤ (R^n)^2 * (∫ x, ‖f x‖^2 ∂mu) := by
  have hmod := logModified_memLp mu ell hell n f R hR hsupp hf
  have hi := hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [← integral_const_mul]
  apply integral_mono (hmod.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (hi.const_mul _)
  intro x
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
    (logModified_norm_le ell n f R hsupp x) 2

variable (K : Type*) [Field K] [NumberField K]

/-- A log-monomial modification of an actual convolution has a FINITE
factorization in the same supported L2 class. No nuclearity or summability
is assumed, and all integral interchanges are justified by L2 Holder. -/
theorem genuine_log_modified_convolution
    (mu : Measure (Classes K)) (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpsi : MemLp psi 2 mu) (htheta : MemLp theta 2 mu)
    (hpres : ∀ x, MeasurePreserving (fun g : Classes K => g⁻¹*x) mu mu)
    (n : ℕ) (x : Classes K) :
    logModified (actualLog K) n (convolution K mu psi theta) x =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
        convolution K mu (logModified (actualLog K) j psi)
          (logModified (actualLog K) (n-j) theta) x := by
  have hi (j : ℕ) : Integrable (fun g =>
      logModified (actualLog K) j psi g *
      logModified (actualLog K) (n-j) theta (g⁻¹*x)) mu := by
    have hp := logModified_memLp mu (actualLog K) hell j psi R hR hpsupp hpsi
    have ht := logModified_memLp mu (actualLog K) hell (n-j) theta S hS htsupp htheta
    simpa only [Pi.mul_apply, Function.comp_def] using
      hp.integrable_mul (ht.comp_measurePreserving (hpres x))
  have hlog (g : Classes K) : (actualLog K x : ℂ) =
      (actualLog K g : ℂ) + (actualLog K (g⁻¹*x) : ℂ) := by
    have hr : actualLog K (g⁻¹*x) = actualLog K x - actualLog K g := by
      change MasulloGRH.genuineRealClassLog K (g⁻¹*x) =
        MasulloGRH.genuineRealClassLog K x - MasulloGRH.genuineRealClassLog K g
      rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
      ring
    rw [hr]
    push_cast
    ring
  change (actualLog K x : ℂ)^n * (∫ g, psi g * theta (g⁻¹*x) ∂mu) = _
  calc
    _ = ∫ g, (actualLog K x : ℂ)^n * (psi g * theta (g⁻¹*x)) ∂mu :=
      (integral_const_mul _ _).symm
    _ = ∫ g, ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
        (logModified (actualLog K) j psi g *
         logModified (actualLog K) (n-j) theta (g⁻¹*x)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with g
      rw [hlog g, add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [logModified]
      ring
    _ = ∑ j ∈ Finset.range (n+1), ∫ g, (n.choose j : ℂ) *
        (logModified (actualLog K) j psi g *
         logModified (actualLog K) (n-j) theta (g⁻¹*x)) ∂mu :=
      integral_finset_sum _ (fun j _ => (hi j).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      rfl

/-- Exact scalar cost aggregation for the finite factorization. -/
theorem log_factorization_cost (R S : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*R^j*S^(n-j)) = (R+S)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end Round104G

namespace Round105G
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round104G
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Both actual Hilbert-Schmidt factors, with an optional output multiplier.
The multiplier may include a signed residual coefficient or cutoff error. -/
def actualFactor (alpha s : ℝ) (c : Classes K → ℂ) (left : Bool)
    (f : Classes K → ℂ) (p : Classes K × Classes K) : ℂ :=
  c p.1 * (if left then leftKernel K (actualLog K) alpha s f p.1 p.2
    else rightKernel K (actualLog K) alpha s f p.1 p.2)

@[simp] theorem actualFactor_one_left (alpha s : ℝ) (f : Classes K → ℂ) :
    actualFactor K alpha s (fun _ => 1) true f =
      fun p => leftKernel K (actualLog K) alpha s f p.1 p.2 := by
  funext p
  simp [actualFactor]
@[simp] theorem actualFactor_one_right (alpha s : ℝ) (f : Classes K → ℂ) :
    actualFactor K alpha s (fun _ => 1) false f =
      fun p => rightKernel K (actualLog K) alpha s f p.1 p.2 := by
  funext p
  simp [actualFactor]

theorem actual_factor_log_energy
    (mu : Measure (Classes K)) (alpha s R : ℝ) (hR : 0 ≤ R)
    (hell : Measurable (actualLog K)) (c : Classes K → ℂ) (left : Bool)
    (f : Classes K → ℂ) (hf : ∀ g, f g ≠ 0 → |actualLog K g| ≤ R)
    (hbase : MemLp (actualFactor K alpha s c left f) 2 (mu.prod mu)) (n : ℕ) :
    MemLp (actualFactor K alpha s c left (logModified (actualLog K) n f)) 2 (mu.prod mu) ∧
    (∫ p, ‖actualFactor K alpha s c left (logModified (actualLog K) n f) p‖^2 ∂(mu.prod mu)) ≤
      (R^n)^2 * (∫ p, ‖actualFactor K alpha s c left f p‖^2 ∂(mu.prod mu)) := by
  let ell : Classes K × Classes K → ℝ := fun p => actualLog K (p.1*p.2⁻¹)
  have hid : ell = fun p => actualLog K p.1 - actualLog K p.2 := by
    funext p
    change MasulloGRH.genuineRealClassLog K (p.1*p.2⁻¹) = _
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    rfl
  have hm : Measurable ell := by
    rw [hid]
    exact (hell.comp measurable_fst).sub (hell.comp measurable_snd)
  have hsup : ∀ p, actualFactor K alpha s c left f p ≠ 0 → |ell p| ≤ R := by
    intro p hp
    apply hf (p.1*p.2⁻¹)
    intro hz
    apply hp
    cases left <;> simp [actualFactor, leftKernel, rightKernel, transportedCutoffKernel, hz]
  have heq : actualFactor K alpha s c left (logModified (actualLog K) n f) =
      logModified ell n (actualFactor K alpha s c left f) := by
    funext p
    cases left <;> simp only [actualFactor, Bool.false_eq_true, ↓reduceIte, logModified,
      leftKernel, rightKernel, transportedCutoffKernel, ell] <;> ring
  rw [heq]
  exact ⟨logModified_memLp (mu.prod mu) ell hm n _ R hR hsup hbase,
    logModified_energy_le (mu.prod mu) ell hm n _ R hR hsup hbase⟩

theorem sqrt_modified_factor_energy_le
    (mu : Measure (Classes K)) (alpha s R : ℝ) (hR : 0 ≤ R)
    (hell : Measurable (actualLog K)) (c : Classes K → ℂ) (left : Bool)
    (f : Classes K → ℂ) (hf : ∀ g, f g ≠ 0 → |actualLog K g| ≤ R)
    (hbase : MemLp (actualFactor K alpha s c left f) 2 (mu.prod mu)) (n : ℕ) :
    Real.sqrt (∫ p, ‖actualFactor K alpha s c left (logModified (actualLog K) n f) p‖^2 ∂(mu.prod mu)) ≤
      R^n * Real.sqrt (∫ p, ‖actualFactor K alpha s c left f p‖^2 ∂(mu.prod mu)) := by
  have h := Real.sqrt_le_sqrt (actual_factor_log_energy K mu alpha s R hR hell c left f hf hbase n).2
  rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hR n)] at h

/-- The full finite binomial factor cost for a log-modified genuine test.
The same multiplier c is used in every left factor, including cutoff errors. -/
theorem genuine_log_factor_cost
    (mu : Measure (Classes K)) (alpha s R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hell : Measurable (actualLog K)) (c : Classes K → ℂ)
    (psi theta : Classes K → ℂ)
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hL : MemLp (actualFactor K alpha s c true psi) 2 (mu.prod mu))
    (hRk : MemLp (actualFactor K alpha s (fun _ => 1) false theta) 2 (mu.prod mu)) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
      Real.sqrt (∫ p, ‖actualFactor K alpha s c true (logModified (actualLog K) j psi) p‖^2 ∂(mu.prod mu)) *
      Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) false
        (logModified (actualLog K) (n-j) theta) p‖^2 ∂(mu.prod mu))) ≤
      (R+S)^n * Real.sqrt (∫ p, ‖actualFactor K alpha s c true psi p‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) false theta p‖^2 ∂(mu.prod mu)) := by
  let EL := Real.sqrt (∫ p, ‖actualFactor K alpha s c true psi p‖^2 ∂(mu.prod mu))
  let ER := Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) false theta p‖^2 ∂(mu.prod mu))
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((n.choose j : ℝ)*R^j*S^(n-j)) * (EL*ER) := by
      apply Finset.sum_le_sum
      intro j hj
      have h1 := sqrt_modified_factor_energy_le K mu alpha s R hR hell c true psi hpsupp hL j
      have h2 := sqrt_modified_factor_energy_le K mu alpha s S hS hell (fun _ => 1) false theta htsupp hRk (n-j)
      have hh := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hR j) (Real.sqrt_nonneg _))
      have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (n.choose j) : (0 : ℝ) ≤ _)
      dsimp [EL, ER]
      nlinarith only [hh']
    _ = _ := by
      rw [← Finset.sum_mul, log_factorization_cost]
      dsimp [EL, ER]
      ring

end
end Round105G

namespace Round105G
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round104G
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
/-- Actual correction factor cost with base square-integrability DERIVED
from the genuine log pushforward, supported tests and ordinary L2 masses. -/
theorem genuine_supported_log_factor_cost
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
    (hR : 0 ≤ R) (hS : 0 ≤ S) (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) *
      Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) true (logModified (actualLog K) j psi) p‖^2 ∂(mu.prod mu)) *
      Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) false
        (logModified (actualLog K) (n-j) theta) p‖^2 ∂(mu.prod mu))) ≤
      (R+S)^n * Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) true psi p‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p, ‖actualFactor K alpha s (fun _ => 1) false theta p‖^2 ∂(mu.prod mu)) := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹) + actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu (actualLog K) psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  exact genuine_log_factor_cost K mu alpha s R S hR hS hell (fun _ => 1) psi theta
    hpsupp htsupp (by simpa [actualFactor] using hA) (by simpa [actualFactor] using hB) n

end
end Round105G

namespace Round105G
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round99G Round104G
open scoped BigOperators
noncomputable section
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
/-- Actual rank-one factors for every logarithmic modification, with
summability derived and a product-energy bound in the fixed original factors. -/
theorem genuine_supported_modified_rankOne_cost
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
    (hR : 0 ≤ R) (hS : 0 ≤ S) {ι : Type*}
    (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) (j k : ℕ) :
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ i, ∀ᵐ x ∂mu, u i x = ∫ y,
        leftKernel K (actualLog K) alpha s (logModified (actualLog K) j psi) x y * e i y ∂mu) ∧
      (∀ i, ∀ᵐ y ∂mu, v i y = ∫ z,
        star (rightKernel K (actualLog K) alpha s (logModified (actualLog K) k theta) z y) * e i z ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖innerSL ℂ (v i)‖ ≤
        (R^j*S^k) *
        Real.sqrt (∫ p : Classes K × Classes K, ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K, ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹) + actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu (actualLog K) psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  have hA' : MemLp (actualFactor K alpha s (fun _ => 1) true psi) 2 (mu.prod mu) := by
    simpa [actualFactor] using hA
  have hB' : MemLp (actualFactor K alpha s (fun _ => 1) false theta) 2 (mu.prod mu) := by
    simpa [actualFactor] using hB
  have hj := (actual_factor_log_energy K mu alpha s R hR hell (fun _ => 1) true psi hpsupp hA' j).1
  have hk := (actual_factor_log_energy K mu alpha s S hS hell (fun _ => 1) false theta htsupp hB' k).1
  simp only [actualFactor_one_left, actualFactor_one_right] at hj hk
  obtain ⟨u, v, hu, hv, hc, hN⟩ := kernel_rankOne_cost_sharp mu
    (leftKernel K (actualLog K) alpha s (logModified (actualLog K) j psi))
    (rightKernel K (actualLog K) alpha s (logModified (actualLog K) k theta)) hj hk e he
  refine ⟨u, v, hu, hv, hc, fun J => (hN J).trans ?_⟩
  have h1 := sqrt_modified_factor_energy_le K mu alpha s R hR hell (fun _ => 1) true psi hpsupp hA' j
  have h2 := sqrt_modified_factor_energy_le K mu alpha s S hS hell (fun _ => 1) false theta htsupp hB' k
  simp only [actualFactor_one_left, actualFactor_one_right] at h1 h2
  have hh := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (mul_nonneg (pow_nonneg hR j) (Real.sqrt_nonneg _))
  nlinarith only [hh]

end
end Round105G

namespace Round106G
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round104G Round105G
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
/-- Actual decaying modified convolution: summability, reconstruction and
cutoff cost convergence, with no assumed kernel energy or nuclear estimate.
This is a residual component, not the full projected global operator. -/
theorem genuine_modified_residual_nuclear_representation
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
    (hR : 0 ≤ R) (hS : 0 ≤ S) {ι : Type*}
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (j k : ℕ)
    (rho : ℕ → Classes K → ℂ)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :

    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u v : ι → Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, T F x = ∫ y,
        transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (NuclearBoundB90.convolution K mu
            (logModified (actualLog K) j psi) (logModified (actualLog K) k theta))
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        (R^j*S^k) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) ∧
      (∀ n, Summable (fun i => Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖)) ∧
      Tendsto (fun n => ∑' i, Round102B.cutoffSize mu (rho n) (u i) * ‖v i‖)
        atTop (𝓝 0) := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹) + actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu (actualLog K) psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  have hA' : MemLp (actualFactor K alpha s (fun _ => 1) true psi) 2 (mu.prod mu) := by
    simpa only [actualFactor_one_left] using hA
  have hB' : MemLp (actualFactor K alpha s (fun _ => 1) false theta) 2 (mu.prod mu) := by
    simpa only [actualFactor_one_right] using hB
  have hj := (actual_factor_log_energy K mu alpha s R hR hell (fun _ => 1) true psi hpsupp hA' j).1
  have hk := (actual_factor_log_energy K mu alpha s S hS hell (fun _ => 1) false theta htsupp hB' k).1
  simp only [actualFactor_one_left, actualFactor_one_right] at hj hk
  obtain ⟨A, hAa, _⟩ := Round100H.kernel_bounded_operator mu _ hj
  obtain ⟨B, hBa, _⟩ := Round100H.kernel_bounded_operator mu _ hk
  obtain ⟨u, v, hu, hv, hc, hN⟩ := genuine_supported_modified_rankOne_cost K mu psi theta
    alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
    hpres hlm hrm hR hS e e.orthonormal j k
  simp only [innerSL_apply_norm] at hc hN
  have huA (i) : u i = A (e i) := by
    apply Lp.ext
    filter_upwards [hu i, hAa (e i)] with x hx hy
    exact hx.trans hy.symm
  refine ⟨A.comp B, u, v, ?_, hc, hN, ?_,
    fun n => Round102B.cutoff_cost_summable mu (rho n) u v (hr n) (hm n) hc,
    Round102B.cutoff_cost_tendsto_zero mu rho u v hr hm hl hc⟩
  · intro F
    have hact := genuine_noncompact_action_composition_ae K mu (actualLog K)
      (logModified (actualLog K) j psi) (logModified (actualLog K) k theta)
      (fun x => F x) alpha s hpres hemb hj hk (Lp.memLp F)
    filter_upwards [hAa (B F), hact] with x hx hact
    change A (B F) x = _
    rw [hx, ← hact]
    apply integral_congr_ae
    filter_upwards [hBa F] with z hz
    rw [hz]
  · intro F
    simpa only [huA] using Round101H.kernel_basis_reconstruction mu
      (rightKernel K (actualLog K) alpha s (logModified (actualLog K) k theta))
      hk A B hBa e v hv F

end
end Round106G

set_option linter.unusedVariables false
namespace Round117G
open MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section

/-- Actual multiplication on L2, with its contraction estimate derived. -/
theorem multiplier_contraction {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (c : X → ℂ) (hc : AEStronglyMeasurable c mu)
    (hn : ∀ x, ‖c x‖ ≤ 1) :
    ∃ M : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, M F x = c x * F x) ∧ (∀ F, ‖M F‖ ≤ ‖F‖) := by
  have hm (F : Lp ℂ 2 mu) : MemLp (fun x => c x * F x) 2 mu := by
    apply (Lp.memLp F).mono (hc.mul (Lp.memLp F).aestronglyMeasurable)
    filter_upwards [] with x
    change ‖c x * F x‖ ≤ ‖F x‖
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hn x) (norm_nonneg (F x))
  let out (F : Lp ℂ 2 mu) := (hm F).toLp (fun x => c x * F x)
  have hout (F : Lp ℂ 2 mu) : ∀ᵐ x ∂mu, out F x = c x * F x :=
    (hm F).coeFn_toLp
  let A : Lp ℂ 2 mu →ₗ[ℂ] Lp ℂ 2 mu :=
    { toFun := out
      map_add' := by
        intro F G
        apply Lp.ext
        filter_upwards [hout (F+G), hout F, hout G,
          Lp.coeFn_add (out F) (out G), Lp.coeFn_add F G] with x hfg hf hg ho hi
        simp only [hfg, ho, hi, Pi.add_apply, hf, hg]
        ring
      map_smul' := by
        intro z F
        apply Lp.ext
        filter_upwards [hout (z • F), hout F,
          Lp.coeFn_smul z (out F), Lp.coeFn_smul z F] with x hzf hf ho hi
        change out (z • F) x = (z • out F) x
        simp only [hzf, ho, hi, Pi.smul_apply, hf, smul_eq_mul]
        ring }
  have hb (F : Lp ℂ 2 mu) : ‖A F‖ ≤ ‖F‖ := by
    change ‖out F‖ ≤ ‖F‖
    rw [Lp.norm_def, Lp.norm_def]
    apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    apply eLpNorm_mono_ae
    filter_upwards [hout F] with x hx
    rw [hx, norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hn x) (norm_nonneg (F x))
  exact ⟨A.mkContinuous 1 (fun F => by simpa using hb F), hout, hb⟩

open NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A Round104G Round105G
variable (K : Type*) [Field K] [NumberField K]

/-- Two-sided genuine residual needed for the first-order commutator.
Nuclear costs and left cutoff convergence are derived from supported tests;
no required summability, nuclearity, or projected estimate is assumed. -/
theorem genuine_input_modified_residual_nuclear
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
    (hR : 0 ≤ R) (hS : 0 ≤ S) {ι : Type*}
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (j k : ℕ)
    (c : Classes K → ℂ)
    (hcm : AEStronglyMeasurable c mu) (hcn : ∀ x, ‖c x‖ ≤ 1)
    (rho : ℕ → Classes K → ℂ)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :

    ∃ T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
    ∃ u : ι → Lp ℂ 2 mu,
    ∃ eta : ι → (Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ F, ∀ᵐ x ∂mu, T F x = ∫ y,
        transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (NuclearBoundB90.convolution K mu
            (logModified (actualLog K) j psi) (logModified (actualLog K) k theta))
          (fun a => stripWeight alpha s (actualLog K a)) x y * (c y * F y) ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖eta i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖eta i‖ ≤
        (R^j*S^k) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ F, HasSum (fun i => eta i F • u i) (T F)) ∧
      (∀ n, Summable (fun i => Round102B.cutoffSize mu (rho n) (u i) * ‖eta i‖)) ∧
      Tendsto (fun n => ∑' i, Round102B.cutoffSize mu (rho n) (u i) * ‖eta i‖)
        atTop (𝓝 0) := by
  obtain ⟨T,u,v,hT,hc,hN,hsum,hcut,hlim⟩ :=
    Round106G.genuine_modified_residual_nuclear_representation K mu psi theta
      alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb hlm hrm hR hS e j k rho hr hm hl
  obtain ⟨M,hM,hMn⟩ := multiplier_contraction mu c hcm hcn
  let eta : ι → (Lp ℂ 2 mu →L[ℂ] ℂ) := fun i => (innerSL ℂ (v i)).comp M
  have heta (i : ι) : ‖eta i‖ ≤ ‖v i‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro F
    change ‖inner ℂ (v i) (M F)‖ ≤ _
    calc
      _ ≤ ‖v i‖ * ‖M F‖ := norm_inner_le_norm _ _
      _ ≤ ‖v i‖ * ‖F‖ := mul_le_mul_of_nonneg_left (hMn F) (norm_nonneg _)
  have hle (i : ι) : ‖u i‖ * ‖eta i‖ ≤ ‖u i‖ * ‖v i‖ :=
    mul_le_mul_of_nonneg_left (heta i) (norm_nonneg _)
  have hc' : Summable (fun i => ‖u i‖ * ‖eta i‖) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hle hc
  have hcut' (n : ℕ) : Summable (fun i => Round102B.cutoffSize mu (rho n) (u i) * ‖eta i‖) := by
    apply Summable.of_nonneg_of_le (fun i => by unfold Round102B.cutoffSize; positivity) _ (hcut n)
    intro i
    exact mul_le_mul_of_nonneg_left (heta i) (Real.sqrt_nonneg _)
  refine ⟨T.comp M,u,eta,?_,hc',?_,?_,hcut',?_⟩
  · intro F
    filter_upwards [hT (M F)] with x hx
    change T (M F) x = _
    rw [hx]
    apply integral_congr_ae
    filter_upwards [hM F] with y hy
    rw [hy]
  · intro J
    exact (Finset.sum_le_sum (fun i _ => hle i)).trans (hN J)
  · intro F
    exact hsum (M F)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    · intro n
      exact tsum_nonneg (fun i => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    · intro n
      exact Summable.tsum_le_tsum
        (fun i => mul_le_mul_of_nonneg_left (heta i) (Real.sqrt_nonneg _)) (hcut' n) (hcut n)

#check genuine_input_modified_residual_nuclear
#print axioms genuine_input_modified_residual_nuclear
end
end Round117G

namespace Round115D
open MasulloGRH MeasureTheory

noncomputable def a (t : ℝ) : ℝ := 2*t/(1+t^2)
noncomputable def b (t : ℝ) : ℝ := 1/(1+t^2)

theorem rational_multiplier_bounds (t : ℝ) :
    0 ≤ b t ∧ b t ≤ 1 ∧ |a t| ≤ 1 := by
  have hq : 0 < 1+t^2 := by positivity
  refine ⟨by unfold b; positivity, ?_, ?_⟩
  · unfold b
    exact (div_le_one hq).mpr (by nlinarith [sq_nonneg t])
  · unfold a
    rw [abs_div, abs_of_pos hq]
    apply (div_le_one hq).mpr
    rw [abs_mul]
    norm_num
    nlinarith [sq_nonneg (|t|-1), sq_abs t]

/-- First-order commutator as output-decay kernels with bounded inputs. -/
theorem rational_commutator_identity (x y : ℝ) :
    a x-a y = -2*(x-y)*b x + 4*(x-y)*b x*b y - (x-y)^2*b x*a y := by
  have hx : 1+x^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+x^2)
  have hy : 1+y^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+y^2)
  unfold a b
  field_simp
  ring

theorem rational_commutator_bound (x y : ℝ) :
    |a x-a y| ≤ (6*|x-y|+(x-y)^2)*b x := by
  obtain ⟨hbx, _, _⟩ := rational_multiplier_bounds x
  obtain ⟨hby, hby1, hay⟩ := rational_multiplier_bounds y
  rw [rational_commutator_identity]
  calc
    _ ≤ |-2*(x-y)*b x| + |4*(x-y)*b x*b y| + |(x-y)^2*b x*a y| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = 2*|x-y| *b x + 4*|x-y| *b x*b y + (x-y)^2*b x*|a y| := by
      simp only [abs_mul, abs_of_nonneg hbx, abs_of_nonneg hby, abs_pow, sq_abs]
      norm_num
    _ ≤ 2*|x-y| *b x + 4*|x-y| *b x + (x-y)^2*b x := by
      have h1 := mul_le_mul_of_nonneg_left hby1 (by positivity : 0 ≤ 4*|x-y| *b x)
      have h2 := mul_le_mul_of_nonneg_left hay (by positivity : 0 ≤ (x-y)^2*b x)
      nlinarith
    _ = _ := by ring

variable (K : Type*) [Field K] [NumberField K]

/-- Exact first-order commutator kernel on genuine arithmetic idele classes.
The three terms all have integrably decaying output multiplier b. -/
theorem genuine_commutator_kernel_identity
    (phi : HeckeIdeleClasses K → ℂ) (x y : HeckeIdeleClasses K) :
    ((a (genuineRealClassLog K x)-a (genuineRealClassLog K y) : ℝ) : ℂ) * phi (x*y⁻¹) =
      (-2:ℂ) * (b (genuineRealClassLog K x) : ℂ) *
        ((genuineRealClassLog K (x*y⁻¹) : ℂ) * phi (x*y⁻¹)) +
      4 * (b (genuineRealClassLog K x) : ℂ) *
        ((genuineRealClassLog K (x*y⁻¹) : ℂ) * phi (x*y⁻¹)) *
        (b (genuineRealClassLog K y) : ℂ) -
      (b (genuineRealClassLog K x) : ℂ) *
        ((genuineRealClassLog K (x*y⁻¹) : ℂ)^2 * phi (x*y⁻¹)) *
        (a (genuineRealClassLog K y) : ℂ) := by
  have hl : genuineRealClassLog K (x*y⁻¹) =
      genuineRealClassLog K x-genuineRealClassLog K y := by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv]
    ring
  rw [rational_commutator_identity, hl]
  push_cast
  ring

/-- Concrete decay uniform in the absolute logarithmic position. -/
theorem genuine_commutator_kernel_bound
    (phi : HeckeIdeleClasses K → ℂ) (x y : HeckeIdeleClasses K) :
    ‖((a (genuineRealClassLog K x)-a (genuineRealClassLog K y) : ℝ) : ℂ) * phi (x*y⁻¹)‖ ≤
      ((6*|genuineRealClassLog K (x*y⁻¹)|+(genuineRealClassLog K (x*y⁻¹))^2) *
        b (genuineRealClassLog K x)) * ‖phi (x*y⁻¹)‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hl : genuineRealClassLog K (x*y⁻¹) =
      genuineRealClassLog K x-genuineRealClassLog K y := by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv]
    ring
  rw [hl]
  exact mul_le_mul_of_nonneg_right (rational_commutator_bound _ _) (norm_nonneg _)

#check rational_commutator_identity
#print axioms rational_commutator_identity
#check genuine_commutator_kernel_identity
#print axioms genuine_commutator_kernel_identity
#check genuine_commutator_kernel_bound
#print axioms genuine_commutator_kernel_bound
end Round115D

namespace Round117G
open MeasureTheory NuclearBoundB90 Round97A
variable (K : Type*) [Field K] [NumberField K]
/-- The actual two commutator input multipliers satisfy all multiplier inputs. -/
theorem genuine_commutator_multiplier_data
    (mu : Measure (Classes K)) (hell : Measurable (actualLog K)) :
    AEStronglyMeasurable (fun x => (Round115D.a (actualLog K x) : ℂ)) mu ∧
    AEStronglyMeasurable (fun x => (Round115D.b (actualLog K x) : ℂ)) mu ∧
    (∀ x, ‖(Round115D.a (actualLog K x) : ℂ)‖ ≤ 1) ∧
    (∀ x, ‖(Round115D.b (actualLog K x) : ℂ)‖ ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Measurable.aestronglyMeasurable
    unfold Round115D.a
    fun_prop
  · apply Measurable.aestronglyMeasurable
    unfold Round115D.b
    fun_prop
  · intro x
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (Round115D.rational_multiplier_bounds (actualLog K x)).2.2
  · intro x
    obtain ⟨h0,h1,_⟩ := Round115D.rational_multiplier_bounds (actualLog K x)
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0] using h1
#check genuine_commutator_multiplier_data
#print axioms genuine_commutator_multiplier_data
end Round117G

namespace Round118G
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round95A Round97A Round104G
open scoped BigOperators Topology
noncomputable section

def leftOrder : Fin 7 → ℕ := ![0,1,0,1,0,1,2]
def rightOrder : Fin 7 → ℕ := ![1,0,1,0,2,1,0]
def coeff : Fin 7 → ℂ := ![-2,-2,4,4,-1,-2,-1]
def inputMultiplier (K : Type*) [Field K] [NumberField K] :
    Fin 7 → Classes K → ℂ :=
  ![fun _ => 1, fun _ => 1,
    fun x => (Round115D.b (actualLog K x) : ℂ),
    fun x => (Round115D.b (actualLog K x) : ℂ),
    fun x => (Round115D.a (actualLog K x) : ℂ),
    fun x => (Round115D.a (actualLog K x) : ℂ),
    fun x => (Round115D.a (actualLog K x) : ℂ)]

variable (K : Type*) [Field K] [NumberField K]
/-- All seven authentic convolution residuals, with a combined finite nuclear
cost independent of the left cutoff. No desired nuclear estimate is assumed.
The full AP and its projected leading term remain outside this statement. -/
theorem genuine_seven_residual_nuclear_cost
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
    (hR : 0 ≤ R) (hS : 0 ≤ S) {ι : Type*}
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu))
    (rho : ℕ → Classes K → ℂ)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    ∃ T : Fin 7 → (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu),
    ∃ u : Fin 7 → ι → Lp ℂ 2 mu,
    ∃ eta : Fin 7 → ι → (Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ l F, ∀ᵐ x ∂mu, T l F x = ∫ y,
        transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu
            (logModified (actualLog K) (leftOrder l) psi)
            (logModified (actualLog K) (rightOrder l) theta))
          (fun a => stripWeight alpha s (actualLog K a)) x y *
            (inputMultiplier K l y * F y) ∂mu) ∧
      (∀ l, Summable (fun i => ‖u l i‖ * ‖eta l i‖)) ∧
      (∀ J : Finset ι, ∑ l : Fin 7, ‖coeff l‖ * (∑ i ∈ J, ‖u l i‖ * ‖eta l i‖) ≤
        (6*(R+S)+(R+S)^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ l F, HasSum (fun i => eta l i F • u l i) (T l F)) ∧
      Tendsto (fun n => ∑ l : Fin 7, ‖coeff l‖ *
        (∑' i, Round102B.cutoffSize mu (rho n) (u l i) * ‖eta l i‖))
        atTop (𝓝 0) := by
  classical
  obtain ⟨ham,hbm,han,hbn⟩ := Round117G.genuine_commutator_multiplier_data K mu hell
  have hcm (l : Fin 7) : AEStronglyMeasurable (inputMultiplier K l) mu := by
    fin_cases l <;> simp only [inputMultiplier]
    all_goals first | exact aestronglyMeasurable_const | exact ham | exact hbm
  have hcn (l : Fin 7) : ∀ x, ‖inputMultiplier K l x‖ ≤ 1 := by
    fin_cases l <;> simp only [inputMultiplier]
    all_goals first | exact han | exact hbn | exact fun x => by norm_num
  have hex (l : Fin 7) := Round117G.genuine_input_modified_residual_nuclear K mu psi theta
    alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
    hpsupp htsupp hpf htf hpres hemb hlm hrm hR hS e
    (leftOrder l) (rightOrder l) (inputMultiplier K l) (hcm l) (hcn l) rho hr hm hl
  choose T u eta hact hsum hbound hrecon hcut hlim using hex
  refine ⟨T,u,eta,hact,hsum,?_,hrecon,?_⟩
  · intro J
    calc
      _ ≤ ∑ l : Fin 7, ‖coeff l‖ *
          ((R^(leftOrder l)*S^(rightOrder l)) *
          Real.sqrt (∫ p : Classes K × Classes K,
            ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
          Real.sqrt (∫ p : Classes K × Classes K,
            ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) := by
        exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hbound l J) (norm_nonneg _))
      _ = _ := by
        simp [Fin.sum_univ_succ, coeff, leftOrder, rightOrder]
        ring
  · have hh := tendsto_finset_sum Finset.univ
      (fun l _ => (hlim l).const_mul (‖coeff l‖))
    simpa using hh

#check genuine_seven_residual_nuclear_cost
#print axioms genuine_seven_residual_nuclear_cost
end
end Round118G

namespace Round118G
open MeasureTheory NuclearBoundB90 Round97A Round104G
open scoped BigOperators
variable (K : Type*) [Field K] [NumberField K]
/-- Exact seven-term kernel identity on genuine idele classes. This is the
operator-order bridge for the residual cost theorem; all moment convolutions
are justified by supported L2 tests, not formal integral interchanges. -/
theorem genuine_seven_commutator_kernel
    (mu : Measure (Classes K)) (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (R S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpsi : MemLp psi 2 mu) (htheta : MemLp theta 2 mu)
    (hpres : ∀ x, MeasurePreserving (fun g : Classes K => g⁻¹*x) mu mu)
    (x y : Classes K) :
    ((Round115D.a (actualLog K x)-Round115D.a (actualLog K y) : ℝ) : ℂ) *
      convolution K mu psi theta (x*y⁻¹) =
    ∑ l : Fin 7, coeff l * (Round115D.b (actualLog K x) : ℂ) *
      convolution K mu (logModified (actualLog K) (leftOrder l) psi)
        (logModified (actualLog K) (rightOrder l) theta) (x*y⁻¹) *
      inputMultiplier K l y := by
  have h1 := genuine_log_modified_convolution K mu psi theta hell R S hR hS
    hpsupp htsupp hpsi htheta hpres 1 (x*y⁻¹)
  have h2 := genuine_log_modified_convolution K mu psi theta hell R S hR hS
    hpsupp htsupp hpsi htheta hpres 2 (x*y⁻¹)
  norm_num [Finset.sum_range_succ, logModified] at h1 h2
  have hk := Round115D.genuine_commutator_kernel_identity K (convolution K mu psi theta) x y
  change ((Round115D.a (actualLog K x)-Round115D.a (actualLog K y) : ℝ) : ℂ) *
      convolution K mu psi theta (x*y⁻¹) = _ at hk
  rw [hk]
  change (-2:ℂ) * (Round115D.b (actualLog K x) : ℂ) *
      ((actualLog K (x*y⁻¹) : ℂ) * convolution K mu psi theta (x*y⁻¹)) +
    4 * (Round115D.b (actualLog K x) : ℂ) *
      ((actualLog K (x*y⁻¹) : ℂ) * convolution K mu psi theta (x*y⁻¹)) *
      (Round115D.b (actualLog K y) : ℂ) -
    (Round115D.b (actualLog K x) : ℂ) *
      ((actualLog K (x*y⁻¹) : ℂ)^2 * convolution K mu psi theta (x*y⁻¹)) *
      (Round115D.a (actualLog K y) : ℂ) = _
  rw [h1, h2]
  simp [Fin.sum_univ_succ, coeff, leftOrder, rightOrder, inputMultiplier]
  ring
#check genuine_seven_commutator_kernel
#print axioms genuine_seven_commutator_kernel
end Round118G

namespace Round119G
open scoped BigOperators Topology
noncomputable section
/-- Upgrade a derived rank-one reconstruction to operator-norm convergence. -/
theorem rankOne_operator_hasSum {H ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (u : ι → H) (eta : ι → (H →L[ℂ] ℂ))
    (hc : Summable (fun i => ‖u i‖ * ‖eta i‖))
    (hr : ∀ F, HasSum (fun i => eta i F • u i) (T F)) :
    HasSum (fun i => (eta i).smulRight (u i)) T := by
  have hb (i : ι) : ‖(eta i).smulRight (u i)‖ ≤ ‖u i‖ * ‖eta i‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro F
    have h := mul_le_mul_of_nonneg_right ((eta i).le_opNorm F) (norm_nonneg (u i))
    simpa [ContinuousLinearMap.smulRight_apply, norm_smul, mul_assoc,
      mul_comm, mul_left_comm] using h
  have hn : Summable (fun i => ‖(eta i).smulRight (u i)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb hc
  have hs := hn.of_norm
  have he : (∑' i, (eta i).smulRight (u i)) = T := by
    ext F
    exact ((ContinuousLinearMap.apply ℂ H F).hasSum hs.hasSum).unique (hr F)
  exact he ▸ hs.hasSum

theorem seven_operator_hasSum {H ι : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (T : Fin 7 → (H →L[ℂ] H)) (u : Fin 7 → ι → H)
    (eta : Fin 7 → ι → (H →L[ℂ] ℂ))
    (hc : ∀ l, Summable (fun i => ‖u l i‖ * ‖eta l i‖))
    (hr : ∀ l F, HasSum (fun i => eta l i F • u l i) (T l F)) :
    HasSum (fun i => ∑ l : Fin 7, Round118G.coeff l • (eta l i).smulRight (u l i))
      (∑ l : Fin 7, Round118G.coeff l • T l) := by
  have h (l : Fin 7) := (rankOne_operator_hasSum (T l) (u l) (eta l) (hc l) (hr l)).const_smul
    (Round118G.coeff l)
  have hh := (h 0).add ((h 1).add ((h 2).add ((h 3).add ((h 4).add ((h 5).add (h 6))))))
  simpa [Fin.sum_univ_succ] using hh
end
end Round119G

namespace Round119G
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round95A Round97A Round104G Round118G
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
/-- Genuine seven residual operators assembled with operator-norm convergence.
The nuclear costs and cutoff limit are derived from supported test masses.
The authentic projected leading term is still unresolved. -/
theorem genuine_commutator_operator_series
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
    (hR : 0 ≤ R) (hS : 0 ≤ S) {ι : Type*}
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu))
    (rho : ℕ → Classes K → ℂ)
    (hr : ∀ n x, ‖rho n x‖ ≤ 1)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    ∃ T : Fin 7 → (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu),
    ∃ u : Fin 7 → ι → Lp ℂ 2 mu,
    ∃ eta : Fin 7 → ι → (Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ l F, ∀ᵐ x ∂mu, T l F x = ∫ y,
        transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu
            (logModified (actualLog K) (leftOrder l) psi)
            (logModified (actualLog K) (rightOrder l) theta))
          (fun a => stripWeight alpha s (actualLog K a)) x y *
            (inputMultiplier K l y * F y) ∂mu) ∧
      (∀ l, Summable (fun i => ‖u l i‖ * ‖eta l i‖)) ∧
      (∀ J : Finset ι, ∑ l : Fin 7, ‖coeff l‖ * (∑ i ∈ J, ‖u l i‖ * ‖eta l i‖) ≤
        (6*(R+S)+(R+S)^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∀ l F, HasSum (fun i => eta l i F • u l i) (T l F)) ∧
      Summable (fun i => ∑ l : Fin 7, ‖coeff l‖ * (‖u l i‖ * ‖eta l i‖)) ∧
      (∑' i, ∑ l : Fin 7, ‖coeff l‖ * (‖u l i‖ * ‖eta l i‖)) ≤
        (6*(R+S)+(R+S)^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => ∑ l : Fin 7, coeff l • (eta l i).smulRight (u l i))
        (∑ l : Fin 7, coeff l • T l) ∧
      Tendsto (fun n => ∑ l : Fin 7, ‖coeff l‖ *
        (∑' i, Round102B.cutoffSize mu (rho n) (u l i) * ‖eta l i‖))
        atTop (𝓝 0) := by
  obtain ⟨T,u,eta,hact,hc,hbound,hr,hlim⟩ :=
    Round118G.genuine_seven_residual_nuclear_cost K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm hR hS e rho hr hm hl
  have hfin (J : Finset ι) :
      (∑ i ∈ J, ∑ l : Fin 7, ‖coeff l‖ * (‖u l i‖ * ‖eta l i‖)) ≤
        (6*(R+S)+(R+S)^2) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu)) := by
    rw [Finset.sum_comm]
    simpa only [Finset.mul_sum] using hbound J
  have hcost : Summable (fun i => ∑ l : Fin 7, ‖coeff l‖ * (‖u l i‖ * ‖eta l i‖)) :=
    summable_of_sum_le (fun i => Finset.sum_nonneg (fun l _ => by positivity)) hfin
  exact ⟨T,u,eta,hact,hc,hbound,hr,hcost,hcost.tsum_le_of_sum_le hfin,
    seven_operator_hasSum T u eta hc hr,hlim⟩
#check genuine_commutator_operator_series
#print axioms genuine_commutator_operator_series
#check rankOne_operator_hasSum
#print axioms rankOne_operator_hasSum
end
end Round119G
