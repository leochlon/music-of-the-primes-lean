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


open MeasureTheory Complex
open scoped ENNReal NNReal
namespace Round101E
/-- Absolute Fubini for the genuine kernel pairing is derived from L2 data. -/
theorem kernel_pairing {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (k : X × X → ℂ)
    (hk : MemLp k 2 (mu.prod mu)) (F G U V : Lp ℂ 2 mu)
    (hU : ∀ᵐ x ∂mu, U x = ∫ y, k (x,y) * F y ∂mu)
    (hV : ∀ᵐ y ∂mu, V y = ∫ x, star (k (x,y)) * G x ∂mu) :
    inner ℂ G U = inner ℂ V F := by
  have hFm := Lp.memLp F
  have hGm := (Lp.memLp G).star
  have ht : MemLp (fun p : X × X => star (G p.1) * F p.2) 2 (mu.prod mu) := by
    apply (memLp_two_iff_integrable_sq_norm
      (hGm.aestronglyMeasurable.comp_fst.mul hFm.aestronglyMeasurable.comp_snd)).mpr
    simpa only [Pi.mul_apply, Pi.star_apply, norm_mul, mul_pow] using
      (hGm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
        (hFm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hi : Integrable (fun p : X × X => (k p * F p.2) * star (G p.1)) (mu.prod mu) := by
    apply (hk.integrable_mul ht).congr
    filter_upwards [] with p
    change k p * (star (G p.1) * F p.2) = _
    ring
  rw [L2.inner_def, L2.inner_def]
  change (∫ x, U x * star (G x) ∂mu) = ∫ y, F y * star (V y) ∂mu
  calc
    _ = ∫ x, ∫ y, (k (x,y) * F y) * star (G x) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [hU] with x hx
      rw [hx, integral_mul_const]
    _ = ∫ y, ∫ x, (k (x,y) * F y) * star (G x) ∂mu ∂mu :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hV] with y hy
      rw [hy]
      change (∫ x, (k (x,y) * F y) * star (G x) ∂mu) =
        F y * (starRingEnd ℂ) (∫ x, star (k (x,y)) * G x ∂mu)
      rw [← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [mul_comm, mul_left_comm, mul_assoc]
end Round101E

namespace Round101E
open MeasureTheory
open scoped BigOperators
/-- Derived summable rank-one expansion equals the actual kernel product. -/
theorem kernel_product_representation {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (B C : X → X → ℂ)
    (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu))
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = ∫ z, B x z * (∫ y, C z y * F y ∂mu) ∂mu) ∧
      (∀ i, ∀ᵐ x ∂mu, u i x = ∫ y, B x y * e i y ∂mu) ∧
      (∀ i, ∀ᵐ x ∂mu, v i x = ∫ y, star (C y x) * e i y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        ((∫ p : X × X, ‖B p.1 p.2‖^2 ∂(mu.prod mu)) +
         (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu))) / 2) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  obtain ⟨A, hAa, hAn⟩ := Round100H.kernel_bounded_operator mu _ hB
  obtain ⟨D, hDa, hDn⟩ := Round100H.kernel_bounded_operator mu _ hC
  obtain ⟨u, v, hu, hv, hc, hN⟩ := Round100E.kernel_pair_nuclear_cost mu B C hB hC e e.orthonormal
  have huA (i) : u i = A (e i) := by
    apply Lp.ext
    filter_upwards [hu i, hAa (e i)] with x hx hy
    exact hx.trans hy.symm
  have hcoef (i) (F : Lp ℂ 2 mu) : inner ℂ (v i) F = inner ℂ (e i) (D F) :=
    (kernel_pairing mu _ hC F (e i) (D F) (v i) (hDa F) (hv i)).symm
  have hs (F : Lp ℂ 2 mu) :
      HasSum (fun i => ((innerSL ℂ (v i)).smulRight (u i)) F) ((A.comp D) F) := by
    have hh := A.hasSum (e.hasSum_repr (D F))
    apply hh.congr_fun
    intro i
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      hcoef, huA, HilbertBasis.repr_apply_apply, map_smul]
  obtain ⟨hn, ht⟩ := Round100E.rankOne_series_of_cost u v hc
  have heq : (∑' i, (innerSL ℂ (v i)).smulRight (u i)) = A.comp D := by
    apply ContinuousLinearMap.ext
    intro F
    exact ((ContinuousLinearMap.apply ℂ (Lp ℂ 2 mu) F).hasSum ht.hasSum).unique (hs F)
  refine ⟨A.comp D, u, v, ?_, hu, hv, hc, hN, ?_⟩
  · intro F
    filter_upwards [hAa (D F)] with x hx
    change A (D F) x = _
    rw [hx]
    apply integral_congr_ae
    filter_upwards [hDa F] with z hz
    rw [hz]
  · rw [← heq]
    exact ht.hasSum
end Round101E




/-! Reused exact A101 sharp factor cost and cutoff domination. -/
namespace Round100A
open Round99G
/-- Summability for correctly oriented factors B e_i and C* e_i. -/
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
end Round100A

namespace Round101A
open Filter
open scoped Topology
/-- Output-cutoff error controls the entire rank-one cost by a vanishing
product-kernel energy. No summability or nuclear convergence is assumed. -/
theorem kernel_cutoff_rankOne_cost
    {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (B C : X → X → ℂ)
    (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu))
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (rho : ℕ → X → ℂ) (hrho : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n x, ‖rho n x‖ ≤ 1)
    (hl : ∀ x, Tendsto (fun n => rho n x) atTop (nhds 1))
    (e : ι → Lp ℂ 2 mu) (he : Orthonormal ℂ e) :
    ∃ u v : ℕ → ι → Lp ℂ 2 mu,
      (∀ n i, ∀ᵐ x ∂mu, u n i x =
        ∫ y, ((rho n x - 1) * B x y) * e i y ∂mu) ∧
      (∀ n i, ∀ᵐ y ∂mu, v n i y =
        ∫ z, star (C z y) * e i z ∂mu) ∧
      (∀ n, Summable (fun i => ‖u n i‖ * ‖innerSL ℂ (v n i)‖)) ∧
      Tendsto (fun n => ∑' i, ‖u n i‖ * ‖innerSL ℂ (v n i)‖)
        atTop (nhds 0) := by
  let D := fun n (p : X × X) => (rho n p.1 - 1) * B p.1 p.2
  have hm (n) : AEStronglyMeasurable (D n) (mu.prod mu) :=
    ((hrho n).comp_fst.sub aestronglyMeasurable_const).mul hB.aestronglyMeasurable
  have hi := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hd (n) (p : X × X) : ‖‖D n p‖^2‖ ≤ 4 * ‖B p.1 p.2‖^2 := by
    have hn : ‖rho n p.1 - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖rho n p.1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by simp only [norm_one]; linarith [hb n p.1]
    have hs : ‖rho n p.1 - 1‖^2 ≤ (4 : ℝ) := by
      nlinarith [norm_nonneg (rho n p.1 - 1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖D n p‖)]
    dsimp [D]
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hD (n) : MemLp (D n) 2 (mu.prod mu) := by
    apply (memLp_two_iff_integrable_sq_norm (hm n)).mpr
    exact (hi.const_mul 4).mono' ((hm n).norm.pow 2)
      (Filter.Eventually.of_forall (hd n))
  have hlim : Tendsto (fun n => ∫ p, ‖D n p‖^2 ∂(mu.prod mu))
      atTop (nhds 0) := by
    have hp : ∀ᵐ p ∂(mu.prod mu), Tendsto (fun n => ‖D n p‖^2)
        atTop (nhds (0 : ℝ)) := by
      apply Filter.Eventually.of_forall
      intro p
      simpa [D] using (((hl p.1).sub_const 1).mul_const (B p.1 p.2)).norm.pow 2
    simpa using tendsto_integral_of_dominated_convergence
      (fun p : X × X => 4 * ‖B p.1 p.2‖^2)
      (fun n => (hm n).norm.pow 2) (hi.const_mul 4)
      (fun n => Filter.Eventually.of_forall (hd n)) hp
  have hex (n) := Round100A.kernel_rankOne_cost_sharp mu
    (fun x y => (rho n x - 1) * B x y) C (hD n) hC e he
  choose u v hu hv hs hcost using hex
  refine ⟨u, v, hu, hv, hs, ?_⟩
  have hupper (n) : (∑' i, ‖u n i‖ * ‖innerSL ℂ (v n i)‖) ≤
      Real.sqrt (∫ p, ‖D n p‖^2 ∂(mu.prod mu)) *
      Real.sqrt (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu)) := by
    exact le_of_tendsto (hs n).hasSum (Filter.Eventually.of_forall (hcost n))
  have hzero := ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp hlim).mul_const
    (Real.sqrt (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu)))
  exact squeeze_zero (fun n => tsum_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    hupper (by simpa using hzero)
end Round101A


namespace Round102E
open Filter
open scoped Topology
/-- A complete basis reconstructs the actual left-cutoff error. Its whole
rank-one cost tends to zero, derived from product-kernel energies. -/
theorem kernel_product_cutoff_representation
    {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (B C : X → X → ℂ)
    (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu))
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (rho : ℕ → X → ℂ) (hrho : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n x, ‖rho n x‖ ≤ 1)
    (hl : ∀ x, Tendsto (fun n => rho n x) atTop (nhds 1))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (R : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (u v : ℕ → ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ z, B x z * (∫ y, C z y * F y ∂mu) ∂mu) ∧
      (∀ n F, ∀ᵐ x ∂mu, R n F x = (rho n x - 1) * T F x) ∧
      (∀ n i, ∀ᵐ x ∂mu, u n i x =
        ∫ y, ((rho n x - 1) * B x y) * e i y ∂mu) ∧
      (∀ n i, ∀ᵐ x ∂mu, v n i x =
        ∫ y, star (C y x) * e i y ∂mu) ∧
      (∀ n, Summable (fun i => ‖u n i‖ * ‖innerSL ℂ (v n i)‖)) ∧
      Tendsto (fun n => ∑' i, ‖u n i‖ * ‖innerSL ℂ (v n i)‖)
        atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (innerSL ℂ (v n i)).smulRight (u n i)) (R n)) := by
  obtain ⟨T, w, z, hT, hw, hz, hcz, hNz, hsz⟩ :=
    Round101E.kernel_product_representation mu B C hB hC e
  obtain ⟨u, v, hu, hv, hcost, hlim⟩ :=
    Round101A.kernel_cutoff_rankOne_cost mu B C hB hC rho hrho hb hl e e.orthonormal
  let D := fun n (p : X × X) => (rho n p.1 - 1) * B p.1 p.2
  have hm (n) : AEStronglyMeasurable (D n) (mu.prod mu) :=
    ((hrho n).comp_fst.sub aestronglyMeasurable_const).mul hB.aestronglyMeasurable
  have hi := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hd (n) (p : X × X) : ‖‖D n p‖^2‖ ≤ 4 * ‖B p.1 p.2‖^2 := by
    have hn : ‖rho n p.1 - 1‖ ≤ 2 := by
      calc
        _ ≤ ‖rho n p.1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 := by simp only [norm_one]; linarith [hb n p.1]
    have hs : ‖rho n p.1 - 1‖^2 ≤ (4 : ℝ) := by
      nlinarith [norm_nonneg (rho n p.1 - 1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖D n p‖)]
    dsimp [D]
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have hD (n) : MemLp (D n) 2 (mu.prod mu) := by
    apply (memLp_two_iff_integrable_sq_norm (hm n)).mpr
    exact (hi.const_mul 4).mono' ((hm n).norm.pow 2)
      (Filter.Eventually.of_forall (hd n))
  have hex (n) : ∃ R : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu,
      (∀ F, ∀ᵐ x ∂mu, R F x = (rho n x - 1) * T F x) ∧
      HasSum (fun i => (innerSL ℂ (v n i)).smulRight (u n i)) R := by
    obtain ⟨R, un, vn, hR, hun, hvn, hcn, hNn, hsn⟩ :=
      Round101E.kernel_product_representation mu
        (fun x y => (rho n x - 1) * B x y) C (hD n) hC e
    have hequ : un = u n := by
      funext i
      apply Lp.ext
      filter_upwards [hun i, hu n i] with x hx hy
      exact hx.trans hy.symm
    have heqv : vn = v n := by
      funext i
      apply Lp.ext
      filter_upwards [hvn i, hv n i] with x hx hy
      exact hx.trans hy.symm
    refine ⟨R, ?_, ?_⟩
    · intro F
      filter_upwards [hR F, hT F] with x hx hy
      rw [hx, hy]
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    · simpa only [hequ, heqv] using hsn
  choose R hR hsum using hex
  exact ⟨T, R, u, v, hT, hR, hu, hv, hcost, hlim, hsum⟩
end Round102E



namespace Round105B

def q (t : ℝ) := 1+t^2
def a (t : ℝ) := 2*t/q t
def b (t : ℝ) := 1/q t

theorem q_pos (t : ℝ) : 0 < q t := by unfold q; positivity

theorem a_bound (t : ℝ) : |a t| ≤ 1 := by
  rw [a, abs_div, abs_of_pos (q_pos t)]
  apply (div_le_iff₀ (q_pos t)).mpr
  rw [abs_mul]
  norm_num
  unfold q
  nlinarith [sq_nonneg (|t|-1), sq_abs t]

theorem b_bound (t : ℝ) : |b t| ≤ 1 := by
  have hp : 0 < b t := by unfold b; exact one_div_pos.mpr (q_pos t)
  rw [abs_of_pos hp]
  unfold b
  apply (div_le_iff₀ (q_pos t)).mpr
  unfold q
  nlinarith [sq_nonneg t]

theorem ratio_square_bound (t : ℝ) : 0 ≤ t^2/q t ∧ t^2/q t ≤ 1 := by
  constructor
  · exact div_nonneg (sq_nonneg t) (q_pos t).le
  · apply (div_le_iff₀ (q_pos t)).mpr
    unfold q
    linarith

structure Term where
  degree : ℕ
  coeff : ℝ → ℝ
  cost : ℝ

def shift (n : ℕ) (m : ℝ → ℝ) (u : Term) : Term :=
  ⟨u.degree+n, fun t => m t*u.coeff t, u.cost⟩

def terms : ℕ → List Term
  | 0 => []
  | d+1 =>
    [⟨2, fun t => 1+4*(d : ℝ)*(t^2/q t), 1+4*(d : ℝ)⟩,
     ⟨3, fun t => -(d : ℝ)*a t, (d : ℝ)⟩] ++
    terms d ++ (terms d).map (shift 1 (fun t => -a t)) ++
    (terms d).map (shift 2 b)

def eval (L : List Term) (t h : ℝ) : ℝ :=
  (L.map (fun u => u.coeff t*h^u.degree)).sum

theorem eval_append (L M : List Term) (t h : ℝ) :
    eval (L++M) t h = eval L t h + eval M t h := by
  simp [eval]

theorem eval_shift (L : List Term) (n : ℕ) (m : ℝ → ℝ) (t h : ℝ) :
    eval (L.map (shift n m)) t h = m t*h^n*eval L t h := by
  induction L with
  | nil => simp [eval]
  | cons u L ih =>
    simp only [List.map_cons, eval, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [shift, pow_add]
    ring

theorem terms_bounded (d : ℕ) :
    ∀ u ∈ terms d, 0 ≤ u.cost ∧ ∀ t, |u.coeff t| ≤ u.cost := by
  induction d with
  | zero => simp [terms]
  | succ d ih =>
    intro u hu
    simp only [terms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_map] at hu
    rcases hu with (((h | h) | h) | h) | h
    · subst u
      refine ⟨by positivity, ?_⟩
      intro t
      have hb := ratio_square_bound t
      change |1+4*(d : ℝ)*(t^2/q t)| ≤ 1+4*(d : ℝ)
      rw [abs_of_nonneg (by have := hb.1; positivity)]
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (sub_nonneg.mpr hb.2)]
    · subst u
      refine ⟨Nat.cast_nonneg d, ?_⟩
      intro t
      change |-(d : ℝ)*a t| ≤ (d : ℝ)
      rw [abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg d)]
      simpa using mul_le_mul_of_nonneg_left (a_bound t) (Nat.cast_nonneg (α := ℝ) d)
    · exact ih u h
    · obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨hc, hb⟩ := ih v hv
      refine ⟨hc, ?_⟩
      intro t
      change |(-a t)*v.coeff t| ≤ v.cost
      rw [abs_mul, abs_neg]
      exact (mul_le_mul (a_bound t) (hb t) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    · obtain ⟨v, hv, rfl⟩ := h
      obtain ⟨hc, hb⟩ := ih v hv
      refine ⟨hc, ?_⟩
      intro t
      change |b t*v.coeff t| ≤ v.cost
      rw [abs_mul]
      exact (mul_le_mul (b_bound t) (hb t) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

end Round105B


namespace Round106H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Each explicitly separated polynomial remainder coefficient has a derived
nuclear representation on the actual idele-class L2 space. The kernel
energies are proved finite from supported tests, not assumed. -/
theorem genuine_separated_term_nuclear_cutoff
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
    (d : ℕ) (term : Round105B.Term) (hterm : term ∈ Round105B.terms d)
    (hm : AEStronglyMeasurable
      (fun x => (term.coeff (actualLog K x) : ℂ)) mu)
    (cutoff : ℕ → Classes K → ℂ)
    (hcutmeas : ∀ n, AEStronglyMeasurable (cutoff n) mu)
    (hcut : ∀ n x, ‖cutoff n x‖ ≤ 1)
    (hcutlim : ∀ x, Tendsto (fun n => cutoff n x) atTop (nhds 1))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu)
      (Err : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (ue ve : ℕ → ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (term.coeff (actualLog K x) : ℂ) *
        ∫ y, transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        (term.cost^2 * (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) +
         (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) / 2) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T ∧
      (∀ n F, ∀ᵐ x ∂mu, Err n F x = (cutoff n x-1)*T F x) ∧
      (∀ n, Summable (fun i => ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)) ∧
      Tendsto (fun n => ∑' i, ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)
        atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (innerSL ℂ (ve n i)).smulRight (ue n i)) (Err n)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  let L := leftKernel K ell alpha s psi
  let C := rightKernel K ell alpha s theta
  let m := fun x : Classes K => (term.coeff (ell x) : ℂ)
  let D := fun x y => m x * L x y
  have hbnd := Round105B.terms_bounded d term hterm
  have hmn (x) : ‖m x‖ ≤ term.cost := by
    simpa only [m, Complex.norm_real, Real.norm_eq_abs] using hbnd.2 (ell x)
  have hDm : AEStronglyMeasurable (fun p : Classes K × Classes K => D p.1 p.2)
      (mu.prod mu) := hm.comp_fst.mul hA.aestronglyMeasurable
  have hAi := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hdom (p : Classes K × Classes K) : ‖D p.1 p.2‖^2 ≤ term.cost^2*‖L p.1 p.2‖^2 := by
    dsimp [D]
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hmn p.1) 2
  have hDi : Integrable (fun p : Classes K × Classes K => ‖D p.1 p.2‖^2)
      (mu.prod mu) := by
    apply (hAi.const_mul (term.cost^2)).mono' (hDm.norm.pow 2)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom p
  have hD := (memLp_two_iff_integrable_sq_norm hDm).mpr hDi
  have henergy : (∫ p : Classes K × Classes K, ‖D p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      term.cost^2 * (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) := by
    rw [← integral_const_mul]
    exact integral_mono hDi (hAi.const_mul _) hdom
  obtain ⟨T0, u, v, hT0, hu, hv, hc, hN, hsum⟩ :=
    Round101E.kernel_product_representation mu D C hD hB e
  obtain ⟨T, Err, ue, ve, hT, hErr, hue, hve, hce, hlim, hse⟩ :=
    Round102E.kernel_product_cutoff_representation mu D C hD hB
      cutoff hcutmeas hcut hcutlim e
  have heq : T0 = T := by
    apply ContinuousLinearMap.ext
    intro F
    apply Lp.ext
    filter_upwards [hT0 F, hT F] with x hx hy
    exact hx.trans hy.symm
  refine ⟨T, u, v, Err, ue, ve, ?_, hc, ?_, ?_, hErr, hce, hlim, hse⟩
  · intro F
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb (Lp.memLp F) hlm hrm).2
    filter_upwards [hT F, hact] with x hx hy
    rw [hx]
    change (∫ z, (m x * L x z) * (∫ y, C z y * F y ∂mu) ∂mu) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    exact congrArg (fun z => m x*z) hy
  · intro J
    have hn := hN J
    dsimp only [L, C] at henergy hn
    linarith
  · simpa only [heq] using hsum

end
#check genuine_separated_term_nuclear_cutoff
#print axioms genuine_separated_term_nuclear_cutoff
end Round106H


namespace Round107H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Actual compact-output convolution has a derived nuclear representation
and vanishing left-cutoff nuclear cost. No nuclear estimate is assumed. -/
theorem genuine_central_output_nuclear_cutoff
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
    (rho : Classes K → ℂ) (U : ℝ) (hU : 0 ≤ U)
    (hrhomeas : AEStronglyMeasurable rho mu)
    (hrhob : ∀ x, ‖rho x‖ ≤ 1)
    (hrhosupp : ∀ x, rho x ≠ 0 → |actualLog K x| ≤ U)
    (cutoff : ℕ → Classes K → ℂ)
    (hcutmeas : ∀ n, AEStronglyMeasurable (cutoff n) mu)
    (hcut : ∀ n x, ‖cutoff n x‖ ≤ 1)
    (hcutlim : ∀ x, Tendsto (fun n => cutoff n x) atTop (nhds 1))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu)
      (Err : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (ue ve : ℕ → ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K rho
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        ((1+U^2)^2 * (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) +
         (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) / 2) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T ∧
      (∀ n F, ∀ᵐ x ∂mu, Err n F x = (cutoff n x-1)*T F x) ∧
      (∀ n, Summable (fun i => ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)) ∧
      Tendsto (fun n => ∑' i, ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)
        atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (innerSL ℂ (ve n i)).smulRight (ue n i)) (Err n)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  let L := leftKernel K ell alpha s psi
  let C := rightKernel K ell alpha s theta
  let m := fun x : Classes K => ((1+(ell x)^2 : ℝ) : ℂ) * rho x
  let D := fun x y => m x * L x y
  have hm : AEStronglyMeasurable m mu := by
    have hq : Measurable (fun x : Classes K => ((1+(ell x)^2 : ℝ) : ℂ)) := by
      dsimp only [ell]
      fun_prop
    exact hq.aestronglyMeasurable.mul hrhomeas
  have hmn (x) : ‖m x‖ ≤ (1+U^2) := by
    by_cases hx : rho x = 0
    · simp only [m, hx, mul_zero, norm_zero]
      positivity
    · have hsq : (ell x)^2 ≤ U^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg (ell x)) hU).mpr (hrhosupp x hx)
        simpa only [sq_abs] using hh
      dsimp only [m]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1+(ell x)^2)]
      calc
        _ ≤ (1+(ell x)^2)*1 := mul_le_mul_of_nonneg_left (hrhob x) (by positivity)
        _ ≤ 1+U^2 := by linarith
  have hDm : AEStronglyMeasurable (fun p : Classes K × Classes K => D p.1 p.2)
      (mu.prod mu) := hm.comp_fst.mul hA.aestronglyMeasurable
  have hAi := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hdom (p : Classes K × Classes K) : ‖D p.1 p.2‖^2 ≤ (1+U^2)^2*‖L p.1 p.2‖^2 := by
    dsimp [D]
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hmn p.1) 2
  have hDi : Integrable (fun p : Classes K × Classes K => ‖D p.1 p.2‖^2)
      (mu.prod mu) := by
    apply (hAi.const_mul ((1+U^2)^2)).mono' (hDm.norm.pow 2)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom p
  have hD := (memLp_two_iff_integrable_sq_norm hDm).mpr hDi
  have henergy : (∫ p : Classes K × Classes K, ‖D p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      (1+U^2)^2 * (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) := by
    rw [← integral_const_mul]
    exact integral_mono hDi (hAi.const_mul _) hdom
  obtain ⟨T0, u, v, hT0, hu, hv, hc, hN, hsum⟩ :=
    Round101E.kernel_product_representation mu D C hD hB e
  obtain ⟨T, Err, ue, ve, hT, hErr, hue, hve, hce, hlim, hse⟩ :=
    Round102E.kernel_product_cutoff_representation mu D C hD hB
      cutoff hcutmeas hcut hcutlim e
  have heq : T0 = T := by
    apply ContinuousLinearMap.ext
    intro F
    apply Lp.ext
    filter_upwards [hT0 F, hT F] with x hx hy
    exact hx.trans hy.symm
  refine ⟨T, u, v, Err, ue, ve, ?_, hc, ?_, ?_, hErr, hce, hlim, hse⟩
  · intro F
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb (Lp.memLp F) hlm hrm).2
    filter_upwards [hT F, hact] with x hx hy
    rw [hx]
    change (∫ z, (m x * L x z) * (∫ y, C z y * F y ∂mu) ∂mu) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    rw [hy, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    have hq : (((1+(ell x)^2 : ℝ) : ℂ) *
        ((1/(1+(ell x)^2) : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      have hp : (1+(ell x)^2 : ℝ) ≠ 0 := by positivity
      simp [hp]
    calc
      _ = (((1+(ell x)^2 : ℝ) : ℂ) * ((1/(1+(ell x)^2) : ℝ) : ℂ)) *
          (transportedCutoffKernel K rho (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y * F y) := by
              dsimp only [m, transportedCutoffKernel, ell]
              ring
      _ = _ := by rw [hq, one_mul]
  · intro J
    have hn := hN J
    dsimp only [L, C] at henergy hn
    linarith
  · simpa only [heq] using hsum

end
#check genuine_central_output_nuclear_cutoff
#print axioms genuine_central_output_nuclear_cutoff
end Round107H


namespace Round107H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Each explicitly separated polynomial remainder coefficient has a derived
nuclear representation on the actual idele-class L2 space. The kernel
energies are proved finite from supported tests, not assumed. -/
theorem genuine_separated_term_sharp_nuclear_cutoff
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
    (d : ℕ) (term : Round105B.Term) (hterm : term ∈ Round105B.terms d)
    (hm : AEStronglyMeasurable
      (fun x => (term.coeff (actualLog K x) : ℂ)) mu)
    (cutoff : ℕ → Classes K → ℂ)
    (hcutmeas : ∀ n, AEStronglyMeasurable (cutoff n) mu)
    (hcut : ∀ n x, ‖cutoff n x‖ ≤ 1)
    (hcutlim : ∀ x, Tendsto (fun n => cutoff n x) atTop (nhds 1))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu)
      (Err : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (ue ve : ℕ → ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (term.coeff (actualLog K x) : ℂ) *
        ∫ y, transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        term.cost * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
         Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∑' i, ‖u i‖ * ‖v i‖) ≤
        term.cost * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
         Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T ∧
      (∀ n F, ∀ᵐ x ∂mu, Err n F x = (cutoff n x-1)*T F x) ∧
      (∀ n, Summable (fun i => ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)) ∧
      Tendsto (fun n => ∑' i, ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)
        atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (innerSL ℂ (ve n i)).smulRight (ue n i)) (Err n)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  let L := leftKernel K ell alpha s psi
  let C := rightKernel K ell alpha s theta
  let m := fun x : Classes K => (term.coeff (ell x) : ℂ)
  let D := fun x y => m x * L x y
  have hbnd := Round105B.terms_bounded d term hterm
  have hmn (x) : ‖m x‖ ≤ term.cost := by
    simpa only [m, Complex.norm_real, Real.norm_eq_abs] using hbnd.2 (ell x)
  have hDm : AEStronglyMeasurable (fun p : Classes K × Classes K => D p.1 p.2)
      (mu.prod mu) := hm.comp_fst.mul hA.aestronglyMeasurable
  have hAi := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hdom (p : Classes K × Classes K) : ‖D p.1 p.2‖^2 ≤ term.cost^2*‖L p.1 p.2‖^2 := by
    dsimp [D]
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hmn p.1) 2
  have hDi : Integrable (fun p : Classes K × Classes K => ‖D p.1 p.2‖^2)
      (mu.prod mu) := by
    apply (hAi.const_mul (term.cost^2)).mono' (hDm.norm.pow 2)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom p
  have hD := (memLp_two_iff_integrable_sq_norm hDm).mpr hDi
  have henergy : (∫ p : Classes K × Classes K, ‖D p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      term.cost^2 * (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) := by
    rw [← integral_const_mul]
    exact integral_mono hDi (hAi.const_mul _) hdom
  obtain ⟨T0, u, v, hT0, hu, hv, hc, hN, hsum⟩ :=
    Round101E.kernel_product_representation mu D C hD hB e
  obtain ⟨T, Err, ue, ve, hT, hErr, hue, hve, hce, hlim, hse⟩ :=
    Round102E.kernel_product_cutoff_representation mu D C hD hB
      cutoff hcutmeas hcut hcutlim e
  have heq : T0 = T := by
    apply ContinuousLinearMap.ext
    intro F
    apply Lp.ext
    filter_upwards [hT0 F, hT F] with x hx hy
    exact hx.trans hy.symm
  obtain ⟨us, vs, hus, hvs, _, hsharp⟩ :=
    Round100A.kernel_rankOne_cost_sharp mu D C hD hB e e.orthonormal
  have heu : us = u := by
    funext i
    apply Lp.ext
    filter_upwards [hus i, hu i] with x hx hy
    exact hx.trans hy.symm
  have hev : vs = v := by
    funext i
    apply Lp.ext
    filter_upwards [hvs i, hv i] with x hx hy
    exact hx.trans hy.symm
  rw [heu, hev] at hsharp
  have hroot : Real.sqrt (∫ p : Classes K × Classes K, ‖D p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      term.cost * Real.sqrt (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) := by
    calc
      _ ≤ Real.sqrt (term.cost^2 *
          (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu))) :=
        Real.sqrt_le_sqrt henergy
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hbnd.1]
  have hcost (J : Finset ι) : ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
      term.cost * Real.sqrt (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K, ‖C p.1 p.2‖^2 ∂(mu.prod mu)) := by
    have hn := hsharp J
    simp only [innerSL_apply_norm] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
  have htotal := le_of_tendsto hc.hasSum (Filter.Eventually.of_forall hcost)
  refine ⟨T, u, v, Err, ue, ve, ?_, hc, hcost, htotal, ?_, hErr, hce, hlim, hse⟩
  · intro F
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb (Lp.memLp F) hlm hrm).2
    filter_upwards [hT F, hact] with x hx hy
    rw [hx]
    change (∫ z, (m x * L x z) * (∫ y, C z y * F y ∂mu) ∂mu) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    exact congrArg (fun z => m x*z) hy
  · simpa only [heq] using hsum

end
#check genuine_separated_term_sharp_nuclear_cutoff
#print axioms genuine_separated_term_sharp_nuclear_cutoff
end Round107H


namespace Round107H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Actual compact-output convolution has a derived nuclear representation
and vanishing left-cutoff nuclear cost. No nuclear estimate is assumed. -/
theorem genuine_central_output_sharp_nuclear_cutoff
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
    (rho : Classes K → ℂ) (U : ℝ) (hU : 0 ≤ U)
    (hrhomeas : AEStronglyMeasurable rho mu)
    (hrhob : ∀ x, ‖rho x‖ ≤ 1)
    (hrhosupp : ∀ x, rho x ≠ 0 → |actualLog K x| ≤ U)
    (cutoff : ℕ → Classes K → ℂ)
    (hcutmeas : ∀ n, AEStronglyMeasurable (cutoff n) mu)
    (hcut : ∀ n x, ‖cutoff n x‖ ≤ 1)
    (hcutlim : ∀ x, Tendsto (fun n => cutoff n x) atTop (nhds 1))
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu)
      (Err : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (ue ve : ℕ → ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K rho
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖v i‖) ∧
      (∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
        (1+U^2) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
         Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      (∑' i, ‖u i‖ * ‖v i‖) ≤
        (1+U^2) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
         Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T ∧
      (∀ n F, ∀ᵐ x ∂mu, Err n F x = (cutoff n x-1)*T F x) ∧
      (∀ n, Summable (fun i => ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)) ∧
      Tendsto (fun n => ∑' i, ‖ue n i‖ * ‖innerSL ℂ (ve n i)‖)
        atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (innerSL ℂ (ve n i)).smulRight (ue n i)) (Err n)) := by
  let ell : Classes K → ℝ := actualLog K
  have hlog (x y : Classes K) : ell x = ell (x*y⁻¹) + ell y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  obtain ⟨hA, hB⟩ := genuine_noncompact_factors_memLp_two K mu ell psi theta alpha s R S
    ha hs hlog hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf hpres hlm hrm
  let L := leftKernel K ell alpha s psi
  let C := rightKernel K ell alpha s theta
  let m := fun x : Classes K => ((1+(ell x)^2 : ℝ) : ℂ) * rho x
  let D := fun x y => m x * L x y
  have hm : AEStronglyMeasurable m mu := by
    have hq : Measurable (fun x : Classes K => ((1+(ell x)^2 : ℝ) : ℂ)) := by
      dsimp only [ell]
      fun_prop
    exact hq.aestronglyMeasurable.mul hrhomeas
  have hmn (x) : ‖m x‖ ≤ (1+U^2) := by
    by_cases hx : rho x = 0
    · simp only [m, hx, mul_zero, norm_zero]
      positivity
    · have hsq : (ell x)^2 ≤ U^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg (ell x)) hU).mpr (hrhosupp x hx)
        simpa only [sq_abs] using hh
      dsimp only [m]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1+(ell x)^2)]
      calc
        _ ≤ (1+(ell x)^2)*1 := mul_le_mul_of_nonneg_left (hrhob x) (by positivity)
        _ ≤ 1+U^2 := by linarith
  have hDm : AEStronglyMeasurable (fun p : Classes K × Classes K => D p.1 p.2)
      (mu.prod mu) := hm.comp_fst.mul hA.aestronglyMeasurable
  have hAi := hA.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hdom (p : Classes K × Classes K) : ‖D p.1 p.2‖^2 ≤ (1+U^2)^2*‖L p.1 p.2‖^2 := by
    dsimp [D]
    rw [norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (hmn p.1) 2
  have hDi : Integrable (fun p : Classes K × Classes K => ‖D p.1 p.2‖^2)
      (mu.prod mu) := by
    apply (hAi.const_mul ((1+U^2)^2)).mono' (hDm.norm.pow 2)
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom p
  have hD := (memLp_two_iff_integrable_sq_norm hDm).mpr hDi
  have henergy : (∫ p : Classes K × Classes K, ‖D p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      (1+U^2)^2 * (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) := by
    rw [← integral_const_mul]
    exact integral_mono hDi (hAi.const_mul _) hdom
  obtain ⟨T0, u, v, hT0, hu, hv, hc, hN, hsum⟩ :=
    Round101E.kernel_product_representation mu D C hD hB e
  obtain ⟨T, Err, ue, ve, hT, hErr, hue, hve, hce, hlim, hse⟩ :=
    Round102E.kernel_product_cutoff_representation mu D C hD hB
      cutoff hcutmeas hcut hcutlim e
  have heq : T0 = T := by
    apply ContinuousLinearMap.ext
    intro F
    apply Lp.ext
    filter_upwards [hT0 F, hT F] with x hx hy
    exact hx.trans hy.symm
  obtain ⟨us, vs, hus, hvs, _, hsharp⟩ :=
    Round100A.kernel_rankOne_cost_sharp mu D C hD hB e e.orthonormal
  have heu : us = u := by
    funext i
    apply Lp.ext
    filter_upwards [hus i, hu i] with x hx hy
    exact hx.trans hy.symm
  have hev : vs = v := by
    funext i
    apply Lp.ext
    filter_upwards [hvs i, hv i] with x hx hy
    exact hx.trans hy.symm
  rw [heu, hev] at hsharp
  have hroot : Real.sqrt (∫ p : Classes K × Classes K, ‖D p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      (1+U^2) * Real.sqrt (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) := by
    calc
      _ ≤ Real.sqrt ((1+U^2)^2 *
          (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu))) :=
        Real.sqrt_le_sqrt henergy
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1+U^2)]
  have hcost (J : Finset ι) : ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤
      (1+U^2) * Real.sqrt (∫ p : Classes K × Classes K, ‖L p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K, ‖C p.1 p.2‖^2 ∂(mu.prod mu)) := by
    have hn := hsharp J
    simp only [innerSL_apply_norm] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
  have htotal := le_of_tendsto hc.hasSum (Filter.Eventually.of_forall hcost)
  refine ⟨T, u, v, Err, ue, ve, ?_, hc, hcost, htotal, ?_, hErr, hce, hlim, hse⟩
  · intro F
    have hact := (genuine_arithmetic_correction_cost_and_action K mu psi theta
      (fun x => F x) alpha s R S ha hs hell V hpush hout hpsi htheta hpsi0 htheta0
      hpsupp htsupp hpf htf hpres hemb (Lp.memLp F) hlm hrm).2
    filter_upwards [hT F, hact] with x hx hy
    rw [hx]
    change (∫ z, (m x * L x z) * (∫ y, C z y * F y ∂mu) ∂mu) = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    rw [hy, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    have hq : (((1+(ell x)^2 : ℝ) : ℂ) *
        ((1/(1+(ell x)^2) : ℝ) : ℂ)) = 1 := by
      rw [← Complex.ofReal_mul]
      have hp : (1+(ell x)^2 : ℝ) ≠ 0 := by positivity
      simp [hp]
    calc
      _ = (((1+(ell x)^2 : ℝ) : ℂ) * ((1/(1+(ell x)^2) : ℝ) : ℂ)) *
          (transportedCutoffKernel K rho (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y * F y) := by
              dsimp only [m, transportedCutoffKernel, ell]
              ring
      _ = _ := by rw [hq, one_mul]
  · simpa only [heq] using hsum

end
#check genuine_central_output_sharp_nuclear_cutoff
#print axioms genuine_central_output_sharp_nuclear_cutoff
end Round107H

namespace Round108H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Right composition preserves the concrete nuclear cost. This lemma is
used below for the derived genuine central-output kernel, not as an
assumed nuclearity criterion for the full target. -/
theorem right_composition_cost
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (T Q : H →L[ℂ] H) (u v : ι → H) (C : ℝ)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hbound : ∀ J : Finset ι, ∑ i ∈ J, ‖u i‖ * ‖v i‖ ≤ C)
    (hsum : HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T) :
    Summable (fun i => ‖u i‖ * ‖(innerSL ℂ (v i)).comp Q‖) ∧
    (∑' i, ‖u i‖ * ‖(innerSL ℂ (v i)).comp Q‖) ≤ ‖Q‖ * C ∧
    HasSum (fun i => ((innerSL ℂ (v i)).comp Q).smulRight (u i)) (T.comp Q) := by
  have hp (i) : ‖u i‖ * ‖(innerSL ℂ (v i)).comp Q‖ ≤
      ‖Q‖ * (‖u i‖ * ‖v i‖) := by
    have h := mul_le_mul_of_nonneg_left
      ((innerSL ℂ (v i)).opNorm_comp_le Q) (norm_nonneg (u i))
    simpa only [innerSL_apply_norm, mul_comm, mul_left_comm, mul_assoc] using h
  have hs : Summable (fun i => ‖u i‖ * ‖(innerSL ℂ (v i)).comp Q‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      hp (hc.mul_left ‖Q‖)
  have hb (J : Finset ι) : ∑ i ∈ J, ‖u i‖ * ‖(innerSL ℂ (v i)).comp Q‖ ≤ ‖Q‖ * C := by
    calc
      _ ≤ ∑ i ∈ J, ‖Q‖ * (‖u i‖ * ‖v i‖) := Finset.sum_le_sum (fun i hi => hp i)
      _ = ‖Q‖ * ∑ i ∈ J, ‖u i‖ * ‖v i‖ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound J) (norm_nonneg Q)
  refine ⟨hs, le_of_tendsto hs.hasSum (Eventually.of_forall hb), ?_⟩
  have h := ((ContinuousLinearMap.compL ℂ H H H).flip Q).hasSum hsum
  apply h.congr_fun
  intro i
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The genuine compact-output operator, in the required convolution-before-
right-projection order. Q is a supplied bounded map, not claimed to be the
unconstructed authentic spectral projection. All nuclear costs are derived. -/
theorem genuine_central_output_right_composition
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
    (rho : Classes K → ℂ) (U : ℝ) (hU : 0 ≤ U)
    (hrhomeas : AEStronglyMeasurable rho mu)
    (hrhob : ∀ x, ‖rho x‖ ≤ 1)
    (hrhosupp : ∀ x, rho x ≠ 0 → |actualLog K x| ≤ U)

    (Q : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (u : ι → Lp ℂ 2 mu) (eta : ι → Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, transportedCutoffKernel K rho (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * (Q F) y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖eta i‖) ∧
      (∑' i, ‖u i‖ * ‖eta i‖) ≤
        ‖Q‖ * ((1+U^2) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
          Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      HasSum (fun i => (eta i).smulRight (u i)) T ∧
      (∀ kappa : Classes K → ℂ,
        (∀ x, |actualLog K x| ≤ U → kappa x = 1) →
        ∀ F, ∀ᵐ x ∂mu, (kappa x-1)*T F x = 0) := by
  obtain ⟨T, u, v, Err, ue, ve, hT, hc, hN, htotal, hsum, hErr, hce, hlim, hse⟩ :=
    Round107H.genuine_central_output_sharp_nuclear_cutoff K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm rho U hU hrhomeas hrhob hrhosupp
      (fun _ _ => 1) (fun _ => aestronglyMeasurable_const)
      (by intro n x; simp) (fun _ => tendsto_const_nhds) e
  obtain ⟨hcQ, hNQ, hsQ⟩ := right_composition_cost T Q u v _ hc hN hsum
  refine ⟨T.comp Q, u, (fun i => (innerSL ℂ (v i)).comp Q), ?_, hcQ, hNQ, hsQ, ?_⟩
  · intro F
    exact hT (Q F)
  · intro kappa hk F
    filter_upwards [hT (Q F)] with x hx
    change (kappa x-1)*T (Q F) x = 0
    by_cases hr : rho x = 0
    · rw [hx]
      simp [transportedCutoffKernel, hr]
    · rw [hk x (hrhosupp x hr), sub_self, zero_mul]

end
#check right_composition_cost
#print axioms right_composition_cost
#check genuine_central_output_right_composition
#print axioms genuine_central_output_right_composition
end Round108H

namespace Round108H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
/-- Correctly ordered bounded right composition of an actual separated
rational residual. The incoming map is explicit and remains uninstantiated. -/
theorem genuine_residual_right_composition
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
    (d : ℕ) (term : Round105B.Term) (hterm : term ∈ Round105B.terms d)
    (hm : AEStronglyMeasurable
      (fun x => (term.coeff (actualLog K x) : ℂ)) mu)

    (Q : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (u : ι → Lp ℂ 2 mu) (eta : ι → Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ F, ∀ᵐ x ∂mu, T F x = (term.coeff (actualLog K x) : ℂ) *
        ∫ y, transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * (Q F) y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖eta i‖) ∧
      (∑' i, ‖u i‖ * ‖eta i‖) ≤
        ‖Q‖ * (term.cost * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
          Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      HasSum (fun i => (eta i).smulRight (u i)) T := by
  obtain ⟨T, u, v, Err, ue, ve, hT, hc, hN, htotal, hsum, hErr, hce, hlim, hse⟩ :=
    Round107H.genuine_separated_term_sharp_nuclear_cutoff K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm d term hterm hm
      (fun _ _ => 1) (fun _ => aestronglyMeasurable_const)
      (by intro n x; simp) (fun _ => tendsto_const_nhds) e
  obtain ⟨hcQ, hNQ, hsQ⟩ := right_composition_cost T Q u v _ hc hN hsum
  exact ⟨T.comp Q, u, (fun i => (innerSL ℂ (v i)).comp Q),
    (fun F => hT (Q F)), hcQ, hNQ, hsQ⟩
end
#check genuine_residual_right_composition
#print axioms genuine_residual_right_composition
end Round108H

namespace Round109H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The right-composition loss is independent of the output cutoff. -/
theorem right_composition_cutoff_cost
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (Err : ℕ → H →L[ℂ] H) (Q : H →L[ℂ] H)
    (u v : ℕ → ι → H)
    (hc : ∀ n, Summable (fun i => ‖u n i‖ * ‖innerSL ℂ (v n i)‖))
    (hl : Tendsto (fun n => ∑' i, ‖u n i‖ * ‖innerSL ℂ (v n i)‖) atTop (nhds 0))
    (hs : ∀ n, HasSum (fun i => (innerSL ℂ (v n i)).smulRight (u n i)) (Err n)) :
    (∀ n, Summable (fun i => ‖u n i‖ * ‖(innerSL ℂ (v n i)).comp Q‖)) ∧
    Tendsto (fun n => ∑' i, ‖u n i‖ * ‖(innerSL ℂ (v n i)).comp Q‖) atTop (nhds 0) ∧
    (∀ n, HasSum (fun i => ((innerSL ℂ (v n i)).comp Q).smulRight (u n i))
      ((Err n).comp Q)) := by
  have hn (n) : Summable (fun i => ‖u n i‖ * ‖v n i‖) := by
    simpa only [innerSL_apply_norm] using hc n
  have hb (n) (J : Finset ι) : ∑ i ∈ J, ‖u n i‖ * ‖v n i‖ ≤
      ∑' i, ‖u n i‖ * ‖v n i‖ := by
    exact (hn n).sum_le_tsum J (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hall (n) := Round108H.right_composition_cost (Err n) Q (u n) (v n)
    (∑' i, ‖u n i‖ * ‖v n i‖) (hn n) (hb n) (hs n)
  refine ⟨fun n => (hall n).1, ?_, fun n => (hall n).2.2⟩
  have hz : Tendsto (fun n => ‖Q‖ * (∑' i, ‖u n i‖ * ‖v n i‖)) atTop (nhds 0) := by
    simpa only [innerSL_apply_norm, mul_zero] using hl.const_mul ‖Q‖
  exact squeeze_zero
    (fun n => tsum_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    (fun n => (hall n).2.1) hz

/-- The actual rational residual after bounded right composition has
summable nuclear cost and an explicit LEFT-cutoff error whose entire
nuclear representation cost tends to zero. No lift estimate is assumed. -/
theorem genuine_residual_right_composition_cutoff
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
    (d : ℕ) (term : Round105B.Term) (hterm : term ∈ Round105B.terms d)
    (hm : AEStronglyMeasurable
      (fun x => (term.coeff (actualLog K x) : ℂ)) mu)

    (cutoff : ℕ → Classes K → ℂ)
    (hcutmeas : ∀ n, AEStronglyMeasurable (cutoff n) mu)
    (hcut : ∀ n x, ‖cutoff n x‖ ≤ 1)
    (hcutlim : ∀ x, Tendsto (fun n => cutoff n x) atTop (nhds 1))
    (Q : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (u : ι → Lp ℂ 2 mu) (eta : ι → Lp ℂ 2 mu →L[ℂ] ℂ)
      (Err : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (ue : ℕ → ι → Lp ℂ 2 mu)
      (etae : ℕ → ι → Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ F, ∀ᵐ x ∂mu, T F x = (term.coeff (actualLog K x) : ℂ) *
        ∫ y, transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * (Q F) y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖eta i‖) ∧
      (∑' i, ‖u i‖ * ‖eta i‖) ≤
        ‖Q‖ * (term.cost * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
          Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu))) ∧
      HasSum (fun i => (eta i).smulRight (u i)) T ∧
      (∀ n F, ∀ᵐ x ∂mu, Err n F x = (cutoff n x-1)*T F x) ∧
      (∀ n, Summable (fun i => ‖ue n i‖ * ‖etae n i‖)) ∧
      Tendsto (fun n => ∑' i, ‖ue n i‖ * ‖etae n i‖) atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (etae n i).smulRight (ue n i)) (Err n)) := by
  obtain ⟨T, u, v, Err, ue, ve, hT, hc, hN, htotal, hsum, hErr, hce, hlim, hse⟩ :=
    Round107H.genuine_separated_term_sharp_nuclear_cutoff K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm d term hterm hm cutoff hcutmeas hcut hcutlim e
  obtain ⟨hcQ, hNQ, hsQ⟩ := Round108H.right_composition_cost T Q u v _ hc hN hsum
  obtain ⟨hceQ, hlimQ, hseQ⟩ := right_composition_cutoff_cost Err Q ue ve hce hlim hse
  exact ⟨T.comp Q, u, (fun i => (innerSL ℂ (v i)).comp Q),
    (fun n => (Err n).comp Q), ue, (fun n i => (innerSL ℂ (ve n i)).comp Q),
    (fun F => hT (Q F)), hcQ, hNQ, hsQ, (fun n F => hErr n (Q F)),
    hceQ, hlimQ, hseQ⟩

end
#check right_composition_cutoff_cost
#print axioms right_composition_cutoff_cost
#check genuine_residual_right_composition_cutoff
#print axioms genuine_residual_right_composition_cutoff
end Round109H

namespace Round109H
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94A Round95A Round96A Round97A
open scoped Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Uniformity in varying bounded right maps follows from the same
cutoff energy; no convergence of the right maps is required. -/
theorem right_composition_cutoff_cost_uniform
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} (Err : ℕ → H →L[ℂ] H) (Q : ℕ → H →L[ℂ] H)
    (M : ℝ) (hQ : ∀ n, ‖Q n‖ ≤ M) (u v : ℕ → ι → H)
    (hc : ∀ n, Summable (fun i => ‖u n i‖ * ‖innerSL ℂ (v n i)‖))
    (hl : Tendsto (fun n => ∑' i, ‖u n i‖ * ‖innerSL ℂ (v n i)‖) atTop (nhds 0))
    (hs : ∀ n, HasSum (fun i => (innerSL ℂ (v n i)).smulRight (u n i)) (Err n)) :
    (∀ n, Summable (fun i => ‖u n i‖ * ‖(innerSL ℂ (v n i)).comp (Q n)‖)) ∧
    Tendsto (fun n => ∑' i, ‖u n i‖ * ‖(innerSL ℂ (v n i)).comp (Q n)‖) atTop (nhds 0) ∧
    (∀ n, HasSum (fun i => ((innerSL ℂ (v n i)).comp (Q n)).smulRight (u n i))
      ((Err n).comp (Q n))) := by
  have hn (n) : Summable (fun i => ‖u n i‖ * ‖v n i‖) := by
    simpa only [innerSL_apply_norm] using hc n
  have hb (n) (J : Finset ι) : ∑ i ∈ J, ‖u n i‖ * ‖v n i‖ ≤
      ∑' i, ‖u n i‖ * ‖v n i‖ := by
    exact (hn n).sum_le_tsum J (fun i hi => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hall (n) := Round108H.right_composition_cost (Err n) (Q n) (u n) (v n)
    (∑' i, ‖u n i‖ * ‖v n i‖) (hn n) (hb n) (hs n)
  refine ⟨fun n => (hall n).1, ?_, fun n => (hall n).2.2⟩
  have hz : Tendsto (fun n => M * (∑' i, ‖u n i‖ * ‖v n i‖)) atTop (nhds 0) := by
    simpa only [innerSL_apply_norm, mul_zero] using hl.const_mul M
  apply squeeze_zero
    (fun n => tsum_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))) _ hz
  intro n
  exact (hall n).2.1.trans (mul_le_mul_of_nonneg_right (hQ n)
    (tsum_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))))

theorem genuine_residual_varying_right_cutoff
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
    (d : ℕ) (term : Round105B.Term) (hterm : term ∈ Round105B.terms d)
    (hm : AEStronglyMeasurable
      (fun x => (term.coeff (actualLog K x) : ℂ)) mu)

    (cutoff : ℕ → Classes K → ℂ)
    (hcutmeas : ∀ n, AEStronglyMeasurable (cutoff n) mu)
    (hcut : ∀ n x, ‖cutoff n x‖ ≤ 1)
    (hcutlim : ∀ x, Tendsto (fun n => cutoff n x) atTop (nhds 1))
    (Q : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
    (M : ℝ) (hQ : ∀ n, ‖Q n‖ ≤ M)
    {ι : Type*} (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (u : ι → Lp ℂ 2 mu) (eta : ℕ → ι → Lp ℂ 2 mu →L[ℂ] ℂ)
      (Err : ℕ → Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu)
      (ue : ℕ → ι → Lp ℂ 2 mu)
      (etae : ℕ → ι → Lp ℂ 2 mu →L[ℂ] ℂ),
      (∀ n F, ∀ᵐ x ∂mu, T n F x = (term.coeff (actualLog K x) : ℂ) *
        ∫ y, transportedCutoffKernel K
          (fun a => ((1/(1+(actualLog K a)^2) : ℝ) : ℂ))
          (convolution K mu psi theta)
          (fun a => stripWeight alpha s (actualLog K a)) x y * (Q n F) y ∂mu) ∧
      (∀ n, Summable (fun i => ‖u i‖ * ‖eta n i‖)) ∧
      (∀ n, (∑' i, ‖u i‖ * ‖eta n i‖) ≤
        ‖Q n‖ * (term.cost * Real.sqrt (∫ p : Classes K × Classes K,
          ‖leftKernel K (actualLog K) alpha s psi p.1 p.2‖^2 ∂(mu.prod mu)) *
          Real.sqrt (∫ p : Classes K × Classes K,
          ‖rightKernel K (actualLog K) alpha s theta p.1 p.2‖^2 ∂(mu.prod mu)))) ∧
      (∀ n, HasSum (fun i => (eta n i).smulRight (u i)) (T n)) ∧
      (∀ n F, ∀ᵐ x ∂mu, Err n F x = (cutoff n x-1)*T n F x) ∧
      (∀ n, Summable (fun i => ‖ue n i‖ * ‖etae n i‖)) ∧
      Tendsto (fun n => ∑' i, ‖ue n i‖ * ‖etae n i‖) atTop (nhds 0) ∧
      (∀ n, HasSum (fun i => (etae n i).smulRight (ue n i)) (Err n)) := by
  obtain ⟨T, u, v, Err, ue, ve, hT, hc, hN, htotal, hsum, hErr, hce, hlim, hse⟩ :=
    Round107H.genuine_separated_term_sharp_nuclear_cutoff K mu psi theta alpha s R S
      ha hs hell V hpush hout hpsi htheta hpsi0 htheta0 hpsupp htsupp hpf htf
      hpres hemb hlm hrm d term hterm hm cutoff hcutmeas hcut hcutlim e
  have hall (n) := Round108H.right_composition_cost T (Q n) u v _ hc hN hsum
  obtain ⟨hceQ, hlimQ, hseQ⟩ :=
    right_composition_cutoff_cost_uniform Err Q M hQ ue ve hce hlim hse
  exact ⟨(fun n => T.comp (Q n)), u, (fun n i => (innerSL ℂ (v i)).comp (Q n)),
    (fun n => (Err n).comp (Q n)), ue, (fun n i => (innerSL ℂ (ve n i)).comp (Q n)),
    (fun n F => hT (Q n F)), (fun n => (hall n).1), (fun n => (hall n).2.1),
    (fun n => (hall n).2.2), (fun n F => hErr n (Q n F)), hceQ, hlimQ, hseQ⟩
end
#check right_composition_cutoff_cost_uniform
#print axioms right_composition_cutoff_cost_uniform
#check genuine_residual_varying_right_cutoff
#print axioms genuine_residual_varying_right_cutoff
end Round109H
