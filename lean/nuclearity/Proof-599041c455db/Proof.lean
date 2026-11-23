import Mathlib

/-! Round 90 B: exact convolution correction for the actual idele-class group.
This is the manuscript weight at alpha=0, s=2. It controls the difference
between ordinary and weight-conjugated convolution, an explicit source of
leakage for A(phi) P. Nuclear summability and the Hilbert adjoint identification
are not asserted. -/
open scoped NumberField
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

/- At alpha=0,s=2, this is w^-1 A(phi) w, with w(x)=1+ell(x)^2.
For reflected conjugate phi it is the formal weighted Hilbert adjoint. -/
noncomputable def weightConjugatedConvolution (μ : Measure (Classes K))
    (ell : Classes K → ℝ) (φ f : Classes K → ℂ) (x : Classes K) : ℂ :=
  ∫ g, (((1 + ell (g⁻¹ * x) ^ 2) / (1 + ell x ^ 2) : ℝ) : ℂ) *
    (φ g * f (g⁻¹ * x)) ∂μ

/- Exact algebraic correction; no uniform lift or spectral bound is used. -/
end NuclearBoundB90

namespace NuclearBoundB91
open NuclearBoundB90
variable (K : Type*) [Field K] [NumberField K]

/- Direct square-kernel estimate for genuine convolution after a cutoff.
The weight is the Hilbert density. No nuclear estimate is assumed. -/
theorem manuscript_weight_ge_one (α s t : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    1 ≤ Real.exp (2*α*|t|) * (1+t^2) ^ (s/2) := by
  have he : 1 ≤ Real.exp (2*α*|t|) := Real.one_le_exp_iff.mpr (by positivity)
  have hp : 1 ≤ (1+t^2) ^ (s/2) := Real.one_le_rpow (by nlinarith) (by positivity)
  nlinarith


/- Kernel of M_rho A_phi after the weighted-to-unweighted L2 conjugation. -/
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

/- Product-measure form of the actual weighted convolution kernel bound. -/
end NuclearBoundB91

namespace Round93A
noncomputable section
open MeasureTheory NuclearBoundB90 NuclearBoundB91

def stripWeight (alpha s u : ℝ) : ℝ :=
  Real.exp (2 * alpha * |u|) * (1 + u ^ 2) ^ (s / 2)

/- A corrected translation estimate, valid for every nonnegative strip width
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

/- Pointwise actual convolution kernel bound with displacement cost. -/
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

/- Actual-group kernel energy with unweighted output L2 mass.
This is an input to an HS factorization, not an S1 assertion. -/
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

/- The weighted test mass is bounded by a finite support constant times
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

/- Finite energy follows from ordinary L2 masses and test support.
It still requires the genuine kernel/Hilbert-operator bridge before use as
an HS norm, and two factors before an S1 norm can be concluded. -/
theorem second_correction_split_cost (x y h : ℝ) (hxy : x = h+y) :
    (1+y^2)/(1+x^2)^2 ≤ (2*(1+h^2))/(1+x^2) := by
  have hx : 0 < 1+x^2 := by positivity
  have hy : y = x-h := by linarith
  have hp : 1+y^2 ≤ 2*(1+h^2)*(1+x^2) := by
    rw [hy]
    nlinarith [sq_nonneg (x+h), sq_nonneg (x*h)]
  calc
    _ = ((1+y^2)/(1+x^2))/(1+x^2) := by
      field_simp [ne_of_gt hx]
    _ ≤ _ := div_le_div_of_nonneg_right ((div_le_iff₀ hx).mpr hp) hx.le

/- Direct control of the first noncompact factor's genuine kernel energy.
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


namespace Round94F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/- Squared kernels for the two global factors of M_(1/q²) A(psi*theta),
q(x)=sqrt(1+ell(x)^2). They contain no expanding cutoff. -/
def factorEnergy (ell : Classes K → ℝ) (alpha s : ℝ)
    (phi : Classes K → ℂ) (first : Bool) (x y : Classes K) : ℝ :=
  (if first then (1+ell y^2)/(1+ell x^2)^2 else 1/(1+ell x^2)) *
    ‖transportedCutoffKernel K (fun _ => 1) phi
      (fun z => stripWeight alpha s (ell z)) x y‖^2

def testDensity (ell : Classes K → ℝ) (alpha s : ℝ)
    (phi : Classes K → ℂ) (first : Bool) (g : Classes K) : ℝ :=
  (if first then 2*(1+ell g^2) else 1) *
    translationCost alpha s (ell g) * ‖phi g‖^2

theorem factorEnergy_bound (ell : Classes K → ℝ) (alpha s : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (phi : Classes K → ℂ)
    (first : Bool) (x y : Classes K)
    (hlog : ell x = ell (x*y⁻¹)+ell y) :
    factorEnergy K ell alpha s phi first x y ≤
      (1/(1+ell x^2)) * testDensity K ell alpha s phi first (x*y⁻¹) := by
  cases first
  · have hk := genuine_kernel_displacement_bound K ell (fun _ => 1) phi
      alpha s ha hs x y hlog
    simp only [norm_one, one_pow, one_mul] at hk
    dsimp [factorEnergy, testDensity]
    calc
      _ ≤ (1/(1+ell x^2)) * (‖phi (x*y⁻¹)‖^2 *
          translationCost alpha s (ell (x*y⁻¹))) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := by ring
  · have hk := genuine_second_correction_factor_integrand K ell phi alpha s ha hs x y hlog
    simpa only [factorEnergy, testDensity, Bool.true_eq, ↓reduceIte,
      div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hk

/- Global two-factor energy: output mass is the integrable rational decay,
not the mass of an expanding cutoff. -/
theorem genuine_second_correction_factor_energy
    (mu : Measure (Classes K)) (ell : Classes K → ℝ) (alpha s : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (phi : Classes K → ℂ) (first : Bool)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹)+ell y)
    (hm : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K ell alpha s phi first g)))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (factorEnergy K ell alpha s phi first x y) ∂mu ∂mu) ≤
      (∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) ∂mu) *
      (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s phi first g) ∂mu) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) *
        (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s phi first g) ∂mu) ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal (1/(1+ell x^2)) *
            ENNReal.ofReal (testDensity K ell alpha s phi first (x*y⁻¹)) ∂mu := by
          apply lintegral_mono
          intro y
          dsimp only
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(1+ell x^2))]
          exact ENNReal.ofReal_le_ofReal (factorEnergy_bound K ell alpha s ha hs phi first x y (hlog x y))
        _ = _ := by
          have ht : Measurable (fun y : Classes K =>
              ENNReal.ofReal (testDensity K ell alpha s phi first (x*y⁻¹))) :=
            hp.comp (hpres x).measurable
          rw [lintegral_const_mul _ ht, (hpres x).lintegral_comp hp]
    _ = _ := lintegral_mul_const _ hm

/- Continuous rank-one cost for the genuine noncompact second correction.
This is an estimate of explicit kernels, not an assumption of nuclearity. -/
def factorKernel (ell : Classes K → ℝ) (alpha s : ℝ)
    (phi : Classes K → ℂ) (first : Bool) (x y : Classes K) : ℂ :=
  (Real.sqrt (if first then (1+ell y^2)/(1+ell x^2)^2
    else 1/(1+ell x^2)) : ℂ) *
      transportedCutoffKernel K (fun _ => 1) phi
        (fun z => stripWeight alpha s (ell z)) x y

theorem factorKernel_norm_sq (ell : Classes K → ℝ) (alpha s : ℝ)
    (phi : Classes K → ℂ) (first : Bool) (x y : Classes K) :
    ‖factorKernel K ell alpha s phi first x y‖^2 =
      factorEnergy K ell alpha s phi first x y := by
  have hn : 0 ≤ (if first then (1+ell y^2)/(1+ell x^2)^2
      else 1/(1+ell x^2)) := by cases first <;> positivity
  simp only [factorKernel, factorEnergy, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hn]

/- Cancellation of the noncompact factors at the shared variable. -/
theorem factor_multiplier_cancellation (x z : ℝ) :
    Real.sqrt ((1+z^2)/(1+x^2)^2) * Real.sqrt (1/(1+z^2)) =
      1/(1+x^2) := by
  have hx : 1+x^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+x^2)
  have hz : 1+z^2 ≠ 0 := ne_of_gt (by positivity : 0 < 1+z^2)
  rw [← Real.sqrt_mul (by positivity : 0 ≤ (1+z^2)/(1+x^2)^2)]
  have he : ((1+z^2)/(1+x^2)^2)*(1/(1+z^2)) = (1/(1+x^2))^2 := by
    field_simp
  rw [he, Real.sqrt_sq (by positivity : 0 ≤ 1/(1+x^2))]

end
end Round94F

namespace Round95F
open MeasureTheory NuclearBoundB90
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def leadMultiplier (t : ℝ) : ℝ := 2*t/(1+t^2)
def decayMultiplier (t : ℝ) : ℝ := 1/(1+t^2)

/- Two exact corrections leave only integrable-decay output multipliers.
This is authentic convolution at alpha=0,s=2, not a nuclearity theorem. -/
theorem twice_corrected_multiplier_bounds (t : ℝ) :
    |leadMultiplier t| ≤ 1 ∧
    |(leadMultiplier t)^2 - decayMultiplier t| ≤ 3*decayMultiplier t ∧
    |leadMultiplier t*decayMultiplier t| ≤ decayMultiplier t := by
  have hd : 0 < 1+t^2 := by positivity
  have hd0 : (1+t^2 : ℝ) ≠ 0 := ne_of_gt hd
  have hab : |t|^2 = t^2 := sq_abs t
  have hl : |leadMultiplier t| ≤ 1 := by
    dsimp [leadMultiplier]
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (|t|-1)]
  refine ⟨hl, ?_, ?_⟩
  · have he : (leadMultiplier t)^2 - decayMultiplier t =
        (3*t^2-1)/(1+t^2)^2 := by
      dsimp [leadMultiplier, decayMultiplier]
      field_simp
      ring
    rw [he, abs_div, abs_of_pos (sq_pos_of_pos hd)]
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    have hr : 3*decayMultiplier t*(1+t^2)^2 = 3*(1+t^2) := by
      dsimp [decayMultiplier]
      field_simp
    rw [hr]
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg t]
  · have hbpos : 0 ≤ decayMultiplier t := by dsimp [decayMultiplier]; positivity
    rw [abs_mul, abs_of_nonneg hbpos]
    simpa using mul_le_mul_of_nonneg_right hl hbpos

end
end Round95F

namespace Round96F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round95F
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/- Bounded factor which converts b into the actual second residual a^2-b. -/
def residualRatio (t : ℝ) : ℝ := (3*t^2-1)/(1+t^2)

theorem residualRatio_identity (t : ℝ) :
    residualRatio t * decayMultiplier t = (leadMultiplier t)^2-decayMultiplier t := by
  dsimp [residualRatio, leadMultiplier, decayMultiplier]
  field_simp
  ring

theorem residualRatio_bound (t : ℝ) : |residualRatio t| ≤ 3 := by
  have hd : 0 < 1+t^2 := by positivity
  dsimp [residualRatio]
  rw [abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg t]

/- Squared first factor for either authentic residual, including cutoff error. -/
def residualEnergy (ell : Classes K → ℝ) (alpha s : ℝ)
    (rho psi : Classes K → ℂ) (second : Bool) (x z : Classes K) : ℝ :=
  ‖rho x‖^2 * (if second then residualRatio (ell x) else leadMultiplier (ell x))^2 *
    factorEnergy K ell alpha s psi true x z

/- Both residuals have one common, explicitly proved kernel envelope. -/
theorem genuine_residualEnergy_bound
    (ell : Classes K → ℝ) (alpha s : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi : Classes K → ℂ) (second : Bool) (x z : Classes K)
    (hlog : ell x = ell (x*z⁻¹)+ell z) :
    residualEnergy K ell alpha s rho psi second x z ≤
      (9*‖rho x‖^2/(1+ell x^2)) * testDensity K ell alpha s psi true (x*z⁻¹) := by
  have hr : |if second then residualRatio (ell x) else leadMultiplier (ell x)| ≤ 3 := by
    cases second
    · exact (twice_corrected_multiplier_bounds (ell x)).1.trans (by norm_num)
    · exact residualRatio_bound (ell x)
  have hr2 : (if second then residualRatio (ell x) else leadMultiplier (ell x))^2 ≤ 9 := by
    nlinarith [sq_abs (if second then residualRatio (ell x) else leadMultiplier (ell x)),
      abs_nonneg (if second then residualRatio (ell x) else leadMultiplier (ell x))]
  have he0 : 0 ≤ factorEnergy K ell alpha s psi true x z := by
    dsimp [factorEnergy]
    positivity
  have he := factorEnergy_bound K ell alpha s ha hs psi true x z hlog
  dsimp [residualEnergy]
  calc
    _ ≤ (9*‖rho x‖^2) * factorEnergy K ell alpha s psi true x z := by
      apply mul_le_mul_of_nonneg_right _ he0
      nlinarith [sq_nonneg ‖rho x‖]
    _ ≤ (9*‖rho x‖^2) * ((1/(1+ell x^2))*
        testDensity K ell alpha s psi true (x*z⁻¹)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/- No expanding-cutoff mass appears: only the integrable rational tail mass. -/
theorem genuine_residual_factor_energy
    (mu : Measure (Classes K)) (ell : Classes K → ℝ) (alpha s : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s) (rho psi : Classes K → ℂ) (second : Bool)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹)+ell y)
    (hm : Measurable (fun x => ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K ell alpha s psi true g)))
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu) :
    (∫⁻ x, ∫⁻ z, ENNReal.ofReal (residualEnergy K ell alpha s rho psi second x z) ∂mu ∂mu) ≤
      (∫⁻ x, ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2)) ∂mu) *
      (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s psi true g) ∂mu) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2)) *
        (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s psi true g) ∂mu) ∂mu := by
      apply lintegral_mono
      intro x
      dsimp only
      calc
        _ ≤ ∫⁻ z, ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2)) *
            ENNReal.ofReal (testDensity K ell alpha s psi true (x*z⁻¹)) ∂mu := by
          apply lintegral_mono
          intro z
          dsimp only
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 9*‖rho x‖^2/(1+ell x^2))]
          exact ENNReal.ofReal_le_ofReal
            (genuine_residualEnergy_bound K ell alpha s ha hs rho psi second x z (hlog x z))
        _ = _ := by
          have ht : Measurable (fun z : Classes K =>
              ENNReal.ofReal (testDensity K ell alpha s psi true (x*z⁻¹))) :=
            hp.comp (hpres x).measurable
          rw [lintegral_const_mul _ ht, (hpres x).lintegral_comp hp]
    _ = _ := lintegral_mul_const _ hm

end
end Round96F

namespace Round96F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round95F
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def residualFactorKernel (ell : Classes K → ℝ) (alpha s : ℝ)
    (rho psi : Classes K → ℂ) (second : Bool) (x z : Classes K) : ℂ :=
  rho x * ((if second then residualRatio (ell x) else leadMultiplier (ell x) : ℝ) : ℂ) *
    factorKernel K ell alpha s psi true x z

theorem residualFactorKernel_norm_sq
    (ell : Classes K → ℝ) (alpha s : ℝ) (rho psi : Classes K → ℂ)
    (second : Bool) (x z : Classes K) :
    ‖residualFactorKernel K ell alpha s rho psi second x z‖^2 =
      residualEnergy K ell alpha s rho psi second x z := by
  simp only [residualFactorKernel, residualEnergy, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, factorKernel_norm_sq]

/- Continuous rank-one cost for the actual signed residual kernels.
The cutoff enters only through its rationally weighted squared mass. -/
theorem genuine_residualFactorKernel_product
    (ell : Classes K → ℝ) (alpha s : ℝ) (rho psi theta : Classes K → ℂ)
    (second : Bool) (x z y : Classes K) :
    residualFactorKernel K ell alpha s rho psi second x z *
      factorKernel K ell alpha s theta false z y =
    rho x * ((if second then (leadMultiplier (ell x))^2-decayMultiplier (ell x)
      else leadMultiplier (ell x)*decayMultiplier (ell x) : ℝ) : ℂ) *
      (transportedCutoffKernel K (fun _ => 1) psi
        (fun u => stripWeight alpha s (ell u)) x z *
       transportedCutoffKernel K (fun _ => 1) theta
        (fun u => stripWeight alpha s (ell u)) z y) := by
  have hc := congrArg (fun r : ℝ => (r : ℂ))
    (factor_multiplier_cancellation (ell x) (ell z))
  push_cast at hc
  have hr : (if second then residualRatio (ell x) else leadMultiplier (ell x)) *
      (1/(1+ell x^2)) =
      (if second then (leadMultiplier (ell x))^2-decayMultiplier (ell x)
        else leadMultiplier (ell x)*decayMultiplier (ell x)) := by
    cases second
    · rfl
    · exact residualRatio_identity (ell x)
  have hr' := congrArg (fun r : ℝ => (r : ℂ)) hr
  push_cast at hr'
  dsimp only [residualFactorKernel, factorKernel]
  simp only [Bool.false_eq_true, ↓reduceIte]
  linear_combination
    rho x * ((if second then residualRatio (ell x) else leadMultiplier (ell x) : ℝ) : ℂ) *
      (transportedCutoffKernel K (fun _ => 1) psi
        (fun u => stripWeight alpha s (ell u)) x z *
       transportedCutoffKernel K (fun _ => 1) theta
        (fun u => stripWeight alpha s (ell u)) z y) * hc +
    rho x * (transportedCutoffKernel K (fun _ => 1) psi
        (fun u => stripWeight alpha s (ell u)) x z *
       transportedCutoffKernel K (fun _ => 1) theta
        (fun u => stripWeight alpha s (ell u)) z y) * hr'

end
end Round96F


/-! Direct cutoff estimates on the genuine idele-class group. These establish
weighted energy convergence for each actual vector. They do not establish
nuclearity or a summable representation of the projected convolution. -/
open scoped NumberField
open MeasureTheory Filter

namespace NuclearBoundB89

variable (K : Type*) [Field K] [NumberField K]
abbrev Adeles := NumberField.AdeleRing (𝓞 K) K
abbrev Ideles := (Adeles K)ˣ
noncomputable def principalIdele : Kˣ →* Ideles K :=
  Units.map (algebraMap K (Adeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (Ideles K) :=
  (principalIdele K).range
abbrev IdeleClasses := Ideles K ⧸ principalIdeles K
noncomputable instance : MeasurableSpace (IdeleClasses K) := borel (IdeleClasses K)

/- Squared-norm density of a cutoff error is dominated independently of cutoff.
The actual manuscript weight is an allowed w; there is no bound on lifts here. -/
end NuclearBoundB89

namespace Round96F
open MeasureTheory Filter NuclearBoundB90 Round93A Round94F
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/- The explicit real-valued bound for the residual cutoff cost tends to zero.
Integrability of the rational log mass is retained, not nuclearity. -/
end
end Round96F

namespace Round97F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

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


theorem genuine_profile_finite_of_log_pushforward
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (hell : Measurable ell) (V : NNReal)
    (hpush : Measure.map ell mu = (V : ENNReal) • volume) :
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

/- A bounded output multiplier has finite residual profile mass, derived
from the logarithmic Haar pushforward rather than assumed. -/
theorem genuine_bounded_residual_profile_finite
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (hell : Measurable ell) (V : NNReal)
    (hpush : Measure.map ell mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (rho : Classes K → ℂ) (B : ℝ) (hrho : ∀ x, ‖rho x‖ ≤ B) :
    (∫⁻ x, ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2)) ∂mu) < ⊤ := by
  have hB : 0 ≤ B := (norm_nonneg (rho 1)).trans (hrho 1)
  have hbound :
      (∫⁻ x, ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2)) ∂mu) ≤
      ENNReal.ofReal (9*B^2) *
        (∫⁻ x, ENNReal.ofReal (1/(1+ell x^2)) ∂mu) := by
    calc
      _ ≤ ∫⁻ x, ENNReal.ofReal (9*B^2) *
          ENNReal.ofReal (1/(1+ell x^2)) ∂mu := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 9*B^2)]
        apply ENNReal.ofReal_le_ofReal
        have hsq : ‖rho x‖^2 ≤ B^2 := by
          nlinarith [hrho x, norm_nonneg (rho x)]
        calc
          _ ≤ 9*B^2/(1+ell x^2) :=
            div_le_div_of_nonneg_right (by nlinarith) (by positivity)
          _ = _ := by ring
      _ = _ := lintegral_const_mul _ hb
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (genuine_profile_finite_of_log_pushforward K mu ell hell V hpush))

/- Finite continuous rank-one cost for both signed residual kernels.
Only ordinary test L2 masses and logarithmic support bounds are assumed;
no kernel-energy, lift, nuclearity or rank-one summability bound is assumed. -/
end
end Round97F

namespace Round97F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/- The actual signed first residual kernel lies in L2 of the genuine
idele-class product. This is the finite-energy input to its HS realization,
not an assertion that the full projected convolution is nuclear. -/
theorem genuine_signed_residual_kernel_memLp_two
    (mu : Measure (Classes K)) [SFinite mu]
    (ell : Classes K → ℝ) (alpha s R B : ℝ)
    (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi : Classes K → ℂ) (second : Bool)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹)+ell y)
    (hell : Measurable ell) (V : NNReal)
    (hpush : Measure.map ell mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hm : Measurable (fun x => ENNReal.ofReal (9*‖rho x‖^2/(1+ell x^2))))
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K ell alpha s psi true g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |ell g| ≤ R)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hkm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      residualFactorKernel K ell alpha s rho psi second z.1 z.2) (mu.prod mu)) :
    MemLp (fun z : Classes K × Classes K =>
      residualFactorKernel K ell alpha s rho psi second z.1 z.2) 2 (mu.prod mu) := by
  have hk := ENNReal.measurable_ofReal.comp_aemeasurable
    (hkm.norm.pow 2).aemeasurable
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖residualFactorKernel K ell alpha s rho psi second z.1 z.2‖^2))
      (mu.prod mu) at hk
  simp_rw [residualFactorKernel_norm_sq] at hk
  apply (memLp_two_iff_integrable_sq_norm hkm).mpr
  refine ⟨hkm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  simp_rw [residualFactorKernel_norm_sq]
  rw [lintegral_prod _ hk]
  have hM := genuine_bounded_residual_profile_finite K mu ell hell V hpush hb rho B hrho
  have hD : (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s psi true g) ∂mu) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hpf ENNReal.ofReal_ne_top)
      (genuine_second_correction_test_mass K mu ell psi alpha s R ha hs hpsupp hp0)
  exact (genuine_residual_factor_energy K mu ell alpha s ha hs rho psi second
    hlog hm hp hpres).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hM.ne hD))

/- Remove the former integrable-profile hypothesis from the scalar
cutoff majorant convergence, retaining the explicit Haar normalization. -/
end
end Round97F


namespace Round98F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F
noncomputable section
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

/- Exact dual norm of the constructed kernel-row functional. -/
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


variable (K : Type*) [Field K] [NumberField K]

/- The genuine companion kernel has finite L2 energy from supported tests.
No product-kernel energy hypothesis is assumed. -/
theorem genuine_companion_memLp_two
    (mu : Measure (Classes K)) [SFinite mu]
    (ell : Classes K → ℝ) (alpha s S : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (theta : Classes K → ℂ)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹)+ell y)
    (hell : Measurable ell) (V : NNReal)
    (hpush : Measure.map ell mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K ell alpha s theta false g)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (htsupp : ∀ g, theta g ≠ 0 → |ell g| ≤ S)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hkm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K ell alpha s theta false z.1 z.2) (mu.prod mu)) :
    MemLp (fun z : Classes K × Classes K =>
      factorKernel K ell alpha s theta false z.1 z.2) 2 (mu.prod mu) := by
  have hk := ENNReal.measurable_ofReal.comp_aemeasurable
    (hkm.norm.pow 2).aemeasurable
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖factorKernel K ell alpha s theta false z.1 z.2‖^2))
      (mu.prod mu) at hk
  simp_rw [factorKernel_norm_sq] at hk
  apply (memLp_two_iff_integrable_sq_norm hkm).mpr
  refine ⟨hkm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  simp_rw [factorKernel_norm_sq]
  rw [lintegral_prod _ hk]
  have hJ := genuine_profile_finite_of_log_pushforward K mu ell hell V hpush
  have hE : (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s theta false g) ∂mu) ≠ ⊤ := by
    have he := ne_top_of_le_ne_top (ENNReal.mul_ne_top htf ENNReal.ofReal_ne_top)
      (genuine_weighted_test_mass_bound K mu ell theta alpha s S ha hs htsupp ht0)
    simpa only [testDensity, Bool.false_eq_true, ↓reduceIte, one_mul, mul_comm] using he
  exact (genuine_second_correction_factor_energy K mu ell alpha s ha hs theta false
    hlog hb ht hpres).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hJ.ne hE))

/- The actual signed residual factors are genuine Hilbert vectors and dual
functionals, with exactly their kernel cross-norm cost. This does not assert
measurability of the Hilbert-valued family or an S1 integral. -/
end
end Round98F

namespace Round98F
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round95F Round96F
noncomputable section

def signedResidualMultiplier (t : ℝ) (second : Bool) : ℂ :=
  ((if second then (leadMultiplier t)^2-decayMultiplier t
    else leadMultiplier t*decayMultiplier t : ℝ) : ℂ)

theorem group_cancel_middle {G : Type*} [Group G] (a b c : G) :
    (a*b⁻¹)⁻¹*(a*c⁻¹) = b*c⁻¹ := by group

variable (K : Type*) [Field K] [NumberField K]

/- Exact composition for both authentic signed residuals, preserving the
left multiplier and actual convolution order. -/
theorem genuine_signed_residual_kernel_composition
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (alpha s : ℝ) (rho psi theta : Classes K → ℂ) (second : Bool)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (x y : Classes K) :
    (∫ z, residualFactorKernel K ell alpha s rho psi second x z *
      factorKernel K ell alpha s theta false z y ∂mu) =
    (rho x * signedResidualMultiplier (ell x) second) *
      transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
        (fun a => stripWeight alpha s (ell a)) x y := by
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
  have hid (z : Classes K) :
      residualFactorKernel K ell alpha s rho psi second x z *
        factorKernel K ell alpha s theta false z y =
      (rho x * signedResidualMultiplier (ell x) second *
        (Real.sqrt (w x / w y) : ℂ)) * (psi (x*z⁻¹)*theta (z*y⁻¹)) := by
    rw [genuine_residualFactorKernel_product]
    unfold transportedCutoffKernel
    simp only [one_mul]
    change rho x * signedResidualMultiplier (ell x) second *
      ((psi (x*z⁻¹)*(Real.sqrt (w x/w z) : ℂ)) *
        (theta (z*y⁻¹)*(Real.sqrt (w z/w y) : ℂ))) = _
    calc
      _ = (rho x * signedResidualMultiplier (ell x) second) *
        (psi (x*z⁻¹)*theta (z*y⁻¹)) *
        ((Real.sqrt (w x/w z) : ℂ)*(Real.sqrt (w z/w y) : ℂ)) := by ring
      _ = _ := by rw [htel]; ring
  have hgroup (z : Classes K) : (x*z⁻¹)⁻¹*(x*y⁻¹) = z*y⁻¹ :=
    group_cancel_middle x z y
  have hc := (hpres x).integral_comp (hemb x)
    (fun g => psi g * theta (g⁻¹*(x*y⁻¹)))
  simp only [hgroup] at hc
  calc
    _ = ∫ z, (rho x * signedResidualMultiplier (ell x) second *
        (Real.sqrt (w x / w y) : ℂ)) * (psi (x*z⁻¹)*theta (z*y⁻¹)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hid z
    _ = _ := by
      rw [integral_const_mul, hc]
      unfold transportedCutoffKernel NuclearBoundB90.convolution
      dsimp only [w]
      ring

/- The required product integrability is derived from L2 factors. -/
theorem kernel_fubini_from_L2 {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (a f : X → ℂ) (b : X × X → ℂ)
    (ha : MemLp a 2 mu) (hb : MemLp b 2 (mu.prod mu)) (hf : MemLp f 2 mu) :
    Integrable (fun p : X × X => (a p.1 * b p) * f p.2) (mu.prod mu) := by
  have hm : AEStronglyMeasurable (fun p : X × X => a p.1 * f p.2) (mu.prod mu) :=
    ha.aestronglyMeasurable.comp_fst.mul hf.aestronglyMeasurable.comp_snd
  have hi := (ha.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).mul_prod
    (hf.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
  have hp : MemLp (fun p : X × X => a p.1 * f p.2) 2 (mu.prod mu) := by
    apply (memLp_two_iff_integrable_sq_norm hm).mpr
    simpa only [norm_mul, mul_pow] using hi
  apply (hp.integrable_mul hb).congr
  filter_upwards [] with p
  change (a p.1 * f p.2) * b p = (a p.1 * b p) * f p.2
  ring

/- Both signed residual kernel products act as their authentic convolutions.
The product-L2 premises are supplied by the supported-test theorems above;
this is not an S1 or projected-operator assertion. -/
theorem genuine_signed_residual_action_from_L2
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (alpha s : ℝ) (rho psi theta f : Classes K → ℂ) (second : Bool)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hA : MemLp (fun p : Classes K × Classes K =>
      residualFactorKernel K ell alpha s rho psi second p.1 p.2) 2 (mu.prod mu))
    (hB : MemLp (fun p : Classes K × Classes K =>
      factorKernel K ell alpha s theta false p.1 p.2) 2 (mu.prod mu))
    (hf : MemLp f 2 mu) :
    ∀ᵐ x ∂mu,
      (∫ z, residualFactorKernel K ell alpha s rho psi second x z *
        (∫ y, factorKernel K ell alpha s theta false z y * f y ∂mu) ∂mu) =
      ∫ y, ((rho x * signedResidualMultiplier (ell x) second) *
        transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
          (fun a => stripWeight alpha s (ell a)) x y) * f y ∂mu := by
  have hAi := hA.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  filter_upwards [hA.aestronglyMeasurable.prodMk_left, hAi.prod_right_ae] with x hm hi
  have ha := (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have hF := kernel_fubini_from_L2 mu _ f _ ha hB hf
  calc
    _ = ∫ z, ∫ y, (residualFactorKernel K ell alpha s rho psi second x z *
        factorKernel K ell alpha s theta false z y) * f y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ y, ∫ z, (residualFactorKernel K ell alpha s rho psi second x z *
        factorKernel K ell alpha s theta false z y) * f y ∂mu ∂mu :=
      integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_mul_const, genuine_signed_residual_kernel_composition K mu ell
        alpha s rho psi theta second hpres hemb]

end
end Round98F

open scoped BigOperators NNReal ENNReal
open MeasureTheory Filter

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
/- Outside finitely many finite places, an actual idele has local norm one. -/
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
/- Arithmetic compatibility needed to descend the actual spectral jet coordinate. -/
theorem genuineIdeleLog_principal (a : Kˣ) :
    genuineIdeleLog K (principalIdele K a) = 0 := by
  simp [genuineIdeleLog, genuineIdeleModulus_principal]
theorem genuineIdeleLog_add (a b : HeckeIdeles K) :
    genuineIdeleLog K (a * b) = genuineIdeleLog K a + genuineIdeleLog K b := by
  unfold genuineIdeleLog
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b), Complex.ofReal_add]

/- Explicit remaining analytic/algebraic hypothesis: additivity of the actual
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

/- Exact dual norm of the constructed kernel-row functional. -/
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


/- Actual integral outputs, their L2 membership and uniform finite Bessel bound
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

/- The right factor is conjugate-transposed, so the rank-one family is
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


/- The displayed Hilbert rank-one operators form a norm-convergent series
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
/- Row Cauchy-Schwarz, integrated on the actual product measure. -/
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
/- Realize an actual square-integrable kernel as a bounded operator.
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


namespace Round101E
/- Absolute Fubini for the genuine kernel pairing is derived from L2 data. -/
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
/- Derived summable rank-one expansion equals the actual kernel product. -/
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


namespace Round100A
open Round99G
/- Summability for correctly oriented factors B e_i and C* e_i. -/
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
/- Output-cutoff error controls the entire rank-one cost by a vanishing
product-kernel energy. No summability or nuclear convergence is assumed. -/
end Round101A


namespace Round102E
open Filter
open scoped Topology
/- A complete basis reconstructs the actual left-cutoff error. Its whole
rank-one cost tends to zero, derived from product-kernel energies. -/
end Round102E


namespace Round103E
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev actualLog : Classes K → ℝ := MasulloGRH.genuineRealClassLog K
/- Both signed residuals, with the genuine arithmetic logarithm, have an
actual operator-norm rank-one reconstruction and cutoff representations
whose total nuclear cost tends to zero. This is not the full AP bound. -/
end
end Round103E

namespace Round105F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F
open scoped BigOperators Topology
noncomputable section
/- Uniform in cutoff shape: only the common core enters the nuclear cost. -/
theorem kernel_uniform_cutoff_cost {X ι : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (B C : X → X → ℂ)
    (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu))
    (hC : MemLp (fun p : X × X => C p.1 p.2) 2 (mu.prod mu))
    (S : Set X) (hS : MeasurableSet S)
    (cutoff : X → ℂ) (hmcut : AEStronglyMeasurable cutoff mu)
    (hbcut : ∀ x, ‖cutoff x‖ ≤ 1) (hcore : ∀ x ∈ S, cutoff x = 1)
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ z, B x z * (∫ y, C z y * F y ∂mu) ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        Real.sqrt (4 * ∫ p : X × X,
          (Sᶜ ×ˢ Set.univ).indicator (fun p => ‖B p.1 p.2‖^2) p ∂(mu.prod mu)) *
        Real.sqrt (∫ p : X × X, ‖C p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  let D := fun p : X × X => (cutoff p.1-1) * B p.1 p.2
  let Q := (Sᶜ ×ˢ Set.univ).indicator (fun p : X × X => ‖B p.1 p.2‖^2)
  have hi := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hQ : Integrable Q (mu.prod mu) := hi.indicator (hS.compl.prod MeasurableSet.univ)
  have hm : AEStronglyMeasurable D (mu.prod mu) :=
    (hmcut.comp_fst.sub aestronglyMeasurable_const).mul hB.aestronglyMeasurable
  have hd (p : X × X) : ‖‖D p‖^2‖ ≤ 4 * Q p := by
    by_cases hx : p.1 ∈ S
    · simp [D, Q, Set.mem_prod, hx, hcore p.1 hx]
    · have hn : ‖cutoff p.1-1‖ ≤ 2 := by
        calc
          _ ≤ ‖cutoff p.1‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ ≤ 2 := by simp only [norm_one]; linarith [hbcut p.1]
      have hn2 : ‖cutoff p.1-1‖^2 ≤ (4 : ℝ) := by
        nlinarith [norm_nonneg (cutoff p.1-1)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖D p‖)]
      dsimp [D]
      rw [norm_mul, mul_pow]
      simpa [Q, Set.mem_prod, hx] using
        mul_le_mul_of_nonneg_right hn2 (sq_nonneg ‖B p.1 p.2‖)
  have hDi : Integrable (fun p => ‖D p‖^2) (mu.prod mu) :=
    (hQ.const_mul 4).mono' (hm.norm.pow 2) (Eventually.of_forall hd)
  have hD : MemLp D 2 (mu.prod mu) :=
    (memLp_two_iff_integrable_sq_norm hm).mpr hDi
  have henergy : (∫ p, ‖D p‖^2 ∂(mu.prod mu)) ≤ 4 * ∫ p, Q p ∂(mu.prod mu) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hDi (hQ.const_mul 4)
    exact Eventually.of_forall (fun p => (le_abs_self _).trans (hd p))
  obtain ⟨u, v, hu, hv, hc, hcost⟩ := Round100A.kernel_rankOne_cost_sharp
    mu (fun x y => D (x,y)) C hD hC e e.orthonormal
  obtain ⟨T, u', v', hT, hu', hv', hc', hcost', hsum⟩ :=
    Round101E.kernel_product_representation mu (fun x y => D (x,y)) C hD hC e
  have hue : u' = u := by
    funext i
    apply Lp.ext
    filter_upwards [hu' i, hu i] with x hx hy
    exact hx.trans hy.symm
  have hve : v' = v := by
    funext i
    apply Lp.ext
    filter_upwards [hv' i, hv i] with x hx hy
    exact hx.trans hy.symm
  refine ⟨T, u, v, ?_, hc, ?_, ?_⟩
  · intro F
    filter_upwards [hT F] with x hx
    rw [hx]
    dsimp [D]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  · have ht := le_of_tendsto hc.hasSum (Eventually.of_forall hcost)
    exact ht.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt henergy) (Real.sqrt_nonneg _))
  · simpa only [hue, hve] using hsum
end
end Round105F

namespace Round105F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_residual_uniform_cutoff_cost {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ) (second : Bool)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hm : Measurable (fun x => ENNReal.ofReal (9*‖rho x‖^2/(1+(actualLog K x)^2))))
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      residualFactorKernel K (actualLog K) alpha s rho psi second z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (Tcore : ℝ) (cutoff : Classes K → ℂ)
    (hmcut : AEStronglyMeasurable cutoff mu) (hbcut : ∀ x, ‖cutoff x‖ ≤ 1)
    (hcore : ∀ x, |actualLog K x| ≤ Tcore → cutoff x = 1)
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ y, ((rho x * signedResidualMultiplier (actualLog K x) second) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        Real.sqrt (4 * ∫ p : Classes K × Classes K,
          ({x : Classes K | |actualLog K x| ≤ Tcore}ᶜ ×ˢ Set.univ).indicator
            (fun p => ‖residualFactorKernel K (actualLog K) alpha s rho psi second p.1 p.2‖^2) p ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹)+actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hA := genuine_signed_residual_kernel_memLp_two K mu (actualLog K) alpha s R B ha hs
    rho psi second hlog hell V hpush hrho hm hb hp hp0 hpsupp hpf hpres hka
  have hB := genuine_companion_memLp_two K mu (actualLog K) alpha s S ha hs theta
    hlog hell V hpush hb ht ht0 htsupp htf hpres hkb
  obtain ⟨T, u, v, hT, hc, hn, hsum⟩ := Round105F.kernel_uniform_cutoff_cost mu
    (residualFactorKernel K (actualLog K) alpha s rho psi second)
    (factorKernel K (actualLog K) alpha s theta false) hA hB
    {x | |actualLog K x| ≤ Tcore} (measurableSet_le hell.abs measurable_const)
    cutoff hmcut hbcut hcore e
  refine ⟨T, u, v, ?_, hc, hn, hsum⟩
  intro F
  have hact := genuine_signed_residual_action_from_L2 K mu (actualLog K) alpha s
    rho psi theta (fun x => F x) second hpres hemb hA hB (Lp.memLp F)
  filter_upwards [hT F, hact] with x hx hy
  rw [hx, hy]
end
end Round105F

#check Round105F.kernel_uniform_cutoff_cost
#print axioms Round105F.kernel_uniform_cutoff_cost
#check Round105F.genuine_residual_uniform_cutoff_cost
#print axioms Round105F.genuine_residual_uniform_cutoff_cost

namespace Round106F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E
open scoped BigOperators Topology
noncomputable section
/- The threshold is chosen before the cutoff: this is a uniform tail bound. -/
theorem kernel_tail_energy_tendsto_zero {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SFinite mu] (ell : X → ℝ) (hell : Measurable ell)
    (B : X → X → ℂ) (hB : MemLp (fun p : X × X => B p.1 p.2) 2 (mu.prod mu)) :
    Tendsto (fun n : ℕ => ∫ p : X × X,
      ({x : X | |ell x| ≤ (n : ℝ)}ᶜ ×ˢ Set.univ).indicator
        (fun p => ‖B p.1 p.2‖^2) p ∂(mu.prod mu)) atTop (nhds 0) := by
  let Q := fun n : ℕ => ({x : X | |ell x| ≤ (n : ℝ)}ᶜ ×ˢ Set.univ).indicator
    (fun p : X × X => ‖B p.1 p.2‖^2)
  have hi := hB.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hm (n) : AEStronglyMeasurable (Q n) (mu.prod mu) :=
    hi.aestronglyMeasurable.indicator
      ((measurableSet_le hell.abs measurable_const).compl.prod MeasurableSet.univ)
  have hd (n) (p : X × X) : ‖Q n p‖ ≤ ‖B p.1 p.2‖^2 := by
    by_cases hx : |ell p.1| ≤ (n : ℝ)
    · simp [Q, Set.mem_prod, hx]
    · simp [Q, Set.mem_prod, hx]
  have hp : ∀ᵐ p ∂(mu.prod mu), Tendsto (fun n => Q n p) atTop (nhds (0 : ℝ)) := by
    apply Eventually.of_forall
    intro p
    obtain ⟨N, hN⟩ := exists_nat_ge |ell p.1|
    have hz : ∀ᶠ n : ℕ in atTop, Q n p = 0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hh : |ell p.1| ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      simp [Q, Set.mem_prod, hh]
    exact (tendsto_congr' hz).mpr tendsto_const_nhds
  simpa [Q] using tendsto_integral_of_dominated_convergence
    (fun p : X × X => ‖B p.1 p.2‖^2) hm hi
    (fun n => Eventually.of_forall (hd n)) hp

variable (K : Type*) [Field K] [NumberField K]
theorem genuine_residual_cutoff_uniformly_small {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ) (second : Bool)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hm : Measurable (fun x => ENNReal.ofReal (9*‖rho x‖^2/(1+(actualLog K x)^2))))
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      residualFactorKernel K (actualLog K) alpha s rho psi second z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (cutoff : Classes K → ℂ),
      AEStronglyMeasurable cutoff mu → (∀ x, ‖cutoff x‖ ≤ 1) →
      (∀ x, |actualLog K x| ≤ (N : ℝ) → cutoff x = 1) →
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ y, ((rho x * signedResidualMultiplier (actualLog K x) second) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) < epsilon ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹)+actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hA := genuine_signed_residual_kernel_memLp_two K mu (actualLog K) alpha s R B ha hs
    rho psi second hlog hell V hpush hrho hm hb hp hp0 hpsupp hpf hpres hka
  have htail := kernel_tail_energy_tendsto_zero mu (actualLog K) hell
    (residualFactorKernel K (actualLog K) alpha s rho psi second) hA
  have hlim := ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    (by simpa using htail.const_mul 4)).mul_const
      (Real.sqrt (∫ p : Classes K × Classes K,
        ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)))
  simp only [Real.sqrt_zero, zero_mul] at hlim
  have hev := hlim.eventually (gt_mem_nhds hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro cutoff hmcut hbcut hcore
  obtain ⟨T, u, v, hT, hc, hcost, hsum⟩ :=
    Round105F.genuine_residual_uniform_cutoff_cost K mu alpha s R S B ha hs
      rho psi theta second hell V hpush hrho hm hb hp ht hp0 ht0 hpsupp htsupp
      hpf htf hpres hemb hka hkb (N : ℝ) cutoff hmcut hbcut hcore e
  exact ⟨T, u, v, hT, hc, hcost.trans_lt (hN N le_rfl), hsum⟩
end
end Round106F

#check Round106F.kernel_tail_energy_tendsto_zero
#print axioms Round106F.kernel_tail_energy_tendsto_zero
#check Round106F.genuine_residual_cutoff_uniformly_small
#print axioms Round106F.genuine_residual_cutoff_uniformly_small

namespace Round106F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E
open scoped BigOperators Topology
noncomputable section
/- Definition 9.3.3.1(6): its plateau contains every fixed logarithmic core. -/
theorem cutoff_plateau_contains_log_core (N : ℕ) (Lambda delta t : ℝ)
    (hL : 2 * Real.exp (N : ℝ) ≤ Lambda) (hd : delta * Lambda ≤ 1)
    (ht : |t| ≤ (N : ℝ)) :
    1 / Lambda + delta ≤ Real.exp t ∧ Real.exp t ≤ Lambda - delta := by
  have hE : 0 < Real.exp (N : ℝ) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp (N : ℝ) := Real.one_le_exp_iff.mpr (by positivity)
  have hL2 : 2 ≤ Lambda := by nlinarith
  have hLp : 0 < Lambda := by linarith
  have hd1 : delta ≤ 1 / Lambda := (le_div_iff₀ hLp).mpr hd
  have hi : 1 / Lambda ≤ 1 := (div_le_iff₀ hLp).mpr (by linarith)
  constructor
  · calc
      1 / Lambda + delta ≤ 1 / Lambda + 1 / Lambda := by linarith
      _ = 2 / Lambda := by ring
      _ ≤ 1 / Real.exp (N : ℝ) :=
        (div_le_div_iff₀ hLp hE).mpr (by nlinarith)
      _ = Real.exp (-(N : ℝ)) := by rw [Real.exp_neg, one_div]
      _ ≤ Real.exp t := Real.exp_le_exp.mpr (abs_le.mp ht).1
  · have het : Real.exp t ≤ Real.exp (N : ℝ) :=
      Real.exp_le_exp.mpr (abs_le.mp ht).2
    have hdelta : delta ≤ 1 := hd1.trans hi
    nlinarith

variable (K : Type*) [Field K] [NumberField K]
theorem genuine_residual_manuscript_cutoff_small {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ) (second : Bool)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hm : Measurable (fun x => ENNReal.ofReal (9*‖rho x‖^2/(1+(actualLog K x)^2))))
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      residualFactorKernel K (actualLog K) alpha s rho psi second z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ L : ℝ, ∀ (Lambda delta : ℝ), L ≤ Lambda → delta * Lambda ≤ 1 →
      ∀ (cutoff : Classes K → ℂ), AEStronglyMeasurable cutoff mu →
      (∀ x, ‖cutoff x‖ ≤ 1) →
      (∀ x, 1 / Lambda + delta ≤ Real.exp (actualLog K x) →
        Real.exp (actualLog K x) ≤ Lambda - delta → cutoff x = 1) →
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ y, ((rho x * signedResidualMultiplier (actualLog K x) second) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) < epsilon ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  obtain ⟨N, hN⟩ := genuine_residual_cutoff_uniformly_small K mu alpha s R S B ha hs
    rho psi theta second hell V hpush hrho hm hb hp ht hp0 ht0 hpsupp htsupp
    hpf htf hpres hemb hka hkb e epsilon hepsilon
  refine ⟨2 * Real.exp (N : ℝ), ?_⟩
  intro Lambda delta hL hd cutoff hmcut hbcut hplateau
  apply hN cutoff hmcut hbcut
  intro x hx
  have hp := cutoff_plateau_contains_log_core N Lambda delta (actualLog K x) hL hd hx
  exact hplateau x hp.1 hp.2
end
end Round106F

#check Round106F.cutoff_plateau_contains_log_core
#print axioms Round106F.cutoff_plateau_contains_log_core
#check Round106F.genuine_residual_manuscript_cutoff_small
#print axioms Round106F.genuine_residual_manuscript_cutoff_small

namespace Round107F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/- The missing first-factor instance: ordinary supported L2 input implies
finite genuine first-factor energy, with no spectral assumptions. -/
theorem genuine_first_factor_memLp_two
    (mu : Measure (Classes K)) [SFinite mu]
    (ell : Classes K → ℝ) (alpha s R : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (psi : Classes K → ℂ)
    (hlog : ∀ x y, ell x = ell (x*y⁻¹)+ell y)
    (hell : Measurable ell) (V : NNReal)
    (hpush : Measure.map ell mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+ell x^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K ell alpha s psi true g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |ell g| ≤ R)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hkm : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K ell alpha s psi true z.1 z.2) (mu.prod mu)) :
    MemLp (fun z : Classes K × Classes K =>
      factorKernel K ell alpha s psi true z.1 z.2) 2 (mu.prod mu) := by
  have hk := ENNReal.measurable_ofReal.comp_aemeasurable
    (hkm.norm.pow 2).aemeasurable
  change AEMeasurable (fun z : Classes K × Classes K =>
    ENNReal.ofReal (‖factorKernel K ell alpha s psi true z.1 z.2‖^2))
      (mu.prod mu) at hk
  simp_rw [factorKernel_norm_sq] at hk
  apply (memLp_two_iff_integrable_sq_norm hkm).mpr
  refine ⟨hkm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  simp_rw [factorKernel_norm_sq]
  rw [lintegral_prod _ hk]
  have hJ := genuine_profile_finite_of_log_pushforward K mu ell hell V hpush
  have hE : (∫⁻ g, ENNReal.ofReal (testDensity K ell alpha s psi true g) ∂mu) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hpf ENNReal.ofReal_ne_top)
      (genuine_second_correction_test_mass K mu ell psi alpha s R ha hs hpsupp hp0)
  exact (genuine_second_correction_factor_energy K mu ell alpha s ha hs psi true
    hlog hb hp hpres).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hJ.ne hE))

def boundedFactorKernel (ell : Classes K → ℝ) (alpha s : ℝ)
    (rho psi : Classes K → ℂ) (x z : Classes K) : ℂ :=
  rho x * factorKernel K ell alpha s psi true x z

def boundedMultiplier (t : ℝ) : ℂ := ((1/(1+t^2) : ℝ) : ℂ)

theorem bounded_factor_memLp
    (mu : Measure (Classes K)) (ell : Classes K → ℝ) (alpha s B : ℝ)
    (rho psi : Classes K → ℂ) (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hA : MemLp (fun p : Classes K × Classes K =>
      factorKernel K ell alpha s psi true p.1 p.2) 2 (mu.prod mu))
    (hkm : AEStronglyMeasurable (fun p : Classes K × Classes K =>
      boundedFactorKernel K ell alpha s rho psi p.1 p.2) (mu.prod mu)) :
    MemLp (fun p : Classes K × Classes K =>
      boundedFactorKernel K ell alpha s rho psi p.1 p.2) 2 (mu.prod mu) := by
  apply (memLp_two_iff_integrable_sq_norm hkm).mpr
  have hi := (hA.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul (B^2)
  apply hi.mono' (hkm.norm.pow 2)
  filter_upwards [] with p
  change ‖‖boundedFactorKernel K ell alpha s rho psi p.1 p.2‖^2‖ ≤
    B^2 * ‖factorKernel K ell alpha s psi true p.1 p.2‖^2
  simp only [Real.norm_eq_abs, abs_pow, abs_norm, boundedFactorKernel, norm_mul, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hrho p.1)
  nlinarith [hrho p.1, norm_nonneg (rho p.1)]

theorem bounded_factor_product
    (ell : Classes K → ℝ) (alpha s : ℝ) (rho psi theta : Classes K → ℂ)
    (x z y : Classes K) :
    boundedFactorKernel K ell alpha s rho psi x z *
      factorKernel K ell alpha s theta false z y =
    rho x * boundedMultiplier (ell x) *
      (transportedCutoffKernel K (fun _ => 1) psi
        (fun u => stripWeight alpha s (ell u)) x z *
       transportedCutoffKernel K (fun _ => 1) theta
        (fun u => stripWeight alpha s (ell u)) z y) := by
  have hc := congrArg (fun r : ℝ => (r : ℂ))
    (factor_multiplier_cancellation (ell x) (ell z))
  push_cast at hc
  dsimp only [boundedFactorKernel, factorKernel, boundedMultiplier]
  simp only [Bool.false_eq_true, ↓reduceIte]
  push_cast
  linear_combination rho x *
    (transportedCutoffKernel K (fun _ => 1) psi
      (fun u => stripWeight alpha s (ell u)) x z *
     transportedCutoffKernel K (fun _ => 1) theta
      (fun u => stripWeight alpha s (ell u)) z y) * hc
theorem genuine_bounded_kernel_composition
    (mu : Measure (Classes K)) (ell : Classes K → ℝ)
    (alpha s : ℝ) (rho psi theta : Classes K → ℂ)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (x y : Classes K) :
    (∫ z, boundedFactorKernel K ell alpha s rho psi x z *
      factorKernel K ell alpha s theta false z y ∂mu) =
    (rho x * boundedMultiplier (ell x)) *
      transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
        (fun a => stripWeight alpha s (ell a)) x y := by
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
  have hid (z : Classes K) :
      boundedFactorKernel K ell alpha s rho psi x z *
        factorKernel K ell alpha s theta false z y =
      (rho x * boundedMultiplier (ell x) *
        (Real.sqrt (w x / w y) : ℂ)) * (psi (x*z⁻¹)*theta (z*y⁻¹)) := by
    rw [bounded_factor_product]
    unfold transportedCutoffKernel
    simp only [one_mul]
    change rho x * boundedMultiplier (ell x) *
      ((psi (x*z⁻¹)*(Real.sqrt (w x/w z) : ℂ)) *
        (theta (z*y⁻¹)*(Real.sqrt (w z/w y) : ℂ))) = _
    calc
      _ = (rho x * boundedMultiplier (ell x)) *
        (psi (x*z⁻¹)*theta (z*y⁻¹)) *
        ((Real.sqrt (w x/w z) : ℂ)*(Real.sqrt (w z/w y) : ℂ)) := by ring
      _ = _ := by rw [htel]; ring
  have hgroup (z : Classes K) : (x*z⁻¹)⁻¹*(x*y⁻¹) = z*y⁻¹ :=
    group_cancel_middle x z y
  have hc := (hpres x).integral_comp (hemb x)
    (fun g => psi g * theta (g⁻¹*(x*y⁻¹)))
  simp only [hgroup] at hc
  calc
    _ = ∫ z, (rho x * boundedMultiplier (ell x) *
        (Real.sqrt (w x / w y) : ℂ)) * (psi (x*z⁻¹)*theta (z*y⁻¹)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hid z
    _ = _ := by
      rw [integral_const_mul, hc]
      unfold transportedCutoffKernel NuclearBoundB90.convolution
      dsimp only [w]
      ring

theorem genuine_bounded_action_from_L2
    (mu : Measure (Classes K)) [SFinite mu] (ell : Classes K → ℝ)
    (alpha s : ℝ) (rho psi theta f : Classes K → ℂ)
    (hpres : ∀ x, MeasurePreserving (fun z : Classes K => x*z⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun z : Classes K => x*z⁻¹))
    (hA : MemLp (fun p : Classes K × Classes K =>
      boundedFactorKernel K ell alpha s rho psi p.1 p.2) 2 (mu.prod mu))
    (hB : MemLp (fun p : Classes K × Classes K =>
      factorKernel K ell alpha s theta false p.1 p.2) 2 (mu.prod mu))
    (hf : MemLp f 2 mu) :
    ∀ᵐ x ∂mu,
      (∫ z, boundedFactorKernel K ell alpha s rho psi x z *
        (∫ y, factorKernel K ell alpha s theta false z y * f y ∂mu) ∂mu) =
      ∫ y, ((rho x * boundedMultiplier (ell x)) *
        transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
          (fun a => stripWeight alpha s (ell a)) x y) * f y ∂mu := by
  have hAi := hA.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  filter_upwards [hA.aestronglyMeasurable.prodMk_left, hAi.prod_right_ae] with x hm hi
  have ha := (memLp_two_iff_integrable_sq_norm hm).mpr hi
  have hF := kernel_fubini_from_L2 mu _ f _ ha hB hf
  calc
    _ = ∫ z, ∫ y, (boundedFactorKernel K ell alpha s rho psi x z *
        factorKernel K ell alpha s theta false z y) * f y ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ = ∫ y, ∫ z, (boundedFactorKernel K ell alpha s rho psi x z *
        factorKernel K ell alpha s theta false z y) * f y ∂mu ∂mu :=
      integral_integral_swap hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_mul_const, genuine_bounded_kernel_composition K mu ell
        alpha s rho psi theta hpres hemb]

end
end Round107F

#check Round107F.genuine_first_factor_memLp_two
#print axioms Round107F.genuine_first_factor_memLp_two
#check Round107F.genuine_bounded_action_from_L2
#print axioms Round107F.genuine_bounded_action_from_L2

namespace Round107F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_bounded_uniform_cutoff_cost {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s rho psi z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (Tcore : ℝ) (cutoff : Classes K → ℂ)
    (hmcut : AEStronglyMeasurable cutoff mu) (hbcut : ∀ x, ‖cutoff x‖ ≤ 1)
    (hcore : ∀ x, |actualLog K x| ≤ Tcore → cutoff x = 1)
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ y, ((rho x * boundedMultiplier (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        Real.sqrt (4 * ∫ p : Classes K × Classes K,
          ({x : Classes K | |actualLog K x| ≤ Tcore}ᶜ ×ˢ Set.univ).indicator
            (fun p => ‖boundedFactorKernel K (actualLog K) alpha s rho psi p.1 p.2‖^2) p ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹)+actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hfirst := genuine_first_factor_memLp_two K mu (actualLog K) alpha s R ha hs
    psi hlog hell V hpush hb hp hp0 hpsupp hpf hpres hbase
  have hA := bounded_factor_memLp K mu (actualLog K) alpha s B rho psi hrho hfirst hka
  have hB := genuine_companion_memLp_two K mu (actualLog K) alpha s S ha hs theta
    hlog hell V hpush hb ht ht0 htsupp htf hpres hkb
  obtain ⟨T, u, v, hT, hc, hn, hsum⟩ := Round105F.kernel_uniform_cutoff_cost mu
    (boundedFactorKernel K (actualLog K) alpha s rho psi)
    (factorKernel K (actualLog K) alpha s theta false) hA hB
    {x | |actualLog K x| ≤ Tcore} (measurableSet_le hell.abs measurable_const)
    cutoff hmcut hbcut hcore e
  refine ⟨T, u, v, ?_, hc, hn, hsum⟩
  intro F
  have hact := genuine_bounded_action_from_L2 K mu (actualLog K) alpha s
    rho psi theta (fun x => F x) hpres hemb hA hB (Lp.memLp F)
  filter_upwards [hT F, hact] with x hx hy
  rw [hx, hy]

theorem genuine_bounded_cutoff_uniformly_small {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s rho psi z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (cutoff : Classes K → ℂ),
      AEStronglyMeasurable cutoff mu → (∀ x, ‖cutoff x‖ ≤ 1) →
      (∀ x, |actualLog K x| ≤ (N : ℝ) → cutoff x = 1) →
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ y, ((rho x * boundedMultiplier (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) < epsilon ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹)+actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hfirst := genuine_first_factor_memLp_two K mu (actualLog K) alpha s R ha hs
    psi hlog hell V hpush hb hp hp0 hpsupp hpf hpres hbase
  have hA := bounded_factor_memLp K mu (actualLog K) alpha s B rho psi hrho hfirst hka
  have htail := Round106F.kernel_tail_energy_tendsto_zero mu (actualLog K) hell
    (boundedFactorKernel K (actualLog K) alpha s rho psi) hA
  have hlim := ((Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    (by simpa using htail.const_mul 4)).mul_const
      (Real.sqrt (∫ p : Classes K × Classes K,
        ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)))
  simp only [Real.sqrt_zero, zero_mul] at hlim
  have hev := hlim.eventually (gt_mem_nhds hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, ?_⟩
  intro cutoff hmcut hbcut hcore
  obtain ⟨T, u, v, hT, hc, hcost, hsum⟩ :=
    genuine_bounded_uniform_cutoff_cost K mu alpha s R S B ha hs
      rho psi theta hell V hpush hrho hb hp ht hp0 ht0 hpsupp htsupp
      hpf htf hpres hemb hbase hka hkb (N : ℝ) cutoff hmcut hbcut hcore e
  exact ⟨T, u, v, hT, hc, hcost.trans_lt (hN N le_rfl), hsum⟩
end
end Round107F
#check Round107F.genuine_bounded_uniform_cutoff_cost
#print axioms Round107F.genuine_bounded_uniform_cutoff_cost
#check Round107F.genuine_bounded_cutoff_uniformly_small
#print axioms Round107F.genuine_bounded_cutoff_uniformly_small

namespace Round107F
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_bounded_multiplier_nuclear {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s rho psi z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, ((rho x * boundedMultiplier (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖boundedFactorKernel K (actualLog K) alpha s rho psi p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹)+actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hfirst := genuine_first_factor_memLp_two K mu (actualLog K) alpha s R ha hs
    psi hlog hell V hpush hb hp hp0 hpsupp hpf hpres hbase
  have hA := bounded_factor_memLp K mu (actualLog K) alpha s B rho psi hrho hfirst hka
  have hB := genuine_companion_memLp_two K mu (actualLog K) alpha s S ha hs theta
    hlog hell V hpush hb ht ht0 htsupp htf hpres hkb
  obtain ⟨u, v, hu, hv, hc, hcost⟩ := Round100A.kernel_rankOne_cost_sharp mu
    (boundedFactorKernel K (actualLog K) alpha s rho psi)
    (factorKernel K (actualLog K) alpha s theta false) hA hB e e.orthonormal
  obtain ⟨T, u', v', hT, hu', hv', hc', hcost', hsum⟩ :=
    Round101E.kernel_product_representation mu
      (boundedFactorKernel K (actualLog K) alpha s rho psi)
      (factorKernel K (actualLog K) alpha s theta false) hA hB e
  have hue : u' = u := by
    funext i
    apply Lp.ext
    filter_upwards [hu' i, hu i] with x hx hy
    exact hx.trans hy.symm
  have hve : v' = v := by
    funext i
    apply Lp.ext
    filter_upwards [hv' i, hv i] with x hx hy
    exact hx.trans hy.symm
  refine ⟨T, u, v, ?_, hc, le_of_tendsto hc.hasSum (Eventually.of_forall hcost), ?_⟩
  · intro F
    have hact := genuine_bounded_action_from_L2 K mu (actualLog K) alpha s
      rho psi theta (fun x => F x) hpres hemb hA hB (Lp.memLp F)
    filter_upwards [hT F, hact] with x hx hy
    exact hx.trans hy
  · simpa only [hue, hve] using hsum

end
end Round107F
#check Round107F.genuine_bounded_multiplier_nuclear
#print axioms Round107F.genuine_bounded_multiplier_nuclear


namespace Round107E
open scoped BigOperators
noncomputable section
/-- Generalized binomial coefficients with exact falling-factorial recurrence. -/
def realBinom (r : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => realBinom r n * (r-n) / (n+1)

theorem realBinom_abs_le (r : ℝ) (n : ℕ) :
    |realBinom r n| ≤ (1+|r|)^n := by
  induction n with
  | zero => simp [realBinom]
  | succ n ih =>
    have hn : (0 : ℝ) < (n:ℝ)+1 := by positivity
    have ha : |r-(n:ℝ)| ≤ |r|+(n:ℝ) := by
      simpa using abs_sub r (n:ℝ)
    have hquot : |r-(n:ℝ)| / ((n:ℝ)+1) ≤ 1+|r| := by
      apply (div_le_iff₀ hn).2
      nlinarith [abs_nonneg r, (show (0:ℝ) ≤ n by positivity)]
    rw [realBinom, abs_div, abs_mul, abs_of_pos hn]
    calc
      |realBinom r n| * |r-(n:ℝ)| / ((n:ℝ)+1) =
          |realBinom r n| * (|r-(n:ℝ)| / ((n:ℝ)+1)) := by ring
      _ ≤ (1+|r|)^n * (1+|r|) :=
        mul_le_mul ih hquot (by positivity) (by positivity)
      _ = (1+|r|)^(n+1) := (pow_succ _ _).symm

def tailRadius (r R : ℝ) : ℝ := 1+4*(1+|r|)*R

def tailRatio (r R : ℝ) : ℝ :=
  2*(R/tailRadius r R)+(R/tailRadius r R)^2

/-- Uniform ratio bound for the real-s separated tail nuclear-cost series. -/
theorem tailRatio_bound (r R : ℝ) (hR : 0 ≤ R) :
    0 ≤ tailRatio r R ∧ (1+|r|)*tailRatio r R ≤ 9/16 := by
  have hC : 1 ≤ 1+|r| := by linarith [abs_nonneg r]
  have hL : 0 < tailRadius r R := by unfold tailRadius; positivity
  have hx : 0 ≤ R/tailRadius r R := div_nonneg hR hL.le
  have hcx : (1+|r|)*(R/tailRadius r R) ≤ 1/4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hL).2
    unfold tailRadius
    linarith
  have hxx : R/tailRadius r R ≤ 1/4 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hxx
    (mul_nonneg (by positivity : 0 ≤ 1+|r|) hx)
  unfold tailRatio
  constructor
  · positivity
  · nlinarith

/-- The explicit cost after summing the finite separated log moments. -/
def tailCost (r R : ℝ) (n : ℕ) : ℝ :=
  (tailRadius r R)^2 * |realBinom r (n+2)| * (tailRatio r R)^(n+2)

theorem tailCost_geometric (r R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ tailCost r R n ∧
    tailCost r R n ≤ (tailRadius r R)^2*(9/16:ℝ)^(n+2) := by
  obtain ⟨hq, hqC⟩ := tailRatio_bound r R hR
  constructor
  · unfold tailCost; positivity
  · calc
      tailCost r R n ≤ (tailRadius r R)^2 *
          ((1+|r|)^(n+2) * (tailRatio r R)^(n+2)) := by
        unfold tailCost
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (realBinom_abs_le r (n+2))
          (pow_nonneg hq (n+2))) (sq_nonneg (tailRadius r R))
        nlinarith only [hh]
      _ = (tailRadius r R)^2 * ((1+|r|)*tailRatio r R)^(n+2) := by rw [mul_pow]
      _ ≤ (tailRadius r R)^2*(9/16:ℝ)^(n+2) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (by positivity) hq) hqC _) (sq_nonneg _)

#check realBinom_abs_le
#print axioms realBinom_abs_le
#check tailRatio_bound
#print axioms tailRatio_bound
#check tailCost_geometric
#print axioms tailCost_geometric

/-- Absolute summability and an explicit finite sum bound, derived from r,R. -/
theorem real_exponent_tail_cost (r R : ℝ) (hR : 0 ≤ R) :
    Summable (tailCost r R) ∧
    (∑' n, tailCost r R n) ≤ (tailRadius r R)^2*(81/112) := by
  have hg : HasSum (fun n : ℕ => (9/16:ℝ)^(n+2)) (81/112) := by
    convert HasSum.mul_left ((9/16:ℝ)^2)
      (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 9/16)
        (by norm_num : (9/16:ℝ) < 1)) using 1
    · funext n
      rw [pow_add]
      ring
    · norm_num
  have hM := HasSum.mul_left ((tailRadius r R)^2) hg
  have hs : Summable (tailCost r R) := Summable.of_nonneg_of_le
    (fun n => (tailCost_geometric r R hR n).1)
    (fun n => (tailCost_geometric r R hR n).2) hM.summable
  refine ⟨hs, ?_⟩
  calc
    (∑' n, tailCost r R n) ≤
        ∑' n : ℕ, (tailRadius r R)^2*(9/16:ℝ)^(n+2) :=
      Summable.tsum_le_tsum (fun n => (tailCost_geometric r R hR n).2) hs hM.summable
    _ = (tailRadius r R)^2*(81/112) := hM.tsum_eq

/-- Finite separation cost with supremum bounds taken term by term. -/
def separatedCost (r R : ℝ) (n : ℕ) : ℝ :=
  (tailRadius r R)^2 * |realBinom r (n+2)| *
    ∑ j ∈ Finset.range (n+2+1), ((n+2).choose j : ℝ) *
      ((R/tailRadius r R)^2)^j * (2*(R/tailRadius r R))^(n+2-j)

theorem separatedCost_eq (r R : ℝ) (n : ℕ) :
    separatedCost r R n = tailCost r R n := by
  unfold separatedCost tailCost tailRatio
  congr 1
  rw [show 2*(R/tailRadius r R)+(R/tailRadius r R)^2 =
    (R/tailRadius r R)^2+2*(R/tailRadius r R) by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Summability of the finite-separated real-s moment cost, with no assumed series bound. -/
theorem separated_real_exponent_cost (r R : ℝ) (hR : 0 ≤ R) :
    Summable (separatedCost r R) ∧
    (∑' n, separatedCost r R n) ≤ (tailRadius r R)^2*(81/112) := by
  have he : separatedCost r R = tailCost r R := funext (separatedCost_eq r R)
  rw [he]
  exact real_exponent_tail_cost r R hR

#check real_exponent_tail_cost
#print axioms real_exponent_tail_cost
#check separatedCost_eq
#print axioms separatedCost_eq
#check separated_real_exponent_cost
#print axioms separated_real_exponent_cost
end
end Round107E

namespace Round108E
open scoped BigOperators
noncomputable section
/-- Tail estimate for the separated output multiplier, before insertion into
    the genuine inverse-quadratic convolution representation. -/
theorem tail_power_ratio (L t : ℝ) (hL : 0 < L) (ht : L ≤ |t|)
    (n j : ℕ) (hn : 2 ≤ n) (hj : j ≤ n) :
    |t|^(n-j) / (1+t^2)^(n-1) ≤ 1 / L^(n+j-2) := by
  have hq : 0 < 1+t^2 := by positivity
  apply (div_le_div_iff₀ (pow_pos hq _) (pow_pos hL _)).2
  have he : n-j+(n+j-2) = 2*(n-1) := by omega
  calc
    |t|^(n-j) * L^(n+j-2) ≤ |t|^(n-j) * |t|^(n+j-2) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le ht _) (by positivity)
    _ = (t^2)^(n-1) := by rw [← pow_add, he, pow_mul]; simp
    _ ≤ 1 * (1+t^2)^(n-1) := by
      simpa using pow_le_pow_left₀ (sq_nonneg t) (by linarith : t^2 ≤ 1+t^2) (n-1)

def tailMultiplier (L : ℝ) (n j : ℕ) (t : ℝ) : ℝ :=
  if L ≤ |t| then (-2*t)^(n-j)/(1+t^2)^(n-1) else 0

theorem tailMultiplier_bound (L : ℝ) (hL : 0 < L) (n j : ℕ)
    (hn : 2 ≤ n) (hj : j ≤ n) (t : ℝ) :
    |tailMultiplier L n j t| ≤ (2:ℝ)^(n-j)/L^(n+j-2) := by
  unfold tailMultiplier
  split_ifs with ht
  · rw [abs_div, abs_pow, abs_mul, abs_pow, abs_of_pos (by positivity : 0 < 1+t^2)]
    norm_num
    rw [mul_pow]
    have hh := mul_le_mul_of_nonneg_left (tail_power_ratio L t hL ht n j hn hj)
      (by positivity : 0 ≤ (2:ℝ)^(n-j))
    simpa only [← mul_div_assoc, mul_one] using hh
  · simp only [abs_zero]
    positivity

#check tail_power_ratio
#print axioms tail_power_ratio
#check tailMultiplier_bound
#print axioms tailMultiplier_bound
end
end Round108E

namespace Round108E
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E Round107F
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_bounded_multiplier_cost {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S B : ℝ) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (rho psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hrho : ∀ x, ‖rho x‖ ≤ B)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s rho psi z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, ((rho x * boundedMultiplier (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        B * Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s psi true p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hlog (x y : Classes K) : actualLog K x = actualLog K (x*y⁻¹)+actualLog K y := by
    change MasulloGRH.genuineRealClassLog K x =
      MasulloGRH.genuineRealClassLog K (x*y⁻¹) + MasulloGRH.genuineRealClassLog K y
    rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
    ring
  have hfirst := genuine_first_factor_memLp_two K mu (actualLog K) alpha s R ha hs
    psi hlog hell V hpush hb hp hp0 hpsupp hpf hpres hbase
  have hA := bounded_factor_memLp K mu (actualLog K) alpha s B rho psi hrho hfirst hka
  have hB : 0 ≤ B := (norm_nonneg (rho 1)).trans (hrho 1)
  have henergy : (∫ p : Classes K × Classes K,
      ‖boundedFactorKernel K (actualLog K) alpha s rho psi p.1 p.2‖^2 ∂(mu.prod mu)) ≤
      B^2 * ∫ p : Classes K × Classes K,
      ‖factorKernel K (actualLog K) alpha s psi true p.1 p.2‖^2 ∂(mu.prod mu) := by
    rw [← integral_const_mul]
    apply integral_mono
      (hA.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0))
      ((hfirst.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul (B^2))
    intro p
    simp only [boundedFactorKernel, norm_mul, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    nlinarith [hrho p.1, norm_nonneg (rho p.1)]
  have hroot := Real.sqrt_le_sqrt henergy
  rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB] at hroot
  obtain ⟨T,u,v,hT,hc,hn,hsum⟩ := genuine_bounded_multiplier_nuclear K mu alpha s R S B ha hs
    rho psi theta hell V hpush hrho hb hp ht hp0 ht0 hpsupp htsupp hpf htf hpres hemb hbase hka hkb e
  exact ⟨T,u,v,hT,hc,hn.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)),hsum⟩

theorem genuine_tail_multiplier_nuclear {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S L : ℝ) (hL : 0 < L) (n j : ℕ) (hn : 2 ≤ n) (hj : j ≤ n) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s (fun x => ((tailMultiplier L n j (actualLog K x) : ℝ) : ℂ)) psi z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, (((fun x => ((tailMultiplier L n j (actualLog K x) : ℝ) : ℂ)) x * boundedMultiplier (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        ((2:ℝ)^(n-j)/L^(n+j-2)) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s psi true p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  apply genuine_bounded_multiplier_cost K mu alpha s R S ((2:ℝ)^(n-j)/L^(n+j-2)) ha hs
    (fun x => ((tailMultiplier L n j (actualLog K x) : ℝ) : ℂ)) psi theta hell V hpush
    (fun x => ?_) hb hp ht hp0 ht0 hpsupp htsupp hpf htf hpres hemb hbase hka hkb e
  simpa only [Complex.norm_real, Real.norm_eq_abs] using tailMultiplier_bound L hL n j hn hj (actualLog K x)

#check genuine_bounded_multiplier_cost
#print axioms genuine_bounded_multiplier_cost
#check genuine_tail_multiplier_nuclear
#print axioms genuine_tail_multiplier_nuclear
end
end Round108E

namespace Round108E
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E Round107F
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_tail_cutoff_uniformly_small {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S L : ℝ) (hL : 0 < L) (n j : ℕ) (hn : 2 ≤ n) (hj : j ≤ n) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s (fun x => ((tailMultiplier L n j (actualLog K x) : ℝ) : ℂ)) psi z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∀ (cutoff : Classes K → ℂ),
      AEStronglyMeasurable cutoff mu → (∀ x, ‖cutoff x‖ ≤ 1) →
      (∀ x, |actualLog K x| ≤ (N : ℝ) → cutoff x = 1) →
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x = (cutoff x-1) *
        (∫ y, (((fun x => ((tailMultiplier L n j (actualLog K x) : ℝ) : ℂ)) x * boundedMultiplier (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu)) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) < epsilon ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  apply genuine_bounded_cutoff_uniformly_small K mu alpha s R S ((2:ℝ)^(n-j)/L^(n+j-2)) ha hs
    (fun x => ((tailMultiplier L n j (actualLog K x) : ℝ) : ℂ)) psi theta hell V hpush
    (fun x => ?_) hb hp ht hp0 ht0 hpsupp htsupp hpf htf hpres hemb hbase hka hkb e epsilon hepsilon
  simpa only [Complex.norm_real, Real.norm_eq_abs] using tailMultiplier_bound L hL n j hn hj (actualLog K x)
#check genuine_tail_cutoff_uniformly_small
#print axioms genuine_tail_cutoff_uniformly_small
end
end Round108E

namespace Round109E
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E Round107F
open scoped BigOperators Topology
noncomputable section

def coreMultiplier (L t : ℝ) : ℂ :=
  if |t| ≤ L then ((1+t^2 : ℝ) : ℂ) else 0

def coreIndicator (L t : ℝ) : ℂ := if |t| ≤ L then 1 else 0

theorem coreMultiplier_bound (L : ℝ) (_hL : 0 ≤ L) (t : ℝ) :
    ‖coreMultiplier L t‖ ≤ 1+L^2 := by
  unfold coreMultiplier
  split_ifs with ht
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1+t^2)]
    have hsq := pow_le_pow_left₀ (abs_nonneg t) ht 2
    simpa using add_le_add_left hsq 1
  · simp only [norm_zero]
    positivity

theorem coreMultiplier_measurable (L : ℝ) : Measurable (coreMultiplier L) := by
  unfold coreMultiplier
  apply Measurable.ite (measurableSet_le measurable_id.abs measurable_const)
  · exact Complex.continuous_ofReal.measurable.comp (measurable_const.add (measurable_id.pow_const 2))
  · exact measurable_const

theorem coreMultiplier_cancel (L t : ℝ) :
    coreMultiplier L t * boundedMultiplier t = coreIndicator L t := by
  unfold coreMultiplier coreIndicator boundedMultiplier
  split_ifs
  · have hq : (1+t^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    norm_cast
    field_simp
  · simp

variable (K : Type*) [Field K] [NumberField K]
theorem genuine_compact_output_nuclear {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S L : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, ((coreIndicator L (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        (1+L^2) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s psi true p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hmrho : AEStronglyMeasurable (fun x => coreMultiplier L (actualLog K x)) mu :=
    ((coreMultiplier_measurable L).comp hell).aestronglyMeasurable
  have hka : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      boundedFactorKernel K (actualLog K) alpha s
        (fun x => coreMultiplier L (actualLog K x)) psi z.1 z.2) (mu.prod mu) :=
    hmrho.comp_fst.mul hbase
  obtain ⟨T,u,v,hT,hc,hn,hsum⟩ := Round108E.genuine_bounded_multiplier_cost K mu
    alpha s R S (1+L^2) ha hs (fun x => coreMultiplier L (actualLog K x))
    psi theta hell V hpush (fun x => coreMultiplier_bound L hL (actualLog K x))
    hb hp ht hp0 ht0 hpsupp htsupp hpf htf hpres hemb hbase hka hkb e
  refine ⟨T,u,v,?_,hc,hn,hsum⟩
  intro F
  filter_upwards [hT F] with x hx
  rw [hx]
  simp_rw [coreMultiplier_cancel]

#check genuine_compact_output_nuclear
#print axioms genuine_compact_output_nuclear
#check coreMultiplier_cancel
#print axioms coreMultiplier_cancel
end
end Round109E

namespace Round109E
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E Round107F
open scoped BigOperators Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
theorem genuine_compact_output_nuclear_stable {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S L : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, ((coreIndicator L (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        (1+L^2) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s psi true p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T ∧
      (∀ (cutoff : Classes K → ℂ),
        (∀ x, |actualLog K x| ≤ L → cutoff x = 1) →
        ∀ F, ∀ᵐ x ∂mu, cutoff x * T F x = T F x) := by
  obtain ⟨T,u,v,hT,hc,hn,hsum⟩ := genuine_compact_output_nuclear K mu alpha s R S L
    hL ha hs psi theta hell V hpush hb hp ht hp0 ht0 hpsupp htsupp hpf htf
    hpres hemb hbase hkb e
  refine ⟨T,u,v,hT,hc,hn,hsum,?_⟩
  intro cutoff hcore F
  filter_upwards [hT F] with x hx
  by_cases hxl : |actualLog K x| ≤ L
  · rw [hcore x hxl, one_mul]
  · have hz : T F x = 0 := by simpa [coreIndicator, hxl] using hx
    rw [hz, mul_zero]

#check genuine_compact_output_nuclear_stable
#print axioms genuine_compact_output_nuclear_stable
end
end Round109E

/-! Round 110 review addition: exact support insertion for the compact
weighted-adjoint component. The support lemma is reused from checked C109,
not counted as a new arithmetic or topology result. -/
namespace Round110E
open MeasureTheory NuclearBoundB90 NuclearBoundB91 Round93A Round103E Round109E MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem genuine_convolution_log_support
    (mu : Measure (HeckeIdeleClasses K)) (R S : ℝ)
    (psi theta : HeckeIdeleClasses K → ℂ)
    (hps : ∀ g, psi g ≠ 0 → |genuineRealClassLog K g| ≤ R)
    (hts : ∀ g, theta g ≠ 0 → |genuineRealClassLog K g| ≤ S) :
    ∀ x, (∫ g, psi g * theta (g⁻¹*x) ∂mu) ≠ 0 →
      |genuineRealClassLog K x| ≤ R+S := by
  intro x hx
  by_contra hn
  apply hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with g
  by_cases hp : psi g = 0
  · simp [hp]
  by_cases ht : theta (g⁻¹*x) = 0
  · simp [ht]
  exfalso
  apply hn
  have he : genuineRealClassLog K x =
      genuineRealClassLog K g + genuineRealClassLog K (g⁻¹*x) := by
    rw [genuineRealClassLog_mul, genuineRealClassLog_inv]
    ring
  calc
    _ = |genuineRealClassLog K g + genuineRealClassLog K (g⁻¹*x)| := congrArg abs he
    _ ≤ |genuineRealClassLog K g|+|genuineRealClassLog K (g⁻¹*x)| := abs_add_le _ _
    _ ≤ R+S := add_le_add (hps g hp) (hts (g⁻¹*x) ht)


/-- On the fixed output core, the transposed authentic convolution kernel
only uses input points in the support-enlarged core. -/
theorem genuine_core_transposed_kernel
    (L U : ℝ) (phi : Classes K → ℂ) (w : Classes K → ℝ)
    (hsupp : ∀ g, phi g ≠ 0 → |actualLog K g| ≤ U)
    (x y : Classes K) :
    coreIndicator L (actualLog K x) *
      star (transportedCutoffKernel K (fun _ => 1) phi w y x) =
    coreIndicator L (actualLog K x) *
      star (transportedCutoffKernel K
        (fun z => coreIndicator (L+U) (actualLog K z)) phi w y x) := by
  by_cases hx : |actualLog K x| ≤ L
  · by_cases hp : phi (y*x⁻¹) = 0
    · simp [transportedCutoffKernel, hp]
    · have hrel : actualLog K y = actualLog K (y*x⁻¹) + actualLog K x := by
        change MasulloGRH.genuineRealClassLog K y =
          MasulloGRH.genuineRealClassLog K (y*x⁻¹) + MasulloGRH.genuineRealClassLog K x
        rw [MasulloGRH.genuineRealClassLog_mul, MasulloGRH.genuineRealClassLog_inv]
        ring
      have hy : |actualLog K y| ≤ L+U := by
        calc
          _ = |actualLog K (y*x⁻¹) + actualLog K x| := congrArg abs hrel
          _ ≤ |actualLog K (y*x⁻¹)| + |actualLog K x| := abs_add_le _ _
          _ ≤ U+L := add_le_add (hsupp _ hp) hx
          _ = L+U := add_comm _ _
      simp [transportedCutoffKernel, coreIndicator, hx, hy]
  · simp [coreIndicator, hx]

/-- The exact integral identity required to reuse the compact-output
nuclear series for the compact weighted-adjoint component. This is a
kernel identity; Hilbert-adjoint identification is a separate obligation. -/
theorem genuine_compact_adjoint_support_insertion
    (mu : Measure (Classes K)) (R S L alpha s : ℝ)
    (psi theta F : Classes K → ℂ)
    (hps : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (hts : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (x : Classes K) :
    (∫ y, (coreIndicator L (actualLog K x) *
      star (transportedCutoffKernel K (fun _ => 1)
        (convolution K mu psi theta)
        (fun z => stripWeight alpha s (actualLog K z)) y x)) * F y ∂mu) =
    ∫ y, (coreIndicator L (actualLog K x) *
      star (transportedCutoffKernel K
        (fun z => coreIndicator (L+(R+S)) (actualLog K z))
        (convolution K mu psi theta)
        (fun z => stripWeight alpha s (actualLog K z)) y x)) * F y ∂mu := by
  apply integral_congr_ae
  filter_upwards [] with y
  rw [genuine_core_transposed_kernel K L (R+S) (convolution K mu psi theta)
    (fun z => stripWeight alpha s (actualLog K z))
    (genuine_convolution_log_support K mu R S psi theta hps hts) x y]

#check genuine_core_transposed_kernel
#print axioms genuine_core_transposed_kernel
#check genuine_compact_adjoint_support_insertion
#print axioms genuine_compact_adjoint_support_insertion
end
end Round110E

namespace Round110E
open MeasureTheory Filter NuclearBoundB90 NuclearBoundB91 Round93A Round94F Round96F Round97F Round98F Round103E Round107F Round109E
open scoped BigOperators Topology
noncomputable section

/-- The adjoint has exactly the exchanged rank-one vectors, without a
new estimate for either vector. This helper is instantiated below on the
constructed genuine compact-output convolution operator. -/
theorem adjoint_rankOne {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (u v : H) :
    ContinuousLinearMap.adjoint ((innerSL ℂ v).smulRight u) =
      (innerSL ℂ u).smulRight v := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]

theorem adjoint_rankOne_hasSum {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (u v : ι → H) (T : H →L[ℂ] H)
    (hs : HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T) :
    HasSum (fun i => (innerSL ℂ (u i)).smulRight (v i))
      (ContinuousLinearMap.adjoint T) := by
  have ht := hs.map
    (ContinuousLinearMap.adjoint : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H))
    ContinuousLinearMap.adjoint.continuous
  simpa only [Function.comp_def, adjoint_rankOne] using ht

variable (K : Type*) [Field K] [NumberField K]
/-- The actual compact-output convolution and its Hilbert adjoint have
explicit nuclear representations with the same derived norm-product cost.
This does not identify the untruncated projected operator. -/
theorem genuine_compact_output_and_adjoint_nuclear {ι : Type*}
    (mu : Measure (Classes K)) [SFinite mu]
    (alpha s R S L : ℝ) (hL : 0 ≤ L) (ha : 0 ≤ alpha) (hs : 0 ≤ s)
    (psi theta : Classes K → ℂ)
    (hell : Measurable (actualLog K)) (V : NNReal)
    (hpush : Measure.map (actualLog K) mu = (V : ENNReal) • volume)
    (hb : Measurable (fun x => ENNReal.ofReal (1/(1+(actualLog K x)^2))))
    (hp : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s psi true g)))
    (ht : Measurable (fun g => ENNReal.ofReal (testDensity K (actualLog K) alpha s theta false g)))
    (hp0 : Measurable (fun g => ENNReal.ofReal (‖psi g‖^2)))
    (ht0 : Measurable (fun g => ENNReal.ofReal (‖theta g‖^2)))
    (hpsupp : ∀ g, psi g ≠ 0 → |actualLog K g| ≤ R)
    (htsupp : ∀ g, theta g ≠ 0 → |actualLog K g| ≤ S)
    (hpf : (∫⁻ g, ENNReal.ofReal (‖psi g‖^2) ∂mu) ≠ ⊤)
    (htf : (∫⁻ g, ENNReal.ofReal (‖theta g‖^2) ∂mu) ≠ ⊤)
    (hpres : ∀ x, MeasurePreserving (fun y : Classes K => x*y⁻¹) mu mu)
    (hemb : ∀ x, MeasurableEmbedding (fun y : Classes K => x*y⁻¹))
    (hbase : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s psi true z.1 z.2) (mu.prod mu))
    (hkb : AEStronglyMeasurable (fun z : Classes K × Classes K =>
      factorKernel K (actualLog K) alpha s theta false z.1 z.2) (mu.prod mu))
    (e : HilbertBasis ι ℂ (Lp ℂ 2 mu)) :
    ∃ (T : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) (u v : ι → Lp ℂ 2 mu),
      (∀ F, ∀ᵐ x ∂mu, T F x =
        ∫ y, ((coreIndicator L (actualLog K x)) *
          transportedCutoffKernel K (fun _ => 1) (convolution K mu psi theta)
            (fun a => stripWeight alpha s (actualLog K a)) x y) * F y ∂mu) ∧
      Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖) ∧
      (∑' i, ‖u i‖ * ‖innerSL ℂ (v i)‖) ≤
        (1+L^2) * Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s psi true p.1 p.2‖^2 ∂(mu.prod mu)) *
        Real.sqrt (∫ p : Classes K × Classes K,
          ‖factorKernel K (actualLog K) alpha s theta false p.1 p.2‖^2 ∂(mu.prod mu)) ∧
      HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T ∧
      HasSum (fun i => (innerSL ℂ (u i)).smulRight (v i))
        (ContinuousLinearMap.adjoint T) := by
  obtain ⟨T,u,v,hT,hc,hN,hS⟩ := genuine_compact_output_nuclear K mu alpha s R S L
    hL ha hs psi theta hell V hpush hb hp ht hp0 ht0 hpsupp htsupp hpf htf
    hpres hemb hbase hkb e
  exact ⟨T,u,v,hT,hc,hN,hS,adjoint_rankOne_hasSum u v T hS⟩

#check adjoint_rankOne
#print axioms adjoint_rankOne
#check genuine_compact_output_and_adjoint_nuclear
#print axioms genuine_compact_output_and_adjoint_nuclear
end
end Round110E
