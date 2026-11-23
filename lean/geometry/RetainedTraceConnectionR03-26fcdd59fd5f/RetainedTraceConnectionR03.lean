import Mathlib

noncomputable section
open Complex Filter Topology
namespace CorrectionApplicationR01

theorem logDeriv_exp : logDeriv Complex.exp = 1 := by
  funext z
  simp [logDeriv_apply, Complex.deriv_exp, Complex.exp_ne_zero]

/- Exact independent Fermat proof bodies, original source lines 2001--2022
   and 3463--3476; only namespace scaffolding is changed. -/
theorem gapsw80_t38_logDeriv_E1_factor {ρ s : ℂ} (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (fun z => (1 - z / ρ) * Complex.exp (z / ρ)) s
      = (s - ρ)⁻¹ + ρ⁻¹ := by
  have _em := Classical.em
  have h1 : (1 : ℂ) - s / ρ ≠ 0 :=
    sub_ne_zero.mpr fun h => hs ((div_eq_one_iff_eq hρ).mp h.symm)
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hρs : ρ - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hmul := logDeriv_mul (f := fun w => 1 - w / ρ)
    (g := fun w => Complex.exp (w / ρ)) s h1 (Complex.exp_ne_zero _)
    (by fun_prop) (by fun_prop)
  rw [hmul]
  have hlin : logDeriv (fun w => (1 : ℂ) - w / ρ) s = (s - ρ)⁻¹ := by
    rw [logDeriv_apply]
    simp only [deriv_const_sub, deriv_div_const, deriv_id'']
    field_simp
    ring
  have hexp : logDeriv (fun w => Complex.exp (w / ρ)) s = ρ⁻¹ := by
    rw [show (fun w => Complex.exp (w / ρ)) = Complex.exp ∘ (· / ρ) from rfl,
      logDeriv_comp Complex.differentiableAt_exp (by fun_prop), logDeriv_exp,
      Pi.one_apply, one_mul, deriv_div_const, deriv_id'', one_div]
  rw [hlin, hexp]

theorem gapsw80_t45_eventually_large_norm_cofinite {ι : Type*} {ρ : ι → ℂ}
    (hρ0 : ∀ j, ρ j ≠ 0) (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    {R : ℝ} (hR : 0 < R) : ∀ᶠ j in cofinite, R ≤ ‖ρ j‖ := by
  have _em := Classical.em
  have h0 := hsum.tendsto_cofinite_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]

/-- The derivative retains every selected zero copy with its sign. -/
theorem compensated_hasDerivAt {ρ z : ℂ} (hz : z ≠ ρ) :
    HasDerivAt (fun w : ℂ => (w-ρ)⁻¹ + ρ⁻¹) (-1 / (z-ρ)^2) z := by
  simpa using (((hasDerivAt_id z).sub_const ρ).inv
    (sub_ne_zero.mpr hz)).add_const (ρ⁻¹)

/-- Direct bound for selected, omitted, or boundary zero copies. -/
theorem correction_summable {ι : Type*} {ρ c : ι → ℂ}
    (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    (hc : ∀ j, ‖c j‖ ≤ 1) (z : ℂ) :
    Summable (fun j => c j / (z-ρ j)^2) := by
  have hlarge := gapsw80_t45_eventually_large_norm_cofinite hρ0 hsum
    (R := 2 * (‖z‖ + 1)) (by positivity)
  refine (hsum.mul_left 4).of_norm_bounded_eventually ?_
  filter_upwards [hlarge] with j hj
  have hr : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hd : ‖ρ j‖ / 2 ≤ ‖z-ρ j‖ := by
    have hn : ‖ρ j‖ - ‖z‖ ≤ ‖z-ρ j‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    linarith
  have hd0 : 0 < ‖z-ρ j‖ := lt_of_lt_of_le (by positivity) hd
  rw [norm_div, norm_pow, Complex.normSq_eq_norm_sq]
  calc
    ‖c j‖ / ‖z-ρ j‖^2 ≤ 1 / ‖z-ρ j‖^2 := by gcongr; exact hc j
    _ ≤ 1 / (‖ρ j‖ / 2)^2 := by gcongr
    _ = 4 * (‖ρ j‖^2)⁻¹ := by field_simp; ring

end CorrectionApplicationR01

namespace ManuscriptRH
structure Parameters where
  width : ℝ
  weight : ℝ
  width_pos : 0 < width

def GenuineZero := {ρ : ℂ // completedRiemannZeta ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1}

noncomputable def zeroOrder (ρ : GenuineZero) : ℕ :=
  analyticOrderNatAt completedRiemannZeta ρ.val

def AdmittedJet (p : Parameters) (ρ : GenuineZero) (m : ℕ) : Prop :=
  m < zeroOrder ρ ∧
    (|ρ.val.re - 1/2| < p.width ∨
      (|ρ.val.re - 1/2| = p.width ∧ (2 : ℝ) * m + 1 < p.weight))

noncomputable def interiorMultiplicity (p : Parameters) (ρ : GenuineZero) : ℕ :=
  if |ρ.val.re - 1/2| < p.width then zeroOrder ρ else 0

noncomputable def boundaryMultiplicity (p : Parameters) (ρ : GenuineZero) : ℕ := by
  classical
  exact if |ρ.val.re - 1/2| = p.width then
    ((Finset.range (zeroOrder ρ)).filter (fun m => (2 : ℝ) * m + 1 < p.weight)).card
    else 0

/-- At the SAME Chapter 13 width, a zero to its right has no retained jet. -/
theorem correction_right_of_width (p : Parameters) (ρ : GenuineZero)
    (h : p.width < ρ.val.re - 1/2) :
    interiorMultiplicity p ρ = 0 ∧ boundaryMultiplicity p ρ = 0 := by
  have ha : p.width < |ρ.val.re - 1/2| :=
    lt_of_lt_of_le h (le_abs_self _)
  constructor
  · unfold interiorMultiplicity
    rw [if_neg (not_lt.mpr ha.le)]
  · unfold boundaryMultiplicity
    rw [if_neg (ne_of_gt ha)]

end ManuscriptRH
#print axioms CorrectionApplicationR01.gapsw80_t38_logDeriv_E1_factor
#print axioms CorrectionApplicationR01.gapsw80_t45_eventually_large_norm_cofinite
#print axioms CorrectionApplicationR01.compensated_hasDerivAt
#print axioms CorrectionApplicationR01.correction_summable
#print axioms ManuscriptRH.correction_right_of_width

namespace RetainedTraceConnectionR03
open CorrectionApplicationR01

/-- Fermat's inverse-square bound applied to the retained occurrence set.
No zeta nonvanishing assumption is made. The real-part bound is supplied
by the actual narrow strip, including its admitted boundary copies. -/
theorem retained_square_continuous {ι : Type*} {ρ : ι → ℂ} {r : ℝ}
    (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    (hstrip : ∀ j, (ρ j).re ≤ r) {q : ℂ} (hq : r < q.re) :
    ContinuousAt (fun z : ℂ => ∑' j, (1 : ℂ) / (z-ρ j)^2) q := by
  have hs : Summable (fun j => (1 : ℂ) / (q-ρ j)^2) :=
    correction_summable hρ0 hsum (by intro j; simp) q
  have hsep : ∀ j, q ≠ ρ j := by
    intro j he
    have := hstrip j
    rw [he] at hq
    linarith
  have hB : Summable (fun j => 4 * ‖(1 : ℂ) / (q-ρ j)^2‖) :=
    hs.norm.mul_left 4
  change Tendsto _ (𝓝 q) _
  apply tendsto_tsum_of_dominated_convergence hB
  · intro j
    exact (continuousAt_const.div
      ((continuousAt_id.sub continuousAt_const).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr (hsep j)))).tendsto
  · have hb : Metric.ball q ((q.re-r)/2) ∈ 𝓝 q :=
      Metric.ball_mem_nhds _ (by linarith)
    filter_upwards [hb] with z hz j
    have hz' : ‖z-q‖ < (q.re-r)/2 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hgap : q.re-r ≤ ‖q-ρ j‖ := by
      have hn := Complex.re_le_norm (q-ρ j)
      simp only [sub_re] at hn
      linarith [hstrip j]
    have htri : ‖q-ρ j‖ ≤ ‖z-q‖ + ‖z-ρ j‖ := by
      have ht := norm_add_le (q-z) (z-ρ j)
      rw [show q-z+(z-ρ j) = q-ρ j by ring, norm_sub_rev q z] at ht
      exact ht
    have hr : 0 < ‖q-ρ j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hsep j))
    have hd : ‖q-ρ j‖ / 2 ≤ ‖z-ρ j‖ := by linarith
    simp only [norm_div, norm_one, norm_pow]
    calc
      1 / ‖z-ρ j‖^2 ≤ 1 / (‖q-ρ j‖/2)^2 := by gcongr
      _ = 4 * (1 / ‖q-ρ j‖^2) := by field_simp; ring

/-- The same reference b is retained for the logged family. -/
theorem retained_anchored_continuous {ι : Type*} {ρ : ι → ℂ} {r : ℝ}
    (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    (hstrip : ∀ j, (ρ j).re ≤ r) {q : ℂ} (hq : r < q.re) (b : ℂ) :
    ContinuousAt (fun z : ℂ => ∑' j,
      ((1 : ℂ) / (z-ρ j)^2 - 1 / (b-ρ j)^2)) q := by
  have hs : ∀ z, Summable (fun j => (1 : ℂ) / (z-ρ j)^2) :=
    fun z => correction_summable hρ0 hsum (by intro j; simp) z
  simp_rw [(hs _).tsum_sub (hs b)]
  exact (retained_square_continuous hρ0 hsum hstrip hq).sub continuousAt_const

end RetainedTraceConnectionR03
#print axioms RetainedTraceConnectionR03.retained_square_continuous
#print axioms RetainedTraceConnectionR03.retained_anchored_continuous
