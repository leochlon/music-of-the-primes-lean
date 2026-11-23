import Mathlib

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

/-! E195 joins the checked integration-by-parts identity to its exact
weight energy estimate. All analytic integrability and boundary premises
are discharged for the actual smooth compactly supported scalar core.
The extension to D's native Lp generator remains a separate obligation. -/
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
