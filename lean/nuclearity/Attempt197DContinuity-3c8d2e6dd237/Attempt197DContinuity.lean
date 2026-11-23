import Mathlib
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

namespace Round196D
open MeasureTheory Round195D

open scoped ContDiff

instance nativeDualMeasure_locallyFinite (u v s : ℝ) :
    IsLocallyFiniteMeasure (nativeDualMeasure u v s) := by
  apply IsLocallyFiniteMeasure.withDensity_ofReal
  unfold Round194C.nativeDualWeight
  have hl : Continuous (fun x : ℝ => Real.log (1+x^2)) :=
    (continuous_const.add (continuous_id.pow 2)).log (fun x => ne_of_gt (by positivity))
  fun_prop

/-- A genuine dense smooth compact core in the actual weighted completion. -/
theorem native_smooth_compact_core_dense (u v s : ℝ) :
    Dense {f : NativeDualFiber u v s | ∃ g : ℝ → ℂ,
      (fun x => f x) =ᵐ[nativeDualMeasure u v s] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num)

#check native_smooth_compact_core_dense
#print axioms native_smooth_compact_core_dense
end Round196D

namespace Round196D
open MeasureTheory Round195D

/-- Strong continuity at zero on the actual dense compact continuous core. -/
theorem nativeTranslation_continuousAt_zero_of_core (u v s : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) (g : ℝ → ℂ)
    (hfg : (fun x => f x) =ᵐ[nativeDualMeasure u v s] g)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ContinuousAt (fun t => nativeTranslation u v s hs t f) 0 := by
  obtain ⟨R, hR, hsupport⟩ := hgs.exists_pos_le_norm
  let S := Metric.closedBall (0 : ℝ) (R+1)
  have hS : MeasurableSet S := measurableSet_closedBall
  have hμS : nativeDualMeasure u v s S ≠ ⊤ :=
    (isCompact_closedBall (0 : ℝ) (R+1)).measure_lt_top.ne
  have hq := memLp_indicator_const (μ := nativeDualMeasure u v s) (2 : ENNReal)
    hS (1 : ℂ) (Or.inr hμS)
  let q : NativeDualFiber u v s := hq.toLp (S.indicator (fun _ => (1 : ℂ)))
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let η := ε / (‖q‖+1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη
  refine ⟨min δ 1, lt_min hδ (by norm_num), ?_⟩
  intro t ht
  have htδ : ‖t‖ < δ := by simpa using (lt_min_iff.mp ht).1
  have ht1 : ‖t‖ < 1 := by simpa using (lt_min_iff.mp ht).2
  have hb : ‖nativeTranslation u v s hs t f - f‖ ≤ η*‖q‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul (g := q)
    have htcoe : (fun x => nativeTranslation u v s hs t f x) =ᵐ[nativeDualMeasure u v s]
        (fun x => f (x+t)) := native_translation_coe u v s t hs f
    filter_upwards [Lp.coeFn_sub (nativeTranslation u v s hs t f) f,
      htcoe, native_translation_ae u v s t hs hfg, hfg, hq.coeFn_toLp]
      with x hsub htrans hshift hx hqx
    simp only [Pi.sub_apply] at hsub
    change ‖(nativeTranslation u v s hs t f - f) x‖ ≤ η * ‖q x‖
    rw [hsub, htrans, hshift, hx]
    change ‖g (x+t)-g x‖ ≤ η * ‖hq.toLp _ x‖
    rw [hqx]
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS, norm_one, mul_one]
      have hd : dist (x+t) x < δ := by simpa [dist_eq_norm] using htδ
      have hsmall : ‖g (x+t)-g x‖ < η := by
        simpa only [dist_eq_norm] using hmod hd
      exact hsmall.le
    · have hxnorm : R+1 < ‖x‖ := by
        simpa only [S, Metric.mem_closedBall, dist_zero_right, not_le] using hxS
      have htri : ‖x‖ ≤ ‖x+t‖+‖t‖ := by
        simpa only [add_sub_cancel_right] using norm_sub_le (x+t) t
      have hz1 := hsupport x (by linarith : R ≤ ‖x‖)
      have hz2 := hsupport (x+t) (by linarith : R ≤ ‖x+t‖)
      simp [hz1, hz2, Set.indicator_of_notMem hxS]
  rw [nativeTranslation_zero, dist_eq_norm]
  apply hb.trans_lt
  have heq : η * (‖q‖+1) = ε := div_mul_cancel₀ ε (by positivity)
  nlinarith

#check nativeTranslation_continuousAt_zero_of_core
#print axioms nativeTranslation_continuousAt_zero_of_core
end Round196D


namespace Round196C
open MeasureTheory Round195D Round196D Filter
open scoped Topology

/-- Density extension for the exact remaining native group-continuity premise.
D still owes continuity at zero on compact smooth representatives. -/
theorem native_translation_tendsto_zero_of_dense
    (u v s : ℝ) (hs : 0 ≤ s)
    (S : Set (NativeDualFiber u v s)) (hS : Dense S)
    (hcore : ∀ g ∈ S, Tendsto (fun t : ℝ => nativeTranslation u v s hs t g)
      (𝓝 0) (𝓝 g)) (f : NativeDualFiber u v s) :
    Tendsto (fun t : ℝ => nativeTranslation u v s hs t f) (𝓝 0) (𝓝 f) := by
  let beta := max |u| |v|+s/4
  let M := Real.exp beta
  have hb : 0 ≤ beta := by dsimp [beta]; positivity
  have hM : 0 < M := Real.exp_pos _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (2*(M+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp (hS f) δ hδ
  have hc := Metric.tendsto_nhds.mp (hcore g hg) (ε/2) (by positivity)
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ)<1)] with t ht
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
  filter_upwards [hc, ht] with t htg ht
  have hlocal : ‖nativeTranslation u v s hs t (f-g)‖ ≤ M*‖f-g‖ := by
    apply (nativeTranslation_bound u v s t hs (f-g)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    change beta*|t| ≤ beta
    nlinarith
  have hnorm : ‖f-g‖ < δ := by simpa only [dist_eq_norm] using hfg
  have hgf : ‖g-f‖ < δ := by simpa only [norm_sub_rev] using hnorm
  have hstep : ‖nativeTranslation u v s hs t f - f‖ ≤
      M*‖f-g‖ + ‖nativeTranslation u v s hs t g-g‖ + ‖g-f‖ := by
    calc
      _ = ‖nativeTranslation u v s hs t (f-g) +
          (nativeTranslation u v s hs t g-g) + (g-f)‖ := by
        congr 1
        rw [map_sub]
        abel
      _ ≤ ‖nativeTranslation u v s hs t (f-g)‖ +
          ‖nativeTranslation u v s hs t g-g‖ + ‖g-f‖ := norm_add₃_le
      _ ≤ _ := by linarith [hlocal]
  have hd : (M+1)*δ = ε/2 := by
    dsimp [δ]
    field_simp [ne_of_gt (show 0 < M+1 by positivity)]
  rw [dist_eq_norm] at htg ⊢
  have hmul : M*‖f-g‖ < M*δ := mul_lt_mul_of_pos_left hnorm hM
  nlinarith

#check native_translation_tendsto_zero_of_dense
#print axioms native_translation_tendsto_zero_of_dense
end Round196C

namespace Round196C
open MeasureTheory Round195D Round196D Filter
open scoped Topology ContDiff

theorem native_translation_continuous_of_smooth_core
    (u v s : ℝ) (hs : 0 ≤ s)
    (hcore : ∀ (f : NativeDualFiber u v s) (g : ℝ → ℂ),
      (fun x => f x) =ᵐ[nativeDualMeasure u v s] g →
      HasCompactSupport g → ContDiff ℝ ∞ g →
      Tendsto (fun t : ℝ => nativeTranslation u v s hs t f) (𝓝 0) (𝓝 f))
    (f : NativeDualFiber u v s) :
    Continuous (fun t : ℝ => nativeTranslation u v s hs t f) := by
  have hzero := native_translation_tendsto_zero_of_dense u v s hs
    _ (native_smooth_compact_core_dense u v s)
    (fun g hg => by
      obtain ⟨k, heq, hcomp, hdiff⟩ := hg
      exact hcore g k heq hcomp hdiff) f
  apply continuous_iff_continuousAt.mpr
  intro t₀
  have ht : Tendsto (fun t : ℝ => t-t₀) (𝓝 t₀) (𝓝 0) := by
    simpa only [sub_self] using
      (show Continuous (fun t : ℝ => t-t₀) from continuous_id.sub continuous_const).tendsto t₀
  have hh := ((nativeTranslation u v s hs t₀).continuous.tendsto f).comp
    (hzero.comp ht)
  simpa only [Function.comp_def, nativeTranslation_group, sub_add_cancel] using hh

#check native_translation_continuous_of_smooth_core
#print axioms native_translation_continuous_of_smooth_core
end Round196C

namespace Round196D
open MeasureTheory Round195D

theorem nativeTranslation_continuous (u v s : ℝ) (hs : 0 ≤ s)
    (f : NativeDualFiber u v s) :
    Continuous (fun t : ℝ => nativeTranslation u v s hs t f) := by
  apply Round196C.native_translation_continuous_of_smooth_core u v s hs _ f
  intro f g hfg hcomp hdiff
  simpa only [ContinuousAt, nativeTranslation_zero] using
    nativeTranslation_continuousAt_zero_of_core u v s hs f g hfg hdiff.continuous hcomp

#check nativeTranslation_continuous
#print axioms nativeTranslation_continuous
end Round196D
