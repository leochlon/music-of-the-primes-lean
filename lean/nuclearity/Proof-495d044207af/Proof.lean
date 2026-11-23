import Mathlib
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped InnerProductSpace
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


/-! E196: actual weighted-fiber numerical range. Both orbit zero and growth
are now supplied by D's constructed Lp translation, not hypothesis fields.
The strong derivative is precisely the unbounded generator-domain witness. -/
namespace Round196E
open Round195D
open scoped InnerProductSpace

theorem native_translation_generator_numerical_range
    (u v s : ℝ) (hs : 0 ≤ s)
    (x y : NativeDualFiber u v s)
    (hd : HasDerivAt (fun t => nativeTranslationVector u v s t hs x) y 0) :
    |(inner ℂ x y).re| ≤ (max |u| |v| + s/4) * ‖x‖^2 := by
  exact Round195E.native_generator_numerical_range
    (Round196D.nativeTranslation u v s hs) (max |u| |v|+s/4)
    (Round196D.nativeTranslation_zero u v s hs)
    (fun t w => Round196D.nativeTranslation_bound u v s t hs w) x y hd

/-- Numerical range is evaluated only on the genuine resolvent range.
There is no bounded whole-space generator and no assumed numerical range. -/
theorem native_fiber_resolvent_coercivity
    (u v s : ℝ) (hs : 0 ≤ s)
    (R : NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s) (z : ℂ)
    (hres : ∀ x : NativeDualFiber u v s,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x))
        (z • R x - x) 0)
    (x : NativeDualFiber u v s) :
    (z.re - (max |u| |v| + s/4)) * ‖R x‖^2 ≤ (inner ℂ (R x) x).re := by
  have hn := (le_abs_self _).trans
    (native_translation_generator_numerical_range u v s hs (R x) (z • R x - x) (hres x))
  have hid : (inner ℂ (R x) (z • R x - x)).re =
      z.re * ‖R x‖^2 - (inner ℂ (R x) x).re := by
    simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      Complex.mul_re, ← Complex.ofReal_pow]
  rw [hid] at hn
  nlinarith

/-- Direct native column-energy input to H195's infinite nuclear assembly.
Its residual hres is the actual generator-resolvent identity, not a trace or
summability assumption. The finite real trace must still be bounded. -/
theorem native_fiber_resolvent_column_square_sum_le
    (u v s : ℝ) (hs : 0 ≤ s)
    {ι : Type*} (J : Finset ι) (e : ι → NativeDualFiber u v s)
    (R : NativeDualFiber u v s →L[ℂ] NativeDualFiber u v s)
    (z : ℂ) (hz : max |u| |v| + s/4 < z.re)
    (hres : ∀ x : NativeDualFiber u v s,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x))
        (z • R x - x) 0) :
    (∑ j ∈ J, ‖R (e j)‖^2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) /
        (z.re - (max |u| |v| + s/4)) := by
  apply (le_div_iff₀ (sub_pos.mpr hz)).2
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    native_fiber_resolvent_coercivity u v s hs R z hres (e j)

#check native_translation_generator_numerical_range
#print axioms native_translation_generator_numerical_range
#check native_fiber_resolvent_coercivity
#print axioms native_fiber_resolvent_coercivity
#check native_fiber_resolvent_column_square_sum_le
#print axioms native_fiber_resolvent_column_square_sum_le
end Round196E

namespace Round196E
open Round195D
open scoped InnerProductSpace

/-- The actual fiber estimate restricts to any native subspace. In the joined
proof V must be the actual geometric annihilator; no identity of V with a jet
span or full native character space is assumed by this energy lemma. -/
theorem native_subspace_resolvent_coercivity
    (u v s : ℝ) (hs : 0 ≤ s) (V : Submodule ℂ (NativeDualFiber u v s))
    (R : V →L[ℂ] V) (z : ℂ)
    (hres : ∀ x : V,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x : NativeDualFiber u v s))
        ((z • R x - x : V) : NativeDualFiber u v s) 0)
    (x : V) :
    (z.re - (max |u| |v| + s/4)) * ‖R x‖^2 ≤ (inner ℂ (R x) x).re := by
  have hn := (le_abs_self _).trans
    (native_translation_generator_numerical_range u v s hs
      (R x : NativeDualFiber u v s) ((z • R x - x : V) : NativeDualFiber u v s) (hres x))
  change (inner ℂ (R x) (z • R x - x)).re ≤
    (max |u| |v| + s/4) * ‖R x‖^2 at hn
  have hid : (inner ℂ (R x) (z • R x - x)).re =
      z.re * ‖R x‖^2 - (inner ℂ (R x) x).re := by
    simp [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      Complex.mul_re, ← Complex.ofReal_pow]
  rw [hid] at hn
  nlinarith

theorem native_subspace_resolvent_column_square_sum_le
    (u v s : ℝ) (hs : 0 ≤ s) (V : Submodule ℂ (NativeDualFiber u v s))
    {ι : Type*} (J : Finset ι) (e : ι → V)
    (R : V →L[ℂ] V) (z : ℂ) (hz : max |u| |v| + s/4 < z.re)
    (hres : ∀ x : V,
      HasDerivAt (fun t => nativeTranslationVector u v s t hs (R x : NativeDualFiber u v s))
        ((z • R x - x : V) : NativeDualFiber u v s) 0) :
    (∑ j ∈ J, ‖R (e j)‖^2) ≤
      (∑ j ∈ J, (inner ℂ (R (e j)) (e j)).re) /
        (z.re - (max |u| |v| + s/4)) := by
  apply (le_div_iff₀ (sub_pos.mpr hz)).2
  rw [mul_comm, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    native_subspace_resolvent_coercivity u v s hs V R z hres (e j)

#check native_subspace_resolvent_coercivity
#print axioms native_subspace_resolvent_coercivity
#check native_subspace_resolvent_column_square_sum_le
#print axioms native_subspace_resolvent_column_square_sum_le
end Round196E

/-! H195: the infinite rank-one series in the reviewed R W R factorization.
This is the requested trace-ideal interface, not the native spectral bound.
The two square-column estimates must be derived on the actual annihilator.
No nuclearity or rank-one summability is assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
namespace Round195H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

/-- A concrete nuclear-series certificate with quantitative total cost. -/
def HasNuclearCost (T : E →L[ℂ] E) (C : ℝ) : Prop :=
  ∃ (v : ι → E) (f : ι → E →L[ℂ] ℂ),
    (∀ x, HasSum (fun i => f i x • v i) (T x)) ∧
    Summable (fun i => ‖f i‖ * ‖v i‖) ∧
    (∑' i, ‖f i‖ * ‖v i‖) ≤ C

/-- Square-column control yields the actual infinite R S expansion, with
S = W R in the reviewed native application. The cost is derived by Young's
inequality; no target rank-one summability is a premise. -/
theorem factorization_has_nuclear_cost
    (b : HilbertBasis ι ℂ E) (R S : E →L[ℂ] E)
    (hr : Summable (fun i => ‖R (b i)‖^2))
    (hs : Summable (fun i => ‖(innerSL ℂ (b i)).comp S‖^2)) :
    HasNuclearCost (ι := ι) (R.comp S)
      (((∑' i, ‖R (b i)‖^2) +
        (∑' i, ‖(innerSL ℂ (b i)).comp S‖^2))/2) := by
  let f : ι → E →L[ℂ] ℂ := fun i => (innerSL ℂ (b i)).comp S
  let v : ι → E := fun i => R (b i)
  have hm : Summable (fun i => (‖v i‖^2 + ‖f i‖^2)/2) :=
    (hr.add hs).div_const 2
  have hp (i : ι) : ‖f i‖ * ‖v i‖ ≤ (‖v i‖^2 + ‖f i‖^2)/2 := by
    nlinarith [sq_nonneg (‖v i‖ - ‖f i‖)]
  have hc : Summable (fun i => ‖f i‖ * ‖v i‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hp hm
  refine ⟨v, f, ?_, hc, ?_⟩
  · intro x
    have hh := R.hasSum (b.hasSum_repr (S x))
    simpa only [f, v, map_smul, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hh
  · calc
      _ ≤ ∑' i, (‖v i‖^2 + ‖f i‖^2)/2 := hc.tsum_le_tsum hp hm
      _ = _ := by rw [tsum_div_const, hr.tsum_add hs]

#check factorization_has_nuclear_cost
#print axioms factorization_has_nuclear_cost

/-- The exact infinite-series slot in the reviewed estimate. W is the
smoothed convolution; in the native application W commutes with R, so
R R W = R W R. Both hypotheses are finite energy estimates, not nuclear
summability. The native spectral/character bounds must discharge them. -/
theorem resolvent_factorization_nuclear_bound
    (b : HilbertBasis ι ℂ E) (R W : E →L[ℂ] E) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset ι, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (hrow : ∀ J : Finset ι, ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z) :
    HasNuclearCost (ι := ι) (R.comp (R.comp W)) (B*Z) := by
  let f : ι → E →L[ℂ] ℂ := fun i => ((innerSL ℂ (b i)).comp R).comp W
  let v : ι → E := fun i => R (b i)
  have hB : 0 ≤ B := (norm_nonneg W).trans hW
  have hp (i : ι) : ‖f i‖ * ‖v i‖ ≤
      B * ((‖R (b i)‖^2 + ‖(innerSL ℂ (b i)).comp R‖^2)/2) := by
    have hf : ‖f i‖ ≤ ‖(innerSL ℂ (b i)).comp R‖ * B := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hW (norm_nonneg _))
    have hh := mul_le_mul_of_nonneg_right hf (norm_nonneg (v i))
    have hy := sq_nonneg (‖R (b i)‖ - ‖(innerSL ℂ (b i)).comp R‖)
    have hz := mul_nonneg hB hy
    dsimp [v] at hh
    nlinarith
  have hfin (J : Finset ι) : ∑ i ∈ J, ‖f i‖ * ‖v i‖ ≤ B*Z := by
    calc
      _ ≤ ∑ i ∈ J, B * ((‖R (b i)‖^2 + ‖(innerSL ℂ (b i)).comp R‖^2)/2) :=
        Finset.sum_le_sum fun i _ => hp i
      _ = B * (((∑ i ∈ J, ‖R (b i)‖^2) +
          (∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2))/2) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ B*Z := mul_le_mul_of_nonneg_left (by linarith [hcol J, hrow J]) hB
  have hc : Summable (fun i => ‖f i‖ * ‖v i‖) :=
    summable_of_sum_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfin
  refine ⟨v, f, ?_, hc, ?_⟩
  · intro x
    have hh := R.hasSum (b.hasSum_repr (R (W x)))
    simpa only [v, f, map_smul, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hh
  · exact le_of_tendsto hc.hasSum (Filter.Eventually.of_forall hfin)

#check resolvent_factorization_nuclear_bound
#print axioms resolvent_factorization_nuclear_bound
end Round195H

namespace Round195H
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Nuclear norm defined by absolutely summable rank-one representations.
An arbitrary summation type is allowed; summability forces countable
nonzero cost. This is a definition, not an assumed trace-class interface. -/
def nuclearNorm (T : H →L[ℂ] H) : ENNReal :=
  sInf {c | ∃ (κ : Type u) (C : ℝ), HasNuclearCost (ι := κ) T C ∧
    c = ENNReal.ofReal C}

theorem nuclearNorm_le_of_cost {κ : Type u} {T : H →L[ℂ] H} {C : ℝ}
    (h : HasNuclearCost (ι := κ) T C) : nuclearNorm T ≤ ENNReal.ofReal C := by
  exact sInf_le ⟨κ, C, h, rfl⟩

/-- Quantitative norm form of the infinite assembly requested by A. All
native finite energy and identification obligations remain explicit. -/
theorem resolvent_nuclearNorm_le [CompleteSpace H]
    {κ : Type u} (b : HilbertBasis κ ℂ H) (R W : H →L[ℂ] H) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset κ, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (hrow : ∀ J : Finset κ, ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z) :
    nuclearNorm (R.comp (R.comp W)) ≤ ENNReal.ofReal (B*Z) :=
  nuclearNorm_le_of_cost (resolvent_factorization_nuclear_bound b R W B Z hW hcol hrow)

#check nuclearNorm
#check resolvent_nuclearNorm_le
#print axioms resolvent_nuclearNorm_le
end Round195H

namespace Round195H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem basis_hasSum_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  have hh := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner x x)
  have he (i : ι) : (inner ℂ x (b i) * inner ℂ (b i) x).re =
      ‖inner ℂ (b i) x‖^2 := by
    rw [← inner_conj_symm (b i) x, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    rw [← Complex.sq_norm, norm_inner_symm]
    simp only [Complex.sq_norm]
    rw [inner_conj_symm]
  have hx : (inner ℂ x x).re = ‖x‖^2 := by
    rw [inner_self_eq_norm_sq_to_K]
    change (((‖x‖ : ℝ) : ℂ)^2).re = ‖x‖^2
    simp [pow_two]
  simpa only [Complex.reCLM_apply, he, hx] using hh

/-- The row estimate is discharged from the column estimate, rather than
passed back to the native spectral proof as an extra hypothesis. -/
theorem finite_rows_le_of_columns
    (b : HilbertBasis ι ℂ E) (R : E →L[ℂ] E) (Z : ℝ)
    (hcol : ∀ J : Finset ι, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (J : Finset ι) :
    ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z := by
  classical
  have hsum (i : ι) :
      HasSum (fun j => ‖inner ℂ (b i) (R (b j))‖^2)
        (‖(innerSL ℂ (b i)).comp R‖^2) := by
    have hh := basis_hasSum_sq b (R.adjoint (b i))
    simpa only [ContinuousLinearMap.innerSL_apply_comp, innerSL_apply_norm,
      ContinuousLinearMap.adjoint_inner_right, norm_inner_symm] using hh
  have hall : HasSum (fun j => ∑ i ∈ J, ‖inner ℂ (b i) (R (b j))‖^2)
      (∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2) := by
    exact hasSum_sum fun i _ => hsum i
  apply le_of_tendsto hall
  apply Filter.Eventually.of_forall
  intro S
  calc
    _ ≤ ∑ j ∈ S, ‖R (b j)‖^2 := Finset.sum_le_sum fun j _ =>
      b.orthonormal.sum_inner_products_le (R (b j))
    _ ≤ Z := hcol S

#check finite_rows_le_of_columns
#print axioms finite_rows_le_of_columns
end Round195H

namespace Round195H
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_nuclearNorm_le_of_columns
    {κ : Type u} (b : HilbertBasis κ ℂ H) (R W : H →L[ℂ] H) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset κ, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z) :
    nuclearNorm (R.comp (R.comp W)) ≤ ENNReal.ofReal (B*Z) := by
  exact resolvent_nuclearNorm_le b R W B Z hW hcol
    (finite_rows_le_of_columns b R Z hcol)

#check resolvent_nuclearNorm_le_of_columns
#print axioms resolvent_nuclearNorm_le_of_columns
end Round195H

/-! H196: the previously absent infinite character-block assembly slot.
The lattice is the concrete finite-level character coordinate lattice, not
an arbitrary enumeration. Its convergence is proved, never assumed. -/
namespace Round196H
open scoped BigOperators

def integerWeight (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ (-2 : ℝ)

theorem integerWeight_nonneg (n : ℤ) : 0 ≤ integerWeight n :=
  Real.rpow_nonneg (by positivity) _

theorem integerWeight_summable : Summable integerWeight := by
  have h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hp
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [integerWeight, abs_of_nonneg, add_comm] using h

def latticeWeight (d : ℕ) (k : Fin d → ℤ) : ℝ :=
  ∏ i, integerWeight (k i)

def latticeMass : ℝ := ∑' n : ℤ, integerWeight n

def latticeConsEquiv (d : ℕ) : (ℤ × (Fin d → ℤ)) ≃ (Fin (d+1) → ℤ) where
  toFun p := Fin.cons p.1 p.2
  invFun k := (k 0, fun i => k i.succ)
  left_inv := by intro p; simp
  right_inv := by
    intro k
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem latticeWeight_nonneg (d : ℕ) (k : Fin d → ℤ) :
    0 ≤ latticeWeight d k := Finset.prod_nonneg fun _ _ => integerWeight_nonneg _

theorem latticeWeight_hasSum (d : ℕ) :
    HasSum (latticeWeight d) (latticeMass ^ d) := by
  induction d with
  | zero =>
      letI : Unique (Fin 0 → ℤ) :=
        { default := fun i => Fin.elim0 i
          uniq := fun f => by funext i; exact Fin.elim0 i }
      simpa [latticeWeight] using (hasSum_fintype (latticeWeight 0))
  | succ d ih =>
      have hp := integerWeight_summable.mul_of_nonneg ih.summable
        integerWeight_nonneg (latticeWeight_nonneg d)
      have hh := integerWeight_summable.hasSum.mul ih hp
      apply (latticeConsEquiv d).hasSum_iff.mp
      simpa [Function.comp_def, latticeConsEquiv, latticeWeight,
        Fin.prod_univ_succ, latticeMass, pow_succ, mul_comm] using hh

/-- The full concrete F × Z^d majorant, including d=0. -/
theorem finite_level_character_majorant {F : Type*} [Fintype F] (d : ℕ) :
    HasSum (fun p : F × (Fin d → ℤ) => latticeWeight d p.2)
      ((Fintype.card F : ℝ) * latticeMass ^ d) := by
  have hf := hasSum_fintype (fun _ : F => (1 : ℝ))
  have hl := latticeWeight_hasSum d
  have hp := hf.summable.mul_of_nonneg hl.summable (by intro; norm_num)
    (latticeWeight_nonneg d)
  simpa using hf.mul hl hp

#check finite_level_character_majorant
#print axioms finite_level_character_majorant
end Round196H

namespace Round196H
open scoped BigOperators
universe u
set_option maxHeartbeats 500000

/-- Infinite character-block assembly with actual rank-one witnesses.
No nuclearity or global cost summability is a hypothesis. Both follow from
finite resolvent column estimates and a proved concrete lattice majorant.
The block identity hT must be supplied by the native character decomposition. -/
theorem finite_level_resolvent_nuclear_assembly
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {F : Type u} [Fintype F] (d : ℕ)
    (E : F × (Fin d → ℤ) → Type u)
    [∀ χ, NormedAddCommGroup (E χ)] [∀ χ, InnerProductSpace ℂ (E χ)]
    [∀ χ, CompleteSpace (E χ)]
    (κ : F × (Fin d → ℤ) → Type u)
    (b : ∀ χ, HilbertBasis (κ χ) ℂ (E χ))
    (R W : ∀ χ, E χ →L[ℂ] E χ)
    (inc : ∀ χ, E χ →L[ℂ] H) (pr : ∀ χ, H →L[ℂ] E χ)
    (hinc : ∀ χ, ‖inc χ‖ ≤ 1) (hpr : ∀ χ, ‖pr χ‖ ≤ 1)
    (B Z : F × (Fin d → ℤ) → ℝ)
    (hW : ∀ χ, ‖W χ‖ ≤ B χ)
    (hcol : ∀ χ (J : Finset (κ χ)), ∑ i ∈ J, ‖R χ (b χ i)‖^2 ≤ Z χ)
    (D : ℝ) (hcost : ∀ χ, B χ * Z χ ≤ D * latticeWeight d χ.2)
    (T : H →L[ℂ] H)
    (hT : ∀ x, HasSum (fun χ => inc χ (R χ (R χ (W χ (pr χ x))))) (T x)) :
    Round195H.nuclearNorm T ≤
      ENNReal.ofReal (D * ((Fintype.card F : ℝ) * latticeMass ^ d)) := by
  classical
  have hwit (χ : F × (Fin d → ℤ)) :=
    Round195H.resolvent_factorization_nuclear_bound (b χ) (R χ) (W χ)
      (B χ) (Z χ) (hW χ) (hcol χ)
      (Round195H.finite_rows_le_of_columns (b χ) (R χ) (Z χ) (hcol χ))
  choose v f hrep hs hb using hwit
  try clear_value v f
  let vv : (Σ χ, κ χ) → H := fun p => inc p.1 (v p.1 p.2)
  let ff : (Σ χ, κ χ) → H →L[ℂ] ℂ := fun p => (f p.1 p.2).comp (pr p.1)
  let cost : (Σ χ, κ χ) → ℝ := fun p => ‖ff p‖ * ‖vv p‖
  have hc0 (p : Σ χ, κ χ) : 0 ≤ cost p := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc_le (χ : F × (Fin d → ℤ)) (i : κ χ) :
      cost ⟨χ,i⟩ ≤ ‖f χ i‖ * ‖v χ i‖ := by
    have h1 : ‖(f χ i).comp (pr χ)‖ ≤ ‖f χ i‖ := by
      calc
        _ ≤ ‖f χ i‖ * ‖pr χ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖f χ i‖ * 1 := mul_le_mul_of_nonneg_left (hpr χ) (norm_nonneg _)
        _ = _ := mul_one _
    have h2 : ‖inc χ (v χ i)‖ ≤ ‖v χ i‖ := by
      calc
        _ ≤ ‖inc χ‖ * ‖v χ i‖ := (inc χ).le_opNorm _
        _ ≤ 1 * ‖v χ i‖ := mul_le_mul_of_nonneg_right (hinc χ) (norm_nonneg _)
        _ = _ := one_mul _
    exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  have hcχ (χ : F × (Fin d → ℤ)) : Summable (fun i => cost ⟨χ,i⟩) :=
    Summable.of_nonneg_of_le (fun i => hc0 _) (hc_le χ) (hs χ)
  have hm := (finite_level_character_majorant (F := F) d).mul_left D
  have hbχ (χ : F × (Fin d → ℤ)) :
      (∑' i, cost ⟨χ,i⟩) ≤ D * latticeWeight d χ.2 :=
    ((hcχ χ).tsum_le_tsum (hc_le χ) (hs χ)).trans ((hb χ).trans (hcost χ))
  have hout : Summable (fun χ => ∑' i, cost ⟨χ,i⟩) :=
    Summable.of_nonneg_of_le (fun χ => tsum_nonneg fun i => hc0 _) hbχ hm.summable
  have hc : Summable cost := (summable_sigma_of_nonneg hc0).mpr ⟨hcχ, hout⟩
  apply Round195H.nuclearNorm_le_of_cost (κ := Σ χ, κ χ)
    (C := D * ((Fintype.card F : ℝ) * latticeMass ^ d))
  refine ⟨vv, ff, ?_, hc, ?_⟩
  · intro x
    have hn : Summable (fun p : Σ χ, κ χ => ‖ff p x • vv p‖) := by
      apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ (hc.mul_right ‖x‖)
      intro p
      rw [norm_smul]
      calc
        _ ≤ (‖ff p‖ * ‖x‖) * ‖vv p‖ :=
          mul_le_mul_of_nonneg_right ((ff p).le_opNorm x) (norm_nonneg _)
        _ = cost p * ‖x‖ := by dsimp only [cost]; ring
    apply (hT x).sigma_of_hasSum _ hn.of_norm
    intro χ
    have hh := (inc χ).hasSum (hrep χ (pr χ x))
    simpa only [ff, vv, ContinuousLinearMap.comp_apply, map_smul] using hh
  · calc
      _ = ∑' χ : F × (Fin d → ℤ), ∑' i : κ χ, cost ⟨χ,i⟩ := hc.tsum_sigma
      _ ≤ ∑' χ : F × (Fin d → ℤ), D * latticeWeight d χ.2 :=
        hout.tsum_le_tsum (g := fun χ : F × (Fin d → ℤ) => D * latticeWeight d χ.2) hbχ hm.summable
      _ = _ := hm.tsum_eq

#check finite_level_resolvent_nuclear_assembly
#print axioms finite_level_resolvent_nuclear_assembly
end Round196H

namespace Round197H
open Round195D Round196H
open scoped BigOperators InnerProductSpace

/-- Concrete E196-to-H196 application on the constructed weighted native
subspaces. The column and row estimates are derived, not assumed. Native
finite traces, character decay and the original operator identity are still
explicit residuals; this is not the full number-field theorem. -/
theorem native_finite_level_resolvent_nuclear_bound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {F : Type} [Fintype F] (d : ℕ)
    (u v s : ℝ) (hs : 0 ≤ s)
    (V : F × (Fin d → ℤ) → Submodule ℂ (NativeDualFiber u v s))
    [∀ χ, CompleteSpace (V χ)]
    (κ : F × (Fin d → ℤ) → Type)
    (b : ∀ χ, HilbertBasis (κ χ) ℂ (V χ))
    (R W : ∀ χ, V χ →L[ℂ] V χ)
    (inc : ∀ χ, V χ →L[ℂ] H) (pr : ∀ χ, H →L[ℂ] V χ)
    (hinc : ∀ χ, ‖inc χ‖ ≤ 1) (hpr : ∀ χ, ‖pr χ‖ ≤ 1)
    (z : ℂ) (hz : max |u| |v| + s/4 < z.re)
    (hres : ∀ χ (x : V χ),
      HasDerivAt (fun t => nativeTranslationVector u v s t hs
        (R χ x : NativeDualFiber u v s))
        ((z • R χ x - x : V χ) : NativeDualFiber u v s) 0)
    (B Z : F × (Fin d → ℤ) → ℝ)
    (hW : ∀ χ, ‖W χ‖ ≤ B χ)
    (htrace : ∀ χ (J : Finset (κ χ)),
      ∑ i ∈ J, (inner ℂ (R χ (b χ i)) (b χ i)).re ≤ Z χ)
    (D : ℝ) (hcost : ∀ χ, B χ * Z χ ≤ D * latticeWeight d χ.2)
    (T : H →L[ℂ] H)
    (hT : ∀ x, HasSum (fun χ => inc χ (R χ (R χ (W χ (pr χ x))))) (T x)) :
    Round195H.nuclearNorm T ≤ ENNReal.ofReal
      ((D / (z.re - (max |u| |v| + s/4))) *
        ((Fintype.card F : ℝ) * latticeMass ^ d)) := by
  have hg : 0 ≤ z.re - (max |u| |v| + s/4) := (sub_pos.mpr hz).le
  apply finite_level_resolvent_nuclear_assembly d (fun χ => V χ) κ b R W
    inc pr hinc hpr B (fun χ => Z χ / (z.re - (max |u| |v| + s/4))) hW
    (fun χ J => (Round196E.native_subspace_resolvent_column_square_sum_le
      u v s hs (V χ) J (b χ) (R χ) z hz (hres χ)).trans
      (div_le_div_of_nonneg_right (htrace χ J) hg))
    (D / (z.re - (max |u| |v| + s/4))) _ T hT
  intro χ
  calc
    _ = (B χ * Z χ) / (z.re - (max |u| |v| + s/4)) := by ring
    _ ≤ (D * latticeWeight d χ.2) / (z.re - (max |u| |v| + s/4)) :=
      div_le_div_of_nonneg_right (hcost χ) hg
    _ = _ := by ring

#check native_finite_level_resolvent_nuclear_bound
#print axioms native_finite_level_resolvent_nuclear_bound
end Round197H
