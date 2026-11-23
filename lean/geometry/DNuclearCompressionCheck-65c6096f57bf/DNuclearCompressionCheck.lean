-- CHECK CONTEXT: DNuclearKernelMeasurableCheck exact proof context
import Mathlib
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace GPointwiseCore
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integral_norm_product_le (mu : Measure X) (V W : Lp ℂ 2 mu) :
    (∫ x, ‖V x‖ * ‖W x‖ ∂mu) ≤ ‖V‖ * ‖W‖ := by
  let v : Lp ℝ 2 mu := (Lp.memLp V).norm.toLp (fun x => ‖V x‖)
  let w : Lp ℝ 2 mu := (Lp.memLp W).norm.toLp (fun x => ‖W x‖)
  have hv : ‖v‖ = ‖V‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hw : ‖w‖ = ‖W‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm, ← Lp.norm_def]
  have hi : (∫ x, ‖V x‖ * ‖W x‖ ∂mu) = inner ℝ v w := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp V).norm.coeFn_toLp, (Lp.memLp W).norm.coeFn_toLp]
      with x hx hy
    change ‖V x‖ * ‖W x‖ = inner ℝ (v x) (w x)
    rw [hx, hy]
    simp [RCLike.inner_apply, mul_comm]
  calc
    _ = inner ℝ v w := hi
    _ ≤ ‖inner ℝ v w‖ := le_abs_self _
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ = _ := by rw [hv, hw]


end GPointwiseCore

namespace ReviewM
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]
theorem integrable_complex_series (mu : Measure X) (F : ι → X → ℂ)
    (hi : ∀ i, Integrable (F i) mu)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂mu)) :
    Integrable (fun x => ∑' i, F i x) mu ∧
      (∫ x, ‖∑' i, F i x‖ ∂mu) ≤ ∑' i, ∫ x, ‖F i x‖ ∂mu := by
  classical
  have hm (i : ι) : AEMeasurable (fun x => ‖F i x‖ₑ) mu :=
    (hi i).aemeasurable.enorm
  have he : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) =
      ENNReal.ofReal (∑' i, ∫ x, ‖F i x‖ ∂mu) := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun x => norm_nonneg _) hs).symm
  have hlin : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) ≠ ⊤ := by rw [he]; exact ENNReal.ofReal_ne_top
  have hae : ∀ᵐ x ∂mu, ∑' i, ‖F i x‖ₑ < ⊤ :=
    ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlin
  have hsum : ∀ᵐ x ∂mu, Summable (fun i => F i x) := by
    filter_upwards [hae] with x hx
    apply Summable.of_norm
    have hn : (∑' i, (‖F i x‖₊ : ENNReal)) ≠ ⊤ := hx.ne
    exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)
  have htotal : Integrable (fun x => ∑' i, F i x) mu := by
    refine ⟨aestronglyMeasurable_of_tendsto_ae
      (atTop : Filter (Finset ι)) (f := fun S x => ∑ i ∈ S, F i x)
      (fun S => Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hi i).1) ?_, ?_⟩
    · filter_upwards [hsum] with x hx
      exact hx.hasSum
    · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm)
        (lt_top_iff_ne_top.mpr hlin)
  refine ⟨htotal, ?_⟩
  have hbound : (∫⁻ x, ‖∑' i, F i x‖ₑ ∂mu) ≤
      ENNReal.ofReal (∑' i, ∫ x, ‖F i x‖ ∂mu) := by
    rw [← he]
    exact lintegral_mono fun x => enorm_tsum_le_tsum_enorm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [← ofReal_integral_norm_eq_lintegral_enorm htotal,
    ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _),
    ENNReal.toReal_ofReal (tsum_nonneg fun i => integral_nonneg fun x => norm_nonneg _)] at hreal
  exact hreal

theorem complex_series_ae_summable (mu : Measure X) (F : ι → X → ℂ)
    (hi : ∀ i, Integrable (F i) mu)
    (hs : Summable (fun i => ∫ x, ‖F i x‖ ∂mu)) :
    ∀ᵐ x ∂mu, Summable (fun i => F i x) := by
  have hm (i : ι) : AEMeasurable (fun x => ‖F i x‖ₑ) mu :=
    (hi i).aemeasurable.enorm
  have hlin : (∫⁻ x, ∑' i, ‖F i x‖ₑ ∂mu) ≠ ⊤ := by
    rw [lintegral_tsum hm]
    simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun i => integral_nonneg fun x => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hm) hlin
  filter_upwards [hae] with x hx
  apply Summable.of_norm
  have hn : (∑' i, (‖F i x‖₊ : ENNReal)) ≠ ⊤ := hx.ne
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)

end
end ReviewM
set_option linter.unusedSectionVars false
namespace HNormalizedKernel
open MeasureTheory Filter
open scoped Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]

def haarKernel (b : X → ℝ) (V : ℝ) (U R : X → ℂ) (x y : X) : ℂ :=
  (U x / (b x : ℂ)) * ((b y : ℂ) * star (R y) / (V : ℂ))

theorem diagonal_formula (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : X → ℂ) (x : X) :
    haarKernel b V U R x x = (V : ℂ)⁻¹ * (U x * star (R x)) := by
  have hb0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  unfold haarKernel
  field_simp

theorem l2_inner_formula (nu : Measure X) (U R : Lp ℂ 2 nu) :
    (∫ x, U x * star (R x) ∂nu) = inner ℂ R U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [RCLike.inner_apply]

/-- Correct original-Haar diagonal density; no lower bound on b is needed. -/
theorem diagonal_integrable (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (U R : Lp ℂ 2 nu) :
    Integrable (fun x => haarKernel b V U R x x) (ENNReal.ofReal V • nu) := by
  simp_rw [diagonal_formula b hb]
  exact (((Lp.memLp U).integrable_mul (Lp.memLp R).star).const_mul _).smul_measure
    (by simp)

/-- The Haar factor cancels exactly once in the diagonal trace coefficient. -/
theorem diagonal_integral (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu) :
    (∫ x, haarKernel b V U R x x ∂(ENNReal.ofReal V • nu)) = inner ℂ R U := by
  simp_rw [diagonal_formula b hb]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le, integral_const_mul,
    Complex.real_smul, l2_inner_formula]
  have hv0 : (V : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hV)
  rw [← mul_assoc, mul_inv_cancel₀ hv0, one_mul]

/-- Full-input kernel action, not merely agreement on a theta core. -/
theorem kernel_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R F : Lp ℂ 2 nu) (x : X) :
    (b x : ℂ) * (∫ y, haarKernel b V U R x y * (F y / (b y : ℂ))
      ∂(ENNReal.ofReal V • nu)) = inner ℂ R F * U x := by
  have bx0 : (b x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb x))
  have v0 : (V : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hV)
  have he (y : X) : haarKernel b V U R x y * (F y / (b y : ℂ)) =
      (U x / (b x : ℂ) / (V : ℂ)) * (F y * star (R y)) := by
    have by0 : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    unfold haarKernel
    field_simp
  simp_rw [he]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le, integral_const_mul,
    Complex.real_smul, l2_inner_formula]
  field_simp

/-- Contractive physical masks remove the cutoff from this canonical diagonal. -/
theorem diagonal_cutoff_limit (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu)
    (omega : ℕ → X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (omega n) (ENNReal.ofReal V • nu))
    (hbound : ∀ n, ∀ᵐ x ∂(ENNReal.ofReal V • nu), ‖omega n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂(ENNReal.ofReal V • nu), Tendsto (fun n => omega n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, omega n x * haarKernel b V U R x x
      ∂(ENNReal.ofReal V • nu)) atTop (𝓝 (inner ℂ R U)) := by
  rw [← diagonal_integral nu b hb V hV U R]
  have hi := diagonal_integrable nu b hb V U R
  apply tendsto_integral_of_dominated_convergence
    (fun x => ‖haarKernel b V U R x x‖)
  · intro n
    exact (hm n).mul hi.aestronglyMeasurable
  · exact hi.norm
  · intro n
    filter_upwards [hbound n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa only [one_mul] using hx.mul
      (tendsto_const_nhds (x := haarKernel b V U R x x))

end
end HNormalizedKernel

/- Insert after GPointwiseCore, ReviewM.integrable_complex_series,
   ReviewM.complex_series_ae_summable and HNormalizedKernel. -/
namespace DNuclearKernel
open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

theorem tested_integrable (nu : Measure X) (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (V : Lp ℂ 2 nu) (i : ι) :
    Integrable (fun x => c i * v i x * star (V x)) nu := by
  simpa only [Pi.mul_apply, mul_assoc] using
    (((Lp.memLp (v i)).integrable_mul (Lp.memLp V).star).const_mul (c i))

theorem tested_integral_norm_le (nu : Measure X) (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (V : Lp ℂ 2 nu) (i : ι) :
    (∫ x, ‖c i * v i x * star (V x)‖ ∂nu) ≤ ‖c i‖ * ‖v i‖ * ‖V‖ := by
  simp only [norm_mul, norm_star, mul_assoc]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (GPointwiseCore.integral_norm_product_le nu (v i) V) (norm_nonneg _)

theorem tested_cost (nu : Measure X) (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖c i‖ * ‖v i‖))
    (V : Lp ℂ 2 nu) :
    Summable (fun i => ∫ x, ‖c i * v i x * star (V x)‖ ∂nu) :=
  Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (tested_integral_norm_le nu c v V) (hc.mul_right ‖V‖)

/-- Absolute Hilbert-space cost gives pointwise absolute column convergence.
The finite-measure test functions are constructed from sigma-finiteness. -/
theorem ae_column_cost (nu : Measure X) [SigmaFinite nu] (c : ι → ℂ)
    (v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖c i‖ * ‖v i‖)) :
    ∀ᵐ x ∂nu, Summable (fun i => ‖c i‖ * ‖v i x‖) := by
  have hn (n : ℕ) : ∀ᵐ x ∂nu, x ∈ spanningSets nu n →
      Summable (fun i => ‖c i‖ * ‖v i x‖) := by
    let A := spanningSets nu n
    have hA := measurableSet_spanningSets nu n
    have hmu := measure_spanningSets_lt_top nu n
    let V : Lp ℂ 2 nu := indicatorConstLp 2 hA hmu.ne 1
    have hv : (V : X → ℂ) =ᵐ[nu] A.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have hs := ReviewM.complex_series_ae_summable nu
      (fun i x => c i * v i x * star (V x))
      (tested_integrable nu c v V) (tested_cost nu c v hc V)
    filter_upwards [hs, hv] with x hx hvx
    intro hax
    have hz := summable_norm_iff.mpr hx
    simpa [hvx, A, hax, norm_mul] using hz
  filter_upwards [ae_all_iff.mpr hn] with x hx
  have hall : x ∈ ⋃ n, spanningSets nu n := by rw [iUnion_spanningSets]; trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hall
  exact hx n hn

/-- The pointwise series represents the given Hilbert-space sum on all inputs. -/
theorem series_representation (nu : Measure X) [SigmaFinite nu]
    (c : ι → ℂ) (v : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖c i‖ * ‖v i‖))
    (out : Lp ℂ 2 nu) (hout : HasSum (fun i => c i • v i) out) :
    (out : X → ℂ) =ᵐ[nu] (fun x => ∑' i, c i * v i x) := by
  have hlocal (A : Set X) (hA : MeasurableSet A) (hmu : nu A < ⊤) :
      Integrable (A.indicator (fun x => ∑' i, c i * v i x)) nu ∧
      (∫ x in A, out x ∂nu) = ∫ x in A, (∑' i, c i * v i x) ∂nu := by
    let V : Lp ℂ 2 nu := indicatorConstLp 2 hA hmu.ne 1
    have hi := tested_integrable nu c v V
    have hs := tested_cost nu c v hc V
    have hv : (V : X → ℂ) =ᵐ[nu] A.indicator (fun _ => (1 : ℂ)) :=
      indicatorConstLp_coeFn
    have he : (fun x => ∑' i, c i * v i x * star (V x)) =ᵐ[nu]
        A.indicator (fun x => ∑' i, c i * v i x) := by
      filter_upwards [hv] with x hx
      rw [tsum_mul_right, hx]
      by_cases ha : x ∈ A <;> simp [ha]
    refine ⟨(ReviewM.integrable_complex_series nu _ hi hs).1.congr he, ?_⟩
    have hp := (innerSL ℂ V).hasSum hout
    change HasSum (fun i => inner ℂ V (c i • v i)) (inner ℂ V out) at hp
    have hp' : HasSum (fun i => c i * inner ℂ V (v i)) (inner ℂ V out) := by
      simpa only [inner_smul_right] using hp
    rw [← L2.inner_indicatorConstLp_one hA hmu.ne, ← hp'.tsum_eq]
    have hcalc (i : ι) : (∫ x, c i * v i x * star (V x) ∂nu) =
        c i * inner ℂ V (v i) := by
      rw [L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, mul_assoc])
    calc
      _ = ∑' i, ∫ x, c i * v i x * star (V x) ∂nu :=
        tsum_congr fun i => (hcalc i).symm
      _ = ∫ x, ∑' i, c i * v i x * star (V x) ∂nu :=
        (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq
      _ = _ := by rw [integral_congr_ae he, integral_indicator hA]
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun A _ hmu => integrableOn_Lp_of_measure_ne_top out one_le_two hmu.ne)
    (fun A hA hmu => (integrable_indicator_iff hA).mp (hlocal A hA hmu).1)
  exact fun A hA hmu => (hlocal A hA hmu).2

/-- The same original-Haar series whose diagonal is used by HOperatorTrace.
Rows are precomposed with the operator; columns carry any left projection. -/
def kernel (nu : Measure X) (b : X → ℝ) (u v : ι → Lp ℂ 2 nu)
    (x y : X) : ℂ :=
  ∑' i, HNormalizedKernel.haarKernel b 1 (v i) (u i) x y

theorem kernel_eq (nu : Measure X) (b : X → ℝ) (u v : ι → Lp ℂ 2 nu)
    (x y : X) : kernel nu b u v x y =
      (∑' i, v i x * star (u i y)) * ((b y : ℂ) / (b x : ℂ)) := by
  unfold kernel
  rw [← tsum_mul_right]
  apply tsum_congr
  intro i
  simp only [HNormalizedKernel.haarKernel, Complex.ofReal_one, div_eq_mul_inv]
  ring

theorem row_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (u v : ι → Lp ℂ 2 nu) (F : Lp ℂ 2 nu) (x : X)
    (hx : Summable (fun i => ‖u i‖ * ‖v i x‖)) :
    Integrable (fun y => kernel nu b u v x y * (F y / (b y : ℂ))) nu ∧
    (b x : ℂ) * (∫ y, kernel nu b u v x y * (F y / (b y : ℂ)) ∂nu) =
      ∑' i, inner ℂ (u i) F * v i x := by
  let f : ι → X → ℂ := fun i y => v i x * star (u i y) * F y
  have hi (i : ι) : Integrable (f i) nu := by
    simpa only [f, Pi.mul_apply, mul_assoc] using
      (((Lp.memLp (u i)).star.integrable_mul (Lp.memLp F)).const_mul (v i x))
  have hbound (i : ι) : (∫ y, ‖f i y‖ ∂nu) ≤ (‖u i‖ * ‖v i x‖) * ‖F‖ := by
    simp only [f, norm_mul, norm_star, mul_assoc]
    rw [integral_const_mul]
    calc
      _ ≤ ‖v i x‖ * (‖u i‖ * ‖F‖) := mul_le_mul_of_nonneg_left
        (GPointwiseCore.integral_norm_product_le nu (u i) F) (norm_nonneg _)
      _ = _ := by ring
  have hs : Summable (fun i => ∫ y, ‖f i y‖ ∂nu) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hbound (hx.mul_right ‖F‖)
  have hsum := ReviewM.integrable_complex_series nu f hi hs
  have hf (i : ι) : (∫ y, f i y ∂nu) = inner ℂ (u i) F * v i x := by
    have he : f i = fun y => v i x * (F y * star (u i y)) := by
      funext y
      dsimp only [f]
      ring
    rw [he, integral_const_mul, HNormalizedKernel.l2_inner_formula]
    ring
  have hk (y : X) : kernel nu b u v x y * (F y / (b y : ℂ)) =
      (b x : ℂ)⁻¹ * (∑' i, f i y) := by
    have hy0 : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    rw [kernel_eq]
    dsimp only [f]
    rw [tsum_mul_right]
    field_simp
  simp_rw [hk]
  refine ⟨hsum.1.const_mul _, ?_⟩
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
  · exact (hasSum_integral_of_summable_integral_norm hi hs).tsum_eq.symm.trans
      (tsum_congr hf)
  · exact_mod_cast (ne_of_gt (hb x))

/-- Full-input integral action of a nuclear factor series. Scalar integrability
and the representative identity are proved from the same two hypotheses used
by H's operator-trace theorem. -/
theorem kernel_action (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hT : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i) (T F))
    (F : Lp ℂ 2 nu) :
    (∀ᵐ x ∂nu, Integrable
      (fun y => kernel nu b u v x y * (F y / (b y : ℂ))) nu) ∧
    (T F : X → ℂ) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, kernel nu b u v x y * (F y / (b y : ℂ)) ∂nu) := by
  have hcx : Summable (fun i => ‖(‖u i‖ : ℂ)‖ * ‖v i‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hc
  have hx := ae_column_cost nu (fun i => (‖u i‖ : ℂ)) v hcx
  have hx' : ∀ᵐ x ∂nu, Summable (fun i => ‖u i‖ * ‖v i x‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hx
  have hcF : Summable (fun i => ‖inner ℂ (u i) F‖ * ‖v i‖) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ (hc.mul_right ‖F‖)
    intro i
    calc
      _ ≤ (‖u i‖ * ‖F‖) * ‖v i‖ := mul_le_mul_of_nonneg_right
        (norm_inner_le_norm (u i) F) (norm_nonneg _)
      _ = _ := by ring
  have hout := series_representation nu (fun i => inner ℂ (u i) F) v hcF (T F) (hT F)
  constructor
  · filter_upwards [hx'] with x hx
    exact (row_action nu b hb u v F x hx).1
  · filter_upwards [hx', hout] with x hx hox
    exact hox.trans (row_action nu b hb u v F x hx).2.symm

/-- Admission and identification of the actual integral output in the completed
space follow from its proved action; they are not additional hypotheses. -/
theorem kernel_toLp (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hT : ∀ F, HasSum (fun i => inner ℂ (u i) F • v i) (T F))
    (F : Lp ℂ 2 nu) :
    let kF := fun x => (b x : ℂ) *
      ∫ y, kernel nu b u v x y * (F y / (b y : ℂ)) ∂nu
    ∃ hm : MemLp kF 2 nu, hm.toLp kF = T F := by
  dsimp only
  have hact := (kernel_action nu b hb T u v hc hT F).2
  have hm := (Lp.memLp (T F)).ae_eq hact
  refine ⟨hm, ?_⟩
  apply Lp.ext
  exact hm.coeFn_toLp.trans hact.symm

end
end DNuclearKernel


/- Insert after DNuclearKernelActionFragment. -/
namespace DNuclearKernel
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The nuclear cost proves convergence on the product measure, separately
from the direct diagonal series used for the trace. -/
theorem kernel_series_ae_summable (nu : Measure X) [SigmaFinite nu]
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    ∀ᵐ p : X × X ∂nu.prod nu,
      Summable (fun i => v i p.1 * star (u i p.2)) := by
  have hm (i : ι) : Measurable
      (fun p : X × X => ‖v i p.1 * star (u i p.2)‖ₑ) :=
    (((Lp.stronglyMeasurable (v i)).comp_measurable measurable_fst).mul
      ((Lp.stronglyMeasurable (u i)).star.comp_measurable measurable_snd)).measurable.enorm
  have hx : ∀ᵐ x ∂nu, Summable (fun i => ‖u i‖ * ‖v i x‖) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using
      ae_column_cost nu (fun i => (‖u i‖ : ℂ)) v
        (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_norm] using hc)
  have hxy : ∀ᵐ x ∂nu, ∀ᵐ y ∂nu,
      (∑' i, ‖v i x * star (u i y)‖ₑ) < ⊤ := by
    filter_upwards [hx] with x hxc
    have hxc' : Summable (fun i => ‖v i x‖ * ‖u i‖) := by
      simpa only [mul_comm] using hxc
    filter_upwards [ae_column_cost nu (fun i => v i x) u hxc'] with y hy
    have hn : Summable (fun i => ‖v i x * star (u i y)‖) := by
      simpa only [norm_mul, norm_star] using hy
    simp_rw [← ofReal_norm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg _) hn]
    exact ENNReal.ofReal_lt_top
  have hprod : ∀ᵐ p : X × X ∂nu.prod nu,
      (∑' i, ‖v i p.1 * star (u i p.2)‖ₑ) < ⊤ :=
    (Measure.ae_prod_iff_ae_ae
      (measurableSet_lt (Measurable.ennreal_tsum hm) measurable_const)).mpr hxy
  filter_upwards [hprod] with p hp
  apply Summable.of_norm
  have hn : (∑' i, (‖v i p.1 * star (u i p.2)‖₊ : ENNReal)) ≠ ⊤ := hp.ne
  exact NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hn)

/-- The full weighted kernel is measurable for the product of the original
Haar measure. Its action and diagonal are identified separately. -/
theorem kernel_aestronglyMeasurable (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hbm : Measurable b)
    (u v : ι → Lp ℂ 2 nu) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    AEStronglyMeasurable (fun p : X × X => kernel nu b u v p.1 p.2) (nu.prod nu) := by
  have hraw : AEStronglyMeasurable
      (fun p : X × X => ∑' i, v i p.1 * star (u i p.2)) (nu.prod nu) := by
    apply aestronglyMeasurable_of_tendsto_ae
      (atTop : Filter (Finset ι))
      (f := fun S p => ∑ i ∈ S, v i p.1 * star (u i p.2))
    · intro S
      apply Finset.aestronglyMeasurable_fun_sum
      intro i _
      exact (((Lp.stronglyMeasurable (v i)).comp_measurable measurable_fst).mul
        ((Lp.stronglyMeasurable (u i)).star.comp_measurable measurable_snd)).aestronglyMeasurable
    · filter_upwards [kernel_series_ae_summable nu u v hc] with p hp
      exact hp.hasSum
  simp_rw [kernel_eq]
  exact hraw.mul
    (((hbm.complex_ofReal.comp measurable_snd).div
      (hbm.complex_ofReal.comp measurable_fst)).aestronglyMeasurable)

end
end DNuclearKernel


-- CHECK CONTEXT: HCompressionTraceCheck exact proof context
set_option linter.unusedSectionVars false

namespace Masullo.TraceClass
open scoped InnerProductSpace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def stdHilbertBasis (𝕜 : Type*) [RCLike 𝕜] (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    HilbertBasis (exists_hilbertBasis 𝕜 E).choose 𝕜 E :=
  (exists_hilbertBasis 𝕜 E).choose_spec.choose
/-- Hilbert-basis trace, used below only after proving its HasSum statement. -/
def trace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, inner ℂ (stdHilbertBasis ℂ H i) (T (stdHilbertBasis ℂ H i))
end
end Masullo.TraceClass



-- EXACT FRAGMENT: HNuclearSupportFragment.lean
/- Source proof blocks generalized only in the nuclear index type from Masullo/Spectral/NuclearTrace.lean,
   through nuclear_diagonal_hasSum. Insert after HTraceFragment; no imports. -/
open scoped InnerProductSpace
namespace Masullo.NuclearDiagonal
variable {κ : Type*}

theorem rankOne_diagonal_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : ι → H) (hb : Orthonormal ℂ b) (u v : H) :
    Summable (fun i => ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ∧
    (∑' i, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
  have key (S : Finset ι) :
      ∑ i ∈ S, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
    have hn (i : ι) : ‖⟪u, b i⟫_ℂ‖ = ‖⟪b i, u⟫_ℂ‖ := norm_inner_symm _ _
    simp only [norm_mul, hn]
    calc
      _ ≤ Real.sqrt (∑ i ∈ S, ‖⟪b i, u⟫_ℂ‖ ^ 2) *
          Real.sqrt (∑ i ∈ S, ‖⟪b i, v⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (‖u‖ ^ 2) * Real.sqrt (‖v‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt (hb.sum_inner_products_le u))
          (Real.sqrt_le_sqrt (hb.sum_inner_products_le v))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖u‖ * ‖v‖ := by simp
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) key,
    le_of_tendsto (summable_of_sum_le (fun _ => norm_nonneg _) key).hasSum
      (Filter.Eventually.of_forall key)⟩

theorem nuclear_diagonal_interchange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun p : κ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) ∧
    (∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) =
      ∑' n, ⟪u n, v n⟫_ℂ := by
  have hf (n : κ) := rankOne_diagonal_bound b b.orthonormal (u n) (v n)
  have hs : Summable (fun n => ∑' i, ‖⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ‖) :=
    Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun n => (hf n).2) hc
  have hp : Summable (fun p : κ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) := by
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun n => (hf n).1, hs⟩
  refine ⟨hp, ?_⟩
  calc
    _ = ∑' n, ∑' i, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ := hp.of_norm.tsum_comm
    _ = _ := tsum_congr (fun n => (b.hasSum_inner_mul_inner (u n) (v n)).tsum_eq)


theorem nuclear_operator_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : κ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' n, ⟪u n, v n⟫_ℂ := by
  have hd (i : ι) :
      (∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [inner_smul_right] using hh.tsum_eq
  calc
    _ = ∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ :=
      tsum_congr (fun i => (hd i).symm)
    _ = _ := (nuclear_diagonal_interchange b u v hc).2

end Masullo.NuclearDiagonal

set_option maxHeartbeats 400000
namespace Masullo.NuclearSeries
variable {κ : Type*}
open scoped InnerProductSpace

/-- Absolute convergence is derived from the existing operator expansion.
Both summable costs and the genuine HasSum equation are indispensable. -/
theorem nuclear_diagonal_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : κ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    Summable (fun i => ‖⟪b i, T (b i)⟫_ℂ‖) := by
  let c : κ → ι → ℂ := fun n i => ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ
  have hp : Summable (fun p : κ × ι => ‖c p.1 p.2‖) :=
    (Masullo.NuclearDiagonal.nuclear_diagonal_interchange b u v hc).1
  have hs : Summable (fun p : ι × κ => ‖c p.2 p.1‖) := hp.prod_symm
  have hr : (∀ i, Summable (fun n => ‖c n i‖)) ∧
      Summable (fun i => ∑' n, ‖c n i‖) :=
    (summable_prod_of_nonneg (fun p : ι × κ => norm_nonneg (c p.2 p.1))).1 hs
  have hd (i : ι) : (∑' n, c n i) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [c, inner_smul_right] using hh.tsum_eq
  have hbound (i : ι) : ‖⟪b i, T (b i)⟫_ℂ‖ ≤ ∑' n, ‖c n i‖ := by
    calc
      ‖⟪b i, T (b i)⟫_ℂ‖ = ‖∑' n, c n i‖ := congrArg norm (hd i).symm
      _ ≤ ∑' n, ‖c n i‖ := norm_tsum_le_tsum_norm (hr.1 i)
  exact Summable.of_nonneg_of_le
    (fun i => norm_nonneg (⟪b i, T (b i)⟫_ℂ)) hbound hr.2

/-- The native application sets T = P.comp (A h). The theorem does not
assume summability of a prescribed zero sum or reverse the operator order. -/
theorem nuclear_diagonal_hasSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : κ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪u n, v n⟫_ℂ) := by
  have hs := (nuclear_diagonal_summable b T u v hc hT).of_norm.hasSum
  rwa [Masullo.NuclearDiagonal.nuclear_operator_diagonal b T u v hc hT] at hs


end Masullo.NuclearSeries


-- EXACT FRAGMENT: HNuclearTraceFragment.lean
/- Append after HTraceFragment and HNuclearSupportFragment. -/
namespace HOperatorTrace
open ContinuousLinearMap Filter
open scoped InnerProductSpace Topology
noncomputable section
variable {κ : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical Hilbert-basis trace of the actual completed operator.
Both the norm cost and the equation on every input are retained explicitly. -/
theorem nuclear_trace (T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) :
    Masullo.TraceClass.trace T = ∑' n, inner ℂ (u n) (v n) :=
  Masullo.NuclearDiagonal.nuclear_operator_diagonal
    (Masullo.TraceClass.stdHilbertBasis ℂ H) T u v hc hT

/-- The same trace is an absolutely convergent diagonal in every Hilbert basis. -/
theorem nuclear_trace_basis (T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x))
    {ι : Type*} (e : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖inner ℂ (e i) (T (e i))‖) ∧
    HasSum (fun i => inner ℂ (e i) (T (e i))) (Masullo.TraceClass.trace T) := by
  rw [nuclear_trace T u v hc hT]
  exact ⟨Masullo.NuclearSeries.nuclear_diagonal_summable e T u v hc hT,
    Masullo.NuclearSeries.nuclear_diagonal_hasSum e T u v hc hT⟩

/-- Any bounded left factor acts on the output columns, with its actual norm. -/
theorem nuclear_left_cost (P : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun n => ‖u n‖ * ‖P (v n)‖) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) (hc.mul_left ‖P‖)
  calc
    ‖u n‖ * ‖P (v n)‖ ≤ ‖u n‖ * (‖P‖ * ‖v n‖) :=
      mul_le_mul_of_nonneg_left (P.le_opNorm (v n)) (norm_nonneg _)
    _ = ‖P‖ * (‖u n‖ * ‖v n‖) := by ring

theorem nuclear_left_factor (P T : H →L[ℂ] H) (u v : κ → H)
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) (x : H) :
    HasSum (fun n => inner ℂ (u n) x • P (v n)) ((P.comp T) x) := by
  have h := P.hasSum (hT x)
  simpa only [map_smul, ContinuousLinearMap.comp_apply] using h

/-- Convolution-first order is preserved by construction; no cyclicity is used. -/
theorem nuclear_left_trace (P T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) :
    Masullo.TraceClass.trace (P.comp T) = ∑' n, inner ℂ (u n) (P (v n)) :=
  nuclear_trace (P.comp T) u (fun n => P (v n))
    (nuclear_left_cost P u v hc) (nuclear_left_factor P T u v hT)

/-- Projection-complement trace with the literal minus sign. -/
theorem nuclear_complement_trace (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (u v : κ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => inner ℂ (u n) x • v n) (T x)) :
    Masullo.TraceClass.trace (((1 : H →L[ℂ] H) - S.starProjection).comp T) =
      ∑' n, inner ℂ (u n) (v n - S.starProjection (v n)) := by
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
    nuclear_left_trace ((1 : H →L[ℂ] H) - S.starProjection) T u v hc hT

end
end HOperatorTrace


-- EXACT FRAGMENT: HCompressionExtensionFragment.lean
/- Append after HNuclearTraceFragment. This transfers a nuclear expansion on
   the actual geometric spectral subspace to the ambient PA operator. -/
namespace HOperatorTrace
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compressed operator extends to exactly PA when the already-proved
source-invariance equation PA S=0 is supplied. No AP commutation is used. -/
theorem source_compression_extension (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0) :
    Sᗮ.subtypeL.comp ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)).comp
      Sᗮ.orthogonalProjection) = ((1 : H →L[ℂ] H)-S.starProjection).comp A := by
  apply ContinuousLinearMap.ext
  intro x
  have hz' : A (S.starProjection x) - S.starProjection (A (S.starProjection x)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply, ContinuousLinearMap.zero_apply] using
        congrArg (fun T : H →L[ℂ] H => T x) hz
  change Sᗮ.starProjection (A (Sᗮ.starProjection x)) = A x-S.starProjection (A x)
  simp only [Submodule.starProjection_orthogonal_val, map_sub]
  rw [(sub_eq_zero.mp hz').symm]
  abel

end
end HOperatorTrace


-- EXACT FRAGMENT: HCompressionTraceFragment.lean
/- Append after HNuclearTraceFragment and HCompressionExtensionFragment. This transfers a nuclear expansion on
   the actual geometric spectral subspace to the ambient PA operator. -/
namespace HOperatorTrace
open ContinuousLinearMap
open scoped InnerProductSpace
noncomputable section
variable {κ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Extend a nuclear expansion from the actual geometric subspace to its
ambient orthogonal extension. This generic intermediate keeps subtype
elaboration separate from the concrete PA compression. -/
theorem orthogonal_extension_factor (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (B : E →L[ℂ] E) (u v : κ → E)
    (hB : ∀ y : E, HasSum (fun i => inner ℂ (u i) y • v i) (B y)) (x : H) :
    HasSum (fun i => inner ℂ (u i : H) x • (v i : H))
      ((E.subtypeL.comp (B.comp E.orthogonalProjection)) x) := by
  have h := E.subtypeL.hasSum (hB (E.orthogonalProjection x))
  have hi (i : κ) : inner ℂ (u i) (E.orthogonalProjection x) =
      inner ℂ (u i : H) x := by
    change inner ℂ (u i : H) (E.starProjection x) = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (u i).property]
  simpa only [map_smul, hi, ContinuousLinearMap.comp_apply] using h

/-- A proved nuclear factorization of the compression yields a nuclear
factorization of the actual ambient PA, with the same norm-product cost. -/
theorem source_compression_factor (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0)
    (u v : κ → Sᗮ)
    (hB : ∀ y : Sᗮ, HasSum (fun i => inner ℂ (u i) y • v i)
      ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) y)) (x : H) :
    HasSum (fun i => inner ℂ (u i : H) x • (v i : H))
      ((((1 : H →L[ℂ] H)-S.starProjection).comp A) x) := by
  have h := orthogonal_extension_factor Sᗮ
    (Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) u v hB x
  rw [source_compression_extension S A hz] at h
  exact h

/-- The global ambient PA trace is the trace of its actual compression,
with nuclearity witnessed by the supplied summable factorization there. -/
theorem source_compression_trace (S : Submodule ℂ H) [S.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hz : ((((1 : H →L[ℂ] H)-S.starProjection).comp A).comp S.starProjection) = 0)
    (u v : κ → Sᗮ) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hB : ∀ y : Sᗮ, HasSum (fun i => inner ℂ (u i) y • v i)
      ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) y)) :
    Masullo.TraceClass.trace (((1 : H →L[ℂ] H)-S.starProjection).comp A) =
      Masullo.TraceClass.trace (Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) := by
  rw [nuclear_trace _ (fun i => (u i : H)) (fun i => (v i : H)) hc
    (source_compression_factor S A hz u v hB), nuclear_trace _ u v hc hB]
  rfl

end
end HOperatorTrace

-- CHECK CONTEXT: MSeriesFragment through diagonal_series
/- Insert after HNormalizedKernel and ReviewM's partition fragment. -/
namespace HNormalizedKernel
open MeasureTheory Filter
open scoped BigOperators Topology
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Explicit Holder cost of the two normalized L2 rows. -/
def diagonalL2Cost (nu : Measure X) (U R : Lp ℂ 2 nu) : ℝ :=
  (∫ x, ‖U x‖ ^ (2 : ℝ) ∂nu) ^ (1 / (2 : ℝ)) *
    (∫ x, ‖R x‖ ^ (2 : ℝ) ∂nu) ^ (1 / (2 : ℝ))

/-- The original-Haar volume cancels in the absolute diagonal estimate too. -/
theorem diagonal_integral_norm_le (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : Lp ℂ 2 nu) :
    (∫ x, ‖haarKernel b V U R x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      diagonalL2Cost nu U R := by
  simp_rw [diagonal_formula b hb, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hV, norm_star]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hV.le]
  rw [integral_const_mul]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hV), one_mul]
  have hU : MemLp (fun x => (U x : ℂ)) (ENNReal.ofReal (2 : ℝ)) nu := by
    simpa using Lp.memLp U
  have hR : MemLp (fun x => (R x : ℂ)) (ENNReal.ofReal (2 : ℝ)) nu := by
    simpa using Lp.memLp R
  exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hU hR

/-- The SAME Haar kernel rows have the expected diagonal coefficient series.
The summability of their explicit L2 costs is the remaining analytic input. -/
theorem diagonal_series (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => diagonalL2Cost nu (U i) (R i))) :
    HasSum (fun i => inner ℂ (R i) (U i))
      (∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu)) := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hs : Summable (fun i => ∫ x,
      ‖haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) :=
    Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _))
      (fun i => diagonal_integral_norm_le nu b hb V hV (U i) (R i)) hcost
  simpa only [diagonal_integral nu b hb V hV] using
    hasSum_integral_of_summable_integral_norm hi hs


end
end HNormalizedKernel

-- CHECK CONTEXT: MNormCostFragment
/- Insert after MSeriesFragment; uses H's exact original-Haar rows. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The integral Holder cost is exactly the Hilbert norm-product nuclear cost. -/
theorem diagonalL2Cost_eq_norm_mul (nu : Measure X) (U R : Lp ℂ 2 nu) :
    diagonalL2Cost nu U R = ‖U‖ * ‖R‖ := by
  have hsq (F : Lp ℂ 2 nu) :
      (∫ x, ‖F x‖ ^ (2 : ℝ) ∂nu) = ‖F‖ ^ 2 := by
    calc
      _ = ∫ x, inner ℝ (F x) (F x) ∂nu := by
        simp only [real_inner_self_eq_norm_sq, Real.rpow_two]
      _ = inner ℝ F F := (L2.inner_def F F).symm
      _ = ‖F‖ ^ 2 := real_inner_self_eq_norm_sq F
  unfold diagonalL2Cost
  rw [hsq U, hsq R, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (norm_nonneg U), Real.sqrt_sq (norm_nonneg R)]

/-- Summable Hilbert factors discharge the original-Haar diagonal cost. -/
theorem diagonal_series_of_norm_cost {ι : Type*} [Countable ι]
    (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hcost : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    HasSum (fun i => inner ℂ (R i) (U i))
      (∫ x, ∑' i, haarKernel b V (U i) (R i) x x ∂(ENNReal.ofReal V • nu)) := by
  apply diagonal_series nu b hb V hV U R
  simpa only [diagonalL2Cost_eq_norm_mul] using hcost

end
end HNormalizedKernel

-- CHECK CONTEXT: MNuclearDiagonalFragment nuclear_diagonal_integrable only
namespace HNormalizedKernel
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The actual original-Haar row series has an integrable diagonal with the
same total nuclear cost, without any further weight or volume factor. -/
theorem nuclear_diagonal_integrable (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu)
    (hc : Summable (fun i => ‖U i‖ * ‖R i‖)) :
    Integrable (fun x => ∑' i, haarKernel b V (U i) (R i) x x)
      (ENNReal.ofReal V • nu) ∧
    (∫ x, ‖∑' i, haarKernel b V (U i) (R i) x x‖ ∂(ENNReal.ofReal V • nu)) ≤
      ∑' i, ‖U i‖ * ‖R i‖ := by
  have hi (i : ι) := diagonal_integrable nu b hb V (U i) (R i)
  have hmajor (i : ι) : (∫ x, ‖haarKernel b V (U i) (R i) x x‖
      ∂(ENNReal.ofReal V • nu)) ≤ ‖U i‖ * ‖R i‖ := by
    simpa only [diagonalL2Cost_eq_norm_mul] using
      diagonal_integral_norm_le nu b hb V hV (U i) (R i)
  have hs := Summable.of_nonneg_of_le
    (fun i => integral_nonneg fun x => norm_nonneg _) hmajor hc
  have h := ReviewM.integrable_complex_series (ENNReal.ofReal V • nu) _ hi hs
  exact ⟨h.1, h.2.trans (hs.tsum_le_tsum hmajor hc)⟩


end
end HNormalizedKernel

-- CHECK CONTEXT: HNuclearKernelFragment nuclear_kernel_trace only
/- Append after HNuclearTraceFragment and MNormCostFragment. -/
namespace HOperatorTrace
open MeasureTheory Filter
open scoped InnerProductSpace Topology
noncomputable section
variable {κ : Type*} [Countable κ]
variable {X : Type*} [MeasurableSpace X]

/-- The original-Haar diagonal of the very same nuclear rows is the actual
completed operator trace. The two analytic assumptions have distinct roles:
`hT` attaches the rows to T, and `hc` provides absolute convergence. -/
theorem nuclear_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (T : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (u v : κ → Lp ℂ 2 nu)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ F, HasSum (fun n => inner ℂ (u n) F • v n) (T F)) :
    (∫ x, ∑' n, HNormalizedKernel.haarKernel b V (v n) (u n) x x
      ∂(ENNReal.ofReal V • nu)) = Masullo.TraceClass.trace T := by
  rw [nuclear_trace T u v hc hT]
  exact (HNormalizedKernel.diagonal_series_of_norm_cost nu b hb V hV v u
    (by simpa only [mul_comm] using hc)).tsum_eq.symm


end
end HOperatorTrace

-- CHECK CONTEXT: DNuclearCompressionFragment
/- Insert after DNuclearKernelMeasurableFragment and the H nuclear diagonal,
   trace and compression fragments. The arithmetic factor estimate remains an
   explicit application obligation; this theorem only transports proved factors. -/
namespace DNuclearKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- Compression factors produce one measurable original-Haar kernel of the
genuine left projected operator, with full-input action and its actual trace.
No nuclearity hypothesis about the free convolution is used. -/
theorem source_compression_kernel (nu : Measure X) [SigmaFinite nu]
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (hbm : Measurable b)
    (S : Submodule ℂ (Lp ℂ 2 nu)) [S.HasOrthogonalProjection]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (hz : ((((1 : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)-S.starProjection).comp A).comp
      S.starProjection) = 0)
    (u v : ι → Sᗮ) (hc : Summable (fun i => ‖u i‖ * ‖v i‖))
    (hB : ∀ y : Sᗮ, HasSum (fun i => inner ℂ (u i) y • v i)
      ((Sᗮ.orthogonalProjection.comp (A.comp Sᗮ.subtypeL)) y)) :
    let k := kernel nu b (fun i => (u i : Lp ℂ 2 nu)) (fun i => (v i : Lp ℂ 2 nu))
    let PA := Sᗮ.starProjection.comp A
    AEStronglyMeasurable (fun p : X × X => k p.1 p.2) (nu.prod nu) ∧
    (∀ F : Lp ℂ 2 nu,
      (∀ᵐ x ∂nu, Integrable (fun y => k x y * (F y / (b y : ℂ))) nu) ∧
      (PA F : X → ℂ) =ᵐ[nu]
        (fun x => (b x : ℂ) * ∫ y, k x y * (F y / (b y : ℂ)) ∂nu)) ∧
    Integrable (fun x => k x x) nu ∧
    (∫ x, k x x ∂nu) = Masullo.TraceClass.trace PA := by
  dsimp only
  have hcost : Summable (fun i => ‖(u i : Lp ℂ 2 nu)‖ * ‖(v i : Lp ℂ 2 nu)‖) := hc
  have hfactor (F : Lp ℂ 2 nu) :
      HasSum (fun i => inner ℂ (u i : Lp ℂ 2 nu) F • (v i : Lp ℂ 2 nu))
        ((Sᗮ.starProjection.comp A) F) := by
    simpa only [ContinuousLinearMap.comp_apply, Submodule.starProjection_orthogonal_val,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using
      HOperatorTrace.source_compression_factor S A hz u v hB F
  refine ⟨kernel_aestronglyMeasurable nu b hbm _ _ hcost,
    (fun F => kernel_action nu b hb (Sᗮ.starProjection.comp A) _ _ hcost hfactor F), ?_, ?_⟩
  · simpa only [kernel, ENNReal.ofReal_one, one_smul] using
      (HNormalizedKernel.nuclear_diagonal_integrable nu b hb 1 (by norm_num)
        (fun i => (v i : Lp ℂ 2 nu)) (fun i => (u i : Lp ℂ 2 nu))
        (by simpa only [mul_comm] using hcost)).1
  · simpa only [kernel, ENNReal.ofReal_one, one_smul] using
      HOperatorTrace.nuclear_kernel_trace nu b hb 1 (by norm_num)
        (Sᗮ.starProjection.comp A) (fun i => (u i : Lp ℂ 2 nu))
        (fun i => (v i : Lp ℂ 2 nu)) hcost hfactor

end
end DNuclearKernel

#check DNuclearKernel.source_compression_kernel
#print axioms DNuclearKernel.source_compression_kernel
