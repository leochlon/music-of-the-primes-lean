import Mathlib

/-! Original-measure shell estimates for B35 (35.7)--(35.8).
The measure is never silently replaced by normalized Haar. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace BReview
variable {X E : Type*} [MeasurableSpace X] (mu : Measure X)

theorem mask_integrable (f : X → ℂ) (hf : Integrable f mu)
    (p : X → ℝ) (hp : Measurable p)
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) :
    Integrable (fun x => (p x : ℂ) * f x) mu := by
  apply hf.norm.mono'
    (((Complex.continuous_ofReal.measurable.comp hp).aestronglyMeasurable).mul
      hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 x)]
  exact (mul_le_mul_of_nonneg_right (hp1 x) (norm_nonneg _)).trans_eq (one_mul _)

theorem finite_shell_contraction (F : Finset E) (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ x, ∑ e ∈ F, p e x ≤ 1)
    (f : X → ℂ) (hf : Integrable f mu) :
    (∑ e ∈ F, ‖∫ x, (p e x : ℂ) * f x ∂mu‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  have hp1 (e : E) (he : e ∈ F) (x : X) : p e x ≤ 1 := by
    exact (Finset.single_le_sum (fun j _ => hp0 j x) he).trans (hpart x)
  have hi (e : E) (he : e ∈ F) :=
    mask_integrable mu f hf (p e) (hp e) (hp0 e) (hp1 e he)
  calc
    _ ≤ ∑ e ∈ F, ∫ x, ‖(p e x : ℂ) * f x‖ ∂mu := by
      apply Finset.sum_le_sum
      intro e he
      exact norm_integral_le_integral_norm _
    _ = ∫ x, ∑ e ∈ F, ‖(p e x : ℂ) * f x‖ ∂mu := by
      symm
      exact integral_finset_sum F (fun e he => (hi e he).norm)
    _ ≤ ∫ x, ‖f x‖ ∂mu := by
      apply integral_mono (integrable_finset_sum F (fun e he => (hi e he).norm)) hf.norm
      intro x
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp0 _ _)]
      rw [← Finset.sum_mul]
      exact (mul_le_mul_of_nonneg_right (hpart x) (norm_nonneg _)).trans_eq (one_mul _)

theorem all_shell_contraction (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f : X → ℂ) (hf : Integrable f mu) :
    Summable (fun e => ‖∫ x, (p e x : ℂ) * f x ∂mu‖) ∧
    (∑' e, ‖∫ x, (p e x : ℂ) * f x ∂mu‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  have hs : Summable (fun e => ‖∫ x, (p e x : ℂ) * f x ∂mu‖) :=
    summable_of_sum_le (fun e => norm_nonneg _)
      (fun F => finite_shell_contraction mu F p hp hp0 (hpart F) f hf)
  exact ⟨hs, le_of_tendsto hs.hasSum (Eventually.of_forall
    (fun F => finite_shell_contraction mu F p hp hp0 (hpart F) f hf))⟩

theorem shell_difference_bound (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f g : X → ℂ) (hf : Integrable f mu) (hg : Integrable g mu) :
    (∑' e, ‖(∫ x, (p e x : ℂ) * f x ∂mu) -
      (∫ x, (p e x : ℂ) * g x ∂mu)‖) ≤ ∫ x, ‖f x-g x‖ ∂mu := by
  classical
  have hp1 (e : E) (x : X) : p e x ≤ 1 := by
    simpa using hpart {e} x
  have he (e : E) :
      (∫ x, (p e x : ℂ) * (f x-g x) ∂mu) =
      (∫ x, (p e x : ℂ) * f x ∂mu) - (∫ x, (p e x : ℂ) * g x ∂mu) := by
    simp_rw [mul_sub]
    exact integral_sub
      (mask_integrable mu f hf (p e) (hp e) (hp0 e) (hp1 e))
      (mask_integrable mu g hg (p e) (hp e) (hp0 e) (hp1 e))
  simpa only [he] using
    (all_shell_contraction mu p hp hp0 hpart (fun x => f x-g x) (hf.sub hg)).2

theorem all_shell_L1_limit (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f : ℕ → X → ℂ) (g : X → ℂ)
    (hf : ∀ n, Integrable (f n) mu) (hg : Integrable g mu)
    (hlim : Tendsto (fun n => ∫ x, ‖f n x-g x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) * f n x ∂mu) -
      (∫ x, (p e x : ℂ) * g x ∂mu)‖) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => tsum_nonneg (fun e => norm_nonneg _))
    (fun n => shell_difference_bound mu p hp hp0 hpart (f n) g (hf n) hg) hlim

theorem physical_tail_limit (f : X → ℂ) (hf : Integrable f mu)
    (chi : ℕ → X → ℝ) (hm : ∀ n, Measurable (chi n))
    (h0 : ∀ n x, 0 ≤ chi n x) (h1 : ∀ n x, chi n x ≤ 1)
    (hc : ∀ x, Tendsto (fun n => chi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, (1-chi n x)*‖f x‖ ∂mu) atTop (𝓝 0) := by
  have hb (n : ℕ) : ∀ᵐ x ∂mu, ‖(1-chi n x)*‖f x‖‖ ≤ ‖f x‖ := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (h1 n x)) (norm_nonneg _))]
    exact (mul_le_mul_of_nonneg_right (by linarith [h0 n x] : 1-chi n x ≤ 1)
      (norm_nonneg _)).trans_eq (one_mul _)
  have hl : ∀ᵐ x ∂mu, Tendsto (fun n => (1-chi n x)*‖f x‖) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with x
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub (hc x)).mul_const ‖f x‖
  simpa using tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => ((measurable_const.sub (hm n)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable.norm) hf.norm hb hl

theorem physical_shell_limit (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ (F : Finset E) x, ∑ e ∈ F, p e x ≤ 1)
    (f : X → ℂ) (hf : Integrable f mu)
    (chi : ℕ → X → ℝ) (hm : ∀ n, Measurable (chi n))
    (h0 : ∀ n x, 0 ≤ chi n x) (h1 : ∀ n x, chi n x ≤ 1)
    (hc : ∀ x, Tendsto (fun n => chi n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∑' e, ‖(∫ x, (p e x : ℂ) * ((chi n x : ℂ)*f x) ∂mu) -
      (∫ x, (p e x : ℂ) * f x ∂mu)‖) atTop (𝓝 0) := by
  apply all_shell_L1_limit mu p hp hp0 hpart
    (fun n x => (chi n x : ℂ)*f x) f
    (fun n => mask_integrable mu f hf (chi n) (hm n) (h0 n) (h1 n)) hf
  have he (n : ℕ) (x : X) :
      ‖(chi n x : ℂ)*f x-f x‖ = (1-chi n x)*‖f x‖ := by
    have heq : (chi n x : ℂ)*f x-f x = -(((1-chi n x : ℝ) : ℂ)*f x) := by
      push_cast
      ring
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (h1 n x))]
  simpa only [he] using physical_tail_limit mu f hf chi hm h0 h1 hc

theorem shell_reconstruction [Countable E] (p : E → X → ℝ)
    (hp : ∀ e, Measurable (p e)) (hp0 : ∀ e x, 0 ≤ p e x)
    (hpart : ∀ x, HasSum (fun e => p e x) 1)
    (f : X → ℂ) (hf : Integrable f mu) :
    HasSum (fun e => ∫ x, (p e x : ℂ)*f x ∂mu) (∫ x, f x ∂mu) := by
  classical
  have hsub (F : Finset E) (x : X) : ∑ e ∈ F, p e x ≤ 1 := by
    simpa only [(hpart x).tsum_eq] using
      (hpart x).summable.sum_le_tsum F (fun e _ => hp0 e x)
  have hp1 (e : E) (x : X) : p e x ≤ 1 := by simpa using hsub {e} x
  have hi (e : E) := mask_integrable mu f hf (p e) (hp e) (hp0 e) (hp1 e)
  have hb (F : Finset E) :
      (∑ e ∈ F, ∫ x, ‖(p e x : ℂ)*f x‖ ∂mu) ≤ ∫ x, ‖f x‖ ∂mu := by
    rw [← integral_finset_sum F (fun e _ => (hi e).norm)]
    apply integral_mono (integrable_finset_sum F (fun e _ => (hi e).norm)) hf.norm
    intro x
    simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp0 _ _)]
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (hsub F x) (norm_nonneg _)).trans_eq (one_mul _)
  have hs : Summable (fun e => ∫ x, ‖(p e x : ℂ)*f x‖ ∂mu) :=
    summable_of_sum_le (fun e => integral_nonneg (fun x => norm_nonneg _)) hb
  have he (x : X) : (∑' e, (p e x : ℂ)*f x) = f x := by
    have ht := ((Complex.ofRealCLM.hasSum (hpart x)).mul_right (f x)).tsum_eq
    simpa using ht
  simpa only [he] using hasSum_integral_of_summable_integral_norm hi hs

end BReview
#print axioms BReview.mask_integrable
#print axioms BReview.finite_shell_contraction
