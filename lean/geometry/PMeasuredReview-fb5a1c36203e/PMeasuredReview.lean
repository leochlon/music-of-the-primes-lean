import Mathlib

-- Reviewed assembly: P Haar normalization, I cutoff/remainder, N positive shells.

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace POriginalHaar

/-- The scalar change from normalized quotient Haar ν to μ=Vν.
This is an equality of actual Bochner integrals, including its 1/V. -/
theorem original_haar_integral {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (V : ℝ) (hV : 0 < V) (d : X → ℂ) :
    (∫ x, (V : ℂ)⁻¹ * d x ∂(ENNReal.ofReal V • nu)) = ∫ x, d x ∂nu := by
  rw [integral_smul_measure, integral_const_mul]
  rw [ENNReal.toReal_ofReal hV.le]
  change (V : ℂ) * ((V : ℂ)⁻¹ * ∫ x, d x ∂nu) = _
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hV)), one_mul]

/-- The original-Haar rank-one density of normalized L2 columns.
For F=√w f and G=√w g this is (w/V) f conj(g). -/
theorem rank_one_original_haar {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (V : ℝ) (hV : 0 < V) (F G : Lp ℂ 2 nu) :
    (∫ x, (V : ℂ)⁻¹ * (F x * star (G x))
      ∂(ENNReal.ofReal V • nu)) = inner ℂ G F := by
  rw [original_haar_integral nu V hV, L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by simp [RCLike.inner_apply])

/-- Weight cancellation is pointwise, so it can be used on the specified
rank-one diagonal; it does not restrict a product-a.e. representative. -/
theorem weighted_rank_one_density (r V : ℝ) (f g : ℂ) :
    (V : ℂ)⁻¹ * (((r : ℂ) * f) * star ((r : ℂ) * g)) =
      ((r*r/V : ℝ) : ℂ) * f * star g := by
  have hr : star (r : ℂ) = (r : ℂ) := by simp
  rw [star_mul, hr]
  push_cast
  ring

end POriginalHaar

#print axioms POriginalHaar.original_haar_integral
#print axioms POriginalHaar.rank_one_original_haar
#print axioms POriginalHaar.weighted_rank_one_density


/-! I35 (35.7)-(35.9): the finite source term and narrow compensator are
retained under the SAME original-Haar mask. No arithmetic density identity
or nuclearity is asserted by this analytic lemma. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace ReviewI
variable {X : Type*} [MeasurableSpace X]

def masked (mu : Measure X) (w f : X → ℂ) : ℂ := ∫ x, w x * f x ∂mu

theorem masked_integrable (mu : Measure X) (w f : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => w x * f x) mu := by
  apply hf.norm.mono' (hw.mul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖w x * f x‖ ≤ ‖f x‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

theorem masked_sub (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    masked mu w (fun x => f x-g x) = masked mu w f-masked mu w g := by
  simp only [masked, mul_sub]
  exact integral_sub (masked_integrable mu w f hw hb hf)
    (masked_integrable mu w g hw hb hg)

theorem masked_error_le (mu : Measure X) (w f g : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hf : Integrable f mu) (hg : Integrable g mu) :
    ‖masked mu w f-masked mu w g‖ ≤ ∫ x, ‖f x-g x‖ ∂mu := by
  rw [← masked_sub mu w f g hw hb hf hg]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (masked_integrable mu w _ hw hb (hf.sub hg)).norm (hf.sub hg).norm
  filter_upwards [hb] with x hx
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- `wide=d_beta(T_beta)`, `narrow=d_alpha(T_alpha)`,
`sandwich=d_beta(S_e T_beta S_e)`, `regularized=d_alpha(R_e T_alpha R_e)`.
The source transport is `sandwich-regularized`. -/
theorem finite_source_compensator_integral
    (mu : Measure X) (w wide narrow sandwich regularized : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hsand : Integrable sandwich mu) (hreg : Integrable regularized mu) :
    masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich x-regularized x)
      +masked mu w (fun x => narrow x-regularized x) =
    masked mu w (fun x => wide x-sandwich x) := by
  rw [masked_sub mu w sandwich regularized hw hb hsand hreg,
    masked_sub mu w narrow regularized hw hb hnarrow hreg,
    masked_sub mu w wide sandwich hw hb hwide hsand]
  ring

/-- The low-energy cutoff converges to the full-input LEFT correction under
any bounded physical/shell mask. The source identity is not replaced by
its total trace; the regularization compensator is present at every n. -/
theorem regularized_source_shell_limit
    (mu : Measure X) (w wide narrow full : X → ℂ)
    (sandwich regularized : ℕ → X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hfull : Integrable full mu)
    (hsand : ∀ n, Integrable (sandwich n) mu)
    (hreg : ∀ n, Integrable (regularized n) mu)
    (hlim : Tendsto (fun n => ∫ x, ‖sandwich n x-full x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) atTop
      (𝓝 (masked mu w (fun x => wide x-full x))) := by
  have ht : Tendsto (fun n => masked mu w (sandwich n)) atTop
      (𝓝 (masked mu w full)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => masked_error_le mu w (sandwich n) full hw hb (hsand n) hfull) hlim
  have he : (fun n => masked mu w wide-masked mu w narrow
      -masked mu w (fun x => sandwich n x-regularized n x)
      +masked mu w (fun x => narrow x-regularized n x)) =
      (fun n => masked mu w wide-masked mu w (sandwich n)) := by
    funext n
    rw [finite_source_compensator_integral mu w wide narrow (sandwich n)
      (regularized n) hw hb hwide hnarrow (hsand n) (hreg n),
      masked_sub mu w wide (sandwich n) hw hb hwide (hsand n)]
  rw [he, masked_sub mu w wide full hw hb hwide hfull]
  exact tendsto_const_nhds.sub ht

/-- Physical exhaustion is justified from an actual integrable Haar density. -/
theorem physical_cutoff_limit (mu : Measure X) (d : X → ℂ) (w : ℕ → X → ℂ)
    (hd : Integrable d mu) (hw : ∀ n, AEStronglyMeasurable (w n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖w n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => w n x) atTop (𝓝 1)) :
    Tendsto (fun n => masked mu (w n) d) atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · intro n
    exact (hw n).mul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    filter_upwards [hb n] with x hx
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [hl] with x hx
    simpa using hx.mul (tendsto_const_nhds (x := d x))

/-- The physical tail is retained as an integral before taking a limit. -/
theorem physical_tail_identity (mu : Measure X) (w d : X → ℂ)
    (hw : AEStronglyMeasurable w mu) (hb : ∀ᵐ x ∂mu, ‖w x‖ ≤ 1)
    (hd : Integrable d mu) :
    (∫ x, d x ∂mu)-masked mu w d = ∫ x, (1-w x)*d x ∂mu := by
  simp only [sub_mul, one_mul, masked]
  exact (integral_sub hd (masked_integrable mu w d hw hb hd)).symm

/-- If the full explicit formula is pole - all zeros, and the native trace
is interior + admitted edge, the correction is omitted - admitted edge. -/
theorem omitted_edge_remainder (pole geometric interior edge omitted spectral : ℂ)
    (hfull : geometric = pole-(interior+omitted))
    (hspec : spectral = interior+edge) :
    pole-geometric-spectral = omitted-edge := by
  rw [hfull, hspec]
  ring

end ReviewI
#print axioms ReviewI.finite_source_compensator_integral
#print axioms ReviewI.regularized_source_shell_limit
#print axioms ReviewI.physical_cutoff_limit
#print axioms ReviewI.omitted_edge_remainder


open MeasureTheory Filter
open scoped BigOperators Topology

namespace NMeasuredShells

variable {X E : Type*} [MeasurableSpace X]

/-- Shell pairing always uses the original quotient Haar measure `mu`. -/
noncomputable def shell (mu : Measure X) (p : X → ℝ) (f : X → ℂ) : ℂ :=
  ∫ x, (p x : ℂ) * f x ∂mu

/-- Bounded measurable shell masks need no separate integrability assumption. -/
theorem masked_integrable (mu : Measure X) (p : X → ℝ) (f : X → ℂ)
    (hp : Measurable p) (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1)
    (hf : Integrable f mu) : Integrable (fun x => (p x : ℂ) * f x) mu := by
  apply hf.norm.mono'
    ((Complex.continuous_ofReal.measurable.comp hp).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p x : ℂ) * f x‖ ≤ ‖f x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
  simpa using mul_le_mul_of_nonneg_right (h1 x) (norm_nonneg (f x))

/-- A finite set of positive descended masks may overlap. -/
theorem finite_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ)
    (hf : Integrable f mu)
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1)
    (hi : ∀ e ∈ F, Integrable (fun x => (p e x : ℂ) * f x) mu) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  calc
    _ ≤ ∑ e ∈ F, ∫ x, ‖(p e x : ℂ) * f x‖ ∂mu := by
      exact Finset.sum_le_sum (fun e he => norm_integral_le_integral_norm _)
    _ = ∫ x, ∑ e ∈ F, ‖(p e x : ℂ) * f x‖ ∂mu := by
      symm
      exact integral_finset_sum F (fun e he => (hi e he).norm)
    _ ≤ ∫ x, ‖f x‖ ∂mu := by
      apply integral_mono
        (integrable_finset_sum F (fun e he => (hi e he).norm)) hf.norm
      intro x
      calc
        (∑ e ∈ F, ‖(p e x : ℂ) * f x‖) = (∑ e ∈ F, p e x) * ‖f x‖ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e he
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp e he x)]
        _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right (hs x) (norm_nonneg _)
        _ = ‖f x‖ := one_mul _

/-- Discharges mask integrability for the positive overlapping partition. -/
theorem measurable_shell_contraction (mu : Measure X) (F : Finset E)
    (p : E → X → ℝ) (f : X → ℂ) (hf : Integrable f mu)
    (hm : ∀ e ∈ F, Measurable (p e))
    (hp : ∀ e ∈ F, ∀ x, 0 ≤ p e x)
    (hs : ∀ x, ∑ e ∈ F, p e x ≤ 1) :
    (∑ e ∈ F, ‖shell mu (p e) f‖) ≤ ∫ x, ‖f x‖ ∂mu := by
  apply finite_shell_contraction mu F p f hf hp hs
  intro e he
  apply masked_integrable mu (p e) f (hm e he) (hp e he) _ hf
  intro x
  exact (Finset.single_le_sum (fun j hj => hp j hj x) he).trans (hs x)

omit [MeasurableSpace X] in
/-- Exact finite regularizer: the narrow remainder has a PLUS sign. -/
theorem regularizer_plus (wide narrow sandwich regNarrow : X → ℂ) :
    (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) = (fun x => wide x - sandwich x) := by
  funext x
  ring

/-- The correction identity holds under every mask before any limit. -/
theorem regularized_shell_eq (mu : Measure X) (p : X → ℝ)
    (wide narrow sandwich regNarrow : X → ℂ) :
    shell mu p (fun x => wide x - narrow x - (sandwich x - regNarrow x)
      + (narrow x - regNarrow x)) =
      shell mu p (fun x => wide x - sandwich x) := by
  rw [regularizer_plus]

/-- A trace-zero transport has a retained masked boundary contribution. -/
theorem shell_sub (mu : Measure X) (p : X → ℝ) (f g : X → ℂ)
    (hf : Integrable (fun x => (p x : ℂ) * f x) mu)
    (hg : Integrable (fun x => (p x : ℂ) * g x) mu) :
    shell mu p (fun x => f x - g x) = shell mu p f - shell mu p g := by
  simp only [shell, mul_sub]
  exact integral_sub hf hg

/-- Original representative and incoming-mask boundaries telescope before integration. -/
theorem boundary_repairs (indicator outgoing incoming : ℂ) :
    indicator - incoming = (indicator - outgoing) + (outgoing - incoming) := by ring

/-- The omitted residue is bounded by every paid finite shell enclosure. -/
theorem finite_residue_certificate [Fintype E]
    (v w : E → ℂ) (m : ℕ) (err : ℝ)
    (hm : ∑ e, v e = (m : ℂ))
    (he : (∑ e, ‖v e - w e‖) ≤ err) :
    ‖(m : ℂ) - ∑ e, w e‖ ≤ err := by
  rw [← hm, ← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans he

end NMeasuredShells

#print axioms NMeasuredShells.finite_shell_contraction
#print axioms NMeasuredShells.regularizer_plus
#print axioms NMeasuredShells.boundary_repairs
#print axioms NMeasuredShells.finite_residue_certificate

namespace PMeasuredReview
open MeasureTheory
variable {X : Type*} [MeasurableSpace X]

/-- The printed next-minus-current shell has the opposite sign from the
positive current-minus-next shell. Both integrals use original Haar. -/
theorem printed_shell_sign (mu : Measure X) (current next : X → ℝ)
    (d : X → ℂ) :
    (∫ x, ((next x-current x : ℝ) : ℂ)*d x ∂mu) =
      -(∫ x, ((current x-next x : ℝ) : ℂ)*d x ∂mu) := by
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by push_cast; ring)

/-- Haar conversion commutes with the SAME physical or shell mask. -/
theorem masked_original_haar (nu : Measure X) (V : ℝ) (hV : 0 < V)
    (w d : X → ℂ) :
    (∫ x, w x*((V : ℂ)⁻¹*d x) ∂(ENNReal.ofReal V • nu)) =
      ∫ x, w x*d x ∂nu := by
  have he : (fun x => w x*((V : ℂ)⁻¹*d x)) =
      (fun x => (V : ℂ)⁻¹*(w x*d x)) := by
    funext x
    ring
  rw [he]
  exact POriginalHaar.original_haar_integral nu V hV _
end PMeasuredReview
#print axioms PMeasuredReview.printed_shell_sign
#print axioms PMeasuredReview.masked_original_haar
