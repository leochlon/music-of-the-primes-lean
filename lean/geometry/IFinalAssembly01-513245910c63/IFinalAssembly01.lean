import Mathlib

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


/-! Positive descended shells of the original Haar diagonal, M36 (36.1)-(36.3).
No disjointness assumption is used. Arithmetic identification of the density
is deliberately a separate obligation, not a new axiom. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace ReviewM

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The masks are the nonnegative descended indentation weights. -/
structure PositivePartition (p : ι → X → ℝ) : Prop where
  measurable : ∀ i, Measurable (p i)
  nonneg : ∀ i x, 0 ≤ p i x
  mass : ∀ x, HasSum (fun i => p i x) 1

theorem partition_partial_le (p : ι → X → ℝ) (hp : PositivePartition p)
    (s : Finset ι) (x : X) : ∑ i ∈ s, p i x ≤ 1 := by
  simpa only [(hp.mass x).tsum_eq] using
    (hp.mass x).summable.sum_le_tsum s (fun i _ => hp.nonneg i x)

theorem partition_le_one (p : ι → X → ℝ) (hp : PositivePartition p)
    (i : ι) (x : X) : p i x ≤ 1 := by
  simpa using partition_partial_le p hp {i} x

/-- Multiplication by any descended shell preserves L1. -/
theorem shell_integrable (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (i : ι) :
    Integrable (fun x => (p i x : ℂ) * d x) μ := by
  apply hd.norm.mono' ((hp.measurable i).complex_ofReal.aestronglyMeasurable.mul
    hd.aestronglyMeasurable)
  filter_upwards [] with x
  change ‖(p i x : ℂ) * d x‖ ≤ ‖d x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg i x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (partition_le_one p hp i x)

/-- Every finite family of shell integrals is bounded by the SAME L1 mass. -/
theorem finite_shell_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) (s : Finset ι) :
    ∑ i ∈ s, ‖∫ x, (p i x : ℂ) * d x ∂μ‖ ≤ ∫ x, ‖d x‖ ∂μ := by
  have hi := fun i => shell_integrable μ p hp d hd i
  calc
    _ ≤ ∑ i ∈ s, ∫ x, ‖(p i x : ℂ) * d x‖ ∂μ :=
      Finset.sum_le_sum fun i _ => norm_integral_le_integral_norm _
    _ = ∫ x, ∑ i ∈ s, ‖(p i x : ℂ) * d x‖ ∂μ :=
      (integral_finset_sum s (fun i _ => (hi i).norm)).symm
    _ ≤ ∫ x, ‖d x‖ ∂μ := by
      apply integral_mono (integrable_finset_sum _ (fun i _ => (hi i).norm)) hd.norm
      intro x
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hp.nonneg _ x)]
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (partition_partial_le p hp s x)

/-- Countably many shells cost no factor equal to the number of shells. -/
theorem positive_shell_l1 (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : X → ℂ) (hd : Integrable d μ) :
    Summable (fun i => ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ∧
    (∑' i, ‖∫ x, (p i x : ℂ) * d x ∂μ‖) ≤ ∫ x, ‖d x‖ ∂μ := by
  have hs := summable_of_sum_le (fun i => norm_nonneg
    (∫ x, (p i x : ℂ) * d x ∂μ)) (finite_shell_bound μ p hp d hd)
  exact ⟨hs, le_of_tendsto hs.hasSum
    (Eventually.of_forall (finite_shell_bound μ p hp d hd))⟩

/-- The same estimate pays the entire shell-vector error. -/
theorem shell_difference_bound (p : ι → X → ℝ) (hp : PositivePartition p)
    (d e : X → ℂ) (hd : Integrable d μ) (he : Integrable e μ) :
    (∑' i, ‖(∫ x, (p i x : ℂ) * d x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) ≤ ∫ x, ‖d x - e x‖ ∂μ := by
  have h := (positive_shell_l1 μ p hp (fun x => d x - e x) (hd.sub he)).2
  simpa only [mul_sub, integral_sub (shell_integrable μ p hp d hd _)
    (shell_integrable μ p hp e he _)] using h

/-- L1 convergence of the original Haar densities gives simultaneous shell convergence. -/
theorem shell_l1_limit (p : ι → X → ℝ) (hp : PositivePartition p)
    (d : ℕ → X → ℂ) (e : X → ℂ) (hd : ∀ n, Integrable (d n) μ)
    (he : Integrable e μ)
    (hlim : Tendsto (fun n => ∫ x, ‖d n x - e x‖ ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' i, ‖(∫ x, (p i x : ℂ) * d n x ∂μ) -
      (∫ x, (p i x : ℂ) * e x ∂μ)‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => tsum_nonneg (fun i => norm_nonneg _))
    (fun n => shell_difference_bound μ p hp (d n) e (hd n) he) hlim


end ReviewM
end


namespace ReviewI
open MeasureTheory Filter
open scoped Topology
variable {X E : Type*} [MeasurableSpace X]

/-- I35 (35.8), assembled with M's reviewed positive-mask theorem. The
entire countable corrected shell vector converges with a single L1 error;
the finite narrow compensator and the source transport both remain. -/
theorem corrected_shell_vector_limit
    (mu : Measure X) (p : E → X → ℝ) (hp : ReviewM.PositivePartition p)
    (wide narrow full : X → ℂ) (sandwich regularized : ℕ → X → ℂ)
    (hwide : Integrable wide mu) (hnarrow : Integrable narrow mu)
    (hfull : Integrable full mu) (hsand : ∀ n, Integrable (sandwich n) mu)
    (hreg : ∀ n, Integrable (regularized n) mu)
    (hlim : Tendsto (fun n => ∫ x, ‖sandwich n x-full x‖ ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' e,
      ‖(masked mu (fun x => (p e x : ℂ)) wide
        -masked mu (fun x => (p e x : ℂ)) narrow
        -masked mu (fun x => (p e x : ℂ)) (fun x => sandwich n x-regularized n x)
        +masked mu (fun x => (p e x : ℂ)) (fun x => narrow x-regularized n x))
        -masked mu (fun x => (p e x : ℂ)) (fun x => wide x-full x)‖)
      atTop (𝓝 0) := by
  have hl' : Tendsto (fun n => ∫ x,
      ‖(wide x-sandwich n x)-(wide x-full x)‖ ∂mu) atTop (𝓝 0) := by
    have he : (fun n => ∫ x, ‖(wide x-sandwich n x)-(wide x-full x)‖ ∂mu) =
        (fun n => ∫ x, ‖sandwich n x-full x‖ ∂mu) := by
      funext n
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (wide x-sandwich n x)-(wide x-full x) = -(sandwich n x-full x) by ring,
        norm_neg]
    rwa [he]
  have ht := ReviewM.shell_l1_limit mu p hp
    (fun n x => wide x-sandwich n x) (fun x => wide x-full x)
    (fun n => hwide.sub (hsand n)) (hwide.sub hfull) hl'
  have he (e : E) (n : ℕ) :
      masked mu (fun x => (p e x : ℂ)) wide
        -masked mu (fun x => (p e x : ℂ)) narrow
        -masked mu (fun x => (p e x : ℂ)) (fun x => sandwich n x-regularized n x)
        +masked mu (fun x => (p e x : ℂ)) (fun x => narrow x-regularized n x) =
      masked mu (fun x => (p e x : ℂ)) (fun x => wide x-sandwich n x) := by
    apply finite_source_compensator_integral mu _ wide narrow (sandwich n) (regularized n)
      ((hp.measurable e).complex_ofReal.aestronglyMeasurable) _
      hwide hnarrow (hsand n) (hreg n)
    filter_upwards [] with x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp.nonneg e x)]
    exact ReviewM.partition_le_one p hp e x
  simp_rw [he]
  exact ht

end ReviewI
#print axioms ReviewI.corrected_shell_vector_limit



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



namespace Masullo.CoreInvarianceExtends
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 theorem core_invariance_extends (T : H →L[ℂ] H) (C : Submodule ℂ H)
    (hC : ∀ x ∈ C, T x ∈ C) :
    ∀ x ∈ C.topologicalClosure, T x ∈ C.topologicalClosure := by
  intro x hx
  exact map_mem_closure T.continuous hx hC

/-- With G the ACTUAL geometric closure, its orthogonal complement projector
is P=1-Q. Invariance of G gives a one-sided triangular block, not commutation. -/
 theorem projection_order_defect (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    T (P x) - P (T x) = Q (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

 theorem convolution_first_compression (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let P := ContinuousLinearMap.id ℂ H - G.starProjection
    P (T x) = P (T (P x)) := by
  dsimp only
  have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
  abel

/-- Both complementary printed-to-convolution-first changes have opposite
signs, for the SAME cutoff. Neither individual defect is set to zero. -/
 theorem paired_cutoff_order_defects (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (T M : H →L[ℂ] H) (hG : ∀ x ∈ G, T x ∈ G) (x : H) :
    let Q := G.starProjection
    let P := ContinuousLinearMap.id ℂ H - Q
    (M (T (P x)) - M (P (T x)) = M (Q (T (P x)))) ∧
    (M (T (Q x)) - M (Q (T x)) = -M (Q (T (P x)))) := by
  dsimp only
  have hh := congrArg M (projection_order_defect G T hG x)
  simp only [map_sub] at hh
  constructor
  · exact hh
  · have hQ : G.starProjection (T (G.starProjection x)) = T (G.starProjection x) :=
      Submodule.starProjection_eq_self_iff.mpr
        (hG _ (Submodule.starProjection_apply_mem G x))
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hQ]
    abel

#print axioms core_invariance_extends
#print axioms projection_order_defect
#print axioms convolution_first_compression
#print axioms paired_cutoff_order_defects
end Masullo.CoreInvarianceExtends



namespace NativeCorrectedShellsR35

/-- Ordered row error for the actual source-projection resolvent solve. -/
theorem row_residual {R : Type*} [Ring R]
    (p j v n js d : R) (hv : v-n=v*js*d*j*n) :
    p*j*v-(p+d)*j*n=(p*j*v*js-1)*d*j*n := by
  calc
    p*j*v-(p+d)*j*n=p*j*(v-n)-d*j*n := by noncomm_ring
    _=p*j*(v*js*d*j*n)-d*j*n := by rw [hv]
    _=(p*j*v*js-1)*d*j*n := by noncomm_ring

/-- Neither the incoming row error nor the outgoing source error is omitted. -/
theorem source_product_error {R : Type*} [Ring R] (a b r s : R) :
    a*r-b*s=(a-b)*s+a*(r-s) := by noncomm_ring

/-- The finite narrow-width compensator must enter with a plus sign. -/
theorem finite_shell_compensator {R : Type*} [Ring R]
    (wide narrow sandwich regularizedNarrow : R) :
    wide-narrow-(sandwich-regularizedNarrow)
      +(narrow-regularizedNarrow)=wide-sandwich := by noncomm_ring

/-- The same full-input correction is retained by a finite sandwich. -/
theorem left_projection_retained {R : Type*} [Ring R]
    (q s t : R) (h : q*s=0) : q*(t-s*t*s)=q*t := by
  calc
    q*(t-s*t*s)=q*t-(q*s)*t*s := by noncomm_ring
    _=q*t := by rw [h]; simp

end NativeCorrectedShellsR35

#print axioms NativeCorrectedShellsR35.row_residual
#print axioms NativeCorrectedShellsR35.source_product_error
#print axioms NativeCorrectedShellsR35.finite_shell_compensator
#print axioms NativeCorrectedShellsR35.left_projection_retained


attribute [local instance] Classical.propDecidable

namespace Masullo.BoundaryJetOrders

/-- The finite set of boundary jets satisfying the STRICT numerical condition
in Proposition 9.1.2.5. This is an index set, not a spectrum or an L-function.
The unresolved analytic bridge is that these are exactly the continuous jets
of the actual weighted idele-class quotient. -/
noncomputable def boundaryJetOrders (N : ℕ) (s : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (2 : ℝ) * j + 1 < s)

/-- Discharges the finite counting premise for boundary multiplicities:
at odd integral weight 2*k+1, the strict cutoff retains min(N,k) jets. -/
theorem boundaryJetOrders_odd (N k : ℕ) :
    boundaryJetOrders N (2 * (k : ℝ) + 1) = Finset.range (min N k) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  constructor
  · intro h
    have hj : (j : ℝ) < (k : ℝ) := by linarith [h.2]
    exact ⟨h.1, by exact_mod_cast hj⟩
  · rintro ⟨hN, hk⟩
    have hj : (j : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ⟨hN, by linarith⟩

/-- Conditional finite-block trace reduction for the binomial jet action
printed at (10.3.1.17). Discharges only its finite trace calculation; the
hypothesis must be proved for the genuine quotient operator before use. -/
theorem trace_of_binomial_jet_action (n : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    Matrix.trace M = (n : ℂ) * a 0 := by
  have hd (i : Fin n) : M i i = a 0 := by simp [hM]
  simp [Matrix.trace, Matrix.diag, hd, nsmul_eq_mul]

/-- Combined exact finite-count and conditional finite-trace step toward the
correct spectral multiplicity. No assertion of analytic jet admissibility,
zero identification, completeness, nuclearity, or infinite summability. -/
theorem boundary_jet_trace_at_odd_weight (N k : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card)
      (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k ∧
      Matrix.trace M = ((min N k : ℕ) : ℂ) * a 0 := by
  have hc : (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k := by
    rw [boundaryJetOrders_odd, Finset.card_range]
  refine ⟨hc, ?_⟩
  simpa only [hc] using trace_of_binomial_jet_action _ a M hM

#check boundaryJetOrders_odd
#print axioms boundaryJetOrders_odd
#check trace_of_binomial_jet_action
#print axioms trace_of_binomial_jet_action
#check boundary_jet_trace_at_odd_weight
#print axioms boundary_jet_trace_at_odd_weight
/-- Numerical boundary multiplicity for every real Sobolev parameter.
This discharges counting only; continuous native jet attachment is unresolved. -/
theorem boundaryJetOrders_all_real (N : ℕ) (s : ℝ) :
    boundaryJetOrders N s = Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range,
    Nat.lt_min, Nat.lt_ceil]
  constructor
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩

#check boundaryJetOrders_all_real
#print axioms boundaryJetOrders_all_real
end Masullo.BoundaryJetOrders


namespace ReviewI
/-- The manuscript's signed orbital shell is the negative positive-stratum shell. -/
theorem printed_shell_sign (next current kernel : ℂ) :
    (next-current)*kernel = -((current-next)*kernel) := by ring
end ReviewI
#print axioms ReviewI.printed_shell_sign
#print axioms POriginalHaar.rank_one_original_haar
#print axioms Masullo.CoreInvarianceExtends.convolution_first_compression
#print axioms Masullo.BoundaryJetOrders.boundaryJetOrders_all_real
#print axioms ReviewI.corrected_shell_vector_limit
