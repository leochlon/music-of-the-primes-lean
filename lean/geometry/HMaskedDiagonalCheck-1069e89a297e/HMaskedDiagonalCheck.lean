import Mathlib
set_option linter.unusedSectionVars false

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
#print axioms HNormalizedKernel.kernel_action
#print axioms HNormalizedKernel.diagonal_integral
#print axioms HNormalizedKernel.diagonal_cutoff_limit


set_option linter.unusedSectionVars false
/- Exact Hilbert-basis trace definitions from Masullo/Analysis/TraceClass.lean.
   The theorems below prove convergence for the finite-rank operators used here. -/
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

namespace HOperatorTrace
open MeasureTheory ContinuousLinearMap InnerProductSpace
open scoped InnerProductSpace BigOperators
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The trace sum of an actual finite-rank operator, in every Hilbert basis. -/
theorem finite_rank_hasSum (U R : ι → H) {κ : Type*} (e : HilbertBasis κ ℂ H) :
    HasSum (fun k => inner ℂ (e k) ((∑ i, rankOne ℂ (U i) (R i)) (e k)))
      (∑ i, inner ℂ (R i) (U i)) := by
  have he : (fun k => inner ℂ (e k) ((∑ i, rankOne ℂ (U i) (R i)) (e k))) =
      fun k => ∑ i, inner ℂ (R i) (e k) * inner ℂ (e k) (U i) := by
    funext k
    simp only [ContinuousLinearMap.sum_apply, rankOne_apply, inner_sum, inner_smul_right]
  rw [he]
  exact hasSum_sum fun i _ => e.hasSum_inner_mul_inner (R i) (U i)

theorem finite_rank_trace (U R : ι → H) :
    Masullo.TraceClass.trace (∑ i, rankOne ℂ (U i) (R i)) =
      ∑ i, inner ℂ (R i) (U i) :=
  (finite_rank_hasSum U R (Masullo.TraceClass.stdHilbertBasis ℂ H)).tsum_eq

/-- Adjoint rows enforce convolution first, left projection second. -/
theorem finite_projection_comp (u : ι → H) (A : H →L[ℂ] H) :
    (∑ i, rankOne ℂ (u i) (u i)).comp A =
      ∑ i, rankOne ℂ (u i) (A.adjoint (u i)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    rankOne_apply, adjoint_inner_left]

/-- The finite-rank sum really is the geometric orthogonal projection. -/
theorem finite_orthogonal_projection (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (u : ι → H) (hu : Orthonormal ℂ u)
    (hspan : Submodule.span ℂ (Set.range u) = E) :
    E.starProjection = ∑ i, rankOne ℂ (u i) (u i) := by
  ext x
  have hp : (∑ i, inner ℂ (u i) x • u i) ∈ E := by
    rw [← hspan]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have ho : ∀ w ∈ E, inner ℂ w (x - ∑ i, inner ℂ (u i) x • u i) = 0 := by
    intro w hw
    rw [← hspan] at hw
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hw
    rw [sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, inner_sub_right, hu.inner_right_fintype, sub_self, mul_zero]
  simpa only [ContinuousLinearMap.sum_apply, rankOne_apply] using
    (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp
      (fun w hw => inner_eq_zero_symm.mpr (ho w hw)))

variable {X : Type*} [MeasurableSpace X]

/-- An original-Haar diagonal integral is the actual operator trace. -/
theorem finite_kernel_trace (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (V : ℝ) (hV : 0 < V) (U R : ι → Lp ℂ 2 nu) :
    (∫ x, ∑ i, HNormalizedKernel.haarKernel b V (U i) (R i) x x
      ∂(ENNReal.ofReal V • nu)) =
      Masullo.TraceClass.trace (∑ i, rankOne ℂ (U i) (R i)) := by
  rw [integral_finset_sum _ (fun i _ =>
    HNormalizedKernel.diagonal_integrable nu b hb V (U i) (R i))]
  simp_rw [HNormalizedKernel.diagonal_integral nu b hb V hV]
  exact (finite_rank_trace U R).symm

/-- Trace/diagonal attachment for a genuine orthogonal projection after any
completed bounded operator A, hence for the constructed arithmetic convolution. -/
theorem projected_operator_kernel_trace (nu : Measure X)
    (b : X → ℝ) (hb : ∀ x, 0 < b x) (V : ℝ) (hV : 0 < V)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [E.HasOrthogonalProjection]
    (u : ι → Lp ℂ 2 nu) (hu : Orthonormal ℂ u)
    (hspan : Submodule.span ℂ (Set.range u) = E)
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    (∫ x, ∑ i, HNormalizedKernel.haarKernel b V (u i) (A.adjoint (u i)) x x
      ∂(ENNReal.ofReal V • nu)) =
      Masullo.TraceClass.trace (E.starProjection.comp A) := by
  rw [finite_orthogonal_projection E u hu hspan, finite_projection_comp]
  exact finite_kernel_trace nu b hb V hV u (fun i => A.adjoint (u i))

end
end HOperatorTrace
#check HOperatorTrace.projected_operator_kernel_trace
#print axioms HOperatorTrace.projected_operator_kernel_trace

namespace DSourceKernel
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology BigOperators InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Integrability of the actual full-input rank-one kernel integrand. -/
theorem rank_integrable (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (U R F : Lp ℂ 2 nu) (x : X) :
    Integrable (fun y => HNormalizedKernel.haarKernel b 1 U R x y *
      (F y / (b y : ℂ))) nu := by
  have he (y : X) : HNormalizedKernel.haarKernel b 1 U R x y *
      (F y / (b y : ℂ)) = (U x / (b x : ℂ)) * (F y * star (R y)) := by
    have hy : (b y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hb y))
    simp only [HNormalizedKernel.haarKernel, Complex.ofReal_one, div_one]
    field_simp
  simp_rw [he]
  exact ((Lp.memLp F).integrable_mul (Lp.memLp R).star).const_mul _

/-- Finite source projection expressed with its actual orthonormal basis. -/
theorem projection_expansion (nu : Measure X)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (v : Lp ℂ 2 nu) :
    E.starProjection v = ∑ i,
      inner ℂ ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu) v •
        ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu) := by
  let e := stdOrthonormalBasis ℂ E
  let w : E := ⟨E.starProjection v, E.starProjection_apply_mem v⟩
  have hw : (w : Lp ℂ 2 nu) = ∑ i, inner ℂ (e i) w • (e i : Lp ℂ 2 nu) := by
    conv_lhs => rw [← e.sum_repr' w]
    simp
  have hi (i) : inner ℂ (e i) w = inner ℂ (e i : Lp ℂ 2 nu) v := by
    change inner ℂ (e i : Lp ℂ 2 nu) (E.starProjection v) = _
    rw [← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (e i).property]
  simpa only [hi] using hw

/-- Every row is precomposed with A, implemented by A.adjoint. -/
def finiteKernel (nu : Measure X) (b : X → ℝ)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (x y : X) : ℂ :=
  ∑ i, HNormalizedKernel.haarKernel b 1
    ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
    (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) x y

/-- The canonical finite-source kernel acts on every completed input. -/
theorem finiteKernel_action (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) (F : Lp ℂ 2 nu) :
    (fun x => (E.starProjection (A F)) x) =ᵐ[nu]
      (fun x => (b x : ℂ) * ∫ y, finiteKernel nu b E A x y *
        (F y / (b y : ℂ)) ∂nu) := by
  classical
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  let c : Fin (Module.finrank ℂ E) → ℂ := fun i => inner ℂ (e i) (A F)
  have he (T : Finset (Fin (Module.finrank ℂ E))) :
      (fun x => (∑ i ∈ T, c i • e i) x) =ᵐ[nu]
      (fun x => ∑ i ∈ T, c i * e i x) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 nu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • e i) (∑ j ∈ T, c j • e j),
        Lp.coeFn_smul (c i) (e i), ih] with x hx hs ht
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, ht] using hx
  rw [projection_expansion]
  filter_upwards [he Finset.univ] with x hx
  change (∑ i, c i • e i) x = _ at hx ⊢
  rw [hx]
  unfold finiteKernel
  simp only [Finset.sum_mul]
  rw [integral_finset_sum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have h := HNormalizedKernel.kernel_action nu b hb 1 (by norm_num)
      (e i) (A.adjoint (e i)) F x
    rw [adjoint_inner_left] at h
    simpa only [ENNReal.ofReal_one, one_smul] using h.symm
  · intro i hi
    exact rank_integrable nu b hb _ _ F x

/-- This is a direct Haar diagonal calculation for the specified finite kernel. -/
theorem finiteKernel_diagonal (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    Integrable (fun x => finiteKernel nu b E A x x) nu ∧
    (∫ x, finiteKernel nu b E A x x ∂nu) =
      ∑ i, inner ℂ ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
        (A ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) := by
  have hi (i) : Integrable (fun x => HNormalizedKernel.haarKernel b 1
      ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
      (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)) x x) nu := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      HNormalizedKernel.diagonal_integrable nu b hb 1
        ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
        (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu))
  constructor
  · exact integrable_finset_sum _ (fun i _ => hi i)
  · unfold finiteKernel
    rw [integral_finset_sum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i hmem
    have h := HNormalizedKernel.diagonal_integral nu b hb 1 (by norm_num)
      ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu)
      (A.adjoint ((stdOrthonormalBasis ℂ E i : E) : Lp ℂ 2 nu))
    rw [adjoint_inner_left] at h
    simpa only [ENNReal.ofReal_one, one_smul] using h

end
end DSourceKernel

/- Append after DSourceKernel and HOperatorTrace. -/
namespace DSourceKernel
open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped BigOperators Topology
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The specified finite source kernel has the trace of the actual source
orthogonal projection after the bounded completed operator A. All finite-frame
hypotheses are discharged by the canonical orthonormal basis of the source span. -/
theorem finiteKernel_trace (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu) :
    (∫ x, finiteKernel nu b E A x x ∂nu) =
      Masullo.TraceClass.trace (E.starProjection.comp A) := by
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have he : E.starProjection = ∑ i, rankOne ℂ (e i) (e i) := by
    apply ContinuousLinearMap.ext
    intro v
    simpa only [ContinuousLinearMap.sum_apply, rankOne_apply, e] using
      projection_expansion nu E v
  rw [he, HOperatorTrace.finite_projection_comp]
  simpa only [finiteKernel, e, ENNReal.ofReal_one, one_smul] using
    HOperatorTrace.finite_kernel_trace nu b hb 1 (by norm_num) e
      (fun i => A.adjoint (e i))

end
end DSourceKernel

/-! Insert after KMaskFragment. Bounded physical multiplication on the common
completed L2 realization. The construction adapts the actual toLp/cutCLM proof
in review_core/Masullo/Geometry/WeightedCutoff.lean, without importing its
separate weighted measure or its conditional trace theorem. -/
noncomputable section
namespace KPhysicalMask
open MeasureTheory Filter
open scoped Topology ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem real_mask_mul_norm_le (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (z : ℂ) :
    ‖(r : ℂ) * z‖ ≤ ‖z‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hr.2

theorem real_mask_sub_norm_le (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) (z : ℂ) :
    ‖(r : ℂ) * z - z‖ ≤ ‖z‖ := by
  have heq : (r : ℂ) * z - z = ((r-1 : ℝ) : ℂ) * z := by push_cast; ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hr.2)]
  apply mul_le_of_le_one_left (norm_nonneg _)
  linarith [hr.1]

theorem realMask_memLp (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    MemLp (fun x => (rho x : ℂ) * f x) 2 mu := by
  refine ⟨hm.complex_ofReal.aestronglyMeasurable.mul (Lp.memLp f).1, ?_⟩
  apply lt_of_le_of_lt _ (Lp.memLp f).2
  exact eLpNorm_mono_ae (Eventually.of_forall (fun x => real_mask_mul_norm_le _ (hb x) _))

def realMask (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) : Lp ℂ 2 mu :=
  (realMask_memLp mu rho hm hb f).toLp (fun x => (rho x : ℂ) * f x)

theorem realMask_ae (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    (realMask mu rho hm hb f : X → ℂ) =ᵐ[mu] fun x => (rho x : ℂ) * f x :=
  MemLp.coeFn_toLp _

theorem realMask_norm_le (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    ‖realMask mu rho hm hb f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [realMask_ae mu rho hm hb f] with x hx
  rw [hx]
  exact real_mask_mul_norm_le _ (hb x) _

/-- Literal multiplication by the manuscript real physical mask. -/
def realMaskCLM (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  LinearMap.mkContinuous
    { toFun := realMask mu rho hm hb
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [realMask_ae mu rho hm hb (f+g),
          realMask_ae mu rho hm hb f, realMask_ae mu rho hm hb g,
          Lp.coeFn_add f g,
          Lp.coeFn_add (realMask mu rho hm hb f) (realMask mu rho hm hb g)]
          with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [realMask_ae mu rho hm hb (c • f), realMask_ae mu rho hm hb f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (realMask mu rho hm hb f)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4, Pi.smul_apply, h2, h3, Pi.smul_apply]
        simp only [smul_eq_mul]
        ring }
    1 (fun f => by simpa using realMask_norm_le mu rho hm hb f)

theorem realMaskCLM_complement_bound
    (mu : Measure X) (rho : X → ℝ) (hm : Measurable rho)
    (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) (f : Lp ℂ 2 mu) :
    ‖realMaskCLM mu rho hm hb f - f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (realMaskCLM mu rho hm hb f) f,
    realMask_ae mu rho hm hb f] with x h1 h2
  change (realMaskCLM mu rho hm hb f : X → ℂ) x = _ at h2
  rw [h1, Pi.sub_apply, h2]
  exact real_mask_sub_norm_le _ (hb x) _

/-- The entire L2 error is bounded with constant one by the original-measure
tail outside the physical plateau. No source index occurs in this estimate. -/
theorem real_mask_tail_eLpNorm (mu : Measure X) (band : Set X)
    (rho : X → ℝ) (hb : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (hp : ∀ x ∈ band, rho x = 1) (f : X → ℂ) :
    eLpNorm (fun x => (rho x : ℂ) * f x - f x) 2 mu ≤
      eLpNorm (bandᶜ.indicator f) 2 mu := by
  apply eLpNorm_mono_ae
  filter_upwards [] with x
  by_cases hx : x ∈ band
  · simp [hp x hx, hx]
  · simpa [hx] using real_mask_sub_norm_le (rho x) (hb x) (f x)

/-- Strong convergence of the genuine bounded multiplication operators. The
plateau application, rather than an assumed Lp limit, supplies pointwise
eventual equality. This is a vector theorem, with no nuclearity conclusion. -/
theorem realMaskCLM_strong (mu : Measure X) (rho : ℕ → X → ℝ)
    (hm : ∀ n, Measurable (rho n))
    (hb : ∀ n x, 0 ≤ rho n x ∧ rho n x ≤ 1)
    (hp : ∀ x, ∀ᶠ n in atTop, rho n x = 1) (f : Lp ℂ 2 mu) :
    Tendsto (fun n => realMaskCLM mu (rho n) (hm n) (hb n) f) atTop (𝓝 f) := by
  let F : ℕ → X → ℂ := fun n x => (rho n x : ℂ) * f x
  have hF : ∀ n, MemLp (F n) 2 mu := fun n => realMask_memLp mu _ (hm n) (hb n) f
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂mu) ≠ ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Lp.memLp f).2).ne
  have hlim : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂mu)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖F n x - f x‖ₑ ^ (2 : ℝ))
      (fun x => ‖f x‖ₑ ^ (2 : ℝ))
      (fun n => by simpa using (((hF n).1.sub (Lp.memLp f).1).enorm.pow_const (2 : ℕ)))
      (fun n => Eventually.of_forall fun x => by
        apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (real_mask_sub_norm_le _ (hb n x) _)) hfin
      (f := fun _ => (0 : ℝ≥0∞))
      (Eventually.of_forall fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hp x] with n hn
        simp [F, hn])
    simpa using h
  have hnorm : Tendsto (fun n => eLpNorm (F n - (f : X → ℂ)) 2 mu)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hlim
    simpa only [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, Pi.sub_apply,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF (f : X → ℂ) (Lp.memLp f)).2 hnorm
  simpa only [Lp.toLp_coeFn] using h

end KPhysicalMask
end
#check KPhysicalMask.realMaskCLM_strong
#print axioms KPhysicalMask.realMaskCLM_strong

/- Append after HSourceTrace and KStrongPhysicalMask. The mask is K's actual
completed multiplication operator; all measures and kernels are unchanged. -/
namespace HNormalizedKernel
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- Multiplying the original-Haar diagonal is exactly multiplying the output
column in L2. The a.e. representative conversion is proved explicitly. -/
theorem realMask_diagonal (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (rho : X → ℝ) (hm : Measurable rho) (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1)
    (U R : Lp ℂ 2 nu) :
    Integrable (fun x => (rho x : ℂ) * haarKernel b 1 U R x x) nu ∧
    (∫ x, (rho x : ℂ) * haarKernel b 1 U R x x ∂nu) =
      inner ℂ R (KPhysicalMask.realMaskCLM nu rho hm hbound U) := by
  let M := KPhysicalMask.realMaskCLM nu rho hm hbound
  have he : (fun x => (rho x : ℂ) * haarKernel b 1 U R x x) =ᵐ[nu]
      (fun x => haarKernel b 1 (M U) R x x) := by
    filter_upwards [KPhysicalMask.realMask_ae nu rho hm hbound U] with x hx
    change (M U : X → ℂ) x = (rho x : ℂ) * U x at hx
    simp only [diagonal_formula b hb, Complex.ofReal_one, inv_one, one_mul, hx]
    ring
  have hi : Integrable (fun x => haarKernel b 1 (M U) R x x) nu := by
    simpa only [ENNReal.ofReal_one, one_smul] using diagonal_integrable nu b hb 1 (M U) R
  refine ⟨hi.congr he.symm, ?_⟩
  rw [integral_congr_ae he]
  simpa only [ENNReal.ofReal_one, one_smul] using
    diagonal_integral nu b hb 1 (by norm_num) (M U) R

end
end HNormalizedKernel

namespace DSourceKernel
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace BigOperators
noncomputable section
variable {X : Type*} [MeasurableSpace X]

/-- The physical cutoff of the finite EA diagonal is the trace of EAM.
The equality uses adjoint rows and finite-dimensional trace, with no
commutation of E, A or M and no nuclearity assumption about A. -/
theorem finiteKernel_realMask_trace (nu : Measure X) (b : X → ℝ) (hb : ∀ x, 0 < b x)
    (E : Submodule ℂ (Lp ℂ 2 nu)) [FiniteDimensional ℂ E]
    (A : Lp ℂ 2 nu →L[ℂ] Lp ℂ 2 nu)
    (rho : X → ℝ) (hm : Measurable rho) (hbound : ∀ x, 0 ≤ rho x ∧ rho x ≤ 1) :
    let M := KPhysicalMask.realMaskCLM nu rho hm hbound
    Integrable (fun x => (rho x : ℂ) * finiteKernel nu b E A x x) nu ∧
    (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x ∂nu) =
      (∫ x, finiteKernel nu b E (A.comp M) x x ∂nu) ∧
    (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x ∂nu) =
      Masullo.TraceClass.trace (E.starProjection.comp (A.comp M)) := by
  dsimp only
  let M := KPhysicalMask.realMaskCLM nu rho hm hbound
  let e : Fin (Module.finrank ℂ E) → Lp ℂ 2 nu := fun i => stdOrthonormalBasis ℂ E i
  have hr (i : Fin (Module.finrank ℂ E)) :=
    HNormalizedKernel.realMask_diagonal nu b hb rho hm hbound (e i) (A.adjoint (e i))
  have hi : Integrable (fun x => (rho x : ℂ) * finiteKernel nu b E A x x) nu := by
    simp only [finiteKernel, Finset.mul_sum]
    exact integrable_finset_sum _ (fun i _ => (hr i).1)
  have he : (∫ x, (rho x : ℂ) * finiteKernel nu b E A x x ∂nu) =
      (∫ x, finiteKernel nu b E (A.comp M) x x ∂nu) := by
    calc
      _ = ∑ i, inner ℂ (A.adjoint (e i)) (M (e i)) := by
        simp only [finiteKernel, Finset.mul_sum]
        rw [integral_finset_sum _ (fun i _ => (hr i).1)]
        exact Finset.sum_congr rfl (fun i _ => (hr i).2)
      _ = _ := by
        rw [(finiteKernel_diagonal nu b hb E (A.comp M)).2]
        apply Finset.sum_congr rfl
        intro i _
        exact A.adjoint_inner_left (M (e i)) (e i)
  exact ⟨hi, he, he.trans (finiteKernel_trace nu b hb E (A.comp M))⟩

end
end DSourceKernel
#check DSourceKernel.finiteKernel_realMask_trace
#print axioms DSourceKernel.finiteKernel_realMask_trace
