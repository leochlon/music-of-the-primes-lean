import Mathlib

set_option maxHeartbeats 800000

/-! L35/L36 source-compensation and measured cutoff consequences.
The arithmetic support/range construction is an explicit premise, not an axiom.
All projections below are the Hilbert-space orthogonal projections. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace ReviewL

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- L35 (35.6): the actual compensated source lies in the restricted closure.
No equality between PW quotient topology and source-closure topology is used. -/
theorem compensated_orthogonal_bound
    (E F : Submodule ℂ H) [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (k : H →L[ℂ] H) (hrange : ∀ x, k (E.starProjection x) ∈ F) (x : H) :
    ‖Fᗮ.starProjection (E.starProjection x)‖ ≤
      ‖ContinuousLinearMap.id ℂ H - k‖ * ‖x‖ := by
  have hz : Fᗮ.starProjection (k (E.starProjection x)) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (hrange x)
  calc
    ‖Fᗮ.starProjection (E.starProjection x)‖ =
        ‖Fᗮ.starProjection (E.starProjection x - k (E.starProjection x))‖ := by
          rw [map_sub, hz, sub_zero]
    _ ≤ ‖E.starProjection x - k (E.starProjection x)‖ :=
      Submodule.norm_starProjection_apply_le (F.orthogonal)
        (E.starProjection x - k (E.starProjection x))
    _ ≤ ‖ContinuousLinearMap.id ℂ H - k‖ * ‖E.starProjection x‖ := by
      exact (ContinuousLinearMap.id ℂ H - k).le_opNorm (E.starProjection x)
    _ ≤ ‖ContinuousLinearMap.id ℂ H - k‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left (E.norm_starProjection_apply_le x) (norm_nonneg _)

/-- The same estimate in the manuscript's `1-F` notation. -/
theorem compensated_source_error
    (E F : Submodule ℂ H) [E.HasOrthogonalProjection] [F.HasOrthogonalProjection]
    (k : H →L[ℂ] H) (hrange : ∀ x, k (E.starProjection x) ∈ F) (x : H) :
    ‖E.starProjection x - F.starProjection (E.starProjection x)‖ ≤
      ‖ContinuousLinearMap.id ℂ H - k‖ * ‖x‖ := by
  simpa only [Submodule.starProjection_orthogonal_val] using
    compensated_orthogonal_bound E F k hrange x

/-- Growing actual support budgets may be used; nesting is not required. -/
theorem compensated_source_limit
    (E : Submodule ℂ H) [E.HasOrthogonalProjection]
    (F : ℕ → Submodule ℂ H) [∀ n, (F n).HasOrthogonalProjection]
    (k : ℕ → H →L[ℂ] H)
    (hrange : ∀ n x, k n (E.starProjection x) ∈ F n)
    (herr : Tendsto (fun n => ‖ContinuousLinearMap.id ℂ H - k n‖) atTop (𝓝 0))
    (x : H) :
    Tendsto (fun n => (F n).starProjection (E.starProjection x))
      atTop (𝓝 (E.starProjection x)) := by
  have he : Tendsto (fun n => E.starProjection x -
      (F n).starProjection (E.starProjection x)) atTop (𝓝 (0 : H)) := by
    apply squeeze_zero_norm (fun n => compensated_source_error E (F n) (k n) (hrange n) x)
    simpa using herr.mul_const ‖x‖
  have hh := (tendsto_const_nhds (x := E.starProjection x)).sub he
  simpa using hh

/-- Original incoming column retained: L35 (35.9), before any norm estimate. -/
theorem full_source_tail {R : Type*} [Ring R]
    (s f e b : R) (hs : s*s=s) (hfs : f*s=f) (hse : s*e=e) :
    (s-f)*b = (s-f)*(s-e)*b+(1-f)*e*b := by
  symm
  calc
    (s-f)*(s-e)*b+(1-f)*e*b = s*s*b-f*s*b-s*e*b+e*b := by noncomm_ring
    _ = (s-f)*b := by rw [hs,hfs,hse]; noncomm_ring

/-- Manuscript (10.4.1.11): convolution first. Only source invariance is used. -/
theorem convolution_first_compression
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (hG : ∀ x ∈ G, A x ∈ G) (x : H) :
    Gᗮ.starProjection (A x) = Gᗮ.starProjection (A (Gᗮ.starProjection x)) := by
  have hQ : G.starProjection (A (G.starProjection x)) = A (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [Submodule.starProjection_orthogonal_val, map_sub, hQ]
  abel

/-- The omitted block in AP-PA is retained, with its original sign. -/
theorem projection_order_defect
    (G : Submodule ℂ H) [G.HasOrthogonalProjection]
    (A : H →L[ℂ] H) (hG : ∀ x ∈ G, A x ∈ G) (x : H) :
    A (Gᗮ.starProjection x) - Gᗮ.starProjection (A x) =
      G.starProjection (A (Gᗮ.starProjection x)) := by
  have hQ : G.starProjection (A (G.starProjection x)) = A (G.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hG _ (Submodule.starProjection_apply_mem G x))
  simp only [Submodule.starProjection_orthogonal_val, map_sub, hQ]
  abel

/-- R35's extracted source return has a negative sign in this width difference. -/
theorem retained_source_return (narrow wide extracted correction moment : ℂ) (m : ℕ)
    (hc : correction = narrow-wide) (he : extracted = (m : ℂ)*moment) :
    correction = (narrow-(wide-extracted))-(m : ℂ)*moment := by
  rw [hc, he]
  ring

section Measures
variable {X : Type*} [MeasurableSpace X]

/-- The original Haar measure remains the diagonal measure. A product-a.e.
kernel identity is not used to restrict an unspecified representative. -/
theorem diagonal_cutoff_limit (mu : Measure X) (d : X → ℂ)
    (hd : Integrable d mu) (rho : ℕ → X → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, rho n x * d x ∂mu) atTop (𝓝 (∫ x, d x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖d x‖)
  · exact fun n => (hm n).mul hd.aestronglyMeasurable
  · exact hd.norm
  · intro n
    filter_upwards [hb n] with x hx
    simpa only [norm_mul, one_mul] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (d x))
  · filter_upwards [hl] with x hx
    simpa using hx.mul_const (d x)

/-- Zero total correction does not erase its localized contribution. -/
theorem masked_zero_correction (mu : Measure X) (z rho : X → ℂ)
    (hz : Integrable z mu) (hm : Integrable (fun x => rho x*z x) mu)
    (hzero : (∫ x, z x ∂mu) = 0) :
    (∫ x, rho x*z x ∂mu) = -∫ x, (1-rho x)*z x ∂mu := by
  have he : (fun x => (1-rho x)*z x) = (fun x => z x-rho x*z x) := by
    funext x; ring
  rw [he, integral_sub hz hm, hzero]
  simp

end Measures

#print axioms compensated_orthogonal_bound
#print axioms compensated_source_limit
#print axioms convolution_first_compression
#print axioms projection_order_defect
#print axioms retained_source_return
#print axioms diagonal_cutoff_limit
#print axioms masked_zero_correction

end ReviewL
