import Mathlib

/-! Round 90 C: direct control of lift ambiguity in the proposed nuclear
majorant. The continuous convolution realization and authentic theta subspace
are NOT constructed by these lemmas. The nuclear bound remains incomplete. -/

open scoped NumberField ENNReal NNReal
open NumberField MeasureTheory

namespace NuclearBoundC90

variable (K : Type*) [Field K] [NumberField K]
abbrev GenuineAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev GenuineIdeles := (GenuineAdeles K)ˣ
noncomputable def principal : Kˣ →* GenuineIdeles K :=
  Units.map (algebraMap K (GenuineAdeles K)).toMonoidHom
abbrev GenuineClasses := GenuineIdeles K ⧸ (principal K).range
noncomputable instance genuineBorel : MeasurableSpace (GenuineClasses K) :=
  borel (GenuineClasses K)

/- The Hilbert calculation below applies to the actual weighted L2 realization
once its Haar measure and manuscript weight are supplied. It does not assume
nuclearity, summability, a lift norm, or a spectral identification. -/
noncomputable abbrev WeightedSpace (μ : Measure (GenuineClasses K))
    (w : GenuineClasses K → ℝ≥0∞) := Lp ℂ 2 (μ.withDensity w)

section LiftEstimate
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- An exact lower bound for the two smoothed choices of a quotient lift. -/
theorem smoothedLift_pair_lower_bound (A : H →L[ℂ] H) (u v : H) :
    2 * ‖A v‖ ≤ ‖A (u + v)‖ + ‖A (u - v)‖ := by
  have he : A (u + v) - A (u - v) = (2 : ℂ) • A v := by
    simp only [map_add, map_sub]
    module
  have hn := norm_sub_le (A (u + v)) (A (u - v))
  rw [he, norm_smul] at hn
  norm_num at hn
  simpa only [map_add, map_sub] using hn

/-- Every geometric perturbation preserves the quotient, but its smoothed
norm is still present in the sum of the two candidate rank-one costs. -/
theorem quotientLift_pair_cost (A : H →L[ℂ] H) (M : Submodule ℂ H)
    (u v : H) (hv : v ∈ M) (η : H →L[ℂ] ℂ) :
    M.mkQ (u + v) = M.mkQ u ∧ M.mkQ (u - v) = M.mkQ u ∧
      2 * ‖A v‖ * ‖η‖ ≤
        ‖A (u + v)‖ * ‖η‖ + ‖A (u - v)‖ * ‖η‖ := by
  have hz : M.mkQ v = 0 := Submodule.Quotient.mk_eq_zero M |>.mpr hv
  refine ⟨?_, ?_, ?_⟩
  · simp [map_add, hz]
  · simp [map_sub, hz]
  · have h := mul_le_mul_of_nonneg_right (smoothedLift_pair_lower_bound A u v)
      (norm_nonneg η)
    simpa only [add_mul] using h

/-- A fixed geometric perturbation has a linearly growing aggregate cost;
no lift bound or summability is assumed. -/
theorem smoothedLift_finite_cost {ι : Type*} (J : Finset ι)
    (A : H →L[ℂ] H) (u : ι → H) (v : H)
    (η : ι → H →L[ℂ] ℂ) (c : ℝ)
    (hη : ∀ i ∈ J, c ≤ ‖η i‖) :
    2 * (J.card : ℝ) * ‖A v‖ * c ≤
      ∑ i ∈ J, (‖A (u i + v)‖ * ‖η i‖ + ‖A (u i - v)‖ * ‖η i‖) := by
  calc
    _ = ∑ _i ∈ J, (2 * ‖A v‖ * c) := by simp; ring
    _ ≤ _ := Finset.sum_le_sum fun i hi => by
      calc
        2 * ‖A v‖ * c ≤ 2 * ‖A v‖ * ‖η i‖ :=
          mul_le_mul_of_nonneg_left (hη i hi) (by positivity)
        _ ≤ _ := by
          simpa only [add_mul] using
            mul_le_mul_of_nonneg_right (smoothedLift_pair_lower_bound A (u i) v)
              (norm_nonneg (η i))

/-- Uniform norms of the coefficient functionals do not bound the primal
lift norms without additional separation information. -/
theorem coefficientSeparation_liftNorm (η θ : H →L[ℂ] ℂ) (u : H)
    (hη : η u = 1) (hθ : θ u = 0) :
    1 ≤ ‖η - θ‖ * ‖u‖ := by
  have h := (η - θ).le_opNorm u
  simpa only [ContinuousLinearMap.sub_apply, hη, hθ, sub_zero, norm_one] using h

end LiftEstimate

/-- Specialization to weighted L2 on the genuine idele-class group.
A and the geometric subspace are supplied, not defined by spectral data. -/
theorem genuineWeightedLift_pair_cost
    (μ : Measure (GenuineClasses K)) (w : GenuineClasses K → ℝ≥0∞)
    (A : WeightedSpace K μ w →L[ℂ] WeightedSpace K μ w)
    (M : Submodule ℂ (WeightedSpace K μ w))
    (u v : WeightedSpace K μ w) (hv : v ∈ M)
    (η : WeightedSpace K μ w →L[ℂ] ℂ) :
    M.mkQ (u + v) = M.mkQ u ∧ M.mkQ (u - v) = M.mkQ u ∧
      2 * ‖A v‖ * ‖η‖ ≤
        ‖A (u + v)‖ * ‖η‖ + ‖A (u - v)‖ * ‖η‖ :=
  quotientLift_pair_cost A M u v hv η

/-- The actual Haar convolution formula; measure hypotheses for boundedness
on weighted L2 are deliberately not asserted. -/
noncomputable def genuineConvolution (μ : Measure (GenuineClasses K))
    (φ f : GenuineClasses K → ℂ) (x : GenuineClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

/-- The same lift obstruction for the genuine integral convolution itself. -/
theorem genuineConvolution_lift_pair_lower_bound
    (μ : Measure (GenuineClasses K)) (φ u v : GenuineClasses K → ℂ)
    (x : GenuineClasses K)
    (hu : Integrable (fun g => φ g * u (g⁻¹ * x)) μ)
    (hv : Integrable (fun g => φ g * v (g⁻¹ * x)) μ) :
    2 * ‖genuineConvolution K μ φ v x‖ ≤
      ‖genuineConvolution K μ φ (fun y => u y + v y) x‖ +
      ‖genuineConvolution K μ φ (fun y => u y - v y) x‖ := by
  have ha : genuineConvolution K μ φ (fun y => u y + v y) x =
      genuineConvolution K μ φ u x + genuineConvolution K μ φ v x := by
    simp only [genuineConvolution, mul_add]
    exact integral_add hu hv
  have hs : genuineConvolution K μ φ (fun y => u y - v y) x =
      genuineConvolution K μ φ u x - genuineConvolution K μ φ v x := by
    simp only [genuineConvolution, mul_sub]
    exact integral_sub hu hv
  rw [ha, hs]
  simpa only [ContinuousLinearMap.id_apply] using
    smoothedLift_pair_lower_bound (ContinuousLinearMap.id ℂ ℂ)
      (genuineConvolution K μ φ u x) (genuineConvolution K μ φ v x)

#check coefficientSeparation_liftNorm
#print axioms coefficientSeparation_liftNorm
#check genuineConvolution_lift_pair_lower_bound
#print axioms genuineConvolution_lift_pair_lower_bound
#check smoothedLift_finite_cost
#print axioms smoothedLift_finite_cost
#check smoothedLift_pair_lower_bound
#check quotientLift_pair_cost
#check genuineWeightedLift_pair_cost
#print axioms genuineWeightedLift_pair_cost

end NuclearBoundC90
