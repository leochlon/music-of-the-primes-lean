import Mathlib
set_option linter.unusedSimpArgs false
open Complex Filter Topology

namespace DCorrectionApplicationR03
open Filter Topology

theorem common_physical_diagonal
    (cut : ℕ → ℕ → Fin 2 → Fin 2 → ℂ → ℂ)
    (uncut : ℕ → Fin 2 → Fin 2 → ℂ → ℂ)
    (K : ℕ → Set ℂ) (err : ℕ → ℝ)
    (hphysical : ∀ n, ∃ cutoffBound : ℕ, ∀ R, cutoffBound ≤ R → ∀ b j z, z ∈ K n →
      ‖cut n R b j z - uncut n b j z‖ ≤ err n) :
    ∃ R : ℕ → ℕ, (∀ n, n ≤ R n) ∧
      ∀ n b j z, z ∈ K n →
        ‖cut n (R n) b j z - uncut n b j z‖ ≤ err n := by
  classical
  choose cutoffBound hBound using hphysical
  refine ⟨fun n => max n (cutoffBound n), fun n => le_max_left _ _, ?_⟩
  intro n b j z hz
  exact hBound n _ (le_max_right _ _) b j z hz

/-- Error for wide minus narrow traces, for either sharp test. -/
theorem correction_diagonal_error (a b c d : ℂ) (e : ℝ)
    (ha : ‖a-b‖ ≤ e) (hc : ‖c-d‖ ≤ e) :
    ‖(a-c)-(b-d)‖ ≤ 2*e := by
  have he : (a-c)-(b-d) = (a-b)-(c-d) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The selected actual physical traces inherit the independently proved
Fermat cutoff-series limit. No zero-limit correction premise is present. -/
theorem correction_diagonal_limit
    (physical exactValue : ℕ → ℂ) (target : ℂ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hcut : ∀ n, ‖physical n - exactValue n‖ ≤ 2 * err n)
    (hexact : Tendsto exactValue atTop (𝓝 target)) :
    Tendsto physical atTop (𝓝 target) := by
  have hnorm : Tendsto (fun n => ‖physical n-exactValue n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hcut (by simpa using herr.const_mul 2)
  have hdiff : Tendsto (fun n => physical n-exactValue n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa using hdiff.add hexact

#print axioms common_physical_diagonal
#print axioms correction_diagonal_error
#print axioms correction_diagonal_limit
end DCorrectionApplicationR03

/-! The actual wide Riesz block lies in the geometric correction kernel.
In the application B and C are the shifted wide and narrow convolution
operators, and J is the actual dense quotient map. No assertion about a
zero-free half-plane or a zero correction is a premise. -/
namespace DCorrectionApplicationR04
open Filter Topology

theorem root_block_in_geometric_kernel
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (B : E →L[ℂ] E) (C : F →L[ℂ] F) (J : E →L[ℂ] F)
    (hJC : ∀ x, J (B x) = C (J x)) (hC : Function.Injective C)
    (n : ℕ) (x : E) (hx : (fun y => B y)^[n] x = 0) : J x = 0 := by
  induction n generalizing x with
  | zero => simpa using congrArg J hx
  | succ n ih =>
    have hBx : (fun y => B y)^[n] (B x) = 0 := by
      simpa only [Function.iterate_succ_apply] using hx
    have hJx : J (B x) = 0 := ih (B x) hBx
    apply hC
    simpa only [_root_.map_zero, ← hJC] using hJx

/-- Negative sharp support places the pole at the reflected zero 1-rho. -/
theorem reflected_negative_exponent (z q : ℂ) :
    (z-(1/2:ℂ)) + ((1-q)-(1/2:ℂ)) = z-q := by ring

/-- A genuine finite root block has the full multiplicity trace, despite
its possible nonorthogonal Jordan coordinates. This is a matrix trace
identity, not an identification of the ambient operator with a zero model. -/
theorem root_block_trace {m : ℕ} (a : ℂ)
    (N : Matrix (Fin m) (Fin m) ℂ) (hN : ∀ i, N i i = 0) :
    Matrix.trace (a • (1 : Matrix (Fin m) (Fin m) ℂ) + N) = (m:ℂ)*a := by
  classical
  simp [Matrix.trace, Matrix.diag, hN, mul_comm]

/-- Both anchored scalar block transforms keep the SAME reference. -/
theorem anchored_block_scaled_limit (m : ℕ) (q b : ℂ)
    (hq : q ≠ b) :
    Tendsto (fun z => (z-q)^2 * ((m:ℂ) *
      ((1:ℂ)/(z-q)^2 - (1:ℂ)/(b-q)^2))) (𝓝[≠] q) (𝓝 (m:ℂ)) := by
  have ht : Tendsto (fun z : ℂ => (m:ℂ) - (z-q)^2 * ((m:ℂ)/(b-q)^2))
      (𝓝[≠] q) (𝓝 (m:ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ =>
        (m:ℂ) - (z-q)^2 * ((m:ℂ)/(b-q)^2)) q := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzq : z-q ≠ 0 := sub_ne_zero.mpr hz
  have hbq : b-q ≠ 0 := sub_ne_zero.mpr hq.symm
  field_simp [hzq, hbq]

#print axioms root_block_in_geometric_kernel
#print axioms root_block_trace
#print axioms anchored_block_scaled_limit
end DCorrectionApplicationR04

namespace DSourceR04
theorem fermat_eventually_large_norm {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, R ≤ ‖ρ j‖ := by
  have _em := Classical.em
  have h0 := hsum.tendsto_atTop_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]


#print axioms fermat_eventually_large_norm
end DSourceR04


/-! Actual trace-density control used in GLOBAL_ROW_LIMIT_R06.md.
The Holder argument is copied at its exact general scope from ALPO
HilbertSchmidtKernel.lean:12-27 and checked here.  Adelic instantiation
and the trace-class diagonal construction are paper mathematics. -/
noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace
namespace ActualRowDensityR06

 theorem product_density_sq_bound {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (f g : X → ℂ)
    (hf : AEStronglyMeasurable f mu) (hg : AEStronglyMeasurable g mu) :
    (∫⁻ x, ‖f x * g x‖ₑ ∂mu)^2 ≤
      (∫⁻ x, ‖f x‖ₑ^2 ∂mu) * ∫⁻ x, ‖g x‖ₑ^2 ∂mu := by
  simp only [enorm_mul]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq mu
    Real.HolderConjugate.two_two hf.enorm hg.enorm
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂mu)^2
      ≤ ((∫⁻ x, ‖f x‖ₑ^2 ∂mu)^(1/2 : ℝ) *
          (∫⁻ x, ‖g x‖ₑ^2 ∂mu)^(1/2 : ℝ))^2 := by gcongr
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_natCast (_ ^ (1/2 : ℝ)),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      norm_num

 theorem multiplier_row {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (eta : ℂ) (k v : H) :
    ⟪star eta • k, v⟫_ℂ = eta * ⟪k,v⟫_ℂ := by
  simp [mul_comm]

 theorem density_unique {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [SigmaFinite mu] (d e : X → ℂ)
    (hd : Integrable d mu) (he : Integrable e mu)
    (h : ∀ S : Set X, MeasurableSet S → mu S < ⊤ →
      (∫ x in S, d x ∂mu) = ∫ x in S, e x ∂mu) : d =ᵐ[mu] e := by
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun _ _ _ => hd.integrableOn) (fun _ _ _ => he.integrableOn) h

 def leftShift : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;0,0]
 def rightShift : Matrix (Fin 2) (Fin 2) ℂ := !![0,0;1,0]

 /-- Cyclic trace equality cannot identify the measured diagonal. -/
 theorem cyclic_trace_not_density :
    Matrix.trace (leftShift * rightShift) =
      Matrix.trace (rightShift * leftShift) ∧
    (leftShift * rightShift) 0 0 ≠ (rightShift * leftShift) 0 0 := by
  norm_num [leftShift, rightShift, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fin.sum_univ_two]

end ActualRowDensityR06
#print axioms ActualRowDensityR06.product_density_sq_bound
#print axioms ActualRowDensityR06.multiplier_row
#print axioms ActualRowDensityR06.density_unique
#print axioms ActualRowDensityR06.cyclic_trace_not_density

namespace DCorrectionDensityR05
open MeasureTheory Filter Topology

/-- The all-multiplier estimate used for the actual correction density.
Integrability here follows from bounded eta and the two L1 densities. -/
theorem multiplier_density_error {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (eta d e : X → ℂ)
    (hd : Integrable (fun x => d x - e x) mu)
    (hprod : Integrable (fun x => eta x * (d x-e x)) mu)
    (heta : ∀ᵐ x ∂mu, ‖eta x‖ ≤ 1) :
    ‖∫ x, eta x * (d x-e x) ∂mu‖ ≤ ∫ x, ‖d x-e x‖ ∂mu := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae hprod.norm hd.norm
  filter_upwards [heta] with x hx
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_right hx (norm_nonneg (d x-e x))

/-- The penalty fixes the actual omitted root block BEFORE the original
physical multiplier is applied; no cyclic density identification is used. -/
theorem penalty_exterior_block_exact
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →L[ℂ] F) (S R B M : E →L[ℂ] E)
    (hR : ∀ x, J (R x) = 0)
    (hS : ∀ x, J x = 0 → S x = x) :
    S.comp (R.comp (B.comp M)) = R.comp (B.comp M) := by
  ext x
  exact hS (R (B (M x))) (hR (B (M x)))

/-- One common path controls BOTH sharp-test densities and every bounded
multiplier, once the actual HS tail and physical tail are below e_n. -/
theorem common_density_path
    (error : ℕ → ℕ → ℕ → Fin 2 → ℝ) (eps : ℕ → ℝ)
    (h : ∀ n, ∃ penaltyBound physicalBound : ℕ,
      ∀ k r, penaltyBound ≤ k → physicalBound ≤ r →
        ∀ j, error n k r j ≤ eps n) :
    ∃ k r : ℕ → ℕ, (∀ n, n ≤ k n ∧ n ≤ r n) ∧
      ∀ n j, error n (k n) (r n) j ≤ eps n := by
  classical
  choose penaltyBound physicalBound hb using h
  refine ⟨fun n => max n (penaltyBound n),
    fun n => max n (physicalBound n), ?_, ?_⟩
  · intro n
    exact ⟨le_max_left _ _, le_max_left _ _⟩
  · intro n j
    exact hb n _ _ (le_max_right _ _) (le_max_right _ _) j

#print axioms multiplier_density_error
#print axioms penalty_exterior_block_exact
#print axioms common_density_path
end DCorrectionDensityR05
