import Mathlib

/-! Round 187 E: the two moment-removal operations in the actual Tate-seed
construction. The manuscript supplies their covariance by change of variables.
This checks the construction algebra, not the analytic covariance, the native
Bochner identity, or the full nuclear theorem. No nuclearity is a hypothesis. -/
namespace Round187E
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem norm_one_tate_seed
    (R : Module.End ℂ V) (d0 d1 Z : V →ₗ[ℂ] ℂ) (f : V) (c : ℂ)
    (hc : c ≠ 1) (h0 : d0 (R f) = d0 f) (h1 : d1 (R f) = d1 f)
    (hZ : Z (R f) = c * Z f) :
    let g := (c - 1)⁻¹ • (R f - f)
    d0 g = 0 ∧ d1 g = 0 ∧ Z g = Z f := by
  dsimp
  have hn : c - 1 ≠ 0 := sub_ne_zero.mpr hc
  constructor
  · simp [map_smul, map_sub, h0]
  constructor
  · simp [map_smul, map_sub, h1]
  · simp only [map_smul, map_sub, smul_eq_mul, hZ]
    field_simp

theorem euler_tate_seed
    (D : Module.End ℂ V) (d0 d1 Z : V →ₗ[ℂ] ℂ) (f : V) (z : ℂ)
    (h0 : ∀ v, d0 (D v) = 0) (h1 : ∀ v, d1 (D v) = d1 v)
    (hZ : ∀ v, Z (D v) = z * Z v) :
    let g := D (D f - f)
    d0 g = 0 ∧ d1 g = 0 ∧ Z g = z * (z - 1) * Z f := by
  dsimp
  constructor
  · exact h0 _
  constructor
  · rw [h1, map_sub, h1, sub_self]
  · rw [hZ, map_sub, hZ]
    ring

/-- κ is the ratio between Tate's class Haar and the native normalized Haar.
Multiplying the geometric seed by κ exactly cancels that ratio. -/
theorem native_haar_seed_normalization
    (M : V →ₗ[ℂ] ℂ) (g : V) (κ L : ℂ) (hκ : κ ≠ 0)
    (hM : M g = κ⁻¹ * L) : M (κ • g) = L := by
  rw [map_smul, smul_eq_mul, hM, ← mul_assoc, mul_inv_cancel₀ hκ, one_mul]

#check norm_one_tate_seed
#print axioms norm_one_tate_seed
#check euler_tate_seed
#print axioms euler_tate_seed
#check native_haar_seed_normalization
#print axioms native_haar_seed_normalization
end Round187E

/-! Round 188 E. Contour residues for the actual unbounded translation
operator must be integrated in its closed graph. This checks the integral
step using the graph as a complete subspace; no bounded full derivative,
spectral totality or nuclearity is a hypothesis. Native graph integrability
is derived in GLOBAL_ESTIMATE.md, not assumed from coefficient decay. -/
noncomputable section
open MeasureTheory
namespace Round188E
variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedSpace ℝ H]
  [IsScalarTower ℝ ℂ H] [CompleteSpace H]

/-- The two coordinate integrals lie in the same closed graph. Applied to
f(t) = g(t) • (R(z(t))x, z(t) • R(z(t))x - x), this proves generator-domain
membership of the contour integral, without requiring D to be bounded. -/
theorem native_resolvent_graph_integral
    (Γ : Submodule ℂ (H × H)) [CompleteSpace Γ]
    (μ : Measure X) (f : X → Γ) (hf : Integrable f μ) :
    ((∫ t, ((f t : H × H).1) ∂μ),
     (∫ t, ((f t : H × H).2) ∂μ)) ∈ Γ := by
  let p : Γ →L[ℂ] H := (ContinuousLinearMap.fst ℂ H H).comp Γ.subtypeL
  let q : Γ →L[ℂ] H := (ContinuousLinearMap.snd ℂ H H).comp Γ.subtypeL
  have hp := p.integral_comp_comm hf
  have hq := q.integral_comp_comm hf
  change (∫ t, (f t : H × H).1 ∂μ) = ((∫ t, f t ∂μ : Γ) : H × H).1 at hp
  change (∫ t, (f t : H × H).2 ∂μ) = ((∫ t, f t ∂μ : Γ) : H × H).2 at hq
  rw [hp, hq]
  exact (∫ t, f t ∂μ : Γ).property

#check native_resolvent_graph_integral
#print axioms native_resolvent_graph_integral
end Round188E
