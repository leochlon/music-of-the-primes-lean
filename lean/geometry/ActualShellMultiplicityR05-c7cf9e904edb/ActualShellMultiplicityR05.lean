import Mathlib

/-! Algebra of the actual two adelic moments and their theta-regularization
cocycle. The analytic identifications are proved in APPLICATION_R03.md.
No projected trace identity is assumed here. -/
noncomputable section
open scoped BigOperators
namespace ActualPolarApplication

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def momentKernel (m₀ m₁ : E →ₗ[ℂ] ℂ) : Submodule ℂ E :=
  m₀.ker ⊓ m₁.ker

/-- Explicit moment-zero remainder for the actual normalized polar tests. -/
theorem polar_remainder (m₀ m₁ : E →ₗ[ℂ] ℂ) (e₀ e₁ f : E)
    (h00 : m₀ e₀ = 1) (h01 : m₀ e₁ = 0)
    (h10 : m₁ e₀ = 0) (h11 : m₁ e₁ = 1) :
    f - (m₀ f • e₀ + m₁ f • e₁) ∈ momentKernel m₀ m₁ := by
  constructor <;> simp [LinearMap.mem_ker, h00, h01, h10, h11]

/-- The two actual normalized tests are constructed from one test and its
idele dilation; the integral of the initial test need not be one. -/
theorem normalized_polar_tests (m₀ m₁ : E →ₗ[ℂ] ℂ) (e re : E)
    (q c : ℂ) (hq : q - 1 ≠ 0) (hc : c ≠ 0)
    (h0 : m₀ e = 1) (hr0 : m₀ re = 1)
    (h1 : m₁ e = c) (hr1 : m₁ re = q * c) :
    let e₀ := (q - 1)⁻¹ • (q • e - re)
    let e₁ := (c * (q - 1))⁻¹ • (re - e)
    m₀ e₀ = 1 ∧ m₁ e₀ = 0 ∧ m₀ e₁ = 0 ∧ m₁ e₁ = 1 := by
  dsimp
  simp only [map_smul, map_sub, smul_eq_mul, h0, hr0, h1, hr1]
  field_simp
  all_goals simp_all

/-- Dilation/convolution preserves the true S_0 kernel of both moments. -/
theorem moment_kernel_invariant (m₀ m₁ : E →ₗ[ℂ] ℂ)
    (B : E →ₗ[ℂ] E) (p q : ℂ)
    (h0 : ∀ f, m₀ (B f) = p * m₀ f)
    (h1 : ∀ f, m₁ (B f) = q * m₁ f)
    {f : E} (hf : f ∈ momentKernel m₀ m₁) :
    B f ∈ momentKernel m₀ m₁ := by
  rcases hf with ⟨hf0, hf1⟩
  constructor
  · change m₀ (B f) = 0
    rw [h0, show m₀ f = 0 from hf0, mul_zero]
  · change m₁ (B f) = 0
    rw [h1, show m₁ f = 0 from hf1, mul_zero]

/-- Matrix trace of the induced operator on the actual two-moment quotient. -/
theorem polar_matrix_trace (p q : ℂ) :
    Matrix.trace (Matrix.diagonal ![p, q]) = p + q := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- A theta regularization has precisely this finite-rank defect under
convolution. In the application c₀,c₁ are explicit compact radial functions. -/
theorem regularization_defect_range
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (m₀ m₁ : E →ₗ[ℂ] ℂ) (c₀ c₁ : F) (f : E) :
    m₁ f • c₁ - m₀ f • c₀ ∈ Submodule.span ℂ ({c₀, c₁} : Set F) := by
  apply Submodule.sub_mem
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

/-- The defect vanishes on precisely the source subspace used to define
Masullo's geometric theta closure. -/
theorem regularization_defect_zero
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (m₀ m₁ : E →ₗ[ℂ] ℂ) (c₀ c₁ : F) {f : E}
    (hf : f ∈ momentKernel m₀ m₁) :
    m₁ f • c₁ - m₀ f • c₀ = 0 := by
  rcases hf with ⟨hf0, hf1⟩
  simp [show m₀ f = 0 from hf0, show m₁ f = 0 from hf1]

end ActualPolarApplication
#print axioms ActualPolarApplication.normalized_polar_tests
#print axioms ActualPolarApplication.polar_matrix_trace
#print axioms ActualPolarApplication.regularization_defect_zero

namespace ActualShellMultiplicityR05
noncomputable section
open ActualPolarApplication
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def eliminate (R : E →ₗ[ℂ] E) (q : ℂ) (f : E) : E :=
  R (R f - q • f) - (R f - q • f)

theorem eliminate_mem (m₀ m₁ : E →ₗ[ℂ] ℂ)
    (R : E →ₗ[ℂ] E) (q : ℂ)
    (h₀ : ∀ f, m₀ (R f) = m₀ f)
    (h₁ : ∀ f, m₁ (R f) = q * m₁ f) (f : E) :
    eliminate R q f ∈ momentKernel m₀ m₁ := by
  constructor
  · change m₀ (eliminate R q f) = 0
    simp only [eliminate, map_sub, h₀, sub_self]
  · change m₁ (eliminate R q f) = 0
    simp only [eliminate, map_sub, map_smul, smul_eq_mul, h₁]
    ring

theorem eliminate_commutes (R S : E →ₗ[ℂ] E) (q : ℂ)
    (hRS : ∀ f, R (S f) = S (R f)) (f : E) :
    eliminate R q (S f) = S (eliminate R q f) := by
  simp only [eliminate, map_sub, map_smul, hRS]

theorem eliminate_eigen (L : E →ₗ[ℂ] ℂ) (R : E →ₗ[ℂ] E)
    (q c : ℂ) (hL : ∀ f, L (R f) = c * L f) (f : E) :
    L (eliminate R q f) = ((c - 1) * (c - q)) * L f := by
  simp only [eliminate, map_sub, map_smul, smul_eq_mul, hL]
  ring

/-- Normalization in the extension from the actual S_0 moment kernel. -/
theorem extension_restrict (q c t : ℂ) (h₀ : c ≠ 1) (h₁ : c ≠ q) :
    (((c - 1) * (c - q))⁻¹) * (((c - 1) * (c - q)) * t) = t := by
  exact inv_mul_cancel_left₀ (mul_ne_zero (sub_ne_zero.mpr h₀)
    (sub_ne_zero.mpr h₁)) t

/-- Commutativity forces the integral-moment cocycle to be a coboundary. -/
theorem exceptional_integral_cocycle (b_g b_k q_g q_k : ℂ)
    (hk : q_k ≠ 1)
    (hcomm : b_g * q_k + b_k = b_k * q_g + b_g) :
    b_g = (b_k / (q_k - 1)) * (q_g - 1) := by
  field_simp [sub_ne_zero.mpr hk]
  linear_combination hcomm

end
end ActualShellMultiplicityR05
#print axioms ActualShellMultiplicityR05.eliminate_mem
#print axioms ActualShellMultiplicityR05.eliminate_commutes
#print axioms ActualShellMultiplicityR05.eliminate_eigen
#print axioms ActualShellMultiplicityR05.extension_restrict
#print axioms ActualShellMultiplicityR05.exceptional_integral_cocycle
