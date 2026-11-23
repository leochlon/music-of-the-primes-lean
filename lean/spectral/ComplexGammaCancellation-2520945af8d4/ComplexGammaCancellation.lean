import Mathlib

open Complex
open scoped BigOperators Topology
noncomputable section
namespace SpectralG909

/-- Reciprocal Gamma recurrence, including every totalized Gamma pole. -/
theorem invGamma_step (s : ℂ) :
    (Gamma s)⁻¹ = s * (Gamma (s + 1))⁻¹ := by
  by_cases hs : s = 0
  · subst s; simp
  · rw [Gamma_add_one s hs, mul_inv]
    simp [hs]

theorem invGamma_shift (j : ℕ) (s : ℂ) :
    (Gamma s)⁻¹ = (∏ k ∈ Finset.range j, (s + (k : ℂ))) *
      (Gamma (s + (j : ℂ)))⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      (Gamma s)⁻¹ = (∏ k ∈ Finset.range j, (s + (k : ℂ))) *
          (Gamma (s + (j : ℂ)))⁻¹ := ih
      _ = (∏ k ∈ Finset.range j, (s + (k : ℂ))) *
          ((s + (j : ℂ)) * (Gamma (s + (j : ℂ) + 1))⁻¹) :=
        congrArg (fun z => (∏ k ∈ Finset.range j, (s + (k : ℂ))) * z)
          (invGamma_step (s + (j : ℂ)))
      _ = _ := by rw [Finset.prod_range_succ]; push_cast; ring

/-- Entire extension of the normalized j-th Taylor polar term. -/
def cancelledPole (j : ℕ) (s : ℂ) : ℂ :=
  (∏ k ∈ Finset.range j, (s + (k : ℂ))) *
    (Gamma (s + (j : ℂ) + 1))⁻¹

theorem cancelledPole_entire (j : ℕ) : Differentiable ℂ (cancelledPole j) := by
  have hP : Differentiable ℂ (fun s : ℂ => ∏ k ∈ Finset.range j, (s + (k : ℂ))) := by
    fun_prop
  exact hP.mul (differentiable_one_div_Gamma.comp
    ((differentiable_id.add_const (j : ℂ)).add_const 1))

theorem cancelledPole_identity (j : ℕ) (s : ℂ) :
    (s + (j : ℂ)) * cancelledPole j s = (Gamma s)⁻¹ := by
  have h := invGamma_shift (j + 1) s
  rw [Finset.prod_range_succ] at h
  simp only [Nat.cast_add, Nat.cast_one, ← add_assoc] at h
  rw [h]
  unfold cancelledPole
  ring

theorem cancelledPole_eq_quotient (j : ℕ) (s : ℂ) (hs : s + (j : ℂ) ≠ 0) :
    cancelledPole j s = (Gamma s)⁻¹ / (s + (j : ℂ)) := by
  apply (eq_div_iff hs).2
  simpa [mul_comm] using cancelledPole_identity j s

/-- All integer angular modes and all real radial twists of the complex local factor. -/
def complexPole (m : ℤ) (τ : ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  cancelledPole j (s + (τ : ℂ) * I + (m.natAbs : ℂ) / 2)

theorem complexPole_entire (m : ℤ) (τ : ℝ) (j : ℕ) :
    Differentiable ℂ (complexPole m τ j) :=
  (cancelledPole_entire j).comp
    ((differentiable_id.add_const ((τ : ℂ) * I)).add_const ((m.natAbs : ℂ) / 2))

theorem complexPole_analytic (m : ℤ) (τ : ℝ) (j : ℕ) (s : ℂ) :
    AnalyticAt ℂ (complexPole m τ j) s :=
  (complexPole_entire m τ j).analyticAt s

/-- The exponential prefactor converting reciprocal Gamma to Gamma_C
for the radial Taylor term after division by pi Gamma_C. -/
def normalizedComplexPole (m : ℤ) (τ : ℝ) (j : ℕ) (s : ℂ) : ℂ :=
  Complex.exp ((s + (τ : ℂ) * I + (m.natAbs : ℂ) / 2) *
    Complex.log (2 * (Real.pi : ℂ))) * complexPole m τ j s

theorem normalizedComplexPole_entire (m : ℤ) (τ : ℝ) (j : ℕ) :
    Differentiable ℂ (normalizedComplexPole m τ j) := by
  have h : Differentiable ℂ (fun s : ℂ =>
      Complex.exp ((s + (τ : ℂ) * I + (m.natAbs : ℂ) / 2) *
        Complex.log (2 * (Real.pi : ℂ)))) := by fun_prop
  exact h.mul (complexPole_entire m τ j)

#print axioms SpectralG909.normalizedComplexPole_entire
#print axioms SpectralG909.complexPole_analytic
#print axioms SpectralG909.cancelledPole_eq_quotient
end SpectralG909
