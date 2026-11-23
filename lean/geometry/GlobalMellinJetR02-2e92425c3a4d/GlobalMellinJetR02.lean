import Mathlib

/-! The actual Mellin-jet matrix used in GLOBAL_SPECTRAL_R02.md.
The coefficients are the Mellin derivatives of the convolution test.
This file checks the finite-dimensional trace computation, not Lidskii,
the adelic quotient, or the final explicit formula. -/
noncomputable section
open scoped BigOperators
namespace GlobalMellinJetR02

/-- Row i is the action on the i-th, unnormalised Mellin derivative. -/
def jetMatrix (n : ℕ) (c : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if j.val ≤ i.val then
    (Nat.choose i.val j.val : ℂ) * c (i.val - j.val) else 0

theorem jetMatrix_diagonal (n : ℕ) (c : ℕ → ℂ) (i : Fin n) :
    jetMatrix n c i i = c 0 := by
  simp [jetMatrix]

theorem jetMatrix_above (n : ℕ) (c : ℕ → ℂ) (i j : Fin n)
    (h : i.val < j.val) : jetMatrix n c i j = 0 := by
  simp [jetMatrix, Nat.not_le.mpr h]

/-- A zero of order n contributes n times the zeroth Mellin coefficient;
the logarithmic derivatives in the off-diagonal entries do not alter it. -/
theorem jetMatrix_trace (n : ℕ) (c : ℕ → ℂ) :
    Matrix.trace (jetMatrix n c) = (n : ℂ) * c 0 := by
  simp [Matrix.trace, Matrix.diag, jetMatrix]

/-- Multiplying the test by -log(norm) shifts every Mellin derivative.
This is the sharp logarithmic test specified in the application. -/
def logSharpCoefficients (c : ℕ → ℂ) (j : ℕ) : ℂ := -c (j + 1)

theorem logSharp_trace (n : ℕ) (c : ℕ → ℂ) :
    Matrix.trace (jetMatrix n (logSharpCoefficients c)) =
      -(n : ℂ) * c 1 := by
  rw [jetMatrix_trace]
  simp [logSharpCoefficients]

/-- A finite collection of genuine root spaces, with their multiplicities. -/
theorem finite_root_trace {ι : Type*} (s : Finset ι)
    (multiplicity : ι → ℕ) (c : ι → ℕ → ℂ) :
    (∑ i ∈ s, Matrix.trace (jetMatrix (multiplicity i) (c i))) =
      ∑ i ∈ s, (multiplicity i : ℂ) * c i 0 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact jetMatrix_trace _ _

end GlobalMellinJetR02

#print axioms GlobalMellinJetR02.jetMatrix_trace
#print axioms GlobalMellinJetR02.logSharp_trace
#print axioms GlobalMellinJetR02.finite_root_trace
