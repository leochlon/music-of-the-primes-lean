import Mathlib

/-! Round 184 A: the positive two-centre kernel in the NEW arithmetic
step of GLOBAL_ESTIMATE.md. For the actual completed Hecke zeros, beta is
Re rho and t is Im rho - T. Subtracting logarithmic derivatives at 2+iT
and -1+iT produces exactly these two kernels. This verifies their finite
weighted domination, not the Hadamard identity or native nuclearity.
No summability or nuclearity hypothesis is introduced. -/
noncomputable section
namespace Round184A

def twoCentreKernel (beta t : ℝ) : ℝ :=
  (2-beta) / ((2-beta)^2+t^2) + (1+beta) / ((1+beta)^2+t^2)

theorem one_pole_comparison (a t : ℝ) (ha : 1 ≤ a) (hb : a ≤ 2) :
    1 / (1+t^2) ≤ 2 * (a / (a^2+t^2)) := by
  have h1 : 0 < 1+t^2 := by positivity
  have h2 : 0 < a^2+t^2 := by nlinarith [sq_nonneg t]
  have h3 : 0 ≤ a*(2-a) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ (2*a-1)*t^2 := mul_nonneg (by linarith) (sq_nonneg t)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ h1 h2).2
  nlinarith

theorem two_centre_zero_kernel (beta t : ℝ)
    (h0 : 0 ≤ beta) (h1 : beta ≤ 1) :
    1 / (1+t^2) ≤ twoCentreKernel beta t := by
  have hl := one_pole_comparison (2-beta) t (by linarith) (by linarith)
  have hr := one_pole_comparison (1+beta) t (by linarith) (by linarith)
  unfold twoCentreKernel
  linarith

/-- Every finite zero window, with its full arithmetic multiplicities,
is dominated by the positive logarithmic-derivative difference. In the
paper derivation this holds for all windows, whose monotone limit is
bounded by twice Re(Xi'/Xi)(2+iT); that analytic identity is not assumed
as a substitute for proving it in the accompanying derivation. -/
theorem weighted_zero_kernel_domination
    {ι : Type*} (J : Finset ι) (beta ordinate : ι → ℝ) (multiplicity : ι → ℕ)
    (T : ℝ) (h0 : ∀ i ∈ J, 0 ≤ beta i) (h1 : ∀ i ∈ J, beta i ≤ 1) :
    (∑ i ∈ J, (multiplicity i : ℝ) * (1 / (1+(ordinate i-T)^2))) ≤
      ∑ i ∈ J, (multiplicity i : ℝ) * twoCentreKernel (beta i) (ordinate i-T) := by
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left
      (two_centre_zero_kernel (beta i) (ordinate i-T) (h0 i hi) (h1 i hi))
      (Nat.cast_nonneg _)

#check two_centre_zero_kernel
#print axioms two_centre_zero_kernel
#check weighted_zero_kernel_domination
#print axioms weighted_zero_kernel_domination
end Round184A
