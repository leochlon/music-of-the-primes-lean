import Mathlib

namespace NativeOrbitalUnfoldingR33

/-- The manuscript's decreasing indicators have this signed telescoping. -/
theorem shell_telescoping {E : Type*} [AddCommGroup E]
    (c : ℕ → E) (n : ℕ) :
    c 0 = c n - ∑ k ∈ Finset.range n, (c (k+1) - c k) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ]
    rw [hn]
    abel

/-- Retain the original Gram factor outside the entire decomposition. -/
theorem ordered_gram_shell {R : Type*} [Ring R]
    (g : R) (c : ℕ → R) (n : ℕ) :
    g * c 0 = g * c n - ∑ k ∈ Finset.range n, g * (c (k+1)-c k) := by
  have h := congrArg (fun x => g*x) (shell_telescoping c n)
  simpa only [mul_sub, Finset.mul_sum] using h

/-- The target is free convolution minus the ORIGINAL source term. -/
theorem target_shell_sign {R : Type*} [Ring R]
    (free source localPart shells : R) (h : source = localPart-shells) :
    free-source = free-localPart+shells := by rw [h]; abel

/-- Source cyclicity leaves an ordered mask commutator. -/
theorem mask_order {R : Type*} [Ring R] (g a m : R) :
    g*(a*m)-g*(m*a)=g*(a*m-m*a) := by noncomm_ring

end NativeOrbitalUnfoldingR33

#print axioms NativeOrbitalUnfoldingR33.shell_telescoping
#print axioms NativeOrbitalUnfoldingR33.ordered_gram_shell
#print axioms NativeOrbitalUnfoldingR33.target_shell_sign
#print axioms NativeOrbitalUnfoldingR33.mask_order
