import Mathlib

namespace NativeGlobalDiagonalR31

/-- Error of the actual finite source projection, with convolution already taken. -/
theorem native_projection_error {R : Type*} [Ring R] (T S E A : R) :
    T - (1-E)*A = (T-(1-S)*A) - (S-E)*A := by
  noncomm_ring

/-- A physical multiplier retains the source term in its original order. -/
theorem localized_source_defect {R : Type*} [Ring R]
    (tr : R →+ ℂ) (M S A : R) :
    tr (M*((1-S)*A)) = tr (M*A) - tr ((M*S)*A) := by
  have h : M*((1-S)*A) = M*A-(M*S)*A := by noncomm_ring
  rw [h, map_sub]

/-- Original annihilating rows remove the source term only in the total trace. -/
theorem unmasked_trace {R : Type*} [Ring R]
    (tr : R →+ ℂ) (S A : R)
    (hcyc : tr (S*A) = tr (A*S)) (hrow : A*S=0) :
    tr ((1-S)*A) = tr A := by
  have h : (1-S)*A=A-S*A := by noncomm_ring
  rw [h, map_sub, hcyc, hrow, map_zero, sub_zero]

/-- Merely reversing projection and convolution leaves an ordered cross block. -/
theorem ordered_cross_block {R : Type*} [Ring R]
    (S A : R) (hinv : (1-S)*A*S=0) :
    A*(1-S) - (1-S)*A = S*A*(1-S) := by
  have h : A*(1-S) - (1-S)*A = S*A*(1-S) - (1-S)*A*S := by
    noncomm_ring
  rw [h, hinv, sub_zero]

#print axioms native_projection_error
#print axioms localized_source_defect
#print axioms unmasked_trace
#print axioms ordered_cross_block
end NativeGlobalDiagonalR31
