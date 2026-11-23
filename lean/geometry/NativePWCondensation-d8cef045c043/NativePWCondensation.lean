import Mathlib

namespace NativePWCondensation

theorem full_input_remainder {R : Type*} [Ring R]
    (M S A : R) : M * S * A - M * S * A * S =
      M * S * A * (1-S) := by noncomm_ring

theorem source_trace_split {R : Type*} [Ring R]
    (S W A M : R) :
    S*A*M - W*M*A = (S-W)*A*M + W*(A*M-M*A) := by
  noncomm_ring

theorem source_invariant_condensation {R : Type*} [Ring R]
    (M S A W : R) (hSA : S*A*S = A*S) (hSW : S*W = W) :
    M*S*A*W = M*A*W := by
  calc
    M*S*A*W = M*(S*A*S)*W := by
      simp only [mul_assoc] at hSA ⊢
      rw [hSW]
    _ = M*(A*S)*W := by rw [hSA]
    _ = M*A*W := by simp only [mul_assoc, hSW]

end NativePWCondensation

#print axioms NativePWCondensation.full_input_remainder
#print axioms NativePWCondensation.source_trace_split
#print axioms NativePWCondensation.source_invariant_condensation

