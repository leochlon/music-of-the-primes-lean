import Mathlib

/- Round 90 D: actual nuclear bound remains incomplete. This file initially
records only the operator-order remainder which a direct bound must control. -/
namespace Round90D
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem convolution_projection_remainder (A P : H →L[ℂ] H) :
    A.comp P = P.comp (A.comp P) + (ContinuousLinearMap.id ℂ H - P).comp (A.comp P) := by
  ext x
  simp

#check convolution_projection_remainder
#print axioms convolution_projection_remainder
end Round90D
