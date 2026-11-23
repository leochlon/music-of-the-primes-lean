import Mathlib
namespace MasulloGRH.Round4A
/-- CONDITIONAL normalization audit for Appendix B.4.2.3: discharges the
chain-rule sign in the logarithmic derivative of a completed functional
equation, provided that equation and local holomorphy have been established.
This does not assume or construct any zero set, trace, or L-function. -/
theorem logDeriv_reflection_of_completed_FE
    (L Ldual : ℂ → ℂ) (a b s : ℂ)
    (hdual : DifferentiableAt ℂ Ldual (1 - s))
    (hne : Ldual (1 - s) ≠ 0)
    (hFE : ∀ z, L z = Complex.exp (a - b * z) * Ldual (1 - z)) :
    deriv L s / L s = -b - deriv Ldual (1 - s) / Ldual (1 - s) := by
  have hEq : L = fun z => Complex.exp (a - b * z) * Ldual (1 - z) := funext hFE
  rw [hEq]
  have hExp := ((hasDerivAt_const s a).sub ((hasDerivAt_id s).const_mul b)).cexp
  have hRef := hdual.hasDerivAt.comp s ((hasDerivAt_const s (1 : ℂ)).sub (hasDerivAt_id s))
  have hd := (hExp.mul hRef).deriv
  change deriv (fun z : ℂ => Complex.exp (a - b * z) * Ldual (1 - z)) s = _ at hd
  rw [hd]
  have hexp : Complex.exp (a - b * s) ≠ 0 := Complex.exp_ne_zero _
  dsimp
  field_simp [hexp, hne]
  ring

#check logDeriv_reflection_of_completed_FE
#print axioms logDeriv_reflection_of_completed_FE
end MasulloGRH.Round4A
