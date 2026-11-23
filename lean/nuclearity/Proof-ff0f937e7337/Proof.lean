import Mathlib

/-! R190 A. Integrating-factor uniqueness for native resolvent residue
chains. This is used after the distributional generator equation has
been established. It assumes no spectral totality or nuclearity. -/
noncomputable section
namespace Round190A

/-- The native residue ODE, with a specified primitive for its lower-chain
forcing, has the explicit exponential-polynomial solution. -/
theorem native_residue_ode_primitive
    (f p : ℝ → ℂ) (p' : ℝ → ℂ) (zeta : ℂ)
    (hp : ∀ x, HasDerivAt p (p' x) x)
    (hf : ∀ x, HasDerivAt f
      (zeta * f x + Complex.exp (zeta * (x : ℂ)) * p' x) x)
    (x : ℝ) :
    f x = Complex.exp (zeta * (x : ℂ)) * (f 0 + p x - p 0) := by
  let g : ℝ → ℂ := fun t => Complex.exp (-zeta * (t : ℂ)) * f t - p t
  have hg (t : ℝ) : HasDerivAt g 0 t := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-zeta)).cexp
    have h := (he.mul (hf t)).sub (hp t)
    convert h using 1
    dsimp [g]
    have hexp : Complex.exp (-zeta * (t : ℂ)) *
        Complex.exp (zeta * (t : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      ring_nf
      exact Complex.exp_zero
    linear_combination -(p' t) * hexp
  have hconst : g x = g 0 := by
    exact is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt)
      (fun t => (hg t).deriv) x 0
  dsimp [g] at hconst
  simp only [mul_zero, Complex.exp_zero, one_mul] at hconst
  have hexp : Complex.exp (zeta * (x : ℂ)) *
      Complex.exp (-zeta * (x : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    exact Complex.exp_zero
  linear_combination Complex.exp (zeta * (x : ℂ)) * hconst - f x * hexp

#check native_residue_ode_primitive
#print axioms native_residue_ode_primitive
end Round190A

/-! R193 A. The native resolvent's column energy makes its Cayley map
contractive. This is the first step in deriving row energy without a
separate adjoint-generator domain assumption; see GLOBAL_ESTIMATE.md.
This component is not a certificate of native spectral exhaustion. -/
namespace Round193A
set_option linter.unusedSimpArgs false
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem native_resolvent_cayley_contraction
    (R : H →L[ℂ] H) (g : ℝ) (hg : 0 < g)
    (henergy : ∀ x : H, g * ‖R x‖ ^ 2 ≤ (inner ℂ (R x) x).re)
    (x : H) : ‖x - ((2 * g : ℝ) : ℂ) • R x‖ ≤ ‖x‖ := by
  have hsym : (inner ℂ x (R x)).re = (inner ℂ (R x) x).re :=
    inner_re_symm (𝕜 := ℂ) x (R x)
  have hsq : ‖x - ((2 * g : ℝ) : ℂ) • R x‖ ^ 2 =
      ‖x‖ ^ 2 - 4 * g * (inner ℂ (R x) x).re +
        4 * g ^ 2 * ‖R x‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp [inner_smul_right, Complex.mul_re, norm_smul,
      abs_of_pos hg, hsym]
    <;> ring
  have he := mul_le_mul_of_nonneg_left (henergy x) (by positivity : 0 ≤ 4 * g)
  nlinarith [norm_nonneg (x - ((2 * g : ℝ) : ℂ) • R x), norm_nonneg x]

#check native_resolvent_cayley_contraction
#print axioms native_resolvent_cayley_contraction
end Round193A
