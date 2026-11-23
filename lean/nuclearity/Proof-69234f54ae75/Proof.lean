import Mathlib
open Complex Set
namespace MasulloGRH
/-- Genuine Riemann zeta under an imaginary norm twist, not a proxy spectrum.
For F=Q and chi=|.|^(i*tau), the finite Hecke function is zeta(s+i*tau).
The identification with the idele-class Euler product is still informal. -/
noncomputable def zetaNormTwist (tau : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + (tau : ℂ) * Complex.I)
def regularZetaTwistDomain (tau : ℝ) : Set ℂ :=
  {s | s + (tau : ℂ) * Complex.I ≠ 1}
theorem zetaNormTwist_differentiableOn (tau : ℝ) :
    DifferentiableOn ℂ (zetaNormTwist tau) (regularZetaTwistDomain tau) := by
  intro s hs
  exact ((differentiableAt_riemannZeta hs).comp s
    (differentiableAt_id.add_const _)).differentiableWithinAt
theorem regularZetaTwistDomain_isOpen (tau : ℝ) :
    IsOpen (regularZetaTwistDomain tau) := by
  exact isOpen_ne.preimage (continuous_id.add continuous_const)
theorem zetaNormTwist_analyticOnNhd (tau : ℝ) :
    AnalyticOnNhd ℂ (zetaNormTwist tau) (regularZetaTwistDomain tau) := by
  exact (zetaNormTwist_differentiableOn tau).analyticOnNhd
    (regularZetaTwistDomain_isOpen tau)
noncomputable def zetaNormTwistDivisor (tau : ℝ) :
    Function.locallyFinsuppWithin (regularZetaTwistDomain tau) ℤ :=
  MeromorphicOn.divisor (zetaNormTwist tau) (regularZetaTwistDomain tau)
theorem zetaNormTwistDivisor_apply (tau : ℝ) (s : ℂ)
    (hs : s + (tau : ℂ) * Complex.I ≠ 1) :
    zetaNormTwistDivisor tau s = (meromorphicOrderAt (zetaNormTwist tau) s).untop₀ := by
  exact MeromorphicOn.divisor_apply
    (zetaNormTwist_analyticOnNhd tau).meromorphicOn hs
end MasulloGRH
#check MasulloGRH.zetaNormTwist_differentiableOn
#print axioms MasulloGRH.zetaNormTwist_differentiableOn
#check MasulloGRH.regularZetaTwistDomain_isOpen
#print axioms MasulloGRH.regularZetaTwistDomain_isOpen
#check MasulloGRH.zetaNormTwist_analyticOnNhd
#print axioms MasulloGRH.zetaNormTwist_analyticOnNhd
#check MasulloGRH.zetaNormTwistDivisor_apply
#print axioms MasulloGRH.zetaNormTwistDivisor_apply

/- Finite-order repair copied with attribution from frozen F/r05/draft.
This is independently checked here, not presumed from peer text. -/
open Set Filter Topology
namespace MasulloGRH
/-- The actual Riemann zeta function, analytic away from its pole, on a
half-plane containing the complete open critical strip. -/
theorem genuine_zeta_analytic_left :
    AnalyticOnNhd ℂ riemannZeta {s : ℂ | s.re < 1} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
    intro h
    subst s
    norm_num at hs
  · exact isOpen_lt Complex.continuous_re continuous_const

theorem genuine_zeta_order_ne_top (s : ℂ) (hs : s.re < 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have hc : Convex ℝ {z : ℂ | z.re < 1} := by
    intro x hx y hy a b ha hb hab
    dsimp at hx hy
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      subst b
      simpa using hy
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1 := mul_lt_mul_of_pos_left hx ha'
      have h2 := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
      have h3 : a * x.re + b * y.re < 1 := by nlinarith
      simpa using h3
  have hz : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  have h0 : analyticOrderAt riemannZeta 0 = 0 :=
    (genuine_zeta_analytic_left 0 (by norm_num)).analyticOrderAt_eq_zero.mpr hz
  exact genuine_zeta_analytic_left.analyticOrderAt_ne_top_of_isPreconnected
    hc.isPreconnected (x := 0) (by norm_num) hs (by rw [h0]; simp)

theorem genuine_zeta_zeros_codiscrete :
    ∀ᶠ s in codiscreteWithin {s : ℂ | s.re < 1}, riemannZeta s ≠ 0 := by
  have hc : Convex ℝ {z : ℂ | z.re < 1} := by
    intro x hx y hy a b ha hb hab
    dsimp at hx hy
    by_cases ha0 : a = 0
    · subst a
      have hb1 : b = 1 := by linarith
      subst b
      simpa using hy
    · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have h1 := mul_lt_mul_of_pos_left hx ha'
      have h2 := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
      have h3 : a * x.re + b * y.re < 1 := by nlinarith
      simpa using h3
  rcases genuine_zeta_analytic_left.eqOn_zero_or_eventually_ne_zero_of_preconnected
    hc.isPreconnected with h | h
  · have hz := h (show (0 : ℂ) ∈ {s : ℂ | s.re < 1} by norm_num)
    simp [riemannZeta_zero] at hz
  · exact h

/-- Actual vertical translates; their identification with Q norm-character
Hecke functions remains an arithmetic interpretation, not an axiom. -/
noncomputable def genuineNormTwistedZeta (τ : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + (τ : ℂ) * Complex.I)

theorem genuine_norm_twist_order_ne_top (τ : ℝ) (s : ℂ) (hs : s.re < 1) :
    analyticOrderAt (genuineNormTwistedZeta τ) s ≠ ⊤ := by
  change analyticOrderAt (riemannZeta ∘ (fun z : ℂ => z + (τ : ℂ) * Complex.I)) s ≠ ⊤
  have hg : AnalyticAt ℂ (fun z : ℂ => z + (τ : ℂ) * Complex.I) s :=
    analyticAt_id.add analyticAt_const
  have hd : deriv (fun z : ℂ => z + (τ : ℂ) * Complex.I) s ≠ 0 := by simp
  rw [analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hg hd]
  apply genuine_zeta_order_ne_top
  simpa using hs
end MasulloGRH
#check MasulloGRH.genuine_zeta_analytic_left
#print axioms MasulloGRH.genuine_zeta_analytic_left
#check MasulloGRH.genuine_zeta_order_ne_top
#print axioms MasulloGRH.genuine_zeta_order_ne_top
#check MasulloGRH.genuine_zeta_zeros_codiscrete
#print axioms MasulloGRH.genuine_zeta_zeros_codiscrete
#check MasulloGRH.genuine_norm_twist_order_ne_top
#print axioms MasulloGRH.genuine_norm_twist_order_ne_top

namespace MasulloGRH
/-- Finite order prevents the genuine divisor from hiding a locally identically zero germ
in the left half-plane, which contains the full open critical strip. -/
theorem zetaNormTwist_order_finite_left (tau : ℝ) (s : ℂ) (hs : s.re < 1) :
    analyticOrderAt (zetaNormTwist tau) s ≠ ⊤ := by
  exact genuine_norm_twist_order_ne_top tau s hs
end MasulloGRH
#check MasulloGRH.zetaNormTwist_order_finite_left
#print axioms MasulloGRH.zetaNormTwist_order_finite_left
