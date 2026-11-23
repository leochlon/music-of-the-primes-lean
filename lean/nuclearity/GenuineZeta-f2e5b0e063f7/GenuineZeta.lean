import Mathlib
noncomputable section
open Filter Topology
namespace MasulloGRH
/-- Actual finite Hecke L-function for the trivial character of Q, on the
    half-plane containing its entire critical strip and excluding its pole. -/
def zetaRegularDomain : Set ℂ := {s | s.re < 1}

theorem zetaRegularDomain_open : IsOpen zetaRegularDomain :=
  isOpen_lt Complex.continuous_re continuous_const

theorem zetaRegularDomain_convex : Convex ℝ zetaRegularDomain := by
  intro x hx y hy a b ha hb hab
  change (a • x + b • y).re < 1
  change Complex.reCLM (a • x + b • y) < 1
  rw [map_add, map_smul, map_smul]
  change a * x.re + b * y.re < 1
  have hx' : 0 < 1 - x.re := sub_pos.mpr hx
  have hy' : 0 < 1 - y.re := sub_pos.mpr hy
  have ha' := mul_nonneg ha hx'.le
  have hb' := mul_nonneg hb hy'.le
  rcases eq_or_lt_of_le ha with h | h
  · have : a = 0 := h.symm
    subst a
    simp_all [zetaRegularDomain]
  · have := mul_pos h hx'
    nlinarith

theorem riemannZeta_analytic_regularDomain :
    AnalyticOnNhd ℂ riemannZeta zetaRegularDomain := by
  apply DifferentiableOn.analyticOnNhd _ zetaRegularDomain_open
  intro s hs
  apply (differentiableAt_riemannZeta _).differentiableWithinAt
  intro h
  subst s
  norm_num [zetaRegularDomain] at hs

theorem riemannZeta_order_finite {s : ℂ} (hs : s.re < 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h0 : (0 : ℂ) ∈ zetaRegularDomain := by norm_num [zetaRegularDomain]
  apply riemannZeta_analytic_regularDomain.analyticOrderAt_ne_top_of_isPreconnected
    zetaRegularDomain_convex.isPreconnected h0 hs
  rw [(riemannZeta_analytic_regularDomain 0 h0).analyticOrderAt_eq_zero.mpr]
  · simp
  · rw [riemannZeta_zero]
    norm_num

/-- Genuine divisor, not a chosen sequence: coefficients are the local
    meromorphic orders of Mathlib's Riemann zeta function. -/
def zetaDivisor : Function.locallyFinsuppWithin zetaRegularDomain ℤ :=
  MeromorphicOn.divisor riemannZeta zetaRegularDomain

theorem riemannZeta_zero_positive_finite_multiplicity {s : ℂ}
    (hs : s.re < 1) (hz : riemannZeta s = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      ∀ᶠ z in 𝓝 s, riemannZeta z = (z - s)^n * g z := by
  obtain ⟨g, hg, hg0, hfac⟩ :=
    (riemannZeta_analytic_regularDomain s hs).analyticOrderAt_ne_top.mp
      (riemannZeta_order_finite hs)
  refine ⟨analyticOrderNatAt riemannZeta s, ?_, g, hg, hg0, ?_⟩
  · by_contra h
    have hn : analyticOrderNatAt riemannZeta s = 0 := Nat.eq_zero_of_not_pos h
    have hv := hfac.self_of_nhds
    simp [hn, hz] at hv
    exact hg0 hv.symm
  · simpa only [smul_eq_mul] using hfac

theorem zetaDivisor_locally_finite {s : ℂ} (hs : s.re < 1) :
    ∃ t ∈ 𝓝 s, (t ∩ zetaDivisor.support).Finite :=
  zetaDivisor.supportLocallyFiniteWithinDomain s hs

theorem zetaDivisor_order {s : ℂ} (hs : s.re < 1) :
    zetaDivisor s = (meromorphicOrderAt riemannZeta s).untop₀ := by
  apply MeromorphicOn.divisor_apply
  · intro z hz
    exact (riemannZeta_analytic_regularDomain z hz).meromorphicAt
  · exact hs

theorem zetaDivisor_nonnegative : 0 ≤ zetaDivisor :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg riemannZeta_analytic_regularDomain

#check zetaRegularDomain_open
#print axioms zetaRegularDomain_open
#check zetaRegularDomain_convex
#print axioms zetaRegularDomain_convex
#check riemannZeta_analytic_regularDomain
#print axioms riemannZeta_analytic_regularDomain
#check riemannZeta_order_finite
#print axioms riemannZeta_order_finite
#check riemannZeta_zero_positive_finite_multiplicity
#print axioms riemannZeta_zero_positive_finite_multiplicity
#check zetaDivisor_locally_finite
#print axioms zetaDivisor_locally_finite
#check zetaDivisor_order
#print axioms zetaDivisor_order
#check zetaDivisor_nonnegative
#print axioms zetaDivisor_nonnegative
end MasulloGRH
