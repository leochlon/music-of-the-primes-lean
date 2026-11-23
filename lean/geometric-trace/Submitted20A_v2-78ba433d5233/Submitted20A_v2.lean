import Mathlib

open Filter Set Complex
open scoped Topology

namespace Round19A

/-! Direct premise P2 of the spectral target: uniqueness of a pole-cleared
completion from its Mellin germ, including exclusion of spurious zeros at
the two norm-twisted poles. P is Mathlib's existing Mellin FE pair; G is an
independently supplied entire function, not a newly defined Hecke function.
The actual number-field theta/finite-Euler/archimedean attachment to P and G
is still required. This is a CONDITIONAL analytic bridge, not zero attachment. -/

theorem shifted_pole_clearing_identification
    (P : WeakFEPair ℂ) (τ : ℝ) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G)
    (hgerm : ∀ z : ℂ, P.k < z.re →
      G z = (z + τ * I) * (z + τ * I - P.k) *
        mellin (fun x => P.f x - P.f₀) (z + τ * I)) :
    (∀ z : ℂ, G z =
      (z + τ * I) * (z + τ * I - P.k) * P.Λ₀ (z + τ * I) -
        (z + τ * I - P.k) * P.f₀ + (z + τ * I) * P.ε * P.g₀) ∧
    G (-(τ : ℂ) * I) = (P.k : ℂ) * P.f₀ ∧
    G ((P.k : ℂ) - τ * I) = (P.k : ℂ) * P.ε * P.g₀ := by
  let R : ℂ → ℂ := fun z =>
    (z + τ * I) * (z + τ * I - P.k) * P.Λ₀ (z + τ * I) -
      (z + τ * I - P.k) * P.f₀ + (z + τ * I) * P.ε * P.g₀
  have hR : Differentiable ℂ R := by
    dsimp [R]
    have hΛ := P.differentiable_Λ₀
    fun_prop
  have hlocal : G =ᶠ[𝓝 ((P.k + 1 : ℝ) : ℂ)] R := by
    have hopen : IsOpen {z : ℂ | P.k < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : ((P.k + 1 : ℝ) : ℂ) ∈ {z : ℂ | P.k < z.re} := by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : P.k < (z + τ * I).re := by simpa using hz
    have hzero : z + τ * I ≠ 0 := by
      intro he
      rw [he] at hz'
      simp only [Complex.zero_re] at hz'
      linarith [P.hk]
    have hk : (P.k : ℂ) - (z + τ * I) ≠ 0 := by
      intro he
      have he' := congrArg Complex.re (sub_eq_zero.mp he)
      simp only [Complex.ofReal_re] at he'
      linarith
    rw [hgerm z hz, (P.hasMellin hz').2]
    dsimp [R, WeakFEPair.Λ]
    field_simp [hzero, hk]
    ring
  have heq : G = R := AnalyticOnNhd.eq_of_eventuallyEq
    (hf := fun z _ => hG.analyticAt z)
    (hg := fun z _ => hR.analyticAt z) hlocal
  refine ⟨fun z => congrFun heq z, ?_, ?_⟩
  · rw [heq]
    simp [R]
  · rw [heq]
    simp [R]

/-- P2 endpoint check: with nonzero constant terms, pole clearing adds no
zeros at the shifted poles. This is required before using an entire divisor. -/
theorem shifted_pole_clearing_no_spurious_endpoint_zeros
    (P : WeakFEPair ℂ) (τ : ℝ) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G)
    (hgerm : ∀ z : ℂ, P.k < z.re →
      G z = (z + τ * I) * (z + τ * I - P.k) *
        mellin (fun x => P.f x - P.f₀) (z + τ * I))
    (hf₀ : P.f₀ ≠ 0) (hg₀ : P.g₀ ≠ 0) :
    G (-(τ : ℂ) * I) ≠ 0 ∧ G ((P.k : ℂ) - τ * I) ≠ 0 := by
  obtain ⟨_, h0, hk⟩ := shifted_pole_clearing_identification P τ G hG hgerm
  rw [h0, hk]
  have hk0 : (P.k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr P.hk.ne'
  exact ⟨mul_ne_zero hk0 hf₀, mul_ne_zero (mul_ne_zero hk0 P.hε) hg₀⟩

#check shifted_pole_clearing_identification
#print axioms shifted_pole_clearing_identification
#check shifted_pole_clearing_no_spurious_endpoint_zeros
#print axioms shifted_pole_clearing_no_spurious_endpoint_zeros
end Round19A

namespace Round20A

/-- CONDITIONAL premise P2 for the spectral target: the Mellin germ and
nonzero theta constants determine an entire pole-cleared function, preserve
every zero multiplicity off the shifted poles, and exclude added endpoint
zeros. The genuine all-Hecke theta/Euler/Gamma attachment is still required.
This integrates the checked Round19A identity rather than repeating its proof. -/
theorem shifted_pole_clearing_divisor_bridge
    (P : WeakFEPair ℂ) (τ : ℝ) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G)
    (hgerm : ∀ z : ℂ, P.k < z.re →
      G z = (z + τ * I) * (z + τ * I - P.k) *
        mellin (fun x => P.f x - P.f₀) (z + τ * I))
    (hf₀ : P.f₀ ≠ 0) (hg₀ : P.g₀ ≠ 0) :
    (∀ x : ℂ, x + τ * I ≠ 0 → x + τ * I - P.k ≠ 0 →
      meromorphicOrderAt G x =
        meromorphicOrderAt (fun z => P.Λ (z + τ * I)) x) ∧
    G (-(τ : ℂ) * I) ≠ 0 ∧ G ((P.k : ℂ) - τ * I) ≠ 0 := by
  obtain ⟨hglobal, _, _⟩ :=
    Round19A.shifted_pole_clearing_identification P τ G hG hgerm
  refine ⟨?_, Round19A.shifted_pole_clearing_no_spurious_endpoint_zeros
    P τ G hG hgerm hf₀ hg₀⟩
  intro x hx0 hxk
  have hopen : IsOpen {z : ℂ | z + τ * I ≠ 0 ∧ z + τ * I - P.k ≠ 0} :=
    (isOpen_ne.preimage (continuous_id.add continuous_const)).inter
      (isOpen_ne.preimage ((continuous_id.add continuous_const).sub continuous_const))
  have he : G =ᶠ[𝓝[≠] x] (fun z =>
      ((z + τ * I) * (z + τ * I - P.k)) * P.Λ (z + τ * I)) := by
    filter_upwards [(hopen.eventually_mem ⟨hx0, hxk⟩).filter_mono nhdsWithin_le_nhds]
      with z hz
    have hk : (P.k : ℂ) - (z + τ * I) ≠ 0 := by
      intro h
      exact hz.2 (sub_eq_zero.mpr (sub_eq_zero.mp h).symm)
    rw [hglobal z]
    dsimp [WeakFEPair.Λ]
    field_simp [hz.1, hk]
    ring
  rw [meromorphicOrderAt_congr he]
  exact meromorphicOrderAt_mul_of_ne_zero
    (((analyticAt_id.add analyticAt_const).mul
      ((analyticAt_id.add analyticAt_const).sub analyticAt_const)))
    (mul_ne_zero hx0 hxk)

#check shifted_pole_clearing_divisor_bridge
#print axioms shifted_pole_clearing_divisor_bridge
end Round20A
