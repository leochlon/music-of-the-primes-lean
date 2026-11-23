import Mathlib

/-! Genuine finite Dirichlet L-functions and arbitrary real norm twists.
This is a concrete rational-field part of the missing Hecke divisor construction.
No GRH or trace identity is assumed or concluded. -/
namespace MasulloGRH
open scoped Topology
open Filter Set

noncomputable def dirichletNormTwist {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℂ :=
  χ.LFunction (s + (τ : ℂ) * Complex.I)

def dirichletRegularDomain (τ : ℝ) : Set ℂ :=
  {s | s + (τ : ℂ) * Complex.I ≠ 1}

theorem dirichletNormTwist_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (dirichletNormTwist χ τ) (dirichletRegularDomain τ) := by
  have hd : DifferentiableOn ℂ (dirichletNormTwist χ τ) (dirichletRegularDomain τ) := by
    intro s hs
    exact ((χ.differentiableAt_LFunction _ (Or.inl hs)).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_ne.preimage (continuous_id.add continuous_const))

#check dirichletNormTwist_analytic
#print axioms dirichletNormTwist_analytic

theorem dirichletNormTwist_ne_zero_right {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) (hs : 1 < s.re) :
    dirichletNormTwist χ τ s ≠ 0 := by
  have hs' : 1 < (s + (τ : ℂ) * Complex.I).re := by simpa using hs
  rw [dirichletNormTwist, χ.LFunction_eq_LSeries hs']
  exact χ.LSeries_ne_zero_of_one_lt_re hs'

#check dirichletNormTwist_ne_zero_right
#print axioms dirichletNormTwist_ne_zero_right

noncomputable def dirichletNormTwistDivisor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) :=
  MeromorphicOn.divisor (dirichletNormTwist χ τ) K

theorem dirichletNormTwist_divisor_on_compact {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hK : IsCompact K) (hreg : K ⊆ dirichletRegularDomain τ) :
    0 ≤ dirichletNormTwistDivisor χ τ K ∧
    (dirichletNormTwistDivisor χ τ K).support.Finite ∧
    ∀ s ∈ K, dirichletNormTwistDivisor χ τ K s =
      ((analyticOrderAt (dirichletNormTwist χ τ) s).map (↑)).untop₀ := by
  have ha : AnalyticOnNhd ℂ (dirichletNormTwist χ τ) K :=
    fun s hs => dirichletNormTwist_analytic χ τ s (hreg hs)
  exact ⟨MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha, (MeromorphicOn.divisor _ K).finiteSupport hK,
    fun s hs => by
      rw [dirichletNormTwistDivisor, MeromorphicOn.divisor_apply ha.meromorphicOn hs, (ha s hs).meromorphicOrderAt_eq]⟩

#check dirichletNormTwist_divisor_on_compact
#print axioms dirichletNormTwist_divisor_on_compact

theorem dirichletRegularDomain_connected (τ : ℝ) :
    IsConnected (dirichletRegularDomain τ) := by
  have heq : dirichletRegularDomain τ = {1 - (τ : ℂ) * Complex.I}ᶜ := by
    ext s
    simp only [dirichletRegularDomain, mem_setOf_eq, mem_compl_iff, mem_singleton_iff,
      eq_sub_iff_add_eq]
  rw [heq]
  exact isConnected_compl_singleton_of_one_lt_rank (by simp) _

#check dirichletRegularDomain_connected
#print axioms dirichletRegularDomain_connected

theorem dirichletNormTwist_order_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletRegularDomain τ) :
    analyticOrderAt (dirichletNormTwist χ τ) s ≠ ⊤ := by
  have ha := dirichletNormTwist_analytic χ τ
  have h2 : (2 : ℂ) ∈ dirichletRegularDomain τ := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  apply ha.analyticOrderAt_ne_top_of_isPreconnected
    (dirichletRegularDomain_connected τ).isPreconnected h2 hs
  have hz := (ha 2 h2).analyticOrderAt_eq_zero.mpr
    (dirichletNormTwist_ne_zero_right χ τ 2 (by norm_num))
  simp [hz]

#check dirichletNormTwist_order_finite
#print axioms dirichletNormTwist_order_finite

theorem dirichletNormTwist_divisor_exact {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hreg : K ⊆ dirichletRegularDomain τ) (s : ℂ) (hs : s ∈ K) :
    dirichletNormTwistDivisor χ τ K s =
      (analyticOrderNatAt (dirichletNormTwist χ τ) s : ℤ) := by
  have ha : AnalyticOnNhd ℂ (dirichletNormTwist χ τ) K :=
    fun x hx => dirichletNormTwist_analytic χ τ x (hreg hx)
  rw [dirichletNormTwistDivisor, MeromorphicOn.divisor_apply ha.meromorphicOn hs,
    (ha s hs).meromorphicOrderAt_eq]
  have hf := dirichletNormTwist_order_finite χ τ s (hreg hs)
  lift analyticOrderAt (dirichletNormTwist χ τ) s to ℕ using hf with m hm
  simp [analyticOrderNatAt, ← hm]

#check dirichletNormTwist_divisor_exact
#print axioms dirichletNormTwist_divisor_exact

theorem dirichletNormTwist_multiplicity_pos_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletRegularDomain τ) :
    0 < analyticOrderNatAt (dirichletNormTwist χ τ) s ↔
      dirichletNormTwist χ τ s = 0 := by
  have hn := (dirichletNormTwist_analytic χ τ s hs).analyticOrderAt_ne_zero
  have hf := dirichletNormTwist_order_finite χ τ s hs
  lift analyticOrderAt (dirichletNormTwist χ τ) s to ℕ using hf with m hm
  simpa [analyticOrderNatAt, ← hm, Nat.pos_iff_ne_zero] using hn

#check dirichletNormTwist_multiplicity_pos_iff
#print axioms dirichletNormTwist_multiplicity_pos_iff

theorem dirichletNormTwist_zeros_finite_on_compact {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hK : IsCompact K) (hreg : K ⊆ dirichletRegularDomain τ) :
    {s : ℂ | s ∈ K ∧ dirichletNormTwist χ τ s = 0}.Finite := by
  apply ((dirichletNormTwistDivisor χ τ K).finiteSupport hK).subset
  intro s hs
  rw [Function.mem_support, dirichletNormTwist_divisor_exact χ τ K hreg s hs.1]
  exact_mod_cast (Nat.ne_of_gt ((dirichletNormTwist_multiplicity_pos_iff
    χ τ s (hreg hs.1)).mpr hs.2))

#check dirichletNormTwist_zeros_finite_on_compact
#print axioms dirichletNormTwist_zeros_finite_on_compact

noncomputable def DirichletZeroCopies {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) :=
  Σ s : {s : ℂ // s ∈ K ∧ dirichletNormTwist χ τ s = 0},
    Fin (analyticOrderNatAt (dirichletNormTwist χ τ) s)

theorem dirichletNormTwist_multiplicity_count_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hK : IsCompact K) (hreg : K ⊆ dirichletRegularDomain τ) :
    Finite (DirichletZeroCopies χ τ K) := by
  classical
  letI : Fintype {s : ℂ // s ∈ K ∧ dirichletNormTwist χ τ s = 0} :=
    (dirichletNormTwist_zeros_finite_on_compact χ τ K hK hreg).fintype
  letI : Fintype (DirichletZeroCopies χ τ K) := by
    unfold DirichletZeroCopies
    infer_instance
  exact Finite.of_fintype _

#check dirichletNormTwist_multiplicity_count_finite
#print axioms dirichletNormTwist_multiplicity_count_finite

noncomputable def completedDirichletNormTwist {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℂ :=
  χ.completedLFunction (s + (τ : ℂ) * Complex.I)

theorem dirichletNormTwist_completion {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    dirichletNormTwist χ τ s = completedDirichletNormTwist χ τ s /
      χ.gammaFactor (s + (τ : ℂ) * Complex.I) := by
  apply χ.LFunction_eq_completed_div_gammaFactor _ (Or.inl ?_)
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

#check dirichletNormTwist_completion
#print axioms dirichletNormTwist_completion

theorem dirichletNormTwist_gamma_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    χ.gammaFactor (s + (τ : ℂ) * Complex.I) ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simpa using hs
  · rw [ho.gammaFactor_def]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    have hr : 0 < (s + (τ : ℂ) * Complex.I + 1).re := by
      simpa using (show 0 < s.re + 1 by linarith)
    exact hr

#check dirichletNormTwist_gamma_ne_zero
#print axioms dirichletNormTwist_gamma_ne_zero

theorem dirichletNormTwist_zero_iff_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    dirichletNormTwist χ τ s = 0 ↔ completedDirichletNormTwist χ τ s = 0 := by
  rw [dirichletNormTwist_completion χ τ s hs,
    div_eq_zero_iff, or_iff_left (dirichletNormTwist_gamma_ne_zero χ τ s hs)]

#check dirichletNormTwist_zero_iff_completed
#print axioms dirichletNormTwist_zero_iff_completed

/-- The open critical strip; no critical-line restriction is built into zeros. -/
def dirichletCriticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

theorem completedDirichletNormTwist_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (completedDirichletNormTwist χ τ) dirichletCriticalStrip := by
  have hd : DifferentiableOn ℂ (completedDirichletNormTwist χ τ) dirichletCriticalStrip := by
    intro s hs
    have h0 : s + (τ : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact (ne_of_gt hs.1) hr
    have h1 : s + (τ : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact (ne_of_lt hs.2) hr
    exact ((χ.differentiableAt_completedLFunction _ (Or.inl h0) (Or.inl h1)).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  exact hd.analyticOnNhd
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))

#check completedDirichletNormTwist_analytic
#print axioms completedDirichletNormTwist_analytic

/-- Multiplicities agree for the actual finite and completed Dirichlet functions. -/
theorem dirichletNormTwist_order_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    analyticOrderAt (dirichletNormTwist χ τ) s =
      analyticOrderAt (completedDirichletNormTwist χ τ) s := by
  let G : ℂ → ℂ := fun z => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹
  have hG : AnalyticAt ℂ G s := by
    rcases χ.even_or_odd with he | ho
    · dsimp [G]
      simp only [he.gammaFactor_def]
      exact (Complex.differentiable_Gammaℝ_inv.comp
        (differentiable_id.add_const _)).analyticAt s
    · dsimp [G]
      simp only [ho.gammaFactor_def]
      exact (Complex.differentiable_Gammaℝ_inv.comp
        ((differentiable_id.add_const _).add_const _)).analyticAt s
  have hGn : G s ≠ 0 := inv_ne_zero (dirichletNormTwist_gamma_ne_zero χ τ s hs.1)
  have he : dirichletNormTwist χ τ =ᶠ[𝓝 s] completedDirichletNormTwist χ τ * G := by
    have hp : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs.1
    filter_upwards [hp] with z hz
    simpa [Pi.mul_apply, G, div_eq_mul_inv] using dirichletNormTwist_completion χ τ z hz
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul (completedDirichletNormTwist_analytic χ τ s hs) hG,
    hG.analyticOrderAt_eq_zero.mpr hGn, add_zero]

#check dirichletNormTwist_order_eq_completed
#print axioms dirichletNormTwist_order_eq_completed

theorem completedDirichletNormTwist_order_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    analyticOrderAt (completedDirichletNormTwist χ τ) s ≠ ⊤ := by
  rw [← dirichletNormTwist_order_eq_completed χ τ s hs]
  apply dirichletNormTwist_order_finite
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  exact (ne_of_lt hs.2) hr

#check completedDirichletNormTwist_order_finite
#print axioms completedDirichletNormTwist_order_finite

theorem dirichletNormTwist_multiplicity_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    analyticOrderNatAt (dirichletNormTwist χ τ) s =
      analyticOrderNatAt (completedDirichletNormTwist χ τ) s := by
  simp only [analyticOrderNatAt, dirichletNormTwist_order_eq_completed χ τ s hs]

#check dirichletNormTwist_multiplicity_eq_completed
#print axioms dirichletNormTwist_multiplicity_eq_completed

/-- The actual completed divisor has the finite function's genuine multiplicities. -/
theorem completedDirichletNormTwist_divisor_exact {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hK : K ⊆ dirichletCriticalStrip) (s : ℂ) (hs : s ∈ K) :
    MeromorphicOn.divisor (completedDirichletNormTwist χ τ) K s =
      (analyticOrderNatAt (dirichletNormTwist χ τ) s : ℤ) := by
  have ha : AnalyticOnNhd ℂ (completedDirichletNormTwist χ τ) K :=
    fun z hz => completedDirichletNormTwist_analytic χ τ z (hK hz)
  rw [MeromorphicOn.divisor_apply ha.meromorphicOn hs, (ha s hs).meromorphicOrderAt_eq,
    ← dirichletNormTwist_order_eq_completed χ τ s (hK hs)]
  have hf : analyticOrderAt (dirichletNormTwist χ τ) s ≠ ⊤ := by
    rw [dirichletNormTwist_order_eq_completed χ τ s (hK hs)]
    exact completedDirichletNormTwist_order_finite χ τ s (hK hs)
  lift analyticOrderAt (dirichletNormTwist χ τ) s to ℕ using hf with m hm
  simp [analyticOrderNatAt, ← hm]

#check completedDirichletNormTwist_divisor_exact
#print axioms completedDirichletNormTwist_divisor_exact

theorem completedDirichletNormTwist_multiplicity_pos_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    0 < analyticOrderNatAt (completedDirichletNormTwist χ τ) s ↔
      completedDirichletNormTwist χ τ s = 0 := by
  have hr : s ∈ dirichletRegularDomain τ := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    exact (ne_of_lt hs.2) hh
  rw [← dirichletNormTwist_multiplicity_eq_completed χ τ s hs]
  exact (dirichletNormTwist_multiplicity_pos_iff χ τ s hr).trans
    (dirichletNormTwist_zero_iff_completed χ τ s hs.1)

#check completedDirichletNormTwist_multiplicity_pos_iff
#print axioms completedDirichletNormTwist_multiplicity_pos_iff

theorem completedDirichletNormTwist_zeros_finite_on_compact {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hcompact : IsCompact K) (hK : K ⊆ dirichletCriticalStrip) :
    {s : ℂ | s ∈ K ∧ completedDirichletNormTwist χ τ s = 0}.Finite := by
  have hr : K ⊆ dirichletRegularDomain τ := by
    intro s hs h
    have hh := congrArg Complex.re h
    simp at hh
    exact (ne_of_lt (hK hs).2) hh
  apply (dirichletNormTwist_zeros_finite_on_compact χ τ K hcompact hr).subset
  intro s hs
  exact ⟨hs.1, (dirichletNormTwist_zero_iff_completed χ τ s (hK hs.1).1).mpr hs.2⟩

#check completedDirichletNormTwist_zeros_finite_on_compact
#print axioms completedDirichletNormTwist_zeros_finite_on_compact

/-- Copies of actual completed zeros, repeated with their genuine analytic order. -/
noncomputable def CompletedDirichletZeroCopies {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) :=
  Σ s : {s : ℂ // s ∈ K ∧ completedDirichletNormTwist χ τ s = 0},
    Fin (analyticOrderNatAt (completedDirichletNormTwist χ τ) s)

theorem completedDirichletNormTwist_multiplicity_count_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hcompact : IsCompact K) (hK : K ⊆ dirichletCriticalStrip) :
    Finite (CompletedDirichletZeroCopies χ τ K) := by
  letI : Finite {s : ℂ // s ∈ K ∧ completedDirichletNormTwist χ τ s = 0} :=
    (completedDirichletNormTwist_zeros_finite_on_compact χ τ K hcompact hK).to_subtype
  unfold CompletedDirichletZeroCopies
  infer_instance

#check completedDirichletNormTwist_multiplicity_count_finite
#print axioms completedDirichletNormTwist_multiplicity_count_finite
end MasulloGRH
