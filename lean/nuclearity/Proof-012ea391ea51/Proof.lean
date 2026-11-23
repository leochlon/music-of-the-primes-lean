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
end MasulloGRH



namespace MasulloGRH
open Filter Set
open scoped Topology

/-- The completed genuine Dirichlet function is analytic on the full open strip. -/
theorem completedDirichletNormTwist_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (completedDirichletNormTwist χ τ) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    have h0 : s + (τ : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith [hs.1]
    have h1 : s + (τ : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith [hs.2]
    exact ((χ.differentiableAt_completedLFunction _ (Or.inl h0) (Or.inl h1)).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)

/-- Completing factors preserve the actual zero multiplicities, including norm twists. -/
theorem dirichletNormTwist_order_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (dirichletNormTwist χ τ) s =
      analyticOrderAt (completedDirichletNormTwist χ τ) s := by
  let G : ℂ → ℂ := fun z => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹
  have hG : AnalyticAt ℂ G s := by
    rcases χ.even_or_odd with he | ho
    · change AnalyticAt ℂ (fun z => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹) s
      simp only [he.gammaFactor_def]
      exact (Complex.differentiable_Gammaℝ_inv.comp
        (differentiable_id.add_const _)).analyticAt s
    · change AnalyticAt ℂ (fun z => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹) s
      simp only [ho.gammaFactor_def]
      exact (Complex.differentiable_Gammaℝ_inv.comp
        ((differentiable_id.add_const _).add_const 1)).analyticAt s
  have hGn : G s ≠ 0 := inv_ne_zero (dirichletNormTwist_gamma_ne_zero χ τ s hpos)
  have heq : dirichletNormTwist χ τ =ᶠ[𝓝 s] G * completedDirichletNormTwist χ τ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with z hz
    change dirichletNormTwist χ τ z = G z * completedDirichletNormTwist χ τ z
    rw [dirichletNormTwist_completion χ τ z hz]
    simp [G, div_eq_mul_inv, mul_comm]
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul hG
    (completedDirichletNormTwist_analytic χ τ s ⟨hpos, hlt⟩),
    hG.analyticOrderAt_eq_zero.mpr hGn, zero_add]

/-- Natural integer multiplicities agree, not just the underlying zero sets. -/
theorem dirichletNormTwist_multiplicity_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderNatAt (dirichletNormTwist χ τ) s =
      analyticOrderNatAt (completedDirichletNormTwist χ τ) s := by
  unfold analyticOrderNatAt
  rw [dirichletNormTwist_order_eq_completed χ τ s hpos hlt]

end MasulloGRH
#check MasulloGRH.completedDirichletNormTwist_analytic
#print axioms MasulloGRH.completedDirichletNormTwist_analytic
#check MasulloGRH.dirichletNormTwist_order_eq_completed
#print axioms MasulloGRH.dirichletNormTwist_order_eq_completed
#check MasulloGRH.dirichletNormTwist_multiplicity_eq_completed
#print axioms MasulloGRH.dirichletNormTwist_multiplicity_eq_completed

namespace MasulloGRH
open Set

theorem completedDirichletNormTwist_order_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (completedDirichletNormTwist χ τ) s ≠ ⊤ := by
  rw [← dirichletNormTwist_order_eq_completed χ τ s hpos hlt]
  apply dirichletNormTwist_order_finite
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

theorem completedDirichletNormTwist_multiplicity_pos_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    0 < analyticOrderNatAt (completedDirichletNormTwist χ τ) s ↔
      completedDirichletNormTwist χ τ s = 0 := by
  rw [← dirichletNormTwist_multiplicity_eq_completed χ τ s hpos hlt,
    ← dirichletNormTwist_zero_iff_completed χ τ s hpos]
  apply dirichletNormTwist_multiplicity_pos_iff
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  linarith

/-- Compact multiplicity counting for the ACTUAL completed functions. -/
theorem completedDirichletNormTwist_copies_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hK : IsCompact K) (hstrip : K ⊆ {s : ℂ | 0 < s.re ∧ s.re < 1}) :
    Finite (Σ s : {s : ℂ // s ∈ K ∧ completedDirichletNormTwist χ τ s = 0},
      Fin (analyticOrderNatAt (completedDirichletNormTwist χ τ) s.val)) := by
  have hreg : K ⊆ dirichletRegularDomain τ := by
    intro s hs h
    have hr := congrArg Complex.re h
    simp at hr
    have ht := (hstrip hs).2
    linarith
  have hf := dirichletNormTwist_zeros_finite_on_compact χ τ K hK hreg
  have hc : {s : ℂ | s ∈ K ∧ completedDirichletNormTwist χ τ s = 0}.Finite := by
    apply hf.subset
    intro s hs
    exact ⟨hs.1, (dirichletNormTwist_zero_iff_completed χ τ s (hstrip hs.1).1).mpr hs.2⟩
  letI : Finite {s : ℂ // s ∈ K ∧ completedDirichletNormTwist χ τ s = 0} := hc.to_subtype
  infer_instance
end MasulloGRH
#check MasulloGRH.completedDirichletNormTwist_order_finite
#print axioms MasulloGRH.completedDirichletNormTwist_order_finite
#check MasulloGRH.completedDirichletNormTwist_multiplicity_pos_iff
#print axioms MasulloGRH.completedDirichletNormTwist_multiplicity_pos_iff
#check MasulloGRH.completedDirichletNormTwist_copies_finite
#print axioms MasulloGRH.completedDirichletNormTwist_copies_finite

/-! Round 7: remove the genuine finite-function pole before bounding the strip
zeros. This repairs the compact-open-strip restriction for the actual Dirichlet
family, and is a prerequisite for its quantitative Hecke divisor count. -/
namespace MasulloGRH
open Filter Set
open scoped Topology

noncomputable def regularizedDirichletNormTwist {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℂ := by
  classical
  exact if χ = 1 then
    DirichletCharacter.LFunctionTrivChar₁ N (s + (τ : ℂ) * Complex.I)
  else dirichletNormTwist χ τ s

theorem regularizedDirichletNormTwist_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (regularizedDirichletNormTwist χ τ) univ := by
  classical
  have hd : Differentiable ℂ (regularizedDirichletNormTwist χ τ) := by
    change Differentiable ℂ (fun s => if χ = 1 then
      DirichletCharacter.LFunctionTrivChar₁ N (s + (τ : ℂ) * Complex.I)
      else dirichletNormTwist χ τ s)
    by_cases hχ : χ = 1
    · simp only [if_pos hχ]
      exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).comp
        (differentiable_id.add_const ((τ : ℂ) * Complex.I))
    · simp only [if_neg hχ]
      exact (DirichletCharacter.differentiable_LFunction hχ).comp
        (differentiable_id.add_const ((τ : ℂ) * Complex.I))
  exact fun s _ => hd.analyticAt s

theorem regularizedDirichletNormTwist_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    regularizedDirichletNormTwist χ τ (2 - (τ : ℂ) * Complex.I) ≠ 0 := by
  classical
  have hn : χ.LFunction 2 ≠ 0 := by
    rw [χ.LFunction_eq_LSeries (by norm_num : 1 < (2 : ℂ).re)]
    exact χ.LSeries_ne_zero_of_one_lt_re (by norm_num)
  by_cases hχ : χ = 1
  · simp only [regularizedDirichletNormTwist, if_pos hχ, sub_add_cancel]
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne (by norm_num : (2 : ℂ) ≠ 1)]
    norm_num [DirichletCharacter.LFunctionTrivChar]
    simpa [hχ] using hn
  · simpa [regularizedDirichletNormTwist, hχ, dirichletNormTwist] using hn

theorem regularizedDirichletNormTwist_zero_iff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s + (τ : ℂ) * Complex.I ≠ 1) :
    regularizedDirichletNormTwist χ τ s = 0 ↔ dirichletNormTwist χ τ s = 0 := by
  classical
  by_cases hχ : χ = 1
  · simp [regularizedDirichletNormTwist, hχ,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs,
      DirichletCharacter.LFunctionTrivChar, dirichletNormTwist, sub_ne_zero.mpr hs]
  · simp [regularizedDirichletNormTwist, hχ]

theorem regularizedDirichletNormTwist_zeros_compact_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    {s : ℂ | s ∈ K ∧ regularizedDirichletNormTwist χ τ s = 0}.Finite := by
  have hd := (regularizedDirichletNormTwist_analytic χ τ).preimage_zero_mem_codiscrete
    (regularizedDirichletNormTwist_ne_zero χ τ)
  have hm := Filter.codiscreteWithin.mono (Set.subset_univ K) hd
  have hh : (K \ ((regularizedDirichletNormTwist χ τ) ⁻¹' {0}ᶜ)).Finite := by
    by_contra hi
    obtain ⟨x, hx, ha⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hi hK
      (fun _ h => h.1)
    exact (mem_codiscreteWithin_accPt.mp hm) x hx ha
  exact hh.subset (by intro s hs; exact ⟨hs.1, fun hz => hz hs.2⟩)

/-- K need not lie inside the strip and may contain the shifted poles. -/
theorem completedDirichletNormTwist_strip_zeros_compact_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    {s : ℂ | s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧
      completedDirichletNormTwist χ τ s = 0}.Finite := by
  apply (regularizedDirichletNormTwist_zeros_compact_finite χ τ K hK).subset
  rintro s ⟨hsK, hpos, hlt, hz⟩
  have h1 : s + (τ : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  exact ⟨hsK, (regularizedDirichletNormTwist_zero_iff χ τ s h1).mpr
    ((dirichletNormTwist_zero_iff_completed χ τ s hpos).mpr hz)⟩

/-- Every genuine strip zero of bounded height is included, even near its boundary. -/
theorem completedDirichletNormTwist_height_zeros_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) :
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧
      completedDirichletNormTwist χ τ s = 0}.Finite := by
  apply (completedDirichletNormTwist_strip_zeros_compact_finite χ τ
    (Metric.closedBall 0 (|T| + 2)) (isCompact_closedBall _ _)).subset
  rintro s ⟨hpos, hlt, hT, hz⟩
  refine ⟨?_, hpos, hlt, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ |T| + 2 := by rw [abs_of_pos hpos]; linarith [le_abs_self T]

/-- Actual completed multiplicities, with no compact-set-within-strip assumption. -/
theorem completedDirichletNormTwist_height_copies_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) :
    Finite (Σ s : {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧
      completedDirichletNormTwist χ τ s = 0},
      Fin (analyticOrderNatAt (completedDirichletNormTwist χ τ) s.val)) := by
  letI : Finite {s : ℂ // 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧
    completedDirichletNormTwist χ τ s = 0} :=
    (completedDirichletNormTwist_height_zeros_finite χ τ T).to_subtype
  infer_instance

end MasulloGRH
#check MasulloGRH.regularizedDirichletNormTwist_analytic
#print axioms MasulloGRH.regularizedDirichletNormTwist_analytic
#check MasulloGRH.regularizedDirichletNormTwist_ne_zero
#print axioms MasulloGRH.regularizedDirichletNormTwist_ne_zero
#check MasulloGRH.regularizedDirichletNormTwist_zero_iff
#print axioms MasulloGRH.regularizedDirichletNormTwist_zero_iff
#check MasulloGRH.regularizedDirichletNormTwist_zeros_compact_finite
#print axioms MasulloGRH.regularizedDirichletNormTwist_zeros_compact_finite
#check MasulloGRH.completedDirichletNormTwist_strip_zeros_compact_finite
#print axioms MasulloGRH.completedDirichletNormTwist_strip_zeros_compact_finite
#check MasulloGRH.completedDirichletNormTwist_height_zeros_finite
#print axioms MasulloGRH.completedDirichletNormTwist_height_zeros_finite
#check MasulloGRH.completedDirichletNormTwist_height_copies_finite
#print axioms MasulloGRH.completedDirichletNormTwist_height_copies_finite
