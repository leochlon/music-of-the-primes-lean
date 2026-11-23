import Mathlib

/-! Round 7 A starting checkpoint: adapted from frozen r05/final/C. Genuine finite Dirichlet L-functions and arbitrary real norm twists.
This is a concrete rational-field part of the missing Hecke divisor construction.
No GRH or trace identity is assumed or concluded. -/
namespace PeerA
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
end PeerA



namespace PeerA
open scoped Topology
open Filter Set

/-- Analyticity of the actual completed norm-twisted function in the open strip. -/
theorem completedDirichletNormTwist_analytic_strip {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (completedDirichletNormTwist χ τ)
      {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  apply DifferentiableOn.analyticOnNhd _
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const))
  intro s hs
  change 0 < s.re ∧ s.re < 1 at hs
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

/-- Completion preserves the full analytic multiplicity, not only the zero set. -/
theorem dirichletNormTwist_order_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (dirichletNormTwist χ τ) s =
      analyticOrderAt (completedDirichletNormTwist χ τ) s := by
  let G : ℂ → ℂ := fun z => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹
  have hGD : Differentiable ℂ G := by
    rcases χ.even_or_odd with he | ho
    · simpa only [G, he.gammaFactor_def] using
        Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const ((τ : ℂ) * Complex.I))
    · simpa only [G, ho.gammaFactor_def] using
        Complex.differentiable_Gammaℝ_inv.comp
          ((differentiable_id.add_const ((τ : ℂ) * Complex.I)).add_const 1)
  have hG : AnalyticAt ℂ G s := hGD.analyticAt s
  have hGn : G s ≠ 0 := inv_ne_zero (dirichletNormTwist_gamma_ne_zero χ τ s hpos)
  have hC := completedDirichletNormTwist_analytic_strip χ τ s ⟨hpos, hlt⟩
  have he : dirichletNormTwist χ τ =ᶠ[𝓝 s] completedDirichletNormTwist χ τ * G := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos] with z hz
    change dirichletNormTwist χ τ z = completedDirichletNormTwist χ τ z * G z
    rw [dirichletNormTwist_completion χ τ z hz, div_eq_mul_inv]
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hC hG,
    hG.analyticOrderAt_eq_zero.mpr hGn, add_zero]

theorem dirichletNormTwist_multiplicity_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderNatAt (dirichletNormTwist χ τ) s =
      analyticOrderNatAt (completedDirichletNormTwist χ τ) s := by
  unfold analyticOrderNatAt
  rw [dirichletNormTwist_order_eq_completed χ τ s hpos hlt]

end PeerA
#check PeerA.completedDirichletNormTwist_analytic_strip
#print axioms PeerA.completedDirichletNormTwist_analytic_strip
#check PeerA.dirichletNormTwist_order_eq_completed
#print axioms PeerA.dirichletNormTwist_order_eq_completed
#check PeerA.dirichletNormTwist_multiplicity_eq_completed
#print axioms PeerA.dirichletNormTwist_multiplicity_eq_completed

namespace PeerA
open scoped Topology
open Filter Set

/-- Genuine Dirichlet continuation with its possible principal pole removed.
The value at the removed pole is the genuine nonzero residue supplied by Mathlib. -/
noncomputable def dirichletPoleCleared {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ N (s + (τ : ℂ) * Complex.I)
  else dirichletNormTwist χ τ s

theorem dirichletPoleCleared_entire {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (dirichletPoleCleared χ τ) univ := by
  have hd : Differentiable ℂ (dirichletPoleCleared χ τ) := by
    by_cases hχ : χ = 1
    · change Differentiable ℂ (fun s => dirichletPoleCleared χ τ s)
      simpa only [dirichletPoleCleared, if_pos hχ, Function.comp_def, id_eq] using
        (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).comp
          (differentiable_id.add_const ((τ : ℂ) * Complex.I))
    · change Differentiable ℂ (fun s => dirichletPoleCleared χ τ s)
      simpa only [dirichletPoleCleared, if_neg hχ, dirichletNormTwist, Function.comp_def, id_eq] using
        (DirichletCharacter.differentiable_LFunction hχ).comp
          (differentiable_id.add_const ((τ : ℂ) * Complex.I))
  exact fun s _ => hd.analyticAt s

theorem dirichletPoleCleared_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletRegularDomain τ) :
    dirichletPoleCleared χ τ s =
      (if χ = 1 then s + (τ : ℂ) * Complex.I - 1 else 1) *
        dirichletNormTwist χ τ s := by
  by_cases hχ : χ = 1
  · subst χ
    simp only [dirichletPoleCleared,
      DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]
    rfl
  · simp [dirichletPoleCleared, hχ]

theorem dirichletPoleCleared_ne_zero_two {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    dirichletPoleCleared χ τ 2 ≠ 0 := by
  have hr : (2 : ℂ) ∈ dirichletRegularDomain τ := by
    intro h; have := congrArg Complex.re h; norm_num at this
  rw [dirichletPoleCleared_eq χ τ 2 hr]
  apply mul_ne_zero _ (dirichletNormTwist_ne_zero_right χ τ 2 (by norm_num))
  split_ifs
  · exact sub_ne_zero.mpr hr
  · exact one_ne_zero

/-- Pole clearing adds no multiplicity at any genuine regular point. -/
theorem dirichletPoleCleared_order_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletRegularDomain τ) :
    analyticOrderAt (dirichletPoleCleared χ τ) s =
      analyticOrderAt (dirichletNormTwist χ τ) s := by
  let P : ℂ → ℂ := fun z => if χ = 1 then z + (τ : ℂ) * Complex.I - 1 else 1
  have hP : AnalyticAt ℂ P s := by
    by_cases hχ : χ = 1
    · simpa only [P, if_pos hχ] using
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const :
          AnalyticAt ℂ (fun z : ℂ => z + (τ : ℂ) * Complex.I - 1) s)
    · simpa only [P, if_neg hχ] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s)
  have hPn : P s ≠ 0 := by
    dsimp [P]; split_ifs
    · exact sub_ne_zero.mpr hs
    · exact one_ne_zero
  have he : dirichletPoleCleared χ τ =ᶠ[𝓝 s] P * dirichletNormTwist χ τ := by
    have hopen : IsOpen (dirichletRegularDomain τ) :=
      isOpen_ne.preimage (continuous_id.add continuous_const)
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact dirichletPoleCleared_eq χ τ z hz
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul hP (dirichletNormTwist_analytic χ τ s hs),
    hP.analyticOrderAt_eq_zero.mpr hPn, zero_add]

/-- Compact sets may now meet the shifted pole and either strip boundary. -/
theorem dirichletPoleCleared_zeros_compact_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    {s : ℂ | s ∈ K ∧ dirichletPoleCleared χ τ s = 0}.Finite := by
  have hd := (dirichletPoleCleared_entire χ τ).preimage_zero_mem_codiscrete
    (dirichletPoleCleared_ne_zero_two χ τ)
  have hm := Filter.codiscreteWithin.mono (Set.subset_univ K) hd
  have hh : (K \ ((dirichletPoleCleared χ τ) ⁻¹' {0}ᶜ)).Finite := by
    by_contra hi
    obtain ⟨x, hx, ha⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hi hK
      (fun _ h => h.1)
    exact (mem_codiscreteWithin_accPt.mp hm) x hx ha
  exact hh.subset (by intro s hs; exact ⟨hs.1, fun hz => hz hs.2⟩)

theorem dirichletNormTwist_strip_zeros_compact_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    {s : ℂ | s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧ dirichletNormTwist χ τ s = 0}.Finite := by
  apply (dirichletPoleCleared_zeros_compact_finite χ τ K hK).subset
  intro s hs
  have hr : s ∈ dirichletRegularDomain τ := by
    intro h; have hx := congrArg Complex.re h
    simp at hx
    linarith [hs.2.2.1]
  exact ⟨hs.1, by rw [dirichletPoleCleared_eq χ τ s hr, hs.2.2.2, mul_zero]⟩

noncomputable def DirichletStripCopies {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) :=
  Σ s : {s : ℂ // s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧ dirichletNormTwist χ τ s = 0},
    Fin (analyticOrderNatAt (dirichletNormTwist χ τ) s)

theorem dirichletNormTwist_strip_copies_compact_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ) (hK : IsCompact K) :
    Finite (DirichletStripCopies χ τ K) := by
  classical
  letI : Fintype {s : ℂ // s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧ dirichletNormTwist χ τ s = 0} :=
    (dirichletNormTwist_strip_zeros_compact_finite χ τ K hK).fintype
  letI : Fintype (DirichletStripCopies χ τ K) := by
    unfold DirichletStripCopies
    infer_instance
  exact Finite.of_fintype _

end PeerA
#check PeerA.dirichletPoleCleared_entire
#print axioms PeerA.dirichletPoleCleared_entire
#check PeerA.dirichletPoleCleared_eq
#print axioms PeerA.dirichletPoleCleared_eq
#check PeerA.dirichletPoleCleared_ne_zero_two
#print axioms PeerA.dirichletPoleCleared_ne_zero_two
#check PeerA.dirichletPoleCleared_order_eq
#print axioms PeerA.dirichletPoleCleared_order_eq
#check PeerA.dirichletPoleCleared_zeros_compact_finite
#print axioms PeerA.dirichletPoleCleared_zeros_compact_finite
#check PeerA.dirichletNormTwist_strip_zeros_compact_finite
#print axioms PeerA.dirichletNormTwist_strip_zeros_compact_finite
#check PeerA.dirichletNormTwist_strip_copies_compact_finite
#print axioms PeerA.dirichletNormTwist_strip_copies_compact_finite

namespace PeerA
open Set

/-- The moving Jensen center may be anywhere to the right of Re(s)=1. -/
theorem dirichletPoleCleared_ne_zero_right {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (hc : 1 < c.re) :
    dirichletPoleCleared χ τ c ≠ 0 := by
  have hr : c ∈ dirichletRegularDomain τ := by
    intro h
    have hx := congrArg Complex.re h
    simp at hx
    linarith
  rw [dirichletPoleCleared_eq χ τ c hr]
  apply mul_ne_zero _ (dirichletNormTwist_ne_zero_right χ τ c hc)
  split_ifs
  · exact sub_ne_zero.mpr hr
  · exact one_ne_zero

/-- Jensen's exact finite divisor identity for the ACTUAL pole-cleared Dirichlet
function. This is the counting step needed before a genuine arithmetic growth
estimate can yield inverse-square summability. No growth or trace is assumed. -/
theorem dirichletPoleCleared_jensen {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R : ℝ) (hR : R ≠ 0) :
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖) c R =
      (∑ᶠ z : ℂ, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
        (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹)) +
      (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
        (Metric.closedBall c |R|) c : ℝ) * Real.log R +
      Real.log ‖meromorphicTrailingCoeffAt (dirichletPoleCleared χ τ) c‖ := by
  have ha : AnalyticOnNhd ℂ (dirichletPoleCleared χ τ) (Metric.closedBall c |R|) :=
    fun z _ => dirichletPoleCleared_entire χ τ z (mem_univ z)
  exact MeromorphicOn.circleAverage_log_norm hR ha.meromorphicOn

/-- The divisor in Jensen counts each genuine strip zero with its full actual
analytic multiplicity. The disk may meet the shifted pole or either boundary. -/
theorem dirichletPoleCleared_jensen_coefficient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c s : ℂ) (R : ℝ)
    (hs : s ∈ Metric.closedBall c |R|) (hpos : 0 < s.re) (hlt : s.re < 1) :
    MeromorphicOn.divisor (dirichletPoleCleared χ τ) (Metric.closedBall c |R|) s =
      (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℤ) := by
  have hr : s ∈ dirichletRegularDomain τ := by
    intro h
    have hx := congrArg Complex.re h
    simp at hx
    linarith
  have ha : AnalyticOnNhd ℂ (dirichletPoleCleared χ τ) (Metric.closedBall c |R|) :=
    fun z _ => dirichletPoleCleared_entire χ τ z (mem_univ z)
  rw [MeromorphicOn.divisor_apply ha.meromorphicOn hs, (ha s hs).meromorphicOrderAt_eq,
    dirichletPoleCleared_order_eq χ τ s hr,
    ← dirichletNormTwist_multiplicity_eq_completed χ τ s hpos hlt]
  have hf := dirichletNormTwist_order_finite χ τ s hr
  lift analyticOrderAt (dirichletNormTwist χ τ) s to ℕ using hf with m hm
  simp [analyticOrderNatAt, ← hm]

end PeerA
#check PeerA.dirichletPoleCleared_ne_zero_right
#print axioms PeerA.dirichletPoleCleared_ne_zero_right
#check PeerA.dirichletPoleCleared_jensen
#print axioms PeerA.dirichletPoleCleared_jensen
#check PeerA.dirichletPoleCleared_jensen_coefficient
#print axioms PeerA.dirichletPoleCleared_jensen_coefficient
