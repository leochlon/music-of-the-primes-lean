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

/-! Round 6 extension by H (final Pi-product repair adapted from frozen r06/draft/D): completion must preserve multiplicities, not merely
zero locations. This is a concrete input to the genuine Hecke divisor target. -/

def dirichletCriticalStrip : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

theorem dirichletCriticalStrip_regular (τ : ℝ) :
    dirichletCriticalStrip ⊆ dirichletRegularDomain τ := by
  intro s hs h
  have hr := congrArg Complex.re h
  simp at hr
  exact (ne_of_lt hs.2) hr

#check dirichletCriticalStrip_regular
#print axioms dirichletCriticalStrip_regular

theorem completedDirichletNormTwist_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    AnalyticOnNhd ℂ (completedDirichletNormTwist χ τ) dirichletCriticalStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro s hs
    apply ((χ.differentiableAt_completedLFunction _ (Or.inl ?_) (Or.inl ?_)).comp s
      (differentiableAt_id.add_const _)).differentiableWithinAt
    · intro h
      have hr := congrArg Complex.re h
      simp at hr
      exact (ne_of_gt hs.1) hr
    · exact dirichletCriticalStrip_regular τ hs
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)

#check completedDirichletNormTwist_analytic
#print axioms completedDirichletNormTwist_analytic

theorem dirichletNormTwist_invGamma_analytic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹) s := by
  have hd : Differentiable ℂ
      (fun z : ℂ => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹) := by
    rcases χ.even_or_odd with he | ho
    · simpa only [he.gammaFactor_def] using
        Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const ((τ : ℂ) * Complex.I))
    · simpa only [ho.gammaFactor_def] using
        Complex.differentiable_Gammaℝ_inv.comp
          ((differentiable_id.add_const ((τ : ℂ) * Complex.I)).add_const 1)
  exact hd.analyticAt s

#check dirichletNormTwist_invGamma_analytic
#print axioms dirichletNormTwist_invGamma_analytic

theorem dirichletNormTwist_order_eq_completed {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    analyticOrderAt (dirichletNormTwist χ τ) s =
      analyticOrderAt (completedDirichletNormTwist χ τ) s := by
  have heq : dirichletNormTwist χ τ =ᶠ[𝓝 s]
      completedDirichletNormTwist χ τ *
        (fun z => (χ.gammaFactor (z + (τ : ℂ) * Complex.I))⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs.1] with z hz
    simpa only [Pi.mul_apply, div_eq_mul_inv] using dirichletNormTwist_completion χ τ z hz
  rw [analyticOrderAt_congr heq, analyticOrderAt_mul
    (completedDirichletNormTwist_analytic χ τ s hs)
    (dirichletNormTwist_invGamma_analytic χ τ s)]
  have hz := (dirichletNormTwist_invGamma_analytic χ τ s).analyticOrderAt_eq_zero.mpr
    (inv_ne_zero (dirichletNormTwist_gamma_ne_zero χ τ s hs.1))
  rw [hz, add_zero]

#check dirichletNormTwist_order_eq_completed
#print axioms dirichletNormTwist_order_eq_completed

theorem dirichletNormTwist_completed_divisor_exact {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (K : Set ℂ)
    (hK : K ⊆ dirichletCriticalStrip) (s : ℂ) (hs : s ∈ K) :
    MeromorphicOn.divisor (completedDirichletNormTwist χ τ) K s =
      dirichletNormTwistDivisor χ τ K s := by
  have ha : AnalyticOnNhd ℂ (completedDirichletNormTwist χ τ) K :=
    fun z hz => completedDirichletNormTwist_analytic χ τ z (hK hz)
  have hb : AnalyticOnNhd ℂ (dirichletNormTwist χ τ) K :=
    fun z hz => dirichletNormTwist_analytic χ τ z
      (dirichletCriticalStrip_regular τ (hK hz))
  rw [MeromorphicOn.divisor_apply ha.meromorphicOn hs, (ha s hs).meromorphicOrderAt_eq,
    dirichletNormTwistDivisor, MeromorphicOn.divisor_apply hb.meromorphicOn hs,
    (hb s hs).meromorphicOrderAt_eq, dirichletNormTwist_order_eq_completed χ τ s (hK hs)]

#check dirichletNormTwist_completed_divisor_exact
#print axioms dirichletNormTwist_completed_divisor_exact

/-! Round 7: a countable exhaustive genuine divisor index, preserving every
analytic multiplicity. This serves the index-construction clause of the genuine
Hecke divisor, restricted here to actual Dirichlet L-functions. No growth or
summability hypothesis is smuggled into the index. -/

def dirichletStripBox (a b n : ℕ) : Set ℂ :=
  Metric.closedBall 0 (n : ℝ) ∩
    {s | 1 / ((a : ℝ) + 1) ≤ s.re ∧ s.re ≤ 1 - 1 / ((b : ℝ) + 1)}

theorem dirichletStripBox_compact (a b n : ℕ) :
    IsCompact (dirichletStripBox a b n) := by
  apply (isCompact_closedBall (0 : ℂ) (n : ℝ)).inter_right
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

#check dirichletStripBox_compact
#print axioms dirichletStripBox_compact

theorem dirichletStripBox_subset (a b n : ℕ) :
    dirichletStripBox a b n ⊆ dirichletCriticalStrip := by
  intro s hs
  have ha : 0 < 1 / ((a : ℝ) + 1) := by positivity
  have hb : 0 < 1 / ((b : ℝ) + 1) := by positivity
  exact ⟨lt_of_lt_of_le ha hs.2.1, by linarith [hs.2.2]⟩

#check dirichletStripBox_subset
#print axioms dirichletStripBox_subset

theorem dirichletNormTwist_zeros_countable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    {s : ℂ | s ∈ dirichletCriticalStrip ∧ dirichletNormTwist χ τ s = 0}.Countable := by
  have hc : (⋃ a : ℕ, ⋃ b : ℕ, ⋃ n : ℕ,
      {s : ℂ | s ∈ dirichletStripBox a b n ∧ dirichletNormTwist χ τ s = 0}).Countable := by
    apply Set.countable_iUnion
    intro a
    apply Set.countable_iUnion
    intro b
    apply Set.countable_iUnion
    intro n
    exact (dirichletNormTwist_zeros_finite_on_compact χ τ _
      (dirichletStripBox_compact a b n)
      ((dirichletStripBox_subset a b n).trans (dirichletCriticalStrip_regular τ))).countable
  apply hc.mono
  intro s hs
  obtain ⟨a, ha⟩ := exists_nat_one_div_lt hs.1.1
  obtain ⟨b, hb⟩ := exists_nat_one_div_lt (show 0 < 1 - s.re by linarith [hs.1.2])
  obtain ⟨n, hn⟩ := exists_nat_ge ‖s‖
  apply Set.mem_iUnion.mpr
  refine ⟨a, Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨n, ?_⟩⟩⟩
  refine ⟨⟨?_, le_of_lt ha, ?_⟩, hs.2⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hn
  · linarith

#check dirichletNormTwist_zeros_countable
#print axioms dirichletNormTwist_zeros_countable

theorem dirichletNormTwist_all_copies_countable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    Countable (DirichletZeroCopies χ τ dirichletCriticalStrip) := by
  letI : Countable {s : ℂ // s ∈ dirichletCriticalStrip ∧ dirichletNormTwist χ τ s = 0} :=
    (dirichletNormTwist_zeros_countable χ τ).to_subtype
  unfold DirichletZeroCopies
  infer_instance

#check dirichletNormTwist_all_copies_countable
#print axioms dirichletNormTwist_all_copies_countable

theorem completedDirichletNormTwist_zeros_countable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    {s : ℂ | s ∈ dirichletCriticalStrip ∧ completedDirichletNormTwist χ τ s = 0}.Countable := by
  apply (dirichletNormTwist_zeros_countable χ τ).mono
  intro s hs
  exact ⟨hs.1, (dirichletNormTwist_zero_iff_completed χ τ s hs.1.1).mpr hs.2⟩

#check completedDirichletNormTwist_zeros_countable
#print axioms completedDirichletNormTwist_zeros_countable

noncomputable def CompletedDirichletStripCopies {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :=
  Σ s : {s : ℂ // s ∈ dirichletCriticalStrip ∧ completedDirichletNormTwist χ τ s = 0},
    Fin (analyticOrderNatAt (completedDirichletNormTwist χ τ) s)

theorem completedDirichletNormTwist_all_copies_countable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    Countable (CompletedDirichletStripCopies χ τ) := by
  letI : Countable {s : ℂ // s ∈ dirichletCriticalStrip ∧
      completedDirichletNormTwist χ τ s = 0} :=
    (completedDirichletNormTwist_zeros_countable χ τ).to_subtype
  unfold CompletedDirichletStripCopies
  infer_instance

#check completedDirichletNormTwist_all_copies_countable
#print axioms completedDirichletNormTwist_all_copies_countable

end MasulloGRH

/-! Round 8: repaired genuine Euler factors, adapted from frozen r07/final/D. -/
namespace MasulloGRH
open scoped Topology
open Filter Set

/-- The actual omitted prime Euler factor is a unit in the right half-plane.
This supplies the primitive/imprimitive divisor comparison. -/
theorem dirichlet_omittedEuler_ne_zero {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (τ : ℝ) (s : ℂ) (hs : 0 < s.re)
    (p : ℕ) (hp : p.Prime) :
    1 - χ (p : ZMod M) * (p : ℂ) ^ (-(s + (τ : ℂ) * Complex.I)) ≠ 0 := by
  have hpow : ‖(p : ℂ) ^ (-(s + (τ : ℂ) * Complex.I))‖ < 1 := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < p by exact_mod_cast hp.pos)]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp.one_lt
    · simpa using (neg_lt_zero.mpr hs)
  have hn : ‖χ (p : ZMod M) * (p : ℂ) ^ (-(s + (τ : ℂ) * Complex.I))‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _))
      (by simpa using hpow)
  intro h
  have he := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hn
  exact (lt_irrefl (1 : ℝ)) hn

noncomputable def dirichletOmittedEulerProduct {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (N : ℕ) (τ : ℝ) (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - χ (p : ZMod M) *
    (p : ℂ) ^ (-(s + (τ : ℂ) * Complex.I)))

theorem dirichletOmittedEulerProduct_analytic {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (N : ℕ) (τ : ℝ) (s : ℂ) :
    AnalyticAt ℂ (dirichletOmittedEulerProduct χ N τ) s := by
  classical
  have hprod : ∀ S : Finset ℕ, (∀ p ∈ S, p ≠ 0) →
      Differentiable ℂ (fun z : ℂ => ∏ p ∈ S,
        (1 - χ (p : ZMod M) * (p : ℂ) ^ (-(z + (τ : ℂ) * Complex.I)))) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _
        simp
    | @insert p S hp ih =>
        intro hS
        simp only [Finset.prod_insert hp]
        apply Differentiable.mul
        · haveI : NeZero p := ⟨hS p (Finset.mem_insert_self p S)⟩
          fun_prop
        · exact ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
  exact (hprod N.primeFactors (fun p hp => (Nat.pos_of_mem_primeFactors hp).ne')).analyticAt s

theorem dirichletOmittedEulerProduct_ne_zero {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (N : ℕ) (τ : ℝ) (s : ℂ) (hs : 0 < s.re) :
    dirichletOmittedEulerProduct χ N τ s ≠ 0 := by
  unfold dirichletOmittedEulerProduct
  exact Finset.prod_ne_zero_iff.mpr fun p hp =>
    dirichlet_omittedEuler_ne_zero χ τ s hs p (Nat.prime_of_mem_primeFactors hp)

/-- Raising the actual Dirichlet level preserves every genuine strip multiplicity,
including arbitrary unitary norm twists. No GRH or trace identity is a premise. -/
theorem dirichletNormTwist_order_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (dirichletNormTwist (DirichletCharacter.changeLevel hMN χ) τ) s =
      analyticOrderAt (dirichletNormTwist χ τ) s := by
  have hs : s ∈ dirichletRegularDomain τ := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have he : dirichletNormTwist (DirichletCharacter.changeLevel hMN χ) τ =ᶠ[𝓝 s]
      dirichletNormTwist χ τ * dirichletOmittedEulerProduct χ N τ := by
    have hu : {z : ℂ | z.re < 1} ∈ 𝓝 s :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt
    filter_upwards [hu] with z hz
    have hz1 : z + (τ : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith
    exact DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hz1)
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul (dirichletNormTwist_analytic χ τ s hs)
      (dirichletOmittedEulerProduct_analytic χ N τ s),
    (dirichletOmittedEulerProduct_analytic χ N τ s).analyticOrderAt_eq_zero.mpr
      (dirichletOmittedEulerProduct_ne_zero χ N τ s hpos), add_zero]

end MasulloGRH
#check MasulloGRH.dirichlet_omittedEuler_ne_zero
#print axioms MasulloGRH.dirichlet_omittedEuler_ne_zero
#check MasulloGRH.dirichletOmittedEulerProduct_analytic
#print axioms MasulloGRH.dirichletOmittedEulerProduct_analytic
#check MasulloGRH.dirichletOmittedEulerProduct_ne_zero
#print axioms MasulloGRH.dirichletOmittedEulerProduct_ne_zero
#check MasulloGRH.dirichletNormTwist_order_changeLevel
#print axioms MasulloGRH.dirichletNormTwist_order_changeLevel

/-! The next implications supply the primitive/imprimitive identification clause
of the genuine divisor theorem. They do not assert the missing growth estimate. -/
namespace MasulloGRH

theorem completedDirichletNormTwist_order_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    analyticOrderAt (completedDirichletNormTwist (DirichletCharacter.changeLevel hMN χ) τ) s =
      analyticOrderAt (completedDirichletNormTwist χ τ) s := by
  rw [← dirichletNormTwist_order_eq_completed _ τ s hs,
    ← dirichletNormTwist_order_eq_completed χ τ s hs]
  exact dirichletNormTwist_order_changeLevel hMN χ τ s hs.1 hs.2

#check completedDirichletNormTwist_order_changeLevel
#print axioms completedDirichletNormTwist_order_changeLevel

theorem completedDirichletNormTwist_multiplicity_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    analyticOrderNatAt (completedDirichletNormTwist (DirichletCharacter.changeLevel hMN χ) τ) s =
      analyticOrderNatAt (completedDirichletNormTwist χ τ) s := by
  simp only [analyticOrderNatAt, completedDirichletNormTwist_order_changeLevel hMN χ τ s hs]

#check completedDirichletNormTwist_multiplicity_changeLevel
#print axioms completedDirichletNormTwist_multiplicity_changeLevel

theorem completedDirichletNormTwist_zero_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) (s : ℂ)
    (hs : s ∈ dirichletCriticalStrip) :
    completedDirichletNormTwist (DirichletCharacter.changeLevel hMN χ) τ s = 0 ↔
      completedDirichletNormTwist χ τ s = 0 := by
  rw [← (completedDirichletNormTwist_analytic _ τ s hs).analyticOrderAt_ne_zero,
    ← (completedDirichletNormTwist_analytic χ τ s hs).analyticOrderAt_ne_zero,
    completedDirichletNormTwist_order_changeLevel hMN χ τ s hs]

#check completedDirichletNormTwist_zero_changeLevel
#print axioms completedDirichletNormTwist_zero_changeLevel

theorem completedDirichletNormTwist_divisor_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) (K : Set ℂ)
    (hK : K ⊆ dirichletCriticalStrip) (s : ℂ) (hs : s ∈ K) :
    MeromorphicOn.divisor (completedDirichletNormTwist (DirichletCharacter.changeLevel hMN χ) τ) K s =
      MeromorphicOn.divisor (completedDirichletNormTwist χ τ) K s := by
  rw [dirichletNormTwist_completed_divisor_exact _ τ K hK s hs,
    dirichletNormTwist_completed_divisor_exact χ τ K hK s hs,
    dirichletNormTwist_divisor_exact _ τ K (hK.trans (dirichletCriticalStrip_regular τ)) s hs,
    dirichletNormTwist_divisor_exact χ τ K (hK.trans (dirichletCriticalStrip_regular τ)) s hs]
  simp only [analyticOrderNatAt,
    dirichletNormTwist_order_changeLevel hMN χ τ s (hK hs).1 (hK hs).2]

#check completedDirichletNormTwist_divisor_changeLevel
#print axioms completedDirichletNormTwist_divisor_changeLevel

/-- Actual completed divisor multiplicity times the inverse-square spectral
weight. Nonzeros have order zero; the strip is not restricted to the critical line. -/
noncomputable def completedDirichletStripWeight {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℝ := by
  classical
  exact if s ∈ dirichletCriticalStrip then
    (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) /
      (1 + ‖s - (1 / 2 : ℂ)‖ ^ 2) else 0

theorem completedDirichletStripWeight_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) :
    completedDirichletStripWeight (DirichletCharacter.changeLevel hMN χ) τ =
      completedDirichletStripWeight χ τ := by
  funext s
  by_cases hs : s ∈ dirichletCriticalStrip
  · simp only [completedDirichletStripWeight, if_pos hs,
      completedDirichletNormTwist_multiplicity_changeLevel hMN χ τ s hs]
  · simp only [completedDirichletStripWeight, if_neg hs]

#check completedDirichletStripWeight_changeLevel
#print axioms completedDirichletStripWeight_changeLevel

/-- This reduces the precise genuine inverse-square divisor sum to the primitive
level once a primitive presentation is supplied. It proves neither summability. -/
theorem completedDirichletStripWeight_summable_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (τ : ℝ) :
    Summable (completedDirichletStripWeight (DirichletCharacter.changeLevel hMN χ) τ) ↔
      Summable (completedDirichletStripWeight χ τ) := by
  rw [completedDirichletStripWeight_changeLevel hMN χ τ]

#check completedDirichletStripWeight_summable_changeLevel
#print axioms completedDirichletStripWeight_summable_changeLevel

end MasulloGRH
