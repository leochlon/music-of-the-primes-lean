import Mathlib

/-! Round 7 A starting checkpoint: adapted from frozen r05/final/C. Genuine finite Dirichlet L-functions and arbitrary real norm twists.
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

end MasulloGRH
#check MasulloGRH.completedDirichletNormTwist_analytic_strip
#print axioms MasulloGRH.completedDirichletNormTwist_analytic_strip
#check MasulloGRH.dirichletNormTwist_order_eq_completed
#print axioms MasulloGRH.dirichletNormTwist_order_eq_completed
#check MasulloGRH.dirichletNormTwist_multiplicity_eq_completed
#print axioms MasulloGRH.dirichletNormTwist_multiplicity_eq_completed

namespace MasulloGRH
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

end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_entire
#print axioms MasulloGRH.dirichletPoleCleared_entire
#check MasulloGRH.dirichletPoleCleared_eq
#print axioms MasulloGRH.dirichletPoleCleared_eq
#check MasulloGRH.dirichletPoleCleared_ne_zero_two
#print axioms MasulloGRH.dirichletPoleCleared_ne_zero_two
#check MasulloGRH.dirichletPoleCleared_order_eq
#print axioms MasulloGRH.dirichletPoleCleared_order_eq

namespace MasulloGRH
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

end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_ne_zero_right
#print axioms MasulloGRH.dirichletPoleCleared_ne_zero_right
#check MasulloGRH.dirichletPoleCleared_jensen
#print axioms MasulloGRH.dirichletPoleCleared_jensen
#check MasulloGRH.dirichletPoleCleared_jensen_coefficient
#print axioms MasulloGRH.dirichletPoleCleared_jensen_coefficient

namespace MasulloGRH
open Set
/-- The exact moving-center counting identity, with the genuine center value
rather than a trailing-coefficient placeholder. Together with genuine arithmetic
upper/lower bounds this is the input to the quantitative strip count. -/
theorem dirichletPoleCleared_jensen_right {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R : ℝ)
    (hc : 1 < c.re) (hR : R ≠ 0) :
    (∑ᶠ z : ℂ, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹)) =
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖) c R -
      Real.log ‖dirichletPoleCleared χ τ c‖ := by
  have ha : AnalyticOnNhd ℂ (dirichletPoleCleared χ τ) (Metric.closedBall c |R|) :=
    fun z _ => dirichletPoleCleared_entire χ τ z (mem_univ z)
  have hac := dirichletPoleCleared_entire χ τ c (mem_univ c)
  have hn := dirichletPoleCleared_ne_zero_right χ τ c hc
  have hz : MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) c = 0 := by
    rw [MeromorphicOn.divisor_apply ha.meromorphicOn (by simp),
      hac.meromorphicOrderAt_eq, hac.analyticOrderAt_eq_zero.mpr hn]
    simp
  have hj := dirichletPoleCleared_jensen χ τ c R hR
  rw [hz, Int.cast_zero, zero_mul, add_zero,
    hac.meromorphicTrailingCoeffAt_of_ne_zero hn] at hj
  linarith
end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_jensen_right
#print axioms MasulloGRH.dirichletPoleCleared_jensen_right


/-! Round 9 H extension. The exact geometric counting implication used with
A's genuine Jensen identity. Arithmetic circle growth remains unproved. -/
namespace MasulloGRH
open Set

theorem dirichletStrip_distance_two_le (s : ℂ) (T : ℝ)
    (hpos : 0 < s.re) (hlt : s.re < 1) (him : |s.im| ≤ T) :
    ‖(2 : ℂ) - s‖ ≤ T + 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im ((2 : ℂ) - s)
  have hnon : 0 ≤ 2 - s.re := by linarith
  norm_num [Complex.sub_re, Complex.sub_im, abs_of_nonneg hnon] at h
  linarith

/-- Each actual strip multiplicity below height T contributes at least log 2
to the Jensen divisor sum with radius 2(T+2). No zero hypothesis is necessary:
a regular nonzero point has actual multiplicity zero. -/
theorem completedDirichlet_jensen_term_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) (T : ℝ)
    (hT : 0 ≤ T) (hpos : 0 < s.re) (hlt : s.re < 1) (him : |s.im| ≤ T) :
    (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) * Real.log 2 ≤
      (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
        (Metric.closedBall 2 |2 * (T + 2)|) s : ℝ) *
        Real.log ((2 * (T + 2)) * ‖(2 : ℂ) - s‖⁻¹) := by
  have hR : 0 < 2 * (T + 2) := by linarith
  have hd := dirichletStrip_distance_two_le s T hpos hlt him
  have hn : (2 : ℂ) - s ≠ 0 := by
    intro hz
    have he := congrArg Complex.re (sub_eq_zero.mp hz)
    norm_num at he
    linarith
  have hp : 0 < ‖(2 : ℂ) - s‖ := norm_pos_iff.mpr hn
  have hm : s ∈ Metric.closedBall (2 : ℂ) |2 * (T + 2)| := by
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, abs_of_pos hR]
    linarith
  rw [dirichletPoleCleared_jensen_coefficient χ τ 2 s (2 * (T + 2)) hm hpos hlt]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  linarith

/-- Finite genuine multiplicity counts are bounded by their contribution to
the Jensen sum. The all-disk comparison and arithmetic growth are separate. -/
theorem completedDirichlet_jensen_finite_count_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (S : Finset ℂ) (T : ℝ)
    (hT : 0 ≤ T) (hS : ∀ s ∈ S, 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T) :
    (∑ s ∈ S, (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ)) * Real.log 2 ≤
      ∑ s ∈ S, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
        (Metric.closedBall 2 |2 * (T + 2)|) s : ℝ) *
        Real.log ((2 * (T + 2)) * ‖(2 : ℂ) - s‖⁻¹) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s hs
  exact completedDirichlet_jensen_term_lower χ τ s T hT
    (hS s hs).1 (hS s hs).2.1 (hS s hs).2.2
end MasulloGRH
#check MasulloGRH.dirichletStrip_distance_two_le
#print axioms MasulloGRH.dirichletStrip_distance_two_le
#check MasulloGRH.completedDirichlet_jensen_term_lower
#print axioms MasulloGRH.completedDirichlet_jensen_term_lower
#check MasulloGRH.completedDirichlet_jensen_finite_count_lower
#print axioms MasulloGRH.completedDirichlet_jensen_finite_count_lower

namespace MasulloGRH
noncomputable def dirichletCenterMajorant : ℝ :=
  1 + ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖

theorem dirichletCenterMajorant_pos : 0 < dirichletCenterMajorant := by
  have h : 0 ≤ ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖ := tsum_nonneg (fun n : ℕ => norm_nonneg (LSeries.term (fun _ => (1 : ℂ)) 2 n))
  dsimp [dirichletCenterMajorant]
  linarith

private theorem center_series_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (s : ℂ) (hs : 2 ≤ s.re) : ‖LSeries f s‖ ≤ dirichletCenterMajorant := by
  have hfs : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => hf n) (by linarith)
  have hones : LSeriesSummable (fun _ => (1 : ℂ)) 2 :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (by intros; simp) (by norm_num)
  have hterm : ∀ n, ‖LSeries.term f s n‖ ≤ ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖ := by
    intro n
    exact (LSeries.norm_term_le s (by simpa using hf n)).trans
      (LSeries.norm_term_le_of_re_le_re (fun _ => (1 : ℂ)) (by simpa using hs) n)
  calc
    ‖LSeries f s‖ ≤ ∑' n, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hfs.norm
    _ ≤ ∑' n, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖ :=
      hfs.norm.tsum_le_tsum hterm hones.norm
    _ ≤ dirichletCenterMajorant := by unfold dirichletCenterMajorant; linarith

/-- An actual arithmetic center bound, uniform in the modulus and vertical height.
It supplies the previously missing lower Jensen input, not the circle growth input. -/
theorem dirichletLFunction_center_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : 2 ≤ s.re) :
    1 / dirichletCenterMajorant ≤ ‖χ.LFunction s‖ := by
  let f : ℕ → ℂ := fun n => χ n * (ArithmeticFunction.moebius n : ℂ)
  have hf : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    dsimp [f]
    rw [norm_mul]
    calc
      ‖χ n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 * 1 :=
        mul_le_mul (χ.norm_le_one _) hm (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hb := center_series_bound f hf s hs
  have hp : LSeries (fun n => χ n) s * LSeries f s = 1 := by
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ (by linarith)
  have hn : ‖LSeries (fun n => χ n) s‖ * ‖LSeries f s‖ = 1 := by
    simpa only [norm_mul, norm_one] using congrArg norm hp
  rw [χ.LFunction_eq_LSeries (by linarith)]
  apply (div_le_iff₀ dirichletCenterMajorant_pos).mpr
  nlinarith [norm_nonneg (LSeries (fun n => χ n) s)]

#check dirichletCenterMajorant_pos
#print axioms dirichletCenterMajorant_pos
#check dirichletLFunction_center_lower
#print axioms dirichletLFunction_center_lower
end MasulloGRH

namespace MasulloGRH
/-- The same center lower bound includes every real norm twist. -/
theorem dirichletNormTwist_center_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (hc : 2 ≤ c.re) :
    1 / dirichletCenterMajorant ≤ ‖dirichletNormTwist χ τ c‖ := by
  exact dirichletLFunction_center_lower χ (c + (τ : ℂ) * Complex.I) (by simpa using hc)

/-- Correct shifted pole clearing preserves the uniform lower Jensen bound. -/
theorem dirichletPoleCleared_center_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (hc : 2 ≤ c.re) :
    1 / dirichletCenterMajorant ≤ ‖dirichletPoleCleared χ τ c‖ := by
  have hr : c ∈ dirichletRegularDomain τ := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    linarith
  have hb := dirichletNormTwist_center_lower χ τ c hc
  rw [dirichletPoleCleared_eq χ τ c hr, norm_mul]
  have hP : 1 ≤ ‖(if χ = 1 then c + (τ : ℂ) * Complex.I - 1 else 1 : ℂ)‖ := by
    split_ifs
    · have hh := Complex.re_le_norm (c + (τ : ℂ) * Complex.I - 1)
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, zero_mul, sub_zero, add_zero, Complex.one_re] at hh
      linarith
    · simp
  nlinarith [norm_nonneg (dirichletNormTwist χ τ c)]

/-- The genuine Jensen sum is now controlled by the circle mean alone plus
an explicit universal constant. The circle growth estimate remains unproved. -/
theorem dirichletPoleCleared_jensen_upper {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R : ℝ)
    (hc : 2 ≤ c.re) (hR : R ≠ 0) :
    (∑ᶠ z : ℂ, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹)) ≤
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖) c R +
      Real.log dirichletCenterMajorant := by
  rw [dirichletPoleCleared_jensen_right χ τ c R (by linarith) hR]
  have hp : 0 < 1 / dirichletCenterMajorant := by
    exact one_div_pos.mpr dirichletCenterMajorant_pos
  have hl := Real.log_le_log hp (dirichletPoleCleared_center_lower χ τ c hc)
  rw [one_div, Real.log_inv] at hl
  linarith
end MasulloGRH
#check MasulloGRH.dirichletNormTwist_center_lower
#print axioms MasulloGRH.dirichletNormTwist_center_lower
#check MasulloGRH.dirichletPoleCleared_center_lower
#print axioms MasulloGRH.dirichletPoleCleared_center_lower
#check MasulloGRH.dirichletPoleCleared_jensen_upper
#print axioms MasulloGRH.dirichletPoleCleared_jensen_upper

/-! Round 10 B: enlarge finite genuine multiplicity contributions to the full
Jensen divisor sum. This closes no arithmetic growth or operator-trace premise. -/
namespace MasulloGRH
open Set

theorem dirichletPoleCleared_jensen_term_nonneg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c z : ℂ) (R : ℝ) (hR : 0 < R) :
    0 ≤ (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹) := by
  by_cases hzc : z = c
  · subst z
    simp
  by_cases hz : z ∈ Metric.closedBall c |R|
  · have ha : AnalyticOnNhd ℂ (dirichletPoleCleared χ τ)
        (Metric.closedBall c |R|) :=
      fun w _ => dirichletPoleCleared_entire χ τ w (mem_univ w)
    have hn : (0 : ℤ) ≤ MeromorphicOn.divisor (dirichletPoleCleared χ τ)
        (Metric.closedBall c |R|) z :=
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha) z
    apply mul_nonneg (by exact_mod_cast hn)
    apply Real.log_nonneg
    have hp : 0 < ‖c - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hzc))
    have hd : ‖c - z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm z c, dist_eq_norm,
        abs_of_pos hR] using hz
    rw [← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
    exact hd
  · simp [hz]

/-- Unlike a partial contribution bound, this compares an arbitrary finite
set with the entire genuine Jensen divisor sum. Compact divisor support and
nonnegative Jensen weights justify the enlargement without any summability axiom. -/
theorem dirichletPoleCleared_partial_jensen_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (S : Finset ℂ) :
    (∑ z ∈ S, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹)) ≤
    ∑ᶠ z : ℂ, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹) := by
  classical
  let D := MeromorphicOn.divisor (dirichletPoleCleared χ τ) (Metric.closedBall c |R|)
  let W : ℂ → ℝ := fun z => (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹)
  have hD := D.finiteSupport (isCompact_closedBall c |R|)
  let U := S ∪ hD.toFinset
  have hcover : Function.support W ⊆ (U : Set ℂ) := by
    intro z hz
    apply Finset.mem_union.mpr
    right
    apply hD.mem_toFinset.mpr
    rw [Function.mem_support]
    intro hdz
    exact hz (by simp [W, hdz])
  change (∑ z ∈ S, W z) ≤ ∑ᶠ z, W z
  rw [finsum_eq_sum_of_support_subset W hcover]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
  intro z _ _
  exact dirichletPoleCleared_jensen_term_nonneg χ τ c z R hR

/-- A genuine full multiplicity count is controlled by the ACTUAL circle
average and an arithmetic universal constant. No circle growth estimate is
assumed or proved here; establishing it is the remaining counting input. -/
theorem completedDirichlet_finite_count_circle_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (S : Finset ℂ) (T : ℝ)
    (hT : 0 ≤ T) (hS : ∀ s ∈ S, 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T) :
    (∑ s ∈ S, (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ)) *
      Real.log 2 ≤
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
      2 (2 * (T + 2)) + Real.log dirichletCenterMajorant := by
  have hR : 0 < 2 * (T + 2) := by linarith
  exact (completedDirichlet_jensen_finite_count_lower χ τ S T hT hS).trans
    ((dirichletPoleCleared_partial_jensen_le χ τ 2 (2 * (T + 2)) hR S).trans
      (dirichletPoleCleared_jensen_upper χ τ 2 (2 * (T + 2)) (by norm_num) hR.ne'))

end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_jensen_term_nonneg
#print axioms MasulloGRH.dirichletPoleCleared_jensen_term_nonneg
#check MasulloGRH.dirichletPoleCleared_partial_jensen_le
#print axioms MasulloGRH.dirichletPoleCleared_partial_jensen_le
#check MasulloGRH.completedDirichlet_finite_count_circle_bound
#print axioms MasulloGRH.completedDirichlet_finite_count_circle_bound

/-! Round 11 B: reuse A round 9 compact finiteness, then count the whole genuine divisor. -/
namespace MasulloGRH
open Set Filter
open scoped Topology

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

/-- The complete set of genuine finite-function strip zeros below height T. -/
def genuineDirichletZerosBelow {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ dirichletNormTwist χ τ s = 0}

theorem genuineDirichletZerosBelow_finite {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) :
    (genuineDirichletZerosBelow χ τ T).Finite := by
  apply (dirichletNormTwist_strip_zeros_compact_finite χ τ
    (Metric.closedBall (2 : ℂ) (|T| + 2)) (isCompact_closedBall _ _)).subset
  intro s hs
  change 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ dirichletNormTwist χ τ s = 0 at hs
  refine ⟨?_, hs.1, hs.2.1, hs.2.2.2⟩
  rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
  exact dirichletStrip_distance_two_le s |T| hs.1 hs.2.1
    (hs.2.2.1.trans (le_abs_self T))

noncomputable def genuineDirichletZeroFinset {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) : Finset ℂ :=
  (genuineDirichletZerosBelow_finite χ τ T).toFinset

theorem mem_genuineDirichletZeroFinset {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) (s : ℂ) :
    s ∈ genuineDirichletZeroFinset χ τ T ↔
      0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T ∧ dirichletNormTwist χ τ s = 0 := by
  simp [genuineDirichletZeroFinset, genuineDirichletZerosBelow]

/-- Full natural-number multiplicity, with no cap and no assumed enumeration. -/
noncomputable def genuineDirichletZeroCount {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) : ℕ :=
  ∑ s ∈ genuineDirichletZeroFinset χ τ T,
    analyticOrderNatAt (dirichletNormTwist χ τ) s

/-- Jensen controls ALL actual zeros below height T, including their full
multiplicities. The actual arithmetic circle-growth bound remains to be proved. -/
theorem genuineDirichletZeroCount_circle_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) (hT : 0 ≤ T) :
    (genuineDirichletZeroCount χ τ T : ℝ) * Real.log 2 ≤
      Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
        2 (2 * (T + 2)) + Real.log dirichletCenterMajorant := by
  have he : (genuineDirichletZeroCount χ τ T : ℝ) =
      ∑ s ∈ genuineDirichletZeroFinset χ τ T,
        (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) := by
    simp only [genuineDirichletZeroCount, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hm := (mem_genuineDirichletZeroFinset χ τ T s).mp hs
    rw [dirichletNormTwist_multiplicity_eq_completed χ τ s hm.1 hm.2.1]
  rw [he]
  apply completedDirichlet_finite_count_circle_bound χ τ _ T hT
  intro s hs
  have hm := (mem_genuineDirichletZeroFinset χ τ T s).mp hs
  exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_zeros_compact_finite
#print axioms MasulloGRH.dirichletPoleCleared_zeros_compact_finite
#check MasulloGRH.dirichletNormTwist_strip_zeros_compact_finite
#print axioms MasulloGRH.dirichletNormTwist_strip_zeros_compact_finite
#check MasulloGRH.genuineDirichletZerosBelow_finite
#print axioms MasulloGRH.genuineDirichletZerosBelow_finite
#check MasulloGRH.mem_genuineDirichletZeroFinset
#print axioms MasulloGRH.mem_genuineDirichletZeroFinset
#check MasulloGRH.genuineDirichletZeroCount_circle_bound
#print axioms MasulloGRH.genuineDirichletZeroCount_circle_bound

namespace MasulloGRH
open Set

/-- The actual strip divisor has a countable support, obtained from genuine
compact-zero finiteness, rather than postulated as a chosen sequence. -/
theorem genuineDirichletZeros_countable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) :
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ dirichletNormTwist χ τ s = 0}.Countable := by
  apply (Set.countable_iUnion (fun n : ℕ =>
    (genuineDirichletZerosBelow_finite χ τ (n : ℝ)).countable)).mono
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_ge |s.im|
  exact Set.mem_iUnion.mpr ⟨n, hs.1, hs.2.1, hn, hs.2.2⟩

/-- Positivity is proved at every genuine zero, so the natural multiplicity
count cannot silently discard a zero through the top-to-zero convention. -/
theorem genuineDirichletZero_multiplicity_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) (hz : dirichletNormTwist χ τ s = 0) :
    0 < analyticOrderNatAt (dirichletNormTwist χ τ) s := by
  have hs : s ∈ dirichletRegularDomain τ := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hn := (dirichletNormTwist_analytic χ τ s hs).analyticOrderAt_ne_zero
  have hf := dirichletNormTwist_order_finite χ τ s hs
  lift analyticOrderAt (dirichletNormTwist χ τ) s to ℕ using hf with m hm
  have hp : 0 < analyticOrderNatAt (dirichletNormTwist χ τ) s ↔
      dirichletNormTwist χ τ s = 0 := by
    simpa [analyticOrderNatAt, ← hm, Nat.pos_iff_ne_zero] using hn
  exact hp.mpr hz

/-- In particular, the number of distinct genuine zeros is no greater than
the exact multiplicity count to which the Jensen bound applies. -/
theorem genuineDirichletZeroFinset_card_le_count {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) :
    (genuineDirichletZeroFinset χ τ T).card ≤ genuineDirichletZeroCount χ τ T := by
  classical
  calc
    (genuineDirichletZeroFinset χ τ T).card =
        ∑ _s ∈ genuineDirichletZeroFinset χ τ T, (1 : ℕ) := by simp
    _ ≤ genuineDirichletZeroCount χ τ T := by
      apply Finset.sum_le_sum
      intro s hs
      have hm := (mem_genuineDirichletZeroFinset χ τ T s).mp hs
      exact genuineDirichletZero_multiplicity_pos χ τ s hm.1 hm.2.1 hm.2.2.2
end MasulloGRH
#check MasulloGRH.genuineDirichletZeros_countable
#print axioms MasulloGRH.genuineDirichletZeros_countable
#check MasulloGRH.genuineDirichletZero_multiplicity_pos
#print axioms MasulloGRH.genuineDirichletZero_multiplicity_pos
#check MasulloGRH.genuineDirichletZeroFinset_card_le_count
#print axioms MasulloGRH.genuineDirichletZeroFinset_card_le_count
