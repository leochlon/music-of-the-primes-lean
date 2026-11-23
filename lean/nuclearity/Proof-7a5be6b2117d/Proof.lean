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

/-! Arithmetic center bound reused verbatim from round 9 participant A. -/
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

/-! Round 10 H: the missing finite-to-whole-disk comparison for the genuine
completed multiplicities, followed by A's arithmetic Jensen upper bound. -/
namespace MasulloGRH
open Set

theorem dirichletJensen_weight_nonneg {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c z : ℂ) (R : ℝ) (hR : 0 < R) :
    0 ≤ (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹) := by
  let D := MeromorphicOn.divisor (dirichletPoleCleared χ τ) (Metric.closedBall c |R|)
  change 0 ≤ (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹)
  have ha : AnalyticOnNhd ℂ (dirichletPoleCleared χ τ) (Metric.closedBall c |R|) :=
    fun w _ => dirichletPoleCleared_entire χ τ w (mem_univ w)
  have hD : 0 ≤ D := MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha
  by_cases hz : D z = 0
  · simp [hz]
  by_cases hcz : c = z
  · simp [hcz]
  have hm : z ∈ Metric.closedBall c |R| := D.supportWithinDomain hz
  have hd : ‖c - z‖ ≤ R := by
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, abs_of_pos hR] at hm
    exact hm
  have hp : 0 < ‖c - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcz)
  apply mul_nonneg (by exact_mod_cast hD z)
  apply Real.log_nonneg
  rw [← div_eq_mul_inv, le_div_iff₀ hp, one_mul]
  exact hd

theorem dirichletJensen_finite_sum_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R : ℝ)
    (hR : 0 < R) (S : Finset ℂ) :
    (∑ z ∈ S, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹)) ≤
    ∑ᶠ z : ℂ, (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
      (Metric.closedBall c |R|) z : ℝ) * Real.log (R * ‖c - z‖⁻¹) := by
  classical
  let D := MeromorphicOn.divisor (dirichletPoleCleared χ τ) (Metric.closedBall c |R|)
  let w : ℂ → ℝ := fun z => (D z : ℝ) * Real.log (R * ‖c - z‖⁻¹)
  have hf : (Function.support w).Finite := by
    apply (D.finiteSupport (isCompact_closedBall c |R|)).subset
    intro z hz
    change D z ≠ 0
    intro he
    apply hz
    simp [w, he]
  have heq : (∑ᶠ z, w z) = ∑ z ∈ S ∪ hf.toFinset, w z := by
    apply finsum_eq_sum_of_support_subset
    intro z hz
    simp only [Finset.mem_coe, Finset.mem_union, hf.mem_toFinset]
    exact Or.inr hz
  change (∑ z ∈ S, w z) ≤ ∑ᶠ z, w z
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
  intro z _ _
  exact dirichletJensen_weight_nonneg χ τ c z R hR

/-- Every finite full-multiplicity genuine strip count is bounded by the actual
circle mean plus an explicit convergent arithmetic constant. No circle-growth
or trace identity is assumed, and no capped multiplicity is substituted. -/
theorem completedDirichlet_count_le_circleAverage {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (S : Finset ℂ) (T : ℝ)
    (hT : 0 ≤ T) (hS : ∀ s ∈ S, 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T) :
    (∑ s ∈ S, (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ)) *
      Real.log 2 ≤
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
      2 (2 * (T + 2)) + Real.log dirichletCenterMajorant := by
  have hR : 0 < 2 * (T + 2) := by linarith
  exact (completedDirichlet_jensen_finite_count_lower χ τ S T hT hS).trans
    ((dirichletJensen_finite_sum_le χ τ 2 (2 * (T + 2)) hR S).trans
      (dirichletPoleCleared_jensen_upper χ τ 2 (2 * (T + 2))
        (by norm_num) (ne_of_gt hR)))
end MasulloGRH
#check MasulloGRH.dirichletJensen_weight_nonneg
#print axioms MasulloGRH.dirichletJensen_weight_nonneg
#check MasulloGRH.dirichletJensen_finite_sum_le
#print axioms MasulloGRH.dirichletJensen_finite_sum_le
#check MasulloGRH.completedDirichlet_count_le_circleAverage
#print axioms MasulloGRH.completedDirichlet_count_le_circleAverage

namespace MasulloGRH
/-- The genuine full completed multiplicity, restricted only by the open
critical strip and height. No critical-line restriction or multiplicity cap. -/
noncomputable def completedDirichletHeightWeight {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) : ℂ → ℝ := by
  classical
  exact fun s => if 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T then
    (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) else 0

theorem completedDirichletHeightWeight_finiteSupport {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) (hT : 0 ≤ T) :
    (Function.support (completedDirichletHeightWeight χ τ T)).Finite := by
  classical
  let D := MeromorphicOn.divisor (dirichletPoleCleared χ τ)
    (Metric.closedBall 2 |2 * (T + 2)|)
  apply (D.finiteSupport (isCompact_closedBall 2 |2 * (T + 2)|)).subset
  intro s hs
  have hstrip : 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T := by
    by_contra hn
    exact hs (by simp [completedDirichletHeightWeight, hn])
  have hR : 0 < 2 * (T + 2) := by linarith
  have hd := dirichletStrip_distance_two_le s T hstrip.1 hstrip.2.1 hstrip.2.2
  have hm : s ∈ Metric.closedBall (2 : ℂ) |2 * (T + 2)| := by
    rw [Metric.mem_closedBall, dist_comm, dist_eq_norm, abs_of_pos hR]
    linarith
  have hc := dirichletPoleCleared_jensen_coefficient χ τ 2 s (2 * (T + 2))
    hm hstrip.1 hstrip.2.1
  change D s ≠ 0
  intro he
  have hn : analyticOrderNatAt (completedDirichletNormTwist χ τ) s = 0 := by
    have hh : (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℤ) = 0 :=
      hc.symm.trans he
    exact_mod_cast hh
  exact hs (by simp [completedDirichletHeightWeight, hstrip, hn])

/-- The complete genuine height count, with all actual multiplicities, is now
bounded by the genuine circle average. The arithmetic circle upper estimate
is still a separate unproved input for inverse-square summability. -/
theorem completedDirichlet_all_height_count_le_circleAverage {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ T : ℝ) (hT : 0 ≤ T) :
    (∑ᶠ s : ℂ, completedDirichletHeightWeight χ τ T s) * Real.log 2 ≤
      Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
        2 (2 * (T + 2)) + Real.log dirichletCenterMajorant := by
  classical
  have hf := completedDirichletHeightWeight_finiteSupport χ τ T hT
  have hS : ∀ s ∈ hf.toFinset, 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T := by
    intro s hs
    have hh := hf.mem_toFinset.mp hs
    by_contra hn
    exact hh (by simp [completedDirichletHeightWeight, hn])
  rw [finsum_eq_sum _ hf]
  have he : (∑ s ∈ hf.toFinset, completedDirichletHeightWeight χ τ T s) =
      ∑ s ∈ hf.toFinset, (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) := by
    apply Finset.sum_congr rfl
    intro s hs
    simp [completedDirichletHeightWeight, hS s hs]
  rw [he]
  exact completedDirichlet_count_le_circleAverage χ τ hf.toFinset T hT hS
end MasulloGRH
#check MasulloGRH.completedDirichletHeightWeight_finiteSupport
#print axioms MasulloGRH.completedDirichletHeightWeight_finiteSupport
#check MasulloGRH.completedDirichlet_all_height_count_le_circleAverage
#print axioms MasulloGRH.completedDirichlet_all_height_count_le_circleAverage

/-! Round 11 H: fixed-radius moving-center counts for the actual completed
Dirichlet divisor. These are the local Jensen input for controlling the
zero-dependent derivative orders in manuscript (10.4.2.34), PDF 464. -/
namespace MasulloGRH

theorem dirichletStrip_distance_moving_le (s : ℂ) (t : ℝ)
    (hpos : 0 < s.re) (hlt : s.re < 1) (him : |s.im - t| ≤ 1) :
    ‖((2 : ℂ) + (t : ℂ) * Complex.I) - s‖ ≤ 3 := by
  have h := Complex.norm_le_abs_re_add_abs_im (((2 : ℂ) + (t : ℂ) * Complex.I) - s)
  have hnon : 0 ≤ 2 - s.re := by linarith
  norm_num [abs_of_nonneg hnon] at h
  rw [abs_sub_comm t s.im] at h
  linarith

/-- A fixed unit-height window is controlled using a radius-six circle,
independently of the ordinate. Full actual multiplicities are retained. -/
theorem completedDirichlet_local_finite_count_le_circleAverage {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ t : ℝ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, 0 < s.re ∧ s.re < 1 ∧ |s.im - t| ≤ 1) :
    (∑ s ∈ S, (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ)) *
      Real.log 2 ≤
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
      ((2 : ℂ) + (t : ℂ) * Complex.I) 6 + Real.log dirichletCenterMajorant := by
  let c : ℂ := 2 + (t : ℂ) * Complex.I
  have hc : c.re = 2 := by simp [c]
  have hterm : ∀ s ∈ S,
      (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) * Real.log 2 ≤
      (MeromorphicOn.divisor (dirichletPoleCleared χ τ)
        (Metric.closedBall c |6|) s : ℝ) * Real.log (6 * ‖c - s‖⁻¹) := by
    intro s hs
    rcases hS s hs with ⟨hpos, hlt, him⟩
    have hd : ‖c - s‖ ≤ 3 := dirichletStrip_distance_moving_le s t hpos hlt him
    have hp : 0 < ‖c - s‖ := by
      apply norm_pos_iff.mpr
      intro hz
      have he := congrArg Complex.re (sub_eq_zero.mp hz)
      rw [hc] at he
      linarith
    have hm : s ∈ Metric.closedBall c |(6 : ℝ)| := by
      rw [Metric.mem_closedBall, dist_comm, dist_eq_norm]
      norm_num
      linarith
    rw [dirichletPoleCleared_jensen_coefficient χ τ c s 6 hm hpos hlt]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    rw [← div_eq_mul_inv, le_div_iff₀ hp]
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum
  exact hsum.trans ((dirichletJensen_finite_sum_le χ τ c 6 (by norm_num) S).trans
    (dirichletPoleCleared_jensen_upper χ τ c 6 (by rw [hc]) (by norm_num)))

noncomputable def completedDirichletLocalWeight {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ t : ℝ) : ℂ → ℝ := by
  classical
  exact fun s => if 0 < s.re ∧ s.re < 1 ∧ |s.im - t| ≤ 1 then
    (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) else 0

theorem completedDirichletLocalWeight_finiteSupport {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ t : ℝ) :
    (Function.support (completedDirichletLocalWeight χ τ t)).Finite := by
  apply (completedDirichletHeightWeight_finiteSupport χ τ (|t| + 1)
    (by positivity)).subset
  intro s hs
  have hstrip : 0 < s.re ∧ s.re < 1 ∧ |s.im - t| ≤ 1 := by
    by_contra hn
    exact hs (by simp [completedDirichletLocalWeight, hn])
  have him : |s.im| ≤ |t| + 1 := by
    have hh := abs_add_le (s.im - t) t
    rw [sub_add_cancel] at hh
    linarith [hstrip.2.2]
  have he : completedDirichletHeightWeight χ τ (|t| + 1) s =
      completedDirichletLocalWeight χ τ t s := by
    simp [completedDirichletHeightWeight, completedDirichletLocalWeight, hstrip, him]
  simpa only [Function.mem_support, he] using hs

/-- The complete local count over every actual strip zero, not a chosen finite
subset. A polynomial vertical growth estimate on the displayed genuine circle
would give the logarithmic local multiplicity bound needed by the trace proof. -/
theorem completedDirichlet_local_count_le_circleAverage {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ t : ℝ) :
    (∑ᶠ s : ℂ, completedDirichletLocalWeight χ τ t s) * Real.log 2 ≤
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
      ((2 : ℂ) + (t : ℂ) * Complex.I) 6 + Real.log dirichletCenterMajorant := by
  classical
  have hf := completedDirichletLocalWeight_finiteSupport χ τ t
  have hS : ∀ s ∈ hf.toFinset, 0 < s.re ∧ s.re < 1 ∧ |s.im - t| ≤ 1 := by
    intro s hs
    have hh := hf.mem_toFinset.mp hs
    by_contra hn
    exact hh (by simp [completedDirichletLocalWeight, hn])
  rw [finsum_eq_sum _ hf]
  have he : (∑ s ∈ hf.toFinset, completedDirichletLocalWeight χ τ t s) =
      ∑ s ∈ hf.toFinset, (analyticOrderNatAt (completedDirichletNormTwist χ τ) s : ℝ) := by
    apply Finset.sum_congr rfl
    intro s hs
    simp [completedDirichletLocalWeight, hS s hs]
  rw [he]
  exact completedDirichlet_local_finite_count_le_circleAverage χ τ t hf.toFinset hS
end MasulloGRH
#check MasulloGRH.dirichletStrip_distance_moving_le
#print axioms MasulloGRH.dirichletStrip_distance_moving_le
#check MasulloGRH.completedDirichlet_local_finite_count_le_circleAverage
#print axioms MasulloGRH.completedDirichlet_local_finite_count_le_circleAverage
#check MasulloGRH.completedDirichletLocalWeight_finiteSupport
#print axioms MasulloGRH.completedDirichletLocalWeight_finiteSupport
#check MasulloGRH.completedDirichlet_local_count_le_circleAverage
#print axioms MasulloGRH.completedDirichlet_local_count_le_circleAverage

/-! Round 12 H: explicit multiplicity budgets for the genuine trace jets.
The logarithmic circle comparison is adapted from frozen round-11 C; that
source did not have a final successful receipt, so it is rechecked here. -/
namespace MasulloGRH
theorem dirichletPoleCleared_circleMean_le_log {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R K : ℝ)
    (hK : 1 ≤ K)
    (hb : ∀ z ∈ Metric.sphere c |R|, ‖dirichletPoleCleared χ τ z‖ ≤ K) :
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖) c R ≤
      Real.log K := by
  have ha : AnalyticOnNhd ℂ (dirichletPoleCleared χ τ) (Metric.sphere c |R|) :=
    fun z _ => dirichletPoleCleared_entire χ τ z (Set.mem_univ z)
  have hi := circleIntegrable_log_norm_meromorphicOn ha.meromorphicOn
  have hl : ∀ z ∈ Metric.sphere c |R|,
      Real.log ‖dirichletPoleCleared χ τ z‖ ≤ Real.log K := by
    intro z hz
    by_cases hn : dirichletPoleCleared χ τ z = 0
    · simpa [hn] using Real.log_nonneg hK
    · exact Real.log_le_log (norm_pos_iff.mpr hn) (hb z hz)
  simpa only [Real.circleAverage_const] using
    Real.circleAverage_mono hi (circleIntegrable_const (Real.log K) c R) hl


/-- An actual zero's full multiplicity is controlled by its moving circle.
This is the pointwise multiplicity input to manuscript (10.4.2.34). -/
theorem completedDirichlet_multiplicity_le_circleMean {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (ρ : ℂ)
    (hpos : 0 < ρ.re) (hlt : ρ.re < 1) :
    (analyticOrderNatAt (completedDirichletNormTwist χ τ) ρ : ℝ) * Real.log 2 ≤
      Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖)
        (2 + (ρ.im : ℂ) * Complex.I) 6 + Real.log dirichletCenterMajorant := by
  classical
  have hS : ∀ s ∈ ({ρ} : Finset ℂ),
      0 < s.re ∧ s.re < 1 ∧ |s.im - ρ.im| ≤ 1 := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst s
    exact ⟨hpos, hlt, by simp⟩
  simpa using completedDirichlet_local_finite_count_le_circleAverage χ τ ρ.im {ρ} hS

/-- A norm bound on the actual circle bounds the exponential multiplicity
factor occurring in the genuine spectral trace estimate. No artificial divisor
or capped multiplicity is used. The arithmetic norm bound remains explicit. -/
theorem completedDirichlet_two_pow_multiplicity_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (ρ : ℂ)
    (hpos : 0 < ρ.re) (hlt : ρ.re < 1) (K : ℝ) (hK : 1 ≤ K)
    (hgrowth : ∀ z ∈ Metric.sphere (2 + (ρ.im : ℂ) * Complex.I) |(6 : ℝ)|,
      ‖dirichletPoleCleared χ τ z‖ ≤ K) :
    (2 : ℝ) ^ analyticOrderNatAt (completedDirichletNormTwist χ τ) ρ ≤
      K * dirichletCenterMajorant := by
  have hm := completedDirichlet_multiplicity_le_circleMean χ τ ρ hpos hlt
  have hb := dirichletPoleCleared_circleMean_le_log χ τ
    (2 + (ρ.im : ℂ) * Complex.I) 6 K hK hgrowth
  have hlog : (analyticOrderNatAt (completedDirichletNormTwist χ τ) ρ : ℝ) *
      Real.log 2 ≤ Real.log K + Real.log dirichletCenterMajorant := by linarith
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_add, Real.exp_log (by linarith : 0 < K),
    Real.exp_log dirichletCenterMajorant_pos,
    Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact he

end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_circleMean_le_log
#print axioms MasulloGRH.dirichletPoleCleared_circleMean_le_log
#check MasulloGRH.completedDirichlet_multiplicity_le_circleMean
#print axioms MasulloGRH.completedDirichlet_multiplicity_le_circleMean
#check MasulloGRH.completedDirichlet_two_pow_multiplicity_le
#print axioms MasulloGRH.completedDirichlet_two_pow_multiplicity_le
