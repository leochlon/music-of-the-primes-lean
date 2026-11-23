import Mathlib
/-! F round 12: genuine logarithmic circle integration. Inherited counting
artifact retained in VerifiedCounts.lean; corrected count extension remains
unverified in CountExtension.lean. -/
namespace MasulloGRH
open Set
noncomputable def dirichletNormTwist {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℂ :=
  χ.LFunction (s + (τ : ℂ) * Complex.I)


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


/-- The actual pole-cleared continuation has an integrable logarithm on every
circle, including circles containing zeros. -/
theorem dirichletPoleCleared_log_circleIntegrable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R : ℝ) :
    CircleIntegrable (fun z => Real.log ‖dirichletPoleCleared χ τ z‖) c R := by
  apply circleIntegrable_log_norm_meromorphicOn
  intro z _
  exact (dirichletPoleCleared_entire χ τ z (mem_univ z)).meromorphicAt

/-- A genuine arithmetic bound on the circle controls its logarithmic mean.
The hypothesis M >= 1 handles Lean's value log(0)=0 without removing zeros. -/
theorem dirichletPoleCleared_circleAverage_le_log {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (c : ℂ) (R M : ℝ)
    (hM : 1 ≤ M)
    (hbound : ∀ z ∈ Metric.sphere c |R|, ‖dirichletPoleCleared χ τ z‖ ≤ M) :
    Real.circleAverage (fun z => Real.log ‖dirichletPoleCleared χ τ z‖) c R ≤
      Real.log M := by
  have hi := dirichletPoleCleared_log_circleIntegrable χ τ c R
  have hh := Real.circleAverage_mono hi (circleIntegrable_const (Real.log M) c R)
    (fun z hz => show Real.log ‖dirichletPoleCleared χ τ z‖ ≤ Real.log M from by
      by_cases hzero : dirichletPoleCleared χ τ z = 0
      · simpa [hzero] using Real.log_nonneg hM
      · exact Real.log_le_log (norm_pos_iff.mpr hzero) (hbound z hz))
  simpa only [Real.circleAverage_const] using hh


end MasulloGRH
#check MasulloGRH.dirichletPoleCleared_entire
#print axioms MasulloGRH.dirichletPoleCleared_entire
#check MasulloGRH.dirichletPoleCleared_log_circleIntegrable
#print axioms MasulloGRH.dirichletPoleCleared_log_circleIntegrable
#check MasulloGRH.dirichletPoleCleared_circleAverage_le_log
#print axioms MasulloGRH.dirichletPoleCleared_circleAverage_le_log
