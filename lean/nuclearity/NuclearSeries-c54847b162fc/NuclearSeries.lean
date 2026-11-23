import Mathlib
open scoped BigOperators
namespace Round103C
theorem rankOne_series_of_cost {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u v : ι → H) (hc : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun i => ‖(innerSL ℂ (v i)).smulRight (u i)‖) ∧
    Summable (fun i => (innerSL ℂ (v i)).smulRight (u i)) := by
  have hb (i : ι) : ‖(innerSL ℂ (v i)).smulRight (u i)‖ ≤ ‖u i‖ * ‖v i‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    intro f
    have h := mul_le_mul_of_nonneg_right ((innerSL ℂ (v i)).le_opNorm f) (norm_nonneg (u i))
    simpa [ContinuousLinearMap.smulRight_apply, norm_smul, innerSL_apply_norm,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hn : Summable (fun i => ‖(innerSL ℂ (v i)).smulRight (u i)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb hc
  exact ⟨hn, hn.of_norm⟩

#check rankOne_series_of_cost
#print axioms rankOne_series_of_cost

/-- Upgrade the same strong reconstruction and derived costs to operator-norm
HasSum. In the actual residual application, the cost is derived from tests. -/
theorem rankOne_operator_hasSum_of_strong {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u v : ι → H) (T : H →L[ℂ] H)
    (hc : Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖))
    (hs : ∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) :
    HasSum (fun i => (innerSL ℂ (v i)).smulRight (u i)) T := by
  have hc' : Summable (fun i => ‖u i‖ * ‖v i‖) := by
    simpa only [innerSL_apply_norm] using hc
  have hh := (rankOne_series_of_cost u v hc').2.hasSum
  have heq : (∑' i, (innerSL ℂ (v i)).smulRight (u i)) = T := by
    apply ContinuousLinearMap.ext
    intro F
    have h := (ContinuousLinearMap.apply ℂ H F).hasSum hh
    exact h.unique (by simpa only [ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply] using hs F)
  simpa only [heq] using hh
#check rankOne_operator_hasSum_of_strong
#print axioms rankOne_operator_hasSum_of_strong
end Round103C

namespace Round103C
/-- Right composition preserves the derived nuclear cost, with explicit
operator-norm dependence. This applies to residuals followed by P. -/
theorem right_composed_nuclear_cost {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u v : ι → H) (T P : H →L[ℂ] H)
    (hc : Summable (fun i => ‖u i‖ * ‖innerSL ℂ (v i)‖))
    (hs : ∀ F, HasSum (fun i => inner ℂ (v i) F • u i) (T F)) :
    Summable (fun i => ‖u i‖ * ‖(innerSL ℂ (v i)).comp P‖) ∧
    (∀ F, HasSum (fun i => ((innerSL ℂ (v i)).comp P) F • u i) ((T.comp P) F)) := by
  have hb (i) : ‖u i‖ * ‖(innerSL ℂ (v i)).comp P‖ ≤
      (‖u i‖ * ‖innerSL ℂ (v i)‖) * ‖P‖ := by
    calc
      _ ≤ ‖u i‖ * (‖innerSL ℂ (v i)‖ * ‖P‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ = _ := by ring
  refine ⟨Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hb (hc.mul_right ‖P‖), ?_⟩
  intro F
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hs (P F)
#check right_composed_nuclear_cost
#print axioms right_composed_nuclear_cost
end Round103C
