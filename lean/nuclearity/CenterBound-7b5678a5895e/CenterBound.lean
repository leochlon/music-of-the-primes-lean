import Mathlib

namespace MasulloGRH
noncomputable def dirichletCenterMajorant : ℝ :=
  1 + ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖

theorem dirichletCenterMajorant_pos : 0 < dirichletCenterMajorant := by
  unfold dirichletCenterMajorant
  have h : 0 ≤ ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖ :=
    tsum_nonneg (fun _ => norm_nonneg _)
  linarith

theorem dirichlet_LSeries_norm_le_centerMajorant {N : ℕ}
    (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s.re = 2) :
    ‖LSeries (fun n => χ (n : ZMod N)) s‖ ≤ dirichletCenterMajorant := by
  have hsum : LSeriesSummable (fun _ => (1 : ℂ)) (2 : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (by intros; simp) (by norm_num)
  have hc : LSeriesSummable (fun n => χ (n : ZMod N)) s :=
    LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
      (fun n _ => χ.norm_le_one _) (by rw [hs]; norm_num)
  have hterm : ∀ n, ‖LSeries.term (fun n => χ (n : ZMod N)) s n‖ ≤
      ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hs]
    split_ifs with hn
    · rfl
    · simp only [norm_one, Complex.re_ofNat]
      exact div_le_div_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    ‖LSeries (fun n => χ (n : ZMod N)) s‖ ≤
        ∑' n, ‖LSeries.term (fun n => χ (n : ZMod N)) s n‖ := norm_tsum_le_tsum_norm hc.norm
    _ ≤ ∑' n, ‖LSeries.term (fun _ => (1 : ℂ)) 2 n‖ :=
      hc.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ dirichletCenterMajorant := by unfold dirichletCenterMajorant; linarith
end MasulloGRH
#check MasulloGRH.dirichlet_LSeries_norm_le_centerMajorant
#print axioms MasulloGRH.dirichlet_LSeries_norm_le_centerMajorant

namespace MasulloGRH
/-- The actual Dirichlet series is uniformly bounded away from zero on Re(s)=2.
This is the missing center-bound input to the genuine-divisor Jensen count. -/
theorem dirichlet_LSeries_center_lower {N : ℕ}
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    dirichletCenterMajorant⁻¹ ≤
      ‖LSeries (fun n => χ (n : ZMod N)) (2 + Complex.I * (t : ℂ))‖ := by
  let B := dirichletCenterMajorant
  let x := ‖LSeries (fun n => χ (n : ZMod N)) (2 + Complex.I * (t : ℂ))‖
  have hB : 0 < B := dirichletCenterMajorant_pos
  have hx : 0 ≤ x := norm_nonneg _
  have h0 := dirichlet_LSeries_norm_le_centerMajorant (1 : DirichletCharacter ℂ N)
    (2 : ℂ) (by norm_num)
  have h2 := dirichlet_LSeries_norm_le_centerMajorant (χ ^ 2)
    (2 + 2 * Complex.I * (t : ℂ)) (by simp)
  have hp := χ.norm_LSeries_product_ge_one (x := 1) (by norm_num) t
  norm_num only [Complex.ofReal_one, one_add_one_eq_two, norm_mul, norm_pow] at hp
  have hu : 1 ≤ (B * x) ^ 4 := by
    calc
      1 ≤ ‖LSeries (fun n => (1 : DirichletCharacter ℂ N) (n : ZMod N)) 2‖ ^ 3 *
          x ^ 4 * ‖LSeries (fun n => (χ ^ 2) (n : ZMod N))
            (2 + 2 * Complex.I * (t : ℂ))‖ := hp
      _ ≤ B ^ 3 * x ^ 4 * B := by
        gcongr
      _ = (B * x) ^ 4 := by ring
  have hbx : 1 ≤ B * x := by
    by_contra h
    have hb : B * x < 1 := lt_of_not_ge h
    have hh : (B * x) ^ 4 < 1 ^ 4 := pow_lt_pow_left₀ hb (mul_nonneg hB.le hx) (by norm_num)
    norm_num at hh
    linarith
  change B⁻¹ ≤ x
  rw [inv_eq_one_div]
  exact (div_le_iff₀ hB).mpr (by nlinarith only [hbx])
end MasulloGRH
#check MasulloGRH.dirichletCenterMajorant_pos
#print axioms MasulloGRH.dirichletCenterMajorant_pos
#check MasulloGRH.dirichlet_LSeries_center_lower
#print axioms MasulloGRH.dirichlet_LSeries_center_lower

namespace MasulloGRH
/-- The lower bound concerns Mathlib's genuine analytically continued L-function. -/
theorem dirichlet_LFunction_center_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (t : ℝ) :
    dirichletCenterMajorant⁻¹ ≤ ‖χ.LFunction (2 + Complex.I * (t : ℂ))‖ := by
  rw [χ.LFunction_eq_LSeries (by simp)]
  exact dirichlet_LSeries_center_lower χ t

/-- Same genuine pole-cleared function as frozen r08/F and r08/A, with shifted poles. -/
noncomputable def dirichletCenterPoleCleared {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ : ℝ) (s : ℂ) : ℂ := by
  classical
  exact if χ = 1 then
    DirichletCharacter.LFunctionTrivChar₁ N (s + (τ : ℂ) * Complex.I)
  else χ.LFunction (s + (τ : ℂ) * Complex.I)

/-- Uniform positive center bound for the actual entire function used by Jensen.
Every real norm twist is retained, with center 2+i(t-tau). -/
theorem dirichletPoleCleared_center_lower {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (τ t : ℝ) :
    dirichletCenterMajorant⁻¹ ≤
      ‖dirichletCenterPoleCleared χ τ (2 + Complex.I * ((t - τ : ℝ) : ℂ))‖ := by
  classical
  have he : (2 + Complex.I * ((t - τ : ℝ) : ℂ)) + (τ : ℂ) * Complex.I =
      2 + Complex.I * (t : ℂ) := by push_cast; ring
  have hne : (2 + Complex.I * (t : ℂ)) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have hl := dirichlet_LFunction_center_lower χ t
  have hf : 1 ≤ ‖(2 + Complex.I * (t : ℂ)) - 1‖ := by
    have hh := Complex.abs_re_le_norm ((2 + Complex.I * (t : ℂ)) - 1)
    norm_num at hh
    exact hh
  by_cases hχ : χ = 1
  · simp only [dirichletCenterPoleCleared, if_pos hχ, he]
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hne,
      DirichletCharacter.LFunctionTrivChar, norm_mul]
    calc
      dirichletCenterMajorant⁻¹ ≤ ‖χ.LFunction (2 + Complex.I * (t : ℂ))‖ := hl
      _ = 1 * ‖(1 : DirichletCharacter ℂ N).LFunction (2 + Complex.I * (t : ℂ))‖ := by rw [hχ, one_mul]
      _ ≤ ‖2 + Complex.I * (t : ℂ) - 1‖ *
          ‖(1 : DirichletCharacter ℂ N).LFunction (2 + Complex.I * (t : ℂ))‖ :=
        mul_le_mul_of_nonneg_right hf (norm_nonneg _)
  · simpa only [dirichletCenterPoleCleared, if_neg hχ, he] using hl

end MasulloGRH
#check MasulloGRH.dirichlet_LFunction_center_lower
#print axioms MasulloGRH.dirichlet_LFunction_center_lower
#check MasulloGRH.dirichletPoleCleared_center_lower
#print axioms MasulloGRH.dirichletPoleCleared_center_lower
