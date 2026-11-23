import Mathlib
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
open Filter Topology
attribute [local instance] Classical.propDecidable

namespace MasulloGRH.Round9A
theorem gamma_meromorphic (s : ℂ) : MeromorphicAt Complex.Gamma s := by
  have h := (Complex.differentiable_one_div_Gamma.analyticAt s).meromorphicAt.inv
  change MeromorphicAt (fun z : ℂ => ((Complex.Gamma z)⁻¹)⁻¹) s at h
  simpa only [inv_inv] using h
theorem reciprocal_gamma_factor (n : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-(n : ℂ)) ∧ g (-(n : ℂ)) ≠ 0 ∧
      ∀ z : ℂ, (Complex.Gamma z)⁻¹ = (z + (n : ℂ)) * g z := by
  induction n with
  | zero =>
    refine ⟨fun z => (Complex.Gamma (z + 1))⁻¹, ?_, ?_, ?_⟩
    · exact (Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add_const 1)).analyticAt _
    · simp [Complex.Gamma_one]
    · intro z
      simpa using Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one z
  | succ n ih =>
    obtain ⟨g, hg, hn, he⟩ := ih
    have hs : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
    refine ⟨fun z => z * g (z + 1), ?_, ?_, ?_⟩
    · apply analyticAt_id.mul
      have hc : AnalyticAt ℂ g (-((n + 1 : ℕ) : ℂ) + 1) := by rw [hs]; exact hg
      exact hc.comp (f := fun z : ℂ => z + 1) (analyticAt_id.add analyticAt_const)
    · apply mul_ne_zero
      · exact neg_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero n)
      · simpa only [hs] using hn
    · intro z
      rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one, he]
      push_cast
      ring
theorem gamma_order_neg_nat (n : ℕ) :
    meromorphicOrderAt Complex.Gamma (-(n : ℂ)) = -1 := by
  obtain ⟨g, hg, hn, he⟩ := reciprocal_gamma_factor n
  apply (meromorphicOrderAt_eq_int_iff (gamma_meromorphic _)).2
  refine ⟨fun z => (g z)⁻¹, hg.inv hn, inv_ne_zero hn,
    Filter.Eventually.of_forall ?_⟩
  intro z
  have hz : Complex.Gamma z = ((z + (n : ℂ)) * g z)⁻¹ := by
    rw [← he z, inv_inv]
  rw [hz]
  simp only [sub_neg_eq_add, zpow_neg_one, smul_eq_mul, mul_inv_rev]
  ring
end MasulloGRH.Round9A

namespace MasulloGRH.Round10A
open MasulloGRH.Round9A
theorem gamma_affine_order (a b x : ℂ) (ha : a ≠ 0) (n : ℕ)
    (hx : a * x + b = -(n : ℂ)) :
    meromorphicOrderAt (fun z => Complex.Gamma (a * z + b)) x = -1 := by
  have hg : AnalyticAt ℂ (fun z : ℂ => a * z + b) x :=
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hd : HasDerivAt (fun z : ℂ => a * z + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := Complex.Gamma) hg
    (by rw [hd.deriv]; exact ha)
  simpa only [Function.comp_def, hx, gamma_order_neg_nat] using h
theorem gammaR_shift_meromorphic (c x : ℂ) :
    MeromorphicAt (fun z => Complex.Gammaℝ (z + c)) x := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + c) / 2)) x :=
    (((differentiable_id.add_const c).neg.div_const 2).const_cpow (Or.inl hp)).analyticAt x
  have hg : MeromorphicAt (fun z : ℂ => Complex.Gamma ((z + c) / 2)) x :=
    (Round9A.gamma_meromorphic _).comp_analyticAt
      (((differentiable_id.add_const c).div_const 2).analyticAt x)
  simp_rw [Complex.Gammaℝ_def]
  exact hu.meromorphicAt.mul hg
theorem gammaC_shift_meromorphic (c x : ℂ) :
    MeromorphicAt (fun z => Complex.Gammaℂ (z + c)) x := by
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hu : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-(z + c))) x :=
    ((differentiable_const 2).mul
      ((differentiable_id.add_const c).neg.const_cpow (Or.inl hp))).analyticAt x
  have hg : MeromorphicAt (fun z : ℂ => Complex.Gamma (z + c)) x :=
    (Round9A.gamma_meromorphic _).comp_analyticAt
      ((differentiable_id.add_const c).analyticAt x)
  simp_rw [Complex.Gammaℂ_def]
  exact hu.meromorphicAt.mul hg
end MasulloGRH.Round10A

namespace MasulloGRH.Round11A
open MasulloGRH.Round10A
theorem finite_product_divisor {ι : Type*} (S : Finset ι)
    (F : ι → ℂ → ℂ) (x : ℂ)
    (hF : ∀ i ∈ S, MeromorphicAt (F i) x) :
    MeromorphicAt (fun z => ∏ i ∈ S, F i z) x ∧
      meromorphicOrderAt (fun z => ∏ i ∈ S, F i z) x =
        ∑ i ∈ S, meromorphicOrderAt (F i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · simpa using (analyticAt_const.meromorphicAt :
          MeromorphicAt (fun _ : ℂ => (1 : ℂ)) x)
      · simp [meromorphicOrderAt_const]
  | @insert a S ha ih =>
      have hi := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      have hm := hF a (Finset.mem_insert_self a S)
      constructor
      · simpa only [Finset.prod_insert ha] using hm.mul hi.1
      · simp only [Finset.prod_insert ha, Finset.sum_insert ha]
        have hh := meromorphicOrderAt_mul hm hi.1
        rw [hi.2] at hh
        exact hh
theorem archimedean_product_order {ι κ : Type*}
    (R : Finset ι) (C : Finset κ) (r : ι → ℂ) (c : κ → ℂ) (x : ℂ) :
    meromorphicOrderAt (fun z =>
      (∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
      (∏ j ∈ C, Complex.Gammaℂ (z + c j))) x =
      (∑ i ∈ R, meromorphicOrderAt (fun z => Complex.Gammaℝ (z + r i)) x) +
      (∑ j ∈ C, meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c j)) x) := by
  have hR := finite_product_divisor R (fun i z => Complex.Gammaℝ (z + r i)) x
    (fun i _ => gammaR_shift_meromorphic (r i) x)
  have hC := finite_product_divisor C (fun i z => Complex.Gammaℂ (z + c i)) x
    (fun i _ => gammaC_shift_meromorphic (c i) x)
  exact (meromorphicOrderAt_mul hR.1 hC.1).trans (congrArg₂ (· + ·) hR.2 hC.2)
end MasulloGRH.Round11A

namespace MasulloGRH.Round13A
theorem meromorphic_germ_eq_of_rightHalfPlane (F G : ℂ → ℂ)
    (hF : MeromorphicOn F Set.univ) (hG : MeromorphicOn G Set.univ)
    (h : ∀ z : ℂ, 1 < z.re → F z = G z) (x : ℂ) :
    F =ᶠ[𝓝[≠] x] G := by
  have hd := hF.fun_sub hG
  have hl : (fun z => F z - G z) =ᶠ[𝓝[≠] (2 : ℂ)] (fun _ => 0) := by
    have ho : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have ht : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    exact ((ho.eventually_mem ht).filter_mono nhdsWithin_le_nhds).mono
      (fun z hz => sub_eq_zero.mpr (h z hz))
  have htwo : meromorphicOrderAt (fun z => F z - G z) (2 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_congr hl]
    simp [meromorphicOrderAt_const]
  have hx : meromorphicOrderAt (fun z => F z - G z) x = ⊤ := by
    by_contra hn
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ x) (Set.mem_univ (2 : ℂ)) hn) htwo
  have he := meromorphicOrderAt_eq_top_iff.mp hx
  filter_upwards [he] with z hz
  exact sub_eq_zero.mp hz
end MasulloGRH.Round13A

namespace MasulloGRH.Round15A
theorem weakFE_norm_twist_meromorphic (P : WeakFEPair ℂ) (τ : ℝ) :
    MeromorphicOn (fun z : ℂ => P.Λ (z + (τ : ℂ) * Complex.I)) Set.univ := by
  have hm (x : ℂ) : MeromorphicAt P.Λ x := by
    unfold WeakFEPair.Λ
    simp only [smul_eq_mul]
    exact ((P.differentiable_Λ₀.analyticAt x).meromorphicAt.sub
      ((analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt).mul
        analyticAt_const.meromorphicAt)).sub
      ((analyticAt_const.meromorphicAt.div
        ((analyticAt_const.sub analyticAt_id).meromorphicAt)).mul
          analyticAt_const.meromorphicAt)
  intro x _
  exact (hm _).comp_analyticAt ((differentiable_id.add_const _).analyticAt x)

end MasulloGRH.Round15A

namespace MasulloGRH.Round16A
open MasulloGRH.Round10A MasulloGRH.Round11A
attribute [local instance] Classical.propDecidable
/-- Supplies the nonpole branch missing from the genuine Gamma divisor count. -/
theorem gamma_affine_full_order (a b x : ℂ) (ha : a ≠ 0) :
    meromorphicOrderAt (fun z => Complex.Gamma (a * z + b)) x =
      if ∃ n : ℕ, a * x + b = -(n : ℂ) then (-1 : WithTop ℤ) else 0 := by
  by_cases h : ∃ n : ℕ, a * x + b = -(n : ℂ)
  · rw [if_pos h]
    obtain ⟨n, hn⟩ := h
    exact gamma_affine_order a b x ha n hn
  · rw [if_neg h]
    have hn : Complex.Gamma (a * x + b) ≠ 0 :=
      Complex.Gamma_ne_zero (fun n hn => h ⟨n, hn⟩)
    have hg := (Complex.differentiable_one_div_Gamma.analyticAt (a * x + b)).inv
      (inv_ne_zero hn)
    change AnalyticAt ℂ (fun z : ℂ => ((Complex.Gamma z)⁻¹)⁻¹) (a * x + b) at hg
    have hg' : AnalyticAt ℂ Complex.Gamma (a * x + b) := by
      simpa only [inv_inv] using hg
    have hc := hg'.comp (f := fun z : ℂ => a * z + b)
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
    have he := meromorphicOrderAt_mul_of_ne_zero (f := fun _ : ℂ => (1 : ℂ)) hc hn
    change meromorphicOrderAt (fun z => Complex.Gamma (a * z + b) * 1) x =
      meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) x at he
    simpa [meromorphicOrderAt_const] using he
/-- Full real-place divisor, including every nonpole and every character shift. -/
theorem gammaR_full_order (c x : ℂ) :
    meromorphicOrderAt (fun z => Complex.Gammaℝ (z + c)) x =
      if ∃ n : ℕ, (x + c) / 2 = -(n : ℂ) then (-1 : WithTop ℤ) else 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + c) / 2)) x :=
    (((differentiable_id.add_const c).neg.div_const 2).const_cpow (Or.inl hp)).analyticAt x
  have hn : (Real.pi : ℂ) ^ (-(x + c) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp)
  have he (z : ℂ) : (z + c) / 2 = (1 / 2 : ℂ) * z + c / 2 := by ring
  have hg := gamma_affine_full_order (1 / 2) (c / 2) x (by norm_num)
  have hm := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => Complex.Gamma ((z + c) / 2)) hu hn
  simp_rw [Complex.Gammaℝ_def]
  exact hm.trans (by simpa only [he] using hg)
/-- Full complex-place divisor with Mathlib's actual GammaC normalization. -/
theorem gammaC_full_order (c x : ℂ) :
    meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c)) x =
      if ∃ n : ℕ, x + c = -(n : ℂ) then (-1 : WithTop ℤ) else 0 := by
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hu : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-(z + c))) x :=
    ((differentiable_const 2).mul
      ((differentiable_id.add_const c).neg.const_cpow (Or.inl hp))).analyticAt x
  have hn : 2 * (2 * (Real.pi : ℂ)) ^ (-(x + c)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))
  have hg := gamma_affine_full_order 1 c x one_ne_zero
  have hm := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => Complex.Gamma (z + c)) hu hn
  simp_rw [Complex.Gammaℂ_def]
  exact hm.trans (by simpa only [one_mul] using hg)
/-- Exact mixed pole/nonpole count; coincident poles retain their place indices.
Discharges the full archimedean divisor premise, without a prescribed zero set. -/
theorem archimedean_full_divisor {ι κ : Type*}
    (R : Finset ι) (C : Finset κ) (r : ι → ℂ) (c : κ → ℂ) (x : ℂ) :
    meromorphicOrderAt (fun z =>
      (∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
      (∏ j ∈ C, Complex.Gammaℂ (z + c j))) x =
      (∑ i ∈ R, if ∃ n : ℕ, (x + r i) / 2 = -(n : ℂ)
        then (-1 : WithTop ℤ) else 0) +
      (∑ j ∈ C, if ∃ n : ℕ, x + c j = -(n : ℂ)
        then (-1 : WithTop ℤ) else 0) := by
  rw [archimedean_product_order]
  simp_rw [gammaR_full_order, gammaC_full_order]
/-- CONDITIONAL completed/finite divisor bridge. The precise premise discharged
is transport from a half-plane Mellin identity to the full, multiplicity-correct
Gamma cancellation ledger. Arithmetic realization of P, L, places and shifts is
still required; L is supplied, never defined to force an equality. -/
theorem attached_archimedean_divisor {ι κ : Type*}
    (R : Finset ι) (C : Finset κ) (r : ι → ℂ) (c : κ → ℂ)
    (P : WeakFEPair ℂ) (hk : P.k = 1) (τ : ℝ) (L : ℂ → ℂ)
    (hL : MeromorphicOn L Set.univ)
    (hM : ∀ z : ℂ, 1 < z.re →
      HasMellin (fun t => P.f t - P.f₀) (z + (τ : ℂ) * Complex.I)
        (((∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
          (∏ j ∈ C, Complex.Gammaℂ (z + c j))) * L z)) (x : ℂ) :
    meromorphicOrderAt (fun z => P.Λ (z + (τ : ℂ) * Complex.I)) x =
      ((∑ i ∈ R, if ∃ n : ℕ, (x + r i) / 2 = -(n : ℂ)
        then (-1 : WithTop ℤ) else 0) +
      (∑ j ∈ C, if ∃ n : ℕ, x + c j = -(n : ℂ)
        then (-1 : WithTop ℤ) else 0)) + meromorphicOrderAt L x := by
  let G : ℂ → ℂ := fun z =>
    (∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
      (∏ j ∈ C, Complex.Gammaℂ (z + c j))
  have hG (z : ℂ) : MeromorphicAt G z :=
    ((finite_product_divisor R _ z (fun i _ => gammaR_shift_meromorphic (r i) z)).1).mul
      ((finite_product_divisor C _ z (fun j _ => gammaC_shift_meromorphic (c j) z)).1)
  have hh (z : ℂ) (hz : 1 < z.re) : P.Λ (z + (τ : ℂ) * Complex.I) = G z * L z := by
    have hs : P.k < (z + (τ : ℂ) * Complex.I).re := by simpa [hk] using hz
    exact (P.hasMellin hs).2.symm.trans (hM z hz).2
  have he := Round13A.meromorphic_germ_eq_of_rightHalfPlane _ _
    (Round15A.weakFE_norm_twist_meromorphic P τ)
    (fun z hz => (hG z).mul (hL z hz)) hh x
  rw [meromorphicOrderAt_congr he, meromorphicOrderAt_mul (hG x) (hL x (Set.mem_univ x))]
  exact congrArg (fun q => q + meromorphicOrderAt L x) (archimedean_full_divisor R C r c x)
#check gamma_affine_full_order
#print axioms gamma_affine_full_order
#check gammaR_full_order
#print axioms gammaR_full_order
#check gammaC_full_order
#print axioms gammaC_full_order
#check archimedean_full_divisor
#print axioms archimedean_full_divisor
#check attached_archimedean_divisor
#print axioms attached_archimedean_divisor
end MasulloGRH.Round16A
