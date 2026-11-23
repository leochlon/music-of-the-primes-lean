import Mathlib
set_option linter.unnecessarySimpa false
open Filter Topology
namespace MasulloGRH.Round9A
/-- Local meromorphicity premise for the actual archimedean Gamma divisor. -/
theorem gamma_meromorphic (s : ℂ) : MeromorphicAt Complex.Gamma s := by
  have h := (Complex.differentiable_one_div_Gamma.analyticAt s).meromorphicAt.inv
  change MeromorphicAt (fun z : ℂ => ((Complex.Gamma z)⁻¹)⁻¹) s at h
  simpa only [inv_inv] using h
/-- Discharges the simple-zero factorization premise for reciprocal Gamma at
all nonpositive integers; these are the local trivial-zero cancellation sites. -/
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
/-- Actual Gamma has a simple meromorphic pole at every nonpositive integer.
This supplies the local pole multiplicity needed before counting genuine
completed-Hecke zeros; no L-function or prescribed zero set is introduced. -/
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
/-- CONDITIONAL local cancellation ledger for a supplied meromorphic finite
continuation L: multiplying by the actual Gamma subtracts exactly one from
its order at each nonpositive integer. Attaching L to finiteHeckeL and the
completed Hecke function remains a separate unresolved arithmetic premise. -/
theorem gamma_completion_order (L : ℂ → ℂ) (n : ℕ)
    (hL : MeromorphicAt L (-(n : ℂ))) :
    meromorphicOrderAt (fun z => Complex.Gamma z * L z) (-(n : ℂ)) =
      -1 + meromorphicOrderAt L (-(n : ℂ)) := by
  have h := meromorphicOrderAt_mul (gamma_meromorphic (-(n : ℂ))) hL
  rw [gamma_order_neg_nat] at h
  exact h
#check gamma_meromorphic
#print axioms gamma_meromorphic
#check reciprocal_gamma_factor
#print axioms reciprocal_gamma_factor
#check gamma_order_neg_nat
#print axioms gamma_order_neg_nat
#check gamma_completion_order
#print axioms gamma_completion_order
end MasulloGRH.Round9A

namespace MasulloGRH.Round10A
open MasulloGRH.Round9A
/-- Discharges the change-of-parameter premise for archimedean Gamma poles:
nonzero affine rescaling and any complex shift preserve their multiplicity. -/
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
/-- Meromorphicity of the actual shifted/scaled Gamma factor; needed to add
its order to the finite continuation's order, rather than just list poles. -/
theorem gamma_affine_meromorphic (a b x : ℂ) :
    MeromorphicAt (fun z => Complex.Gamma (a * z + b)) x := by
  exact (gamma_meromorphic _).comp_analyticAt
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
/-- CONDITIONAL exact local cancellation for the affine Gamma arguments
occurring at real and complex places in the completed Hecke product. -/
theorem gamma_affine_completion_order (L : ℂ → ℂ) (a b x : ℂ)
    (ha : a ≠ 0) (n : ℕ) (hx : a * x + b = -(n : ℂ))
    (hL : MeromorphicAt L x) :
    meromorphicOrderAt (fun z => Complex.Gamma (a * z + b) * L z) x =
      -1 + meromorphicOrderAt L x := by
  have h := meromorphicOrderAt_mul (gamma_affine_meromorphic a b x) hL
  rw [gamma_affine_order a b x ha n hx] at h
  exact h
#check gamma_affine_order
#print axioms gamma_affine_order
#check gamma_affine_completion_order
#print axioms gamma_affine_completion_order
end MasulloGRH.Round10A

namespace MasulloGRH.Round10A
/-- Actual real-place Gamma factor, including pi normalization. Supplies
one unit of cancellation at (x+c)/2=-n for every complex character shift c. -/
theorem gammaR_shift_order (c x : ℂ) (n : ℕ)
    (hx : (x + c) / 2 = -(n : ℂ)) :
    meromorphicOrderAt (fun z => Complex.Gammaℝ (z + c)) x = -1 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + c) / 2)) x :=
    (((differentiable_id.add_const c).neg.div_const 2).const_cpow (Or.inl hp)).analyticAt x
  have hn : (Real.pi : ℂ) ^ (-(x + c) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp)
  have he (z : ℂ) : (z + c) / 2 = (1 / 2 : ℂ) * z + c / 2 := by ring
  have hg := gamma_affine_order (1 / 2) (c / 2) x (by norm_num) n
    (by rw [← he]; exact hx)
  have hm := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => Complex.Gamma ((z + c) / 2)) hu hn
  simp_rw [Complex.Gammaℝ_def]
  exact hm.trans (by simpa only [he] using hg)
/-- Actual complex-place Gamma factor, including Mathlib's leading 2.
Supplies one unit of cancellation at x+c=-n, retaining every complex shift. -/
theorem gammaC_shift_order (c x : ℂ) (n : ℕ)
    (hx : x + c = -(n : ℂ)) :
    meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c)) x = -1 := by
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hu : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-(z + c))) x :=
    ((differentiable_const 2).mul
      ((differentiable_id.add_const c).neg.const_cpow (Or.inl hp))).analyticAt x
  have hn : 2 * (2 * (Real.pi : ℂ)) ^ (-(x + c)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))
  have hg := gamma_affine_order 1 c x one_ne_zero n (by simpa using hx)
  have hm := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => Complex.Gamma (z + c)) hu hn
  simp_rw [Complex.Gammaℂ_def]
  exact hm.trans (by simpa only [one_mul] using hg)
/-- The simultaneous local archimedean pole statement needed for trivial-zero
cancellation in the genuine completed Hecke divisor, in actual Mathlib factors. -/
theorem archimedean_shift_poles (c : ℂ) (n : ℕ) :
    meromorphicOrderAt (fun z => Complex.Gammaℝ (z + c)) (-c - 2 * n) = -1 ∧
    meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c)) (-c - n) = -1 := by
  constructor
  · apply gammaR_shift_order c _ n
    ring
  · apply gammaC_shift_order c _ n
    ring
#check gammaR_shift_order
#print axioms gammaR_shift_order
#check gammaC_shift_order
#print axioms gammaC_shift_order
#check archimedean_shift_poles
#print axioms archimedean_shift_poles
end MasulloGRH.Round10A

namespace MasulloGRH.Round10A
/-- Supplies meromorphicity of the actual real normalized factor, the missing
hypothesis for adding its divisor to that of a genuine finite continuation. -/
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
/-- Supplies the same divisor-addition premise for the actual complex factor. -/
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
/-- CONDITIONAL local divisor cancellation with the actual normalized
archimedean factors. L is any supplied local meromorphic continuation; its
arithmetic identification is a separate unresolved premise, not assumed here. -/
theorem archimedean_completion_order (L : ℂ → ℂ) (c x : ℂ)
    (hL : MeromorphicAt L x) (n : ℕ) :
    ((x + c) / 2 = -(n : ℂ) →
      meromorphicOrderAt (fun z => Complex.Gammaℝ (z + c) * L z) x =
        -1 + meromorphicOrderAt L x) ∧
    (x + c = -(n : ℂ) →
      meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c) * L z) x =
        -1 + meromorphicOrderAt L x) := by
  constructor
  · intro hx
    have h := meromorphicOrderAt_mul (gammaR_shift_meromorphic c x) hL
    rw [gammaR_shift_order c x n hx] at h
    exact h
  · intro hx
    have h := meromorphicOrderAt_mul (gammaC_shift_meromorphic c x) hL
    rw [gammaC_shift_order c x n hx] at h
    exact h
#check gammaR_shift_meromorphic
#print axioms gammaR_shift_meromorphic
#check gammaC_shift_meromorphic
#print axioms gammaC_shift_meromorphic
#check archimedean_completion_order
#print axioms archimedean_completion_order
end MasulloGRH.Round10A

namespace MasulloGRH.Round11A
open MasulloGRH.Round10A
/-- Finite divisor-addition premise for the full archimedean completion;
indices retain distinct places even when their pole locations coincide. -/
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
/-- Exact divisor of the actual normalized archimedean product at every
complex parameter. This supplies the finite-product multiplicity premise;
it does not construct or identify any Hecke continuation. -/
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
#check archimedean_product_order
#print axioms archimedean_product_order
end MasulloGRH.Round11A

namespace MasulloGRH.Round11A
open MasulloGRH.Round10A
/-- Simultaneous poles add with their place multiplicities, even when every
pole is at the same point. Supplies the coincident-pole cancellation premise. -/
theorem coincident_archimedean_poles {ι κ : Type*}
    (R : Finset ι) (C : Finset κ) (r : ι → ℂ) (c : κ → ℂ) (x : ℂ)
    (nr : ι → ℕ) (nc : κ → ℕ)
    (hr : ∀ i ∈ R, (x + r i) / 2 = -(nr i : ℂ))
    (hc : ∀ j ∈ C, x + c j = -(nc j : ℂ)) :
    meromorphicOrderAt (fun z =>
      (∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
      (∏ j ∈ C, Complex.Gammaℂ (z + c j))) x =
      R.card • (-1 : WithTop ℤ) + C.card • (-1 : WithTop ℤ) := by
  rw [archimedean_product_order]
  have hR : (∑ i ∈ R, meromorphicOrderAt (fun z => Complex.Gammaℝ (z + r i)) x) =
      ∑ _i ∈ R, (-1 : WithTop ℤ) :=
    Finset.sum_congr rfl (fun i hi => gammaR_shift_order (r i) x (nr i) (hr i hi))
  have hC : (∑ j ∈ C, meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c j)) x) =
      ∑ _j ∈ C, (-1 : WithTop ℤ) :=
    Finset.sum_congr rfl (fun j hj => gammaC_shift_order (c j) x (nc j) (hc j hj))
  rw [hR, hC]
  simp only [Finset.sum_const]
/-- CONDITIONAL divisor bridge for any supplied meromorphic finite
continuation L and the actual Gamma factors. The positive norm and nonzero
constant normalizations add no zeros or poles. Attaching L and the shifts to
the checked finite Hecke Euler germ is still an unresolved arithmetic premise. -/
theorem normalized_archimedean_completion_order {ι κ : Type*}
    (R : Finset ι) (C : Finset κ) (r : ι → ℂ) (c : κ → ℂ)
    (L : ℂ → ℂ) (x A : ℂ) (Q : ℝ) (hA : A ≠ 0) (hQ : 0 < Q)
    (hL : MeromorphicAt L x) :
    meromorphicOrderAt (fun z => (A * (Q : ℂ) ^ (z / 2)) *
      (((∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
        (∏ j ∈ C, Complex.Gammaℂ (z + c j))) * L z)) x =
      ((∑ i ∈ R, meromorphicOrderAt (fun z => Complex.Gammaℝ (z + r i)) x) +
       (∑ j ∈ C, meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c j)) x)) +
      meromorphicOrderAt L x := by
  have hQ0 : (Q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hQ
  have hu : AnalyticAt ℂ (fun z : ℂ => A * (Q : ℂ) ^ (z / 2)) x :=
    ((differentiable_const A).mul
      ((differentiable_id.div_const 2).const_cpow (Or.inl hQ0))).analyticAt x
  have hn : A * (Q : ℂ) ^ (x / 2) ≠ 0 :=
    mul_ne_zero hA (Complex.cpow_ne_zero_iff.mpr (Or.inl hQ0))
  have hR := finite_product_divisor R (fun i z => Complex.Gammaℝ (z + r i)) x
    (fun i _ => gammaR_shift_meromorphic (r i) x)
  have hC := finite_product_divisor C (fun j z => Complex.Gammaℂ (z + c j)) x
    (fun j _ => gammaC_shift_meromorphic (c j) x)
  have hh := meromorphicOrderAt_mul (hR.1.mul hC.1) hL
  have he := archimedean_product_order R C r c x
  have hh' := hh.trans (congrArg (fun k => k + meromorphicOrderAt L x) he)
  exact (meromorphicOrderAt_mul_of_ne_zero hu hn).trans hh'
#check finite_product_divisor
#print axioms finite_product_divisor
#check coincident_archimedean_poles
#print axioms coincident_archimedean_poles
#check normalized_archimedean_completion_order
#print axioms normalized_archimedean_completion_order
end MasulloGRH.Round11A

namespace MasulloGRH.Round11A
open MasulloGRH.Round10A
attribute [local instance] Classical.propDecidable
/-- Completes the local Gamma divisor premise: no extra poles or zeros
occur away from the nonpositive integers under a nonconstant affine map. -/
theorem gamma_affine_divisor (a b x : ℂ) (ha : a ≠ 0) :
    meromorphicOrderAt (fun z => Complex.Gamma (a * z + b)) x =
      if ∃ n : ℕ, a * x + b = -(n : ℂ) then -1 else 0 := by
  by_cases h : ∃ n : ℕ, a * x + b = -(n : ℂ)
  · rw [if_pos h]
    obtain ⟨n, hn⟩ := h
    exact gamma_affine_order a b x ha n hn
  · rw [if_neg h]
    have hn : ∀ n : ℕ, a * x + b ≠ -(n : ℂ) := by simpa only [not_exists] using h
    have hr : AnalyticAt ℂ (fun z : ℂ => (Complex.Gamma (a * z + b))⁻¹) x :=
      (Complex.differentiable_one_div_Gamma.comp
        (((differentiable_const a).mul differentiable_id).add_const b)).analyticAt x
    have hg : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma (a * z + b)) x := by
      have ht := hr.inv (inv_ne_zero (Complex.Gamma_ne_zero hn))
      change AnalyticAt ℂ (fun z : ℂ => ((Complex.Gamma (a * z + b))⁻¹)⁻¹) x at ht
      simpa only [inv_inv] using ht
    have he := meromorphicOrderAt_mul_of_ne_zero (f := fun _ : ℂ => (1 : ℂ))
      hg (Complex.Gamma_ne_zero hn)
    change meromorphicOrderAt (fun z => Complex.Gamma (a * z + b) * 1) x =
      meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) x at he
    simpa [meromorphicOrderAt_const] using he

/-- Real-place full local divisor, needed to exclude spurious completed zeros. -/
theorem gammaR_shift_divisor (c x : ℂ) :
    meromorphicOrderAt (fun z => Complex.Gammaℝ (z + c)) x =
      if ∃ n : ℕ, (x + c) / 2 = -(n : ℂ) then -1 else 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hu : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + c) / 2)) x :=
    (((differentiable_id.add_const c).neg.div_const 2).const_cpow (Or.inl hp)).analyticAt x
  have hn : (Real.pi : ℂ) ^ (-(x + c) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp)
  have he (z : ℂ) : (z + c) / 2 = (1 / 2 : ℂ) * z + c / 2 := by ring
  have hg := gamma_affine_divisor (1 / 2) (c / 2) x (by norm_num)
  have hm := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => Complex.Gamma ((z + c) / 2)) hu hn
  simp_rw [Complex.Gammaℝ_def]
  exact hm.trans (by simpa only [he] using hg)

/-- Complex-place full local divisor with the actual normalization. -/
theorem gammaC_shift_divisor (c x : ℂ) :
    meromorphicOrderAt (fun z => Complex.Gammaℂ (z + c)) x =
      if ∃ n : ℕ, x + c = -(n : ℂ) then -1 else 0 := by
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hu : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-(z + c))) x :=
    ((differentiable_const 2).mul
      ((differentiable_id.add_const c).neg.const_cpow (Or.inl hp))).analyticAt x
  have hn : 2 * (2 * (Real.pi : ℂ)) ^ (-(x + c)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl hp))
  have hg := gamma_affine_divisor 1 c x one_ne_zero
  have hm := meromorphicOrderAt_mul_of_ne_zero
    (f := fun z : ℂ => Complex.Gamma (z + c)) hu hn
  simp_rw [Complex.Gammaℂ_def]
  exact hm.trans (by simpa only [one_mul] using hg)

/-- Full finite archimedean divisor: every place contributes minus one
exactly at its actual Gamma pole, including mixed and coincident poles.
This discharges the archimedean multiplicity count, not Hecke continuation. -/
theorem archimedean_divisor_count {ι κ : Type*}
    (R : Finset ι) (C : Finset κ) (r : ι → ℂ) (c : κ → ℂ) (x : ℂ) :
    meromorphicOrderAt (fun z =>
      (∏ i ∈ R, Complex.Gammaℝ (z + r i)) *
      (∏ j ∈ C, Complex.Gammaℂ (z + c j))) x =
      (∑ i ∈ R, if ∃ n : ℕ, (x + r i) / 2 = -(n : ℂ) then (-1 : WithTop ℤ) else 0) +
      (∑ j ∈ C, if ∃ n : ℕ, x + c j = -(n : ℂ) then (-1 : WithTop ℤ) else 0) := by
  rw [archimedean_product_order]
  simp_rw [gammaR_shift_divisor, gammaC_shift_divisor]
#check gamma_affine_divisor
#print axioms gamma_affine_divisor
#check gammaR_shift_divisor
#print axioms gammaR_shift_divisor
#check gammaC_shift_divisor
#print axioms gammaC_shift_divisor
#check archimedean_divisor_count
#print axioms archimedean_divisor_count
end MasulloGRH.Round11A
