import Mathlib

/-! H195: the infinite rank-one series in the reviewed R W R factorization.
This is the requested trace-ideal interface, not the native spectral bound.
The two square-column estimates must be derived on the actual annihilator.
No nuclearity or rank-one summability is assumed. -/
noncomputable section
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
namespace Round195H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

/-- A concrete nuclear-series certificate with quantitative total cost. -/
def HasNuclearCost (T : E →L[ℂ] E) (C : ℝ) : Prop :=
  ∃ (v : ι → E) (f : ι → E →L[ℂ] ℂ),
    (∀ x, HasSum (fun i => f i x • v i) (T x)) ∧
    Summable (fun i => ‖f i‖ * ‖v i‖) ∧
    (∑' i, ‖f i‖ * ‖v i‖) ≤ C

/-- Square-column control yields the actual infinite R S expansion, with
S = W R in the reviewed native application. The cost is derived by Young's
inequality; no target rank-one summability is a premise. -/
theorem factorization_has_nuclear_cost
    (b : HilbertBasis ι ℂ E) (R S : E →L[ℂ] E)
    (hr : Summable (fun i => ‖R (b i)‖^2))
    (hs : Summable (fun i => ‖(innerSL ℂ (b i)).comp S‖^2)) :
    HasNuclearCost (ι := ι) (R.comp S)
      (((∑' i, ‖R (b i)‖^2) +
        (∑' i, ‖(innerSL ℂ (b i)).comp S‖^2))/2) := by
  let f : ι → E →L[ℂ] ℂ := fun i => (innerSL ℂ (b i)).comp S
  let v : ι → E := fun i => R (b i)
  have hm : Summable (fun i => (‖v i‖^2 + ‖f i‖^2)/2) :=
    (hr.add hs).div_const 2
  have hp (i : ι) : ‖f i‖ * ‖v i‖ ≤ (‖v i‖^2 + ‖f i‖^2)/2 := by
    nlinarith [sq_nonneg (‖v i‖ - ‖f i‖)]
  have hc : Summable (fun i => ‖f i‖ * ‖v i‖) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hp hm
  refine ⟨v, f, ?_, hc, ?_⟩
  · intro x
    have hh := R.hasSum (b.hasSum_repr (S x))
    simpa only [f, v, map_smul, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hh
  · calc
      _ ≤ ∑' i, (‖v i‖^2 + ‖f i‖^2)/2 := hc.tsum_le_tsum hp hm
      _ = _ := by rw [tsum_div_const, hr.tsum_add hs]

#check factorization_has_nuclear_cost
#print axioms factorization_has_nuclear_cost

/-- The exact infinite-series slot in the reviewed estimate. W is the
smoothed convolution; in the native application W commutes with R, so
R R W = R W R. Both hypotheses are finite energy estimates, not nuclear
summability. The native spectral/character bounds must discharge them. -/
theorem resolvent_factorization_nuclear_bound
    (b : HilbertBasis ι ℂ E) (R W : E →L[ℂ] E) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset ι, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (hrow : ∀ J : Finset ι, ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z) :
    HasNuclearCost (ι := ι) (R.comp (R.comp W)) (B*Z) := by
  let f : ι → E →L[ℂ] ℂ := fun i => ((innerSL ℂ (b i)).comp R).comp W
  let v : ι → E := fun i => R (b i)
  have hB : 0 ≤ B := (norm_nonneg W).trans hW
  have hp (i : ι) : ‖f i‖ * ‖v i‖ ≤
      B * ((‖R (b i)‖^2 + ‖(innerSL ℂ (b i)).comp R‖^2)/2) := by
    have hf : ‖f i‖ ≤ ‖(innerSL ℂ (b i)).comp R‖ * B := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hW (norm_nonneg _))
    have hh := mul_le_mul_of_nonneg_right hf (norm_nonneg (v i))
    have hy := sq_nonneg (‖R (b i)‖ - ‖(innerSL ℂ (b i)).comp R‖)
    have hz := mul_nonneg hB hy
    dsimp [v] at hh
    nlinarith
  have hfin (J : Finset ι) : ∑ i ∈ J, ‖f i‖ * ‖v i‖ ≤ B*Z := by
    calc
      _ ≤ ∑ i ∈ J, B * ((‖R (b i)‖^2 + ‖(innerSL ℂ (b i)).comp R‖^2)/2) :=
        Finset.sum_le_sum fun i _ => hp i
      _ = B * (((∑ i ∈ J, ‖R (b i)‖^2) +
          (∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2))/2) := by
        rw [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ B*Z := mul_le_mul_of_nonneg_left (by linarith [hcol J, hrow J]) hB
  have hc : Summable (fun i => ‖f i‖ * ‖v i‖) :=
    summable_of_sum_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hfin
  refine ⟨v, f, ?_, hc, ?_⟩
  · intro x
    have hh := R.hasSum (b.hasSum_repr (R (W x)))
    simpa only [v, f, map_smul, HilbertBasis.repr_apply_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hh
  · exact le_of_tendsto hc.hasSum (Filter.Eventually.of_forall hfin)

#check resolvent_factorization_nuclear_bound
#print axioms resolvent_factorization_nuclear_bound
end Round195H

namespace Round195H
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Nuclear norm defined by absolutely summable rank-one representations.
An arbitrary summation type is allowed; summability forces countable
nonzero cost. This is a definition, not an assumed trace-class interface. -/
def nuclearNorm (T : H →L[ℂ] H) : ENNReal :=
  sInf {c | ∃ (κ : Type u) (C : ℝ), HasNuclearCost (ι := κ) T C ∧
    c = ENNReal.ofReal C}

theorem nuclearNorm_le_of_cost {κ : Type u} {T : H →L[ℂ] H} {C : ℝ}
    (h : HasNuclearCost (ι := κ) T C) : nuclearNorm T ≤ ENNReal.ofReal C := by
  exact sInf_le ⟨κ, C, h, rfl⟩

/-- Quantitative norm form of the infinite assembly requested by A. All
native finite energy and identification obligations remain explicit. -/
theorem resolvent_nuclearNorm_le [CompleteSpace H]
    {κ : Type u} (b : HilbertBasis κ ℂ H) (R W : H →L[ℂ] H) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset κ, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (hrow : ∀ J : Finset κ, ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z) :
    nuclearNorm (R.comp (R.comp W)) ≤ ENNReal.ofReal (B*Z) :=
  nuclearNorm_le_of_cost (resolvent_factorization_nuclear_bound b R W B Z hW hcol hrow)

#check nuclearNorm
#check resolvent_nuclearNorm_le
#print axioms resolvent_nuclearNorm_le
end Round195H

namespace Round195H
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] {ι : Type*}

theorem basis_hasSum_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖^2) (‖x‖^2) := by
  have hh := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner x x)
  have he (i : ι) : (inner ℂ x (b i) * inner ℂ (b i) x).re =
      ‖inner ℂ (b i) x‖^2 := by
    rw [← inner_conj_symm (b i) x, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    rw [← Complex.sq_norm, norm_inner_symm]
    simp only [Complex.sq_norm]
    rw [inner_conj_symm]
  have hx : (inner ℂ x x).re = ‖x‖^2 := by
    rw [inner_self_eq_norm_sq_to_K]
    change (((‖x‖ : ℝ) : ℂ)^2).re = ‖x‖^2
    simp [pow_two]
  simpa only [Complex.reCLM_apply, he, hx] using hh

/-- The row estimate is discharged from the column estimate, rather than
passed back to the native spectral proof as an extra hypothesis. -/
theorem finite_rows_le_of_columns
    (b : HilbertBasis ι ℂ E) (R : E →L[ℂ] E) (Z : ℝ)
    (hcol : ∀ J : Finset ι, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z)
    (J : Finset ι) :
    ∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2 ≤ Z := by
  classical
  have hsum (i : ι) :
      HasSum (fun j => ‖inner ℂ (b i) (R (b j))‖^2)
        (‖(innerSL ℂ (b i)).comp R‖^2) := by
    have hh := basis_hasSum_sq b (R.adjoint (b i))
    simpa only [ContinuousLinearMap.innerSL_apply_comp, innerSL_apply_norm,
      ContinuousLinearMap.adjoint_inner_right, norm_inner_symm] using hh
  have hall : HasSum (fun j => ∑ i ∈ J, ‖inner ℂ (b i) (R (b j))‖^2)
      (∑ i ∈ J, ‖(innerSL ℂ (b i)).comp R‖^2) := by
    exact hasSum_sum fun i _ => hsum i
  apply le_of_tendsto hall
  apply Filter.Eventually.of_forall
  intro S
  calc
    _ ≤ ∑ j ∈ S, ‖R (b j)‖^2 := Finset.sum_le_sum fun j _ =>
      b.orthonormal.sum_inner_products_le (R (b j))
    _ ≤ Z := hcol S

#check finite_rows_le_of_columns
#print axioms finite_rows_le_of_columns
end Round195H

namespace Round195H
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_nuclearNorm_le_of_columns
    {κ : Type u} (b : HilbertBasis κ ℂ H) (R W : H →L[ℂ] H) (B Z : ℝ)
    (hW : ‖W‖ ≤ B)
    (hcol : ∀ J : Finset κ, ∑ i ∈ J, ‖R (b i)‖^2 ≤ Z) :
    nuclearNorm (R.comp (R.comp W)) ≤ ENNReal.ofReal (B*Z) := by
  exact resolvent_nuclearNorm_le b R W B Z hW hcol
    (finite_rows_le_of_columns b R Z hcol)

#check resolvent_nuclearNorm_le_of_columns
#print axioms resolvent_nuclearNorm_le_of_columns
end Round195H

/-! H196: the previously absent infinite character-block assembly slot.
The lattice is the concrete finite-level character coordinate lattice, not
an arbitrary enumeration. Its convergence is proved, never assumed. -/
namespace Round196H
open scoped BigOperators

def integerWeight (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ (-2 : ℝ)

theorem integerWeight_nonneg (n : ℤ) : 0 ≤ integerWeight n :=
  Real.rpow_nonneg (by positivity) _

theorem integerWeight_summable : Summable integerWeight := by
  have h : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 : ℝ)) := by
    have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hp
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor <;> simpa [integerWeight, abs_of_nonneg, add_comm] using h

def latticeWeight (d : ℕ) (k : Fin d → ℤ) : ℝ :=
  ∏ i, integerWeight (k i)

def latticeMass : ℝ := ∑' n : ℤ, integerWeight n

def latticeConsEquiv (d : ℕ) : (ℤ × (Fin d → ℤ)) ≃ (Fin (d+1) → ℤ) where
  toFun p := Fin.cons p.1 p.2
  invFun k := (k 0, fun i => k i.succ)
  left_inv := by intro p; simp
  right_inv := by
    intro k
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem latticeWeight_nonneg (d : ℕ) (k : Fin d → ℤ) :
    0 ≤ latticeWeight d k := Finset.prod_nonneg fun _ _ => integerWeight_nonneg _

theorem latticeWeight_hasSum (d : ℕ) :
    HasSum (latticeWeight d) (latticeMass ^ d) := by
  induction d with
  | zero =>
      letI : Unique (Fin 0 → ℤ) :=
        { default := fun i => Fin.elim0 i
          uniq := fun f => by funext i; exact Fin.elim0 i }
      simpa [latticeWeight] using (hasSum_fintype (latticeWeight 0))
  | succ d ih =>
      have hp := integerWeight_summable.mul_of_nonneg ih.summable
        integerWeight_nonneg (latticeWeight_nonneg d)
      have hh := integerWeight_summable.hasSum.mul ih hp
      apply (latticeConsEquiv d).hasSum_iff.mp
      simpa [Function.comp_def, latticeConsEquiv, latticeWeight,
        Fin.prod_univ_succ, latticeMass, pow_succ, mul_comm] using hh

/-- The full concrete F × Z^d majorant, including d=0. -/
theorem finite_level_character_majorant {F : Type*} [Fintype F] (d : ℕ) :
    HasSum (fun p : F × (Fin d → ℤ) => latticeWeight d p.2)
      ((Fintype.card F : ℝ) * latticeMass ^ d) := by
  have hf := hasSum_fintype (fun _ : F => (1 : ℝ))
  have hl := latticeWeight_hasSum d
  have hp := hf.summable.mul_of_nonneg hl.summable (by intro; norm_num)
    (latticeWeight_nonneg d)
  simpa using hf.mul hl hp

#check finite_level_character_majorant
#print axioms finite_level_character_majorant
end Round196H

namespace Round196H
open scoped BigOperators
universe u
set_option maxHeartbeats 500000

/-- Infinite character-block assembly with actual rank-one witnesses.
No nuclearity or global cost summability is a hypothesis. Both follow from
finite resolvent column estimates and a proved concrete lattice majorant.
The block identity hT must be supplied by the native character decomposition. -/
theorem finite_level_resolvent_nuclear_assembly
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {F : Type u} [Fintype F] (d : ℕ)
    (E : F × (Fin d → ℤ) → Type u)
    [∀ χ, NormedAddCommGroup (E χ)] [∀ χ, InnerProductSpace ℂ (E χ)]
    [∀ χ, CompleteSpace (E χ)]
    (κ : F × (Fin d → ℤ) → Type u)
    (b : ∀ χ, HilbertBasis (κ χ) ℂ (E χ))
    (R W : ∀ χ, E χ →L[ℂ] E χ)
    (inc : ∀ χ, E χ →L[ℂ] H) (pr : ∀ χ, H →L[ℂ] E χ)
    (hinc : ∀ χ, ‖inc χ‖ ≤ 1) (hpr : ∀ χ, ‖pr χ‖ ≤ 1)
    (B Z : F × (Fin d → ℤ) → ℝ)
    (hW : ∀ χ, ‖W χ‖ ≤ B χ)
    (hcol : ∀ χ (J : Finset (κ χ)), ∑ i ∈ J, ‖R χ (b χ i)‖^2 ≤ Z χ)
    (D : ℝ) (hcost : ∀ χ, B χ * Z χ ≤ D * latticeWeight d χ.2)
    (T : H →L[ℂ] H)
    (hT : ∀ x, HasSum (fun χ => inc χ (R χ (R χ (W χ (pr χ x))))) (T x)) :
    Round195H.nuclearNorm T ≤
      ENNReal.ofReal (D * ((Fintype.card F : ℝ) * latticeMass ^ d)) := by
  classical
  have hwit (χ : F × (Fin d → ℤ)) :=
    Round195H.resolvent_factorization_nuclear_bound (b χ) (R χ) (W χ)
      (B χ) (Z χ) (hW χ) (hcol χ)
      (Round195H.finite_rows_le_of_columns (b χ) (R χ) (Z χ) (hcol χ))
  choose v f hrep hs hb using hwit
  try clear_value v f
  let vv : (Σ χ, κ χ) → H := fun p => inc p.1 (v p.1 p.2)
  let ff : (Σ χ, κ χ) → H →L[ℂ] ℂ := fun p => (f p.1 p.2).comp (pr p.1)
  let cost : (Σ χ, κ χ) → ℝ := fun p => ‖ff p‖ * ‖vv p‖
  have hc0 (p : Σ χ, κ χ) : 0 ≤ cost p := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc_le (χ : F × (Fin d → ℤ)) (i : κ χ) :
      cost ⟨χ,i⟩ ≤ ‖f χ i‖ * ‖v χ i‖ := by
    have h1 : ‖(f χ i).comp (pr χ)‖ ≤ ‖f χ i‖ := by
      calc
        _ ≤ ‖f χ i‖ * ‖pr χ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖f χ i‖ * 1 := mul_le_mul_of_nonneg_left (hpr χ) (norm_nonneg _)
        _ = _ := mul_one _
    have h2 : ‖inc χ (v χ i)‖ ≤ ‖v χ i‖ := by
      calc
        _ ≤ ‖inc χ‖ * ‖v χ i‖ := (inc χ).le_opNorm _
        _ ≤ 1 * ‖v χ i‖ := mul_le_mul_of_nonneg_right (hinc χ) (norm_nonneg _)
        _ = _ := one_mul _
    exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
  have hcχ (χ : F × (Fin d → ℤ)) : Summable (fun i => cost ⟨χ,i⟩) :=
    Summable.of_nonneg_of_le (fun i => hc0 _) (hc_le χ) (hs χ)
  have hm := (finite_level_character_majorant (F := F) d).mul_left D
  have hbχ (χ : F × (Fin d → ℤ)) :
      (∑' i, cost ⟨χ,i⟩) ≤ D * latticeWeight d χ.2 :=
    ((hcχ χ).tsum_le_tsum (hc_le χ) (hs χ)).trans ((hb χ).trans (hcost χ))
  have hout : Summable (fun χ => ∑' i, cost ⟨χ,i⟩) :=
    Summable.of_nonneg_of_le (fun χ => tsum_nonneg fun i => hc0 _) hbχ hm.summable
  have hc : Summable cost := (summable_sigma_of_nonneg hc0).mpr ⟨hcχ, hout⟩
  apply Round195H.nuclearNorm_le_of_cost (κ := Σ χ, κ χ)
    (C := D * ((Fintype.card F : ℝ) * latticeMass ^ d))
  refine ⟨vv, ff, ?_, hc, ?_⟩
  · intro x
    have hn : Summable (fun p : Σ χ, κ χ => ‖ff p x • vv p‖) := by
      apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ (hc.mul_right ‖x‖)
      intro p
      rw [norm_smul]
      calc
        _ ≤ (‖ff p‖ * ‖x‖) * ‖vv p‖ :=
          mul_le_mul_of_nonneg_right ((ff p).le_opNorm x) (norm_nonneg _)
        _ = cost p * ‖x‖ := by dsimp only [cost]; ring
    apply (hT x).sigma_of_hasSum _ hn.of_norm
    intro χ
    have hh := (inc χ).hasSum (hrep χ (pr χ x))
    simpa only [ff, vv, ContinuousLinearMap.comp_apply, map_smul] using hh
  · calc
      _ = ∑' χ : F × (Fin d → ℤ), ∑' i : κ χ, cost ⟨χ,i⟩ := hc.tsum_sigma
      _ ≤ ∑' χ : F × (Fin d → ℤ), D * latticeWeight d χ.2 :=
        hout.tsum_le_tsum (g := fun χ : F × (Fin d → ℤ) => D * latticeWeight d χ.2) hbχ hm.summable
      _ = _ := hm.tsum_eq

#check finite_level_resolvent_nuclear_assembly
#print axioms finite_level_resolvent_nuclear_assembly
end Round196H
