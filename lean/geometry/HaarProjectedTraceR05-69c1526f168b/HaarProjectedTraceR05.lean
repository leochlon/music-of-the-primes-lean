-- ALPO analytic proofs ported to the allocated Mathlib API; see VERIFICATION.md.
import Mathlib

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

section Auxiliary

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

theorem ennreal_mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

end Auxiliary

section HilbertSchmidt

variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
  {L : Type*} [NormedAddCommGroup L] [InnerProductSpace 𝕜 L] [CompleteSpace L]

theorem enorm_inner_le (x y : H) : ‖⟪x, y⟫_𝕜‖ₑ ≤ ‖x‖ₑ * ‖y‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm x y)

theorem enorm_inner_comm (x y : H) : ‖⟪x, y⟫_𝕜‖ₑ = ‖⟪y, x⟫_𝕜‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_inner_symm]

theorem enorm_apply_le (A : H →L[𝕜] K) (x : H) : ‖A x‖ₑ ≤ ‖A‖ₑ * ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (A.le_opNorm x)

theorem enorm_sq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (x : H) :
    ‖x‖ₑ ^ 2 = ∑' i, ‖⟪b i, x⟫_𝕜‖ₑ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h1 := lp.norm_rpow_eq_tsum hp (b.repr x)
  have h2 := (lp.memℓp (b.repr x)).summable hp
  simp only [LinearIsometryEquiv.norm_map, HilbertBasis.repr_apply_apply, ENNReal.toReal_ofNat,
    Real.rpow_two] at h1 h2
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h2]
  congr 1
  ext i
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem tsum_enorm_sq_eq_adjoint {ι κ : Type*} (b : HilbertBasis ι 𝕜 H)
    (c : HilbertBasis κ 𝕜 K) (T : H →L[𝕜] K) :
    ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by
  calc ∑' i, ‖T (b i)‖ₑ ^ 2 = ∑' i, ∑' j, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := by
        congr 1; ext i; exact enorm_sq_eq_tsum c _
    _ = ∑' j, ∑' i, ‖⟪c j, T (b i)⟫_𝕜‖ₑ ^ 2 := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ‖⟪b i, (T†) (c j)⟫_𝕜‖ₑ ^ 2 := by
        congr 1; ext j; congr 1; ext i
        rw [← adjoint_inner_left, enorm_inner_comm]
    _ = ∑' j, ‖(T†) (c j)‖ₑ ^ 2 := by
        congr 1; ext j; exact (enorm_sq_eq_tsum b _).symm

variable (𝕜 H) in

def stdHilbertBasis : HilbertBasis (exists_hilbertBasis 𝕜 H).choose 𝕜 H :=
  (exists_hilbertBasis 𝕜 H).choose_spec.choose

def hsNormSq (T : H →L[𝕜] K) : ℝ≥0∞ := ∑' i, ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2

theorem hsNormSq_eq_tsum {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    hsNormSq T = ∑' i, ‖T (b i)‖ₑ ^ 2 := by
  rw [hsNormSq, tsum_enorm_sq_eq_adjoint _ (stdHilbertBasis 𝕜 K),
    tsum_enorm_sq_eq_adjoint b (stdHilbertBasis 𝕜 K)]

theorem hsNormSq_adjoint (T : H →L[𝕜] K) : hsNormSq (T†) = hsNormSq T := by
  rw [hsNormSq_eq_tsum (stdHilbertBasis 𝕜 K) (T†), hsNormSq,
    tsum_enorm_sq_eq_adjoint (stdHilbertBasis 𝕜 H) (stdHilbertBasis 𝕜 K)]

def IsHilbertSchmidt (T : H →L[𝕜] K) : Prop := hsNormSq T < ∞

theorem isHilbertSchmidt_iff {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) :
    IsHilbertSchmidt T ↔ ∑' i, ‖T (b i)‖ₑ ^ 2 < ∞ := by
  rw [IsHilbertSchmidt, hsNormSq_eq_tsum b]

theorem isHilbertSchmidt_adjoint_iff (T : H →L[𝕜] K) :
    IsHilbertSchmidt (T†) ↔ IsHilbertSchmidt T := by
  rw [IsHilbertSchmidt, IsHilbertSchmidt, hsNormSq_adjoint]

theorem IsHilbertSchmidt.adjoint {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (T†) :=
  (isHilbertSchmidt_adjoint_iff T).2 hT

def hsNorm (T : H →L[𝕜] K) : ℝ := √(hsNormSq T).toReal

theorem hsNorm_nonneg (T : H →L[𝕜] K) : 0 ≤ hsNorm T := Real.sqrt_nonneg _

theorem hsNorm_sq (T : H →L[𝕜] K) : hsNorm T ^ 2 = (hsNormSq T).toReal :=
  Real.sq_sqrt ENNReal.toReal_nonneg

theorem hsNorm_adjoint (T : H →L[𝕜] K) : hsNorm (T†) = hsNorm T := by
  rw [hsNorm, hsNorm, hsNormSq_adjoint]

theorem enorm_apply_sq_le (T : H →L[𝕜] K) (x : H) :
    ‖T x‖ₑ ^ 2 ≤ hsNormSq T * ‖x‖ₑ ^ 2 := by
  let c := stdHilbertBasis 𝕜 K
  rw [← hsNormSq_adjoint, hsNormSq_eq_tsum c, enorm_sq_eq_tsum c, ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun j => ?_
  rw [← adjoint_inner_left, ← mul_pow]
  gcongr
  exact enorm_inner_le _ _

theorem norm_le_hsNorm {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) : ‖T‖ ≤ hsNorm T := by
  refine T.opNorm_le_bound (hsNorm_nonneg T) fun x => ?_
  have h := enorm_apply_sq_le T x
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_toReal hT.ne,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [← Real.sqrt_sq (norm_nonneg (T x)), hsNorm, ← Real.sqrt_sq (norm_nonneg x),
    ← Real.sqrt_mul ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h

theorem hsNormSq_zero : hsNormSq (0 : H →L[𝕜] K) = 0 := by
  simp [hsNormSq]

theorem hsNormSq_smul (c : 𝕜) (T : H →L[𝕜] K) : hsNormSq (c • T) = ‖c‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, smul_apply, enorm_smul, mul_pow, ENNReal.tsum_mul_left]

theorem hsNormSq_add_le (S T : H →L[𝕜] K) :
    hsNormSq (S + T) ≤ 2 * hsNormSq S + 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  calc ‖(S + T) _‖ₑ ^ 2 ≤ (‖S _‖ₑ + ‖T _‖ₑ) ^ 2 := by
        gcongr; exact enorm_add_le _ _
    _ ≤ _ := ennreal_add_sq_le _ _

theorem hsNormSq_comp_left_le (A : K →L[𝕜] L) (T : H →L[𝕜] K) :
    hsNormSq (A.comp T) ≤ ‖A‖ₑ ^ 2 * hsNormSq T := by
  simp only [hsNormSq, ← ENNReal.tsum_mul_left, comp_apply]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← mul_pow]
  gcongr
  exact enorm_apply_le _ _

theorem hsNormSq_comp_right_le (T : K →L[𝕜] L) (B : H →L[𝕜] K) :
    hsNormSq (T.comp B) ≤ ‖B‖ₑ ^ 2 * hsNormSq T := by
  rw [← hsNormSq_adjoint, adjoint_comp, ← hsNormSq_adjoint T]
  calc hsNormSq ((B†).comp (T†)) ≤ ‖B†‖ₑ ^ 2 * hsNormSq (T†) := hsNormSq_comp_left_le _ _
    _ = ‖B‖ₑ ^ 2 * hsNormSq (T†) := by
        rw [← ofReal_norm, ← ofReal_norm, adjoint.norm_map]

theorem IsHilbertSchmidt.comp_left {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (A : K →L[𝕜] L) :
    IsHilbertSchmidt (A.comp T) :=
  (hsNormSq_comp_left_le A T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsHilbertSchmidt.comp_right {T : K →L[𝕜] L} (hT : IsHilbertSchmidt T) (B : H →L[𝕜] K) :
    IsHilbertSchmidt (T.comp B) :=
  (hsNormSq_comp_right_le T B).trans_lt (ENNReal.mul_lt_top (by simp) hT)

variable (𝕜 H K) in

def hilbertSchmidt : Submodule 𝕜 (H →L[𝕜] K) where
  carrier := {T | IsHilbertSchmidt T}
  add_mem' {S T} hS hT := by
    refine (hsNormSq_add_le S T).trans_lt ?_
    exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hS, ENNReal.mul_lt_top (by simp) hT⟩
  zero_mem' := by
    show hsNormSq (0 : H →L[𝕜] K) < ∞
    simp [hsNormSq_zero]
  smul_mem' c T hT := by
    show hsNormSq (c • T) < ∞
    rw [hsNormSq_smul]
    exact ENNReal.mul_lt_top (by simp) hT

theorem IsHilbertSchmidt.add {S T : H →L[𝕜] K} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) :=
  (hilbertSchmidt 𝕜 H K).add_mem hS hT

theorem IsHilbertSchmidt.smul {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) (c : 𝕜) :
    IsHilbertSchmidt (c • T) :=
  (hilbertSchmidt 𝕜 H K).smul_mem c hT

theorem IsHilbertSchmidt.hasSum_norm_sq {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) {ι : Type*}
    (b : HilbertBasis ι 𝕜 H) : HasSum (fun i => ‖T (b i)‖ ^ 2) (hsNorm T ^ 2) := by
  have hfin : ∑' i, ‖T (b i)‖ₑ ^ 2 ≠ ∞ := by rw [← hsNormSq_eq_tsum b]; exact hT.ne
  have hs := ENNReal.summable_toReal hfin
  rw [hsNorm_sq, hsNormSq_eq_tsum b, ENNReal.tsum_toReal_eq fun i => by simp]
  convert hs.hasSum using 2

theorem hasSum_inner_comp_comm {ι κ : Type*} (e : HilbertBasis ι 𝕜 H) (f : HilbertBasis κ 𝕜 K)
    {A : K →L[𝕜] H} {B : H →L[𝕜] K} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    HasSum (fun i => ⟪e i, A (B (e i))⟫_𝕜) (∑' j, ⟪f j, B (A (f j))⟫_𝕜) := by
  let F : ι → κ → 𝕜 := fun i j => ⟪(B†) (f j), e i⟫_𝕜 * ⟪e i, A (f j)⟫_𝕜

  have hfin : ∑' p : ι × κ, ‖Function.uncurry F p‖ₑ ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' p : ι × κ,
      (‖⟪e p.1, (B†) (f p.2)⟫_𝕜‖ₑ ^ 2 + ‖⟪e p.1, A (f p.2)⟫_𝕜‖ₑ ^ 2)) ?_ ?_
    · rw [ENNReal.tsum_add, ENNReal.tsum_prod', ENNReal.tsum_prod', ENNReal.tsum_comm,
        ENNReal.tsum_comm (f := fun i j => ‖⟪e i, A (f j)⟫_𝕜‖ₑ ^ 2)]
      simp only [← enorm_sq_eq_tsum e, ← hsNormSq_eq_tsum f]
      exact ENNReal.add_ne_top.2 ⟨(hB.adjoint).ne, hA.ne⟩
    · refine ENNReal.tsum_le_tsum fun p => ?_
      simp only [Function.uncurry, F, enorm_mul]
      rw [enorm_inner_comm ((B†) (f p.2))]
      exact ennreal_mul_le_sq_add_sq _ _
  have hF : Summable (Function.uncurry F) := by
    refine Summable.of_norm ?_
    convert ENNReal.summable_toReal hfin using 2
  have h1 : ∀ i, ∑' j, F i j = ⟪e i, A (B (e i))⟫_𝕜 := by
    intro i
    rw [← adjoint_inner_left A]
    refine ((f.hasSum_inner_mul_inner ((A†) (e i)) (B (e i))).congr_fun fun j => ?_).tsum_eq
    simp only [F]
    rw [adjoint_inner_left, adjoint_inner_left, mul_comm]
  have h2 : ∀ j, ∑' i, F i j = ⟪f j, B (A (f j))⟫_𝕜 := by
    intro j
    rw [← adjoint_inner_left B]
    exact (e.hasSum_inner_mul_inner ((B†) (f j)) (A (f j))).tsum_eq
  have hsum := hF.prod
  simp only [Function.uncurry_apply_pair] at hsum
  have hval : ∑' j, ⟪f j, B (A (f j))⟫_𝕜 = ∑' i, ∑' j, F i j := by
    simp_rw [← h2]
    exact hF.tsum_comm
  rw [hval, show (fun i => ⟪e i, A (B (e i))⟫_𝕜) = fun i => ∑' j, F i j from
    funext fun i => (h1 i).symm]
  exact hsum.hasSum

end HilbertSchmidt

end

end GroundTheory.Automorphic


namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

theorem ennreal_two_mul_le_sq_add_sq (a b : ℝ≥0∞) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  rcases eq_or_ne b ∞ with rfl | hb
  · simp
  lift a to NNReal using ha
  lift b to NNReal using hb
  norm_cast
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [sq_nonneg ((a : ℝ) - b)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Abs

theorem isSelfAdjoint_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : IsSelfAdjoint A :=
  ((nonneg_iff_isPositive A).1 hA).isSelfAdjoint

theorem adjoint_eq_of_nonneg {A : H →L[ℂ] H} (hA : 0 ≤ A) : A† = A :=
  (isSelfAdjoint_of_nonneg hA).adjoint_eq

theorem inner_apply_eq_norm_sqrt_sq {A : H →L[ℂ] H} (hA : 0 ≤ A) (x : H) :
    ⟪x, A x⟫_ℂ = ((‖CFC.sqrt A x‖ ^ 2 : ℝ) : ℂ) := by
  have hs : (CFC.sqrt A)† = CFC.sqrt A := adjoint_eq_of_nonneg (CFC.sqrt_nonneg A)
  have hA' : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA).symm
  conv_lhs => rw [hA', mul_def, comp_apply, ← hs, adjoint_inner_right, hs]
  rw [inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

theorem norm_abs_apply (T : H →L[ℂ] H) (x : H) : ‖CFC.abs T x‖ = ‖T x‖ := by
  have hR : (CFC.abs T)† = CFC.abs T := adjoint_eq_of_nonneg (CFC.abs_nonneg T)
  have h : ‖CFC.abs T x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    congr 1
    conv_lhs => rw [← adjoint_inner_right (CFC.abs T), hR, ← comp_apply, ← mul_def,
      CFC.abs_mul_abs, star_eq_adjoint, mul_def, comp_apply, adjoint_inner_right]
  have := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

theorem exists_polar (T : H →L[ℂ] H) :
    ∃ V : H →L[ℂ] H, ‖V‖ ≤ 1 ∧ V.comp (CFC.abs T) = T ∧ (V†).comp T = CFC.abs T := by
  set R := CFC.abs T with hRdef
  set M : Submodule ℂ H := (LinearMap.range R.toLinearMap).topologicalClosure with hM
  have : CompleteSpace M := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  let e : H →ₗ[ℂ] M := R.toLinearMap.codRestrict M
    (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))
  have he : ∀ x, (e x : H) = R x := fun x => rfl
  have hdense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
    intro y hy
    change y ∈ ((LinearMap.range R.toLinearMap).topologicalClosure : Set H) at hy
    rw [Submodule.topologicalClosure_coe, LinearMap.coe_range] at hy
    exact hy
  have hnorm : ∀ x, ‖T.toLinearMap x‖ ≤ 1 * ‖e x‖ := by
    intro x
    rw [one_mul, Submodule.coe_norm, he, norm_abs_apply]
    rfl
  let W : M →L[ℂ] H := T.toLinearMap.extendOfNorm e
  have hW : ∀ x, W (e x) = T x := fun x => LinearMap.extendOfNorm_eq hdense ⟨1, hnorm⟩ x
  have hWiso : ∀ m, ‖W m‖ = ‖m‖ := by
    intro m
    refine hdense.induction_on m (isClosed_eq W.continuous.norm continuous_norm) fun x => ?_
    rw [hW, Submodule.coe_norm, he, norm_abs_apply]
  let Wi : M →ₗᵢ[ℂ] H := { W.toLinearMap with norm_map' := hWiso }
  have hWinner : ∀ m m' : M, ⟪W m, W m'⟫_ℂ = ⟪m, m'⟫_ℂ := fun m m' => Wi.inner_map_map m m'
  refine ⟨W.comp M.orthogonalProjection, ?_, ?_, ?_⟩
  · refine (opNorm_comp_le _ _).trans ?_
    have h1 : ‖W‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun m => by rw [hWiso, one_mul]
    calc ‖W‖ * ‖M.orthogonalProjection‖ ≤ 1 * 1 := by
          gcongr
          exact Submodule.orthogonalProjection_norm_le M
      _ = 1 := one_mul 1
  · ext x
    show W (M.orthogonalProjection ((e x : M) : H)) = T x
    rw [Submodule.orthogonalProjection_mem_subspace_eq_self, hW]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [comp_apply, adjoint_inner_left, comp_apply, ← hW x, hWinner,
      Submodule.inner_orthogonalProjection_eq_of_mem_left, he]

end Abs

section TraceNorm

def traceNorm (T : H →L[ℂ] H) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re
    ⟪stdHilbertBasis ℂ H i, CFC.abs T (stdHilbertBasis ℂ H i)⟫_ℂ)

theorem ofReal_re_inner_abs (T : H →L[ℂ] H) (x : H) :
    ENNReal.ofReal (RCLike.re ⟪x, CFC.abs T x⟫_ℂ) = ‖CFC.sqrt (CFC.abs T) x‖ₑ ^ 2 := by
  rw [inner_apply_eq_norm_sqrt_sq (CFC.abs_nonneg T), RCLike.re_to_complex, Complex.ofReal_re,
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem traceNorm_eq_hsNormSq (T : H →L[ℂ] H) :
    traceNorm T = hsNormSq (CFC.sqrt (CFC.abs T)) := by
  simp only [traceNorm, ofReal_re_inner_abs]
  rfl

theorem traceNorm_eq_tsum {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    traceNorm T = ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, CFC.abs T (b i)⟫_ℂ) := by
  simp only [traceNorm_eq_hsNormSq, ofReal_re_inner_abs, hsNormSq_eq_tsum b]

def IsTraceClass (T : H →L[ℂ] H) : Prop := traceNorm T < ∞

theorem isTraceClass_iff_isHilbertSchmidt_sqrt (T : H →L[ℂ] H) :
    IsTraceClass T ↔ IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) := by
  rw [IsTraceClass, traceNorm_eq_hsNormSq, IsHilbertSchmidt]

theorem traceNorm_le_of_adjoint_comp {ι : Type*} (b : HilbertBasis ι ℂ H) {T V : H →L[ℂ] H}
    (hV : (V†).comp T = CFC.abs T) : traceNorm T ≤ ∑' i, ‖⟪V (b i), T (b i)⟫_ℂ‖ₑ := by
  rw [traceNorm_eq_tsum b]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← hV, comp_apply, adjoint_inner_right, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (RCLike.re_le_norm _)

theorem enorm_le_one_of_norm_le_one {A : H →L[ℂ] H} (hA : ‖A‖ ≤ 1) : ‖A‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 hA

theorem tsum_enorm_inner_le_traceNorm {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    {U W : H →L[ℂ] H} (hU : ‖U‖ ≤ 1) (hW : ‖W‖ ≤ 1) :
    ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ traceNorm T := by
  obtain ⟨V, hV1, hVT, -⟩ := exists_polar T
  set s := CFC.sqrt (CFC.abs T) with hsdef
  have hs : s† = s := adjoint_eq_of_nonneg (CFC.sqrt_nonneg _)
  have hss : s.comp s = CFC.abs T := CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
  have hpt : ∀ x y, ⟪U x, T (W y)⟫_ℂ = ⟪s ((V†) (U x)), s (W y)⟫_ℂ := by
    intro x y
    conv_lhs => rw [← hVT, ← hss, comp_apply, comp_apply, ← adjoint_inner_left V,
      ← hs, adjoint_inner_right, hs]
  have hVU : ‖(V†).comp U‖ ≤ 1 := by
    refine (opNorm_comp_le _ _).trans ?_
    rw [adjoint.norm_map]
    calc ‖V‖ * ‖U‖ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have key : 2 * ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ 2 * traceNorm T := by
    calc 2 * ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ
        ≤ ∑' i, (‖s ((V†) (U (b i)))‖ₑ ^ 2 + ‖s (W (b i))‖ₑ ^ 2) := by
          rw [← ENNReal.tsum_mul_left]
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [hpt]
          calc 2 * ‖⟪s ((V†) (U (b i))), s (W (b i))⟫_ℂ‖ₑ
              ≤ 2 * (‖s ((V†) (U (b i)))‖ₑ * ‖s (W (b i))‖ₑ) := by
                gcongr; exact enorm_inner_le _ _
            _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
      _ = hsNormSq (s.comp ((V†).comp U)) + hsNormSq (s.comp W) := by
          rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
          rfl
      _ ≤ ‖(V†).comp U‖ₑ ^ 2 * hsNormSq s + ‖W‖ₑ ^ 2 * hsNormSq s :=
          add_le_add (hsNormSq_comp_right_le _ _) (hsNormSq_comp_right_le _ _)
      _ ≤ 1 ^ 2 * hsNormSq s + 1 ^ 2 * hsNormSq s := by
          gcongr
          · exact enorm_le_one_of_norm_le_one hVU
          · exact enorm_le_one_of_norm_le_one hW
      _ = 2 * traceNorm T := by rw [traceNorm_eq_hsNormSq, one_pow, one_mul, two_mul]
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 key

end TraceNorm

section Ideal

theorem norm_id_le_one : ‖ContinuousLinearMap.id ℂ H‖ ≤ 1 := norm_id_le

theorem tsum_enorm_inner_le {ι : Type*} (b : HilbertBasis ι ℂ H) (T U W : H →L[ℂ] H) :
    ∑' i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ ≤ ‖U‖ₑ * ‖W‖ₑ * traceNorm T := by
  rcases eq_or_ne U 0 with rfl | hU
  · simp
  rcases eq_or_ne W 0 with rfl | hW
  · simp
  have hu : 0 < ‖U‖ := norm_pos_iff.2 hU
  have hw : 0 < ‖W‖ := norm_pos_iff.2 hW
  set U₀ : H →L[ℂ] H := ((‖U‖⁻¹ : ℝ) : ℂ) • U with hU₀def
  set W₀ : H →L[ℂ] H := ((‖W‖⁻¹ : ℝ) : ℂ) • W with hW₀def
  have hU₀ : ‖U₀‖ ≤ 1 := by
    rw [hU₀def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hu.ne']
  have hW₀ : ‖W₀‖ ≤ 1 := by
    rw [hW₀def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hw.ne']
  have hUx : ∀ x, U x = ((‖U‖ : ℝ) : ℂ) • U₀ x := fun x => by
    rw [hU₀def, smul_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne',
      Complex.ofReal_one, one_smul]
  have hWx : ∀ x, W x = ((‖W‖ : ℝ) : ℂ) • W₀ x := fun x => by
    rw [hW₀def, smul_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne',
      Complex.ofReal_one, one_smul]
  have hpt : ∀ i, ‖⟪U (b i), T (W (b i))⟫_ℂ‖ₑ =
      ‖U‖ₑ * ‖W‖ₑ * ‖⟪U₀ (b i), T (W₀ (b i))⟫_ℂ‖ₑ := by
    intro i
    have h : ⟪U (b i), T (W (b i))⟫_ℂ =
        ((‖U‖ * ‖W‖ : ℝ) : ℂ) * ⟪U₀ (b i), T (W₀ (b i))⟫_ℂ := by
      rw [hUx, hWx, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
        Complex.ofReal_mul, mul_assoc]
    rw [h, enorm_mul]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
  simp_rw [hpt, ENNReal.tsum_mul_left]
  gcongr
  exact tsum_enorm_inner_le_traceNorm b T hU₀ hW₀

theorem traceNorm_zero : traceNorm (0 : H →L[ℂ] H) = 0 := by
  simp [traceNorm]

theorem traceNorm_add_le (S T : H →L[ℂ] H) : traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (S + T)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc traceNorm (S + T) ≤ ∑' i, ‖⟪V (b i), (S + T) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖⟪V (b i), S (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ +
          ‖⟪V (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [add_apply, inner_add_right, id_apply]
        exact enorm_add_le _ _
    _ = _ := ENNReal.tsum_add
    _ ≤ ‖V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm S +
          ‖V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T :=
        add_le_add (tsum_enorm_inner_le b S _ _) (tsum_enorm_inner_le b T _ _)
    _ ≤ 1 * 1 * traceNorm S + 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm S + traceNorm T := by simp only [one_mul]

theorem traceNorm_comp_left_le (C T : H →L[ℂ] H) : traceNorm (C.comp T) ≤ ‖C‖ₑ * traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (C.comp T)
  let b := stdHilbertBasis ℂ H
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  have hCV : ‖(C†).comp V‖ₑ ≤ ‖C‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((opNorm_comp_le _ _).trans ?_)
    rw [adjoint.norm_map]
    calc ‖C‖ * ‖V‖ ≤ ‖C‖ * 1 := by gcongr
      _ = ‖C‖ := mul_one _
  calc traceNorm (C.comp T) ≤ ∑' i, ‖⟪V (b i), (C.comp T) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪((C†).comp V) (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ := by
        congr 1; ext i
        rw [comp_apply, comp_apply, adjoint_inner_left, id_apply]
    _ ≤ ‖(C†).comp V‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ ‖C‖ₑ * 1 * traceNorm T := by gcongr
    _ = ‖C‖ₑ * traceNorm T := by rw [mul_one]

theorem traceNorm_comp_right_le (T C : H →L[ℂ] H) :
    traceNorm (T.comp C) ≤ ‖C‖ₑ * traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (T.comp C)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc traceNorm (T.comp C) ≤ ∑' i, ‖⟪V (b i), (T.comp C) (b i)⟫_ℂ‖ₑ :=
        traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪V (b i), T (C (b i))⟫_ℂ‖ₑ := rfl
    _ ≤ ‖V‖ₑ * ‖C‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ 1 * ‖C‖ₑ * traceNorm T := by gcongr
    _ = ‖C‖ₑ * traceNorm T := by rw [one_mul]

theorem traceNorm_adjoint_le (T : H →L[ℂ] H) : traceNorm (T†) ≤ traceNorm T := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (T†)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc traceNorm (T†) ≤ ∑' i, ‖⟪V (b i), (T†) (b i)⟫_ℂ‖ₑ := traceNorm_le_of_adjoint_comp b hV
    _ = ∑' i, ‖⟪ContinuousLinearMap.id ℂ H (b i), T (V (b i))⟫_ℂ‖ₑ := by
        congr 1; ext i
        rw [adjoint_inner_right, enorm_inner_comm, id_apply]
    _ ≤ ‖ContinuousLinearMap.id ℂ H‖ₑ * ‖V‖ₑ * traceNorm T := tsum_enorm_inner_le b T _ _
    _ ≤ 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm T := by simp only [one_mul]

theorem traceNorm_adjoint (T : H →L[ℂ] H) : traceNorm (T†) = traceNorm T :=
  le_antisymm (traceNorm_adjoint_le T) (by simpa using traceNorm_adjoint_le (T†))

theorem traceNorm_smul_le (c : ℂ) (T : H →L[ℂ] H) : traceNorm (c • T) ≤ ‖c‖ₑ * traceNorm T := by
  have h : c • T = (c • ContinuousLinearMap.id ℂ H).comp T := by ext x; simp
  rw [h]
  refine (traceNorm_comp_left_le _ _).trans ?_
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ((norm_smul_le _ _).trans ?_)
  calc ‖c‖ * ‖ContinuousLinearMap.id ℂ H‖ ≤ ‖c‖ * 1 := by gcongr; exact norm_id_le_one
    _ = ‖c‖ := mul_one _

theorem isTraceClass_iff (T : H →L[ℂ] H) : IsTraceClass T ↔ traceNorm T < ∞ := Iff.rfl

theorem IsTraceClass.add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) :=
  (traceNorm_add_le S T).trans_lt (ENNReal.add_lt_top.2 ⟨hS, hT⟩)

theorem IsTraceClass.smul {T : H →L[ℂ] H} (hT : IsTraceClass T) (c : ℂ) :
    IsTraceClass (c • T) :=
  (traceNorm_smul_le c T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsTraceClass.comp_left {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    IsTraceClass (C.comp T) :=
  (traceNorm_comp_left_le C T).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    IsTraceClass (T.comp C) :=
  (traceNorm_comp_right_le T C).trans_lt (ENNReal.mul_lt_top (by simp) hT)

theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) : IsTraceClass (T†) := by
  rw [IsTraceClass, traceNorm_adjoint]; exact hT

variable (H) in

def traceClass : Submodule ℂ (H →L[ℂ] H) where
  carrier := {T | IsTraceClass T}
  add_mem' hS hT := hS.add hT
  zero_mem' := by
    show traceNorm (0 : H →L[ℂ] H) < ∞
    rw [traceNorm_zero]; exact ENNReal.zero_lt_top
  smul_mem' c _ hT := hT.smul c

theorem two_mul_traceNorm_comp_le (A B : H →L[ℂ] H) :
    2 * traceNorm (A.comp B) ≤ hsNormSq A + hsNormSq B := by
  obtain ⟨V, hV1, -, hV⟩ := exists_polar (A.comp B)
  let b := stdHilbertBasis ℂ H
  have hV1' : ‖V‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one hV1
  calc 2 * traceNorm (A.comp B) ≤ 2 * ∑' i, ‖⟪V (b i), A (B (b i))⟫_ℂ‖ₑ := by
        gcongr; exact traceNorm_le_of_adjoint_comp b hV
    _ ≤ ∑' i, (‖((A†).comp V) (b i)‖ₑ ^ 2 + ‖B (b i)‖ₑ ^ 2) := by
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun i => ?_
        rw [← adjoint_inner_left, ← comp_apply (A†) V]
        calc 2 * ‖⟪((A†).comp V) (b i), B (b i)⟫_ℂ‖ₑ
            ≤ 2 * (‖((A†).comp V) (b i)‖ₑ * ‖B (b i)‖ₑ) := by gcongr; exact enorm_inner_le _ _
          _ ≤ _ := ennreal_two_mul_le_sq_add_sq _ _
    _ = hsNormSq ((A†).comp V) + hsNormSq B := by
        rw [ENNReal.tsum_add, hsNormSq_eq_tsum b, hsNormSq_eq_tsum b]
    _ ≤ ‖V‖ₑ ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr; exact hsNormSq_comp_right_le _ _
    _ ≤ 1 ^ 2 * hsNormSq (A†) + hsNormSq B := by gcongr
    _ = hsNormSq A + hsNormSq B := by rw [one_pow, one_mul, hsNormSq_adjoint]

theorem isTraceClass_comp {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B) :
    IsTraceClass (A.comp B) := by
  have h := (two_mul_traceNorm_comp_le A B).trans_lt (ENNReal.add_lt_top.2 ⟨hA, hB⟩)
  rw [IsTraceClass]
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.mul_top two_ne_zero] at h
  exact lt_irrefl _ h

theorem IsTraceClass.exists_comp {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    ∃ A B : H →L[ℂ] H, IsHilbertSchmidt A ∧ IsHilbertSchmidt B ∧ T = A.comp B := by
  obtain ⟨V, -, hVT, -⟩ := exists_polar T
  have hs : IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) :=
    (isTraceClass_iff_isHilbertSchmidt_sqrt T).1 hT
  refine ⟨V.comp (CFC.sqrt (CFC.abs T)), CFC.sqrt (CFC.abs T), hs.comp_left V, hs, ?_⟩
  have hss : (CFC.sqrt (CFC.abs T)).comp (CFC.sqrt (CFC.abs T)) = CFC.abs T :=
    CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
  rw [comp_assoc, hss, hVT]

end Ideal

section Trace

def trace (T : H →L[ℂ] H) : ℂ :=
  ∑' i, ⟪stdHilbertBasis ℂ H i, T (stdHilbertBasis ℂ H i)⟫_ℂ

theorem trace_comp_comm_of_isHilbertSchmidt {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : trace (A.comp B) = trace (B.comp A) :=
  (hasSum_inner_comp_comm (stdHilbertBasis ℂ H) (stdHilbertBasis ℂ H) hA hB).tsum_eq

theorem IsTraceClass.hasSum_trace {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (trace T) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  have h1 := hasSum_inner_comp_comm b (stdHilbertBasis ℂ H) hA hB
  rw [trace_comp_comm_of_isHilbertSchmidt hA hB]
  exact h1

theorem tsum_enorm_inner_self_le {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H) :
    ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ ≤ traceNorm T := by
  have hI : ‖ContinuousLinearMap.id ℂ H‖ₑ ≤ 1 := enorm_le_one_of_norm_le_one norm_id_le_one
  calc ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ
      = ∑' i, ‖⟪ContinuousLinearMap.id ℂ H (b i), T (ContinuousLinearMap.id ℂ H (b i))⟫_ℂ‖ₑ :=
        rfl
    _ ≤ ‖ContinuousLinearMap.id ℂ H‖ₑ * ‖ContinuousLinearMap.id ℂ H‖ₑ * traceNorm T :=
        tsum_enorm_inner_le b T _ _
    _ ≤ 1 * 1 * traceNorm T := by gcongr
    _ = traceNorm T := by simp only [one_mul]

theorem IsTraceClass.summable_norm_inner {T : H →L[ℂ] H} (hT : IsTraceClass T) {ι : Type*}
    (b : HilbertBasis ι ℂ H) : Summable fun i => ‖⟪b i, T (b i)⟫_ℂ‖ := by
  have h := ENNReal.summable_toReal ((tsum_enorm_inner_self_le b T).trans_lt hT).ne
  simpa using h

theorem enorm_trace_le (T : H →L[ℂ] H) : ‖trace T‖ₑ ≤ traceNorm T := by
  by_cases hT : IsTraceClass T
  · let b := stdHilbertBasis ℂ H
    have hs := hT.summable_norm_inner b
    calc ‖trace T‖ₑ = ENNReal.ofReal ‖trace T‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (∑' i, ‖⟪b i, T (b i)⟫_ℂ‖) :=
          ENNReal.ofReal_le_ofReal ((hT.hasSum_trace b).norm_le_of_bounded hs.hasSum fun _ => le_rfl)
      _ = ∑' i, ‖⟪b i, T (b i)⟫_ℂ‖ₑ := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
          simp only [ofReal_norm]
      _ ≤ traceNorm T := tsum_enorm_inner_self_le b T
  · rw [IsTraceClass, not_lt, top_le_iff] at hT
    rw [hT]; exact le_top

theorem trace_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by
  let b := stdHilbertBasis ℂ H
  refine ((hS.add hT).hasSum_trace b).unique ?_
  convert (hS.hasSum_trace b).add (hT.hasSum_trace b) using 1
  ext i
  rw [add_apply, inner_add_right]

theorem trace_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (c • T) = c * trace T := by
  let b := stdHilbertBasis ℂ H
  refine ((hT.smul c).hasSum_trace b).unique ?_
  have hfun : (fun i => ⟪b i, (c • T) (b i)⟫_ℂ) = fun i => c * ⟪b i, T (b i)⟫_ℂ := by
    ext i; rw [smul_apply, inner_smul_right]
  rw [hfun]
  exact (hT.hasSum_trace b).mul_left c

theorem trace_comp_comm {T : H →L[ℂ] H} (hT : IsTraceClass T) (C : H →L[ℂ] H) :
    trace (C.comp T) = trace (T.comp C) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  calc trace (C.comp (A.comp B)) = trace ((C.comp A).comp B) := by rw [comp_assoc]
    _ = trace (B.comp (C.comp A)) := trace_comp_comm_of_isHilbertSchmidt (hA.comp_left C) hB
    _ = trace ((B.comp C).comp A) := by rw [comp_assoc]
    _ = trace (A.comp (B.comp C)) := trace_comp_comm_of_isHilbertSchmidt (hB.comp_right C) hA
    _ = trace ((A.comp B).comp C) := by rw [comp_assoc]

theorem trace_adjoint {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    trace (T†) = starRingEnd ℂ (trace T) := by
  let b := stdHilbertBasis ℂ H
  refine (hT.adjoint.hasSum_trace b).unique ?_
  have hfun : (fun i => ⟪b i, (T†) (b i)⟫_ℂ) = fun i => star ⟪b i, T (b i)⟫_ℂ := by
    ext i; rw [adjoint_inner_right, ← inner_conj_symm]; rfl
  rw [hfun, starRingEnd_apply]
  exact (hT.hasSum_trace b).star

end Trace

end

end GroundTheory.Automorphic

#print axioms GroundTheory.Automorphic.isTraceClass_comp
#print axioms GroundTheory.Automorphic.trace_comp_comm


noncomputable section
namespace GeometricTraceR03
open GroundTheory.Automorphic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (V : Submodule ℂ H) [CompleteSpace V]

/-- Extending a trace-class operator by zero along the genuine orthogonal projection. -/
theorem extension_isTraceClass {T : V →L[ℂ] V} (hT : IsTraceClass T) :
    IsTraceClass (V.subtypeL.comp (T.comp V.orthogonalProjection)) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  have hp (v : V) : V.orthogonalProjection (V.subtypeL v) = v :=
    V.orthogonalProjection_mem_subspace_eq_self v
  have hf : V.subtypeL.comp ((A.comp B).comp V.orthogonalProjection) =
      (V.subtypeL.comp (A.comp V.orthogonalProjection)).comp
      (V.subtypeL.comp (B.comp V.orthogonalProjection)) := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, hp]
  rw [hf]
  exact isTraceClass_comp
    ((hA.comp_right V.orthogonalProjection).comp_left V.subtypeL)
    ((hB.comp_right V.orthogonalProjection).comp_left V.subtypeL)

/-- The trace is preserved; no invariance of an orthogonal complement is assumed. -/
theorem extension_trace {T : V →L[ℂ] V} (hT : IsTraceClass T) :
    trace (V.subtypeL.comp (T.comp V.orthogonalProjection)) = trace T := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  have hp (v : V) : V.orthogonalProjection (V.subtypeL v) = v :=
    V.orthogonalProjection_mem_subspace_eq_self v
  have hc := (hasSum_inner_comp_comm (stdHilbertBasis ℂ H) (stdHilbertBasis ℂ V)
    (hA.comp_left V.subtypeL) (hB.comp_right V.orthogonalProjection)).tsum_eq
  have he : trace (V.subtypeL.comp ((A.comp B).comp V.orthogonalProjection)) =
      trace (B.comp A) := by
    simpa only [trace, ContinuousLinearMap.comp_apply, hp] using hc
  exact he.trans (trace_comp_comm_of_isHilbertSchmidt hB hA)
end GeometricTraceR03

#print axioms GeometricTraceR03.extension_isTraceClass
#print axioms GeometricTraceR03.extension_trace


set_option maxHeartbeats 1000000
namespace GeometricTraceR04
noncomputable section
open GroundTheory.Automorphic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The compressed operator is constructed from the genuine orthogonal projection.
Trace class of this constructed operator is an explicit application hypothesis. -/
theorem actual_projection_trace (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H) (hA : ∀ v ∈ V, A v ∈ V)
    (hB : IsTraceClass (Vᗮ.orthogonalProjection.comp (A.comp Vᗮ.subtypeL))) :
    IsTraceClass ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A) ∧
    trace ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A) =
      trace (Vᗮ.orthogonalProjection.comp (A.comp Vᗮ.subtypeL)) := by
  let B := Vᗮ.orthogonalProjection.comp (A.comp Vᗮ.subtypeL)
  have he : Vᗮ.subtypeL.comp (B.comp Vᗮ.orthogonalProjection) =
      (ContinuousLinearMap.id ℂ H - V.starProjection).comp A := by
    ext x
    change Vᗮ.starProjection (A (Vᗮ.starProjection x)) =
      A x - V.starProjection (A x)
    have hm : V.starProjection (A (V.starProjection x)) = A (V.starProjection x) :=
      V.starProjection_eq_self_iff.mpr (hA _ (V.starProjection_apply_mem x))
    simp only [Submodule.starProjection_orthogonal_val, map_sub]
    rw [hm]
    abel
  constructor
  · rw [← he]
    exact GeometricTraceR03.extension_isTraceClass Vᗮ hB
  · rw [← he]
    exact GeometricTraceR03.extension_trace Vᗮ hB
end
end GeometricTraceR04
#print axioms GeometricTraceR04.actual_projection_trace


-- Source port: ALPO GroundTheory/AutomorphicForms/TraceNormComp.lean

namespace GroundTheory.Automorphic

open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem eq_zero_of_hsNormSq_eq_zero {T : H →L[ℂ] H} (h : hsNormSq T = 0) : T = 0 := by
  ext x
  have hx := enorm_apply_sq_le T x
  rw [h, zero_mul, nonpos_iff_eq_zero, pow_eq_zero_iff two_ne_zero, enorm_eq_zero] at hx
  simpa using hx

theorem eq_zero_of_hsNorm_eq_zero {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) (h : hsNorm T = 0) :
    T = 0 := by
  refine eq_zero_of_hsNormSq_eq_zero ?_
  rw [hsNorm, Real.sqrt_eq_zero ENNReal.toReal_nonneg, ENNReal.toReal_eq_zero_iff] at h
  exact h.resolve_right hT.ne

theorem traceNorm_comp_le {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hB : IsHilbertSchmidt B) : (traceNorm (A.comp B)).toReal ≤ hsNorm A * hsNorm B := by
  have key : ∀ t : ℝ, 0 < t → 2 * (traceNorm (A.comp B)).toReal ≤
      t ^ 2 * hsNorm A ^ 2 + (t⁻¹) ^ 2 * hsNorm B ^ 2 := by
    intro t ht
    have hAB : A.comp B = ((t : ℂ) • A).comp (((t⁻¹ : ℝ) : ℂ) • B) := by
      ext x
      simp only [comp_apply, smul_apply, map_smul, smul_smul]
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
    have h := two_mul_traceNorm_comp_le ((t : ℂ) • A) (((t⁻¹ : ℝ) : ℂ) • B)
    rw [← hAB, hsNormSq_smul, hsNormSq_smul] at h
    have hfin : ‖(t : ℂ)‖ₑ ^ 2 * hsNormSq A + ‖((t⁻¹ : ℝ) : ℂ)‖ₑ ^ 2 * hsNormSq B ≠ ∞ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hA.ne, ENNReal.mul_ne_top (by simp) hB.ne⟩
    have h' := ENNReal.toReal_mono hfin h
    rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hA.ne)
      (ENNReal.mul_ne_top (by simp) hB.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow, toReal_enorm, toReal_enorm, ← hsNorm_sq,
      ← hsNorm_sq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos (inv_pos.2 ht)] at h'
    simpa using h'
  rcases (hsNorm_nonneg A).eq_or_lt with ha | ha
  · rw [eq_zero_of_hsNorm_eq_zero hA ha.symm, zero_comp, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  rcases (hsNorm_nonneg B).eq_or_lt with hb | hb
  · rw [eq_zero_of_hsNorm_eq_zero hB hb.symm, comp_zero, traceNorm_zero, ENNReal.toReal_zero]
    exact mul_nonneg (hsNorm_nonneg _) (hsNorm_nonneg _)
  have h := key (Real.sqrt (hsNorm B / hsNorm A)) (Real.sqrt_pos.2 (div_pos hb ha))
  rw [inv_pow, Real.sq_sqrt (div_nonneg hb.le ha.le)] at h
  have e : hsNorm B / hsNorm A * hsNorm A ^ 2 + (hsNorm B / hsNorm A)⁻¹ * hsNorm B ^ 2 =
      2 * (hsNorm A * hsNorm B) := by
    field_simp
    ring
  linarith

end

end GroundTheory.Automorphic


-- Source port: ALPO GroundTheory/AutomorphicForms/TraceStrongLimit.lean

namespace GroundTheory.Automorphic

open scoped InnerProductSpace ENNReal Topology
open ContinuousLinearMap InnerProductSpace Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section FinProj

variable {ι : Type*} [Fintype ι]

def finProj (u : ι → H) : H →L[ℂ] H := ∑ i, rankOne ℂ (u i) (u i)

theorem finProj_apply (u : ι → H) (x : H) : finProj u x = ∑ i, ⟪u i, x⟫_ℂ • u i := by
  simp [finProj, rankOne_apply]

theorem finProj_mem_span (u : ι → H) (x : H) : finProj u x ∈ Submodule.span ℂ (Set.range u) := by
  rw [finProj_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable {u : ι → H}

theorem inner_finProj_right (hu : Orthonormal ℂ u) (x : H) (j : ι) :
    ⟪u j, finProj u x⟫_ℂ = ⟪u j, x⟫_ℂ := by
  rw [finProj_apply]
  exact hu.inner_right_fintype _ j

theorem inner_sub_finProj_eq_zero (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ⟪g, x - finProj u x⟫_ℂ = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hg
  rw [sum_inner]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [inner_smul_left, inner_sub_right, inner_finProj_right hu, sub_self, mul_zero]

theorem norm_sub_finProj_le (hu : Orthonormal ℂ u) (x : H) {g : H}
    (hg : g ∈ Submodule.span ℂ (Set.range u)) : ‖x - finProj u x‖ ≤ ‖x - g‖ := by
  have hmem : finProj u x - g ∈ Submodule.span ℂ (Set.range u) :=
    Submodule.sub_mem _ (finProj_mem_span u x) hg
  have h0 : ⟪x - finProj u x, finProj u x - g⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_sub_finProj_eq_zero hu x hmem, map_zero]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_sub_cancel] at h
  rw [mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _), h]
  exact le_add_of_nonneg_right (mul_self_nonneg _)

theorem norm_sub_finProj_le_norm (hu : Orthonormal ℂ u) (x : H) : ‖x - finProj u x‖ ≤ ‖x‖ := by
  simpa using norm_sub_finProj_le hu x (Submodule.zero_mem _)

theorem hasSum_inner_comp_finProj (u : ι → H) (S : H →L[ℂ] H) {κ : Type*}
    (b : HilbertBasis κ ℂ H) :
    HasSum (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) (∑ i, ⟪u i, S (u i)⟫_ℂ) := by
  have h : (fun β => ⟪b β, S (finProj u (b β))⟫_ℂ) =
      fun β => ∑ i, ⟪u i, b β⟫_ℂ * ⟪b β, S (u i)⟫_ℂ := by
    ext β
    rw [finProj_apply, map_sum, inner_sum]
    simp only [map_smul, inner_smul_right]
  rw [h]
  exact hasSum_sum fun i _ => b.hasSum_inner_mul_inner (u i) (S (u i))

theorem trace_comp_finProj [CompleteSpace H] (u : ι → H) (S : H →L[ℂ] H) :
    trace (S.comp (finProj u)) = ∑ i, ⟪u i, S (u i)⟫_ℂ :=
  (hasSum_inner_comp_finProj u S (stdHilbertBasis ℂ H)).tsum_eq

end FinProj

section Limits

variable [CompleteSpace H]

theorem tendsto_trace_comp {α : Type*} {F : Filter α} {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (P : α → H →L[ℂ] H) (hP1 : ∀ a x, ‖x - P a x‖ ≤ ‖x‖)
    (hP : ∀ x, Tendsto (fun a => P a x) F (𝓝 x)) :
    Tendsto (fun a => trace (T.comp (P a))) F (𝓝 (trace T)) := by
  obtain ⟨A, B, hA, hB, rfl⟩ := hT.exists_comp
  set Q : α → H →L[ℂ] H := fun a => ContinuousLinearMap.id ℂ H - P a with hQ

  have hdiff : ∀ a, trace (A.comp B) - trace ((A.comp B).comp (P a)) =
      trace (((Q a).comp A).comp B) := by
    intro a
    have hsplit : A.comp B = (A.comp B).comp (P a) + (A.comp B).comp (Q a) := by
      rw [← comp_add]; simp [hQ]
    have h1 : trace (A.comp B) =
        trace ((A.comp B).comp (P a)) + trace ((A.comp B).comp (Q a)) := by
      conv_lhs => rw [hsplit]
      exact trace_add (hT.comp_right _) (hT.comp_right _)
    rw [h1, add_sub_cancel_left, ← trace_comp_comm hT (Q a), comp_assoc]

  let b := stdHilbertBasis ℂ H
  have hQA : ∀ a, IsHilbertSchmidt ((Q a).comp A) := fun a => hA.comp_left _
  have hsq : ∀ a, hsNorm ((Q a).comp A) ^ 2 = ∑' e, ‖A (b e) - P a (A (b e))‖ ^ 2 := by
    intro a
    rw [((hQA a).hasSum_norm_sq b).tsum_eq.symm]
    rfl
  have hlim2 : Tendsto (fun a => hsNorm ((Q a).comp A) ^ 2) F (𝓝 0) := by
    simp_rw [hsq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := F)
      (f := fun a e => ‖A (b e) - P a (A (b e))‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun e => ‖A (b e)‖ ^ 2) (hA.hasSum_norm_sq b).summable ?_ ?_
    · simpa using h
    · intro e
      have := ((tendsto_const_nhds (x := A (b e))).sub (hP (A (b e)))).norm.pow 2
      simpa using this
    · refine Eventually.of_forall fun a e => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hP1 a _) 2
  have hlim : Tendsto (fun a => hsNorm ((Q a).comp A)) F (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hlim2
    simp only [Real.sqrt_zero] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (hsNorm_nonneg _)

  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ a, ‖trace ((A.comp B).comp (P a)) - trace (A.comp B)‖ ≤
      hsNorm ((Q a).comp A) * hsNorm B := by
    intro a
    rw [norm_sub_rev, hdiff a]
    have hfin : traceNorm (((Q a).comp A).comp B) ≠ ∞ := (isTraceClass_comp (hQA a) hB).ne
    have h1 : ‖trace (((Q a).comp A).comp B)‖ ≤ (traceNorm (((Q a).comp A).comp B)).toReal := by
      rw [← toReal_enorm]
      exact ENNReal.toReal_mono hfin (enorm_trace_le _)
    exact h1.trans (traceNorm_comp_le (hQA a) hB)
  refine squeeze_zero (fun a => norm_nonneg _) hbound ?_
  simpa using hlim.mul_const (hsNorm B)

end Limits

end

end GroundTheory.Automorphic

namespace GeometricTraceR06
noncomputable section
open GroundTheory.Automorphic Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cutoff_geometric_trace (V : Submodule ℂ H) [CompleteSpace V]
    (A R : H →L[ℂ] H)
    (hPA : IsTraceClass ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A))
    (hRA : IsTraceClass (R.comp A)) :
    IsTraceClass (R.comp (V.starProjection.comp A)) ∧
    trace (R.comp (V.starProjection.comp A)) = trace (R.comp A) -
      trace (R.comp ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A)) := by
  have hS := hPA.comp_left R
  have he : R.comp (V.starProjection.comp A) = R.comp A +
      (-1 : ℂ) • R.comp ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A) := by
    rw [neg_one_smul, ← sub_eq_add_neg, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  constructor
  · exact hRA.add (hS.smul (-1))
  · rw [trace_add hRA (hS.smul (-1)), trace_smul (-1) hS]
    ring

theorem geometric_cutoff_limit (V : Submodule ℂ H) [CompleteSpace V]
    (A : H →L[ℂ] H)
    (hPA : IsTraceClass ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A))
    {ι : Type*} {F : Filter ι} (R : ι → H →L[ℂ] H)
    (hR1 : ∀ i x, ‖x - R i x‖ ≤ ‖x‖)
    (hR : ∀ x, Tendsto (fun i => R i x) F (𝓝 x))
    (hRA : ∀ i, IsTraceClass ((R i).comp A))
    (hzero : ∀ i, trace ((R i).comp A) = 0) :
    Tendsto (fun i => trace ((R i).comp (V.starProjection.comp A))) F
      (𝓝 (-trace ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A))) := by
  have hl := tendsto_trace_comp hPA R hR1 hR
  have hl' : Tendsto (fun i => trace ((R i).comp
      ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A))) F
      (𝓝 (trace ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A))) := by
    simpa only [trace_comp_comm hPA] using hl
  have heq : (fun i => trace ((R i).comp (V.starProjection.comp A))) =
      fun i => -trace ((R i).comp ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A)) := by
    funext i
    rw [(cutoff_geometric_trace V A (R i) hPA (hRA i)).2, hzero i, zero_sub]
  rw [heq]
  exact hl'.neg
end
end GeometricTraceR06
#print axioms GroundTheory.Automorphic.tendsto_trace_comp
#print axioms GeometricTraceR06.cutoff_geometric_trace
#print axioms GeometricTraceR06.geometric_cutoff_limit

set_option linter.unusedSectionVars false

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace PhysicalCutoffR01

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def cut (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hs).toLp (s.indicator (f : X → ℂ))

theorem cut_ae (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    (cut μ s hs f : X → ℂ) =ᵐ[μ] s.indicator (f : X → ℂ) :=
  MemLp.coeFn_toLp _

theorem cut_norm_le (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖cut μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cut_ae μ s hs f] with x hx
  rw [hx]
  by_cases h : x ∈ s <;> simp [h]

def cutCLM (s : Set X) (hs : MeasurableSet s) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := cut μ s hs
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [cut_ae μ s hs (f+g), cut_ae μ s hs f, cut_ae μ s hs g,
          Lp.coeFn_add f g, Lp.coeFn_add (cut μ s hs f) (cut μ s hs g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx]
          exact h4
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [cut_ae μ s hs (c • f), cut_ae μ s hs f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (cut μ s hs f)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h3] }
    1 (fun f => by simpa using cut_norm_le μ s hs f)

theorem cut_complement_bound (s : Set X) (hs : MeasurableSet s) (f : Lp ℂ 2 μ) :
    ‖f - cutCLM μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub f (cutCLM μ s hs f), cut_ae μ s hs f] with x h1 h2
  change (cutCLM μ s hs f : X → ℂ) x = _ at h2
  rw [h1, Pi.sub_apply, h2]
  by_cases hx : x ∈ s <;> simp [hx]

def band (ell : X → ℝ) (n : ℕ) : Set X := {x | |ell x| ≤ (n : ℝ)}

theorem band_measurable (ell : X → ℝ) (hell : Measurable ell) (n : ℕ) :
    MeasurableSet (band ell n) := measurableSet_le hell.abs measurable_const

theorem eventually_mem_band (ell : X → ℝ) (x : X) :
    ∀ᶠ n in atTop, x ∈ band ell n := by
  obtain ⟨N, hN⟩ := exists_nat_ge |ell x|
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans (by exact_mod_cast hn)

theorem physical_band_strong (ell : X → ℝ) (hell : Measurable ell) (f : Lp ℂ 2 μ) :
    Tendsto (fun n => cutCLM μ (band ell n) (band_measurable ell hell n) f)
      atTop (𝓝 f) := by
  let F : ℕ → X → ℂ := fun n => (band ell n).indicator (f : X → ℂ)
  have hF : ∀ n, MemLp (F n) 2 μ := fun n =>
    (Lp.memLp f).indicator (band_measurable ell hell n)
  have hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≠ ⊤ := by
    simpa using (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (Lp.memLp f).2).ne
  have hlim : Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ^ (2 : ℝ) ∂μ)
      atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence'
      (F := fun n x => ‖F n x - f x‖ₑ ^ (2 : ℝ))
      (fun x => ‖f x‖ₑ ^ (2 : ℝ))
      (fun n => by simpa using (((hF n).1.sub (Lp.memLp f).1).enorm.pow_const (2 : ℕ)))
      (fun n => Eventually.of_forall fun x => by
        by_cases hx : x ∈ band ell n <;> simp [F, hx]) hfin
      (f := fun _ => (0 : ℝ≥0∞))
      (Eventually.of_forall fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_mem_band ell x] with n hn
        simp [F, hn])
    simpa using h
  have hnorm : Tendsto (fun n => eLpNorm (F n - (f : X → ℂ)) 2 μ)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hlim
    simpa only [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat, Pi.sub_apply,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF (f : X → ℂ) (Lp.memLp f)).2 hnorm
  simpa only [Lp.toLp_coeFn] using h

end PhysicalCutoffR01
#print axioms PhysicalCutoffR01.physical_band_strong
#print axioms PhysicalCutoffR01.cut_complement_bound


namespace WeightedProjectedTraceR01
noncomputable section
open MeasureTheory Filter PhysicalCutoffR01 GroundTheory.Automorphic
open scoped Topology
variable {X : Type*} [MeasurableSpace X]
def weightedMeasure (mu : Measure X) (ell : X → ℝ) (alpha s : ℝ) : Measure X :=
  mu.withDensity (fun x => ENNReal.ofReal
    (Real.exp (2 * alpha * |ell x|) * (1 + (ell x)^2) ^ (s/2)))

theorem actual_weighted_projected_trace_limit
    (mu : Measure X) (ell : X → ℝ) (hell : Measurable ell) (alpha s : ℝ)
    (V : Submodule ℂ (Lp ℂ 2 (weightedMeasure mu ell alpha s))) [CompleteSpace V]
    (A : Lp ℂ 2 (weightedMeasure mu ell alpha s) →L[ℂ]
      Lp ℂ 2 (weightedMeasure mu ell alpha s))
    (hT : IsTraceClass ((ContinuousLinearMap.id ℂ _ - V.starProjection).comp A)) :
    Tendsto (fun n => trace (((ContinuousLinearMap.id ℂ _ - V.starProjection).comp A).comp
      (cutCLM (weightedMeasure mu ell alpha s) (band ell n) (band_measurable ell hell n))))
      atTop (𝓝 (trace ((ContinuousLinearMap.id ℂ _ - V.starProjection).comp A))) := by
  exact tendsto_trace_comp hT _
    (fun n f => cut_complement_bound _ _ _ f)
    (fun f => physical_band_strong _ ell hell f)
end
end WeightedProjectedTraceR01
#print axioms WeightedProjectedTraceR01.actual_weighted_projected_trace_limit


/- R03: the compact-character truncation tends to finite-level averaging E,
not to the identity on the full weighted Hilbert space. Complete it there.
The paper instantiation is E=averaging over U, S=rectangular character sum,
and T=(1-projection_V).comp (convolution_mu h), with h U-invariant. -/
namespace GlobalLocalClosureR03
noncomputable section
open Filter GroundTheory.Automorphic
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def completedCutoff (E S : H →L[ℂ] H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - E + S

theorem completed_strong (E : H →L[ℂ] H) (S : ℕ → H →L[ℂ] H)
    (hS : ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (E x))) :
    ∀ x, Tendsto (fun n => completedCutoff E (S n) x) atTop (𝓝 x) := by
  intro x
  have h := (tendsto_const_nhds (x := x - E x)).add (hS x)
  simpa [completedCutoff] using h

theorem completed_comp (T E S : H →L[ℂ] H) (hTE : T.comp E = T) :
    T.comp (completedCutoff E S) = T.comp S := by
  ext x
  have hx : T (E x) = T x := congrArg (fun F : H →L[ℂ] H => F x) hTE
  simp [completedCutoff, hx]

theorem finite_level_trace_limit (T E : H →L[ℂ] H)
    (S : ℕ → H →L[ℂ] H) (hT : IsTraceClass T) (hTE : T.comp E = T)
    (hc : ∀ n x, ‖E x - S n x‖ ≤ ‖x‖)
    (hS : ∀ x, Tendsto (fun n => S n x) atTop (𝓝 (E x))) :
    Tendsto (fun n => trace (T.comp (S n))) atTop (𝓝 (trace T)) := by
  have hb : ∀ n x, ‖x - completedCutoff E (S n) x‖ ≤ ‖x‖ := by
    intro n x
    have he : x - completedCutoff E (S n) x = E x - S n x := by
      simp only [completedCutoff, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
      abel
    rw [he]
    exact hc n x
  have ht := tendsto_trace_comp hT (fun n => completedCutoff E (S n)) hb
    (completed_strong E S hS)
  simpa only [completed_comp T E _ hTE] using ht

/- These two angular sums determine the factor 1/2 at a real place.
For r=exp(u)>1 they become the even/odd GammaReal radial densities. -/
theorem real_even_angular (r : ℝ) (hm : r - 1 ≠ 0) (hp : r + 1 ≠ 0) :
    (1 / (r - 1) + 1 / (r + 1)) / 2 = r / (r^2 - 1) := by
  have hd : r^2 - 1 ≠ 0 := by
    have he : r^2 - 1 = (r - 1) * (r + 1) := by ring
    rw [he]
    exact mul_ne_zero hm hp
  field_simp
  ring

theorem real_odd_angular (r : ℝ) (hm : r - 1 ≠ 0) (hp : r + 1 ≠ 0) :
    (1 / (r - 1) - 1 / (r + 1)) / 2 = 1 / (r^2 - 1) := by
  have hd : r^2 - 1 ≠ 0 := by
    have he : r^2 - 1 = (r - 1) * (r + 1) := by ring
    rw [he]
    exact mul_ne_zero hm hp
  field_simp
  ring
end
end GlobalLocalClosureR03
#print axioms GlobalLocalClosureR03.completed_strong
#print axioms GlobalLocalClosureR03.completed_comp
#print axioms GlobalLocalClosureR03.finite_level_trace_limit
#print axioms GlobalLocalClosureR03.real_even_angular
#print axioms GlobalLocalClosureR03.real_odd_angular


/- R05: actual convolution measure scaling, with the geometric projection
kept fixed in the original weighted Hilbert space.  The integral action
premises below identify bounded maps, not their desired trace values. -/
namespace HaarProjectedTraceR05
open MeasureTheory ContinuousLinearMap GroundTheory.Automorphic
noncomputable section
variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem convolution_measure_scale (μ : Measure X) (c : ℝ≥0∞)
    (h : X → ℂ) (π : X → H →L[ℂ] H) (u : H) :
    (∫ x, h x • π x u ∂(c • μ)) =
      (c.toReal : ℂ) • (∫ x, h x • π x u ∂μ) := by
  rw [integral_smul_measure, Complex.coe_smul]

theorem actual_projected_measure_scale (μ : Measure X) (c : ℝ≥0∞)
    (h : X → ℂ) (π : X → H →L[ℂ] H)
    (A₀ A₁ : H →L[ℂ] H)
    (h₀ : ∀ u, A₀ u = ∫ x, h x • π x u ∂μ)
    (h₁ : ∀ u, A₁ u = ∫ x, h x • π x u ∂(c • μ))
    (V : Submodule ℂ H) [CompleteSpace V] :
    (ContinuousLinearMap.id ℂ H - V.starProjection).comp A₁ =
      (c.toReal : ℂ) •
        ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A₀) := by
  have ha : A₁ = (c.toReal : ℂ) • A₀ := by
    ext u
    rw [smul_apply, h₀, h₁, convolution_measure_scale]
  rw [ha]
  ext u
  simp only [comp_apply, smul_apply, map_smul]

theorem actual_projected_trace_scale (μ : Measure X) (c : ℝ≥0∞)
    (h : X → ℂ) (π : X → H →L[ℂ] H)
    (A₀ A₁ : H →L[ℂ] H)
    (h₀ : ∀ u, A₀ u = ∫ x, h x • π x u ∂μ)
    (h₁ : ∀ u, A₁ u = ∫ x, h x • π x u ∂(c • μ))
    (V : Submodule ℂ H) [CompleteSpace V]
    (hnuc : IsTraceClass ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A₀)) :
    trace ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A₁) =
      (c.toReal : ℂ) *
        trace ((ContinuousLinearMap.id ℂ H - V.starProjection).comp A₀) := by
  rw [actual_projected_measure_scale μ c h π A₀ A₁ h₀ h₁ V]
  exact trace_smul _ hnuc

theorem density_measure_scale (μ : Measure X) (v : ℝ) (hv : 0 < v)
    (d : X → ℂ) :
    (∫ x, (v : ℂ)⁻¹ * d x ∂(ENNReal.ofReal v • μ)) = ∫ x, d x ∂μ := by
  rw [integral_smul_measure, ENNReal.toReal_ofReal hv.le, integral_const_mul,
    Complex.real_smul, ← mul_assoc, mul_inv_cancel₀]
  · simp
  · exact_mod_cast hv.ne'

theorem qi_volume_strict : 0 < Real.pi / 4 ∧ Real.pi / 4 < 1 := by
  constructor
  · positivity
  · have := Real.pi_lt_four
    linarith

theorem qi_nonzero_local_not_rescaled (w : ℝ) (hw : w ≠ 0) :
    Real.pi / 4 * w ≠ w := by
  intro h
  have hz : (Real.pi / 4 - 1) * w = 0 := by nlinarith
  have hv := (mul_eq_zero.mp hz).resolve_right hw
  have hp := qi_volume_strict.2
  linarith
end
end HaarProjectedTraceR05
#print axioms HaarProjectedTraceR05.actual_projected_trace_scale
#print axioms HaarProjectedTraceR05.density_measure_scale
#print axioms HaarProjectedTraceR05.qi_nonzero_local_not_rescaled
