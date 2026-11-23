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


namespace GroundTheory.Automorphic.L2Kernel

open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

section SlopeTestRemainingChoices

theorem lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)),
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (μ : Measure α)
    (g : α → E) : eLpNorm g 2 μ ^ 2 = ∫⁻ a, ‖g a‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num [ENNReal.rpow_two]

theorem lt_top_of_sq_lt_top {a : ℝ≥0∞} (h : a ^ 2 < ∞) : a < ∞ := by
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_pow two_ne_zero] at h
  exact lt_irrefl _ h

end SlopeTestRemainingChoices

variable {𝕜 : Type*} [RCLike 𝕜]
  {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]

section Kernel

def kernelFun (k : X × Y → 𝕜) (f : Y → 𝕜) (x : X) : 𝕜 := ∫ y, k (x, y) * f y ∂ν

variable (k : Lp 𝕜 2 (μ.prod ν))

theorem measurable_rowSq :
    Measurable fun x => ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν :=
  ((Lp.stronglyMeasurable k).measurable.enorm.pow_const 2).lintegral_prod_right'

theorem lintegral_rowSq : ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∂μ = ‖k‖ₑ ^ 2 := by
  rw [← lintegral_prod _ ((Lp.stronglyMeasurable k).measurable.enorm.pow_const 2).aemeasurable,
    Lp.enorm_def, eLpNorm_two_sq]

theorem ae_rowSq_lt_top : ∀ᵐ x ∂μ, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞ := by
  refine ae_lt_top (measurable_rowSq k) ?_
  rw [lintegral_rowSq]
  exact (ENNReal.pow_lt_top enorm_lt_top).ne

theorem enorm_Lp_sq (f : Lp 𝕜 2 ν) : ‖f‖ₑ ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν := by
  rw [Lp.enorm_def, eLpNorm_two_sq]

theorem measurable_row (x : X) : Measurable fun y => k (x, y) :=
  (Lp.stronglyMeasurable k).measurable.comp measurable_prodMk_left

theorem lintegral_row_mul_sq_le (x : X) (f : Lp 𝕜 2 ν) :
    (∫⁻ y, ‖k (x, y) * f y‖ₑ ∂ν) ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 := by
  simp only [enorm_mul]
  rw [enorm_Lp_sq]
  exact lintegral_mul_sq_le ν (measurable_row k x).enorm.aemeasurable
    (Lp.aestronglyMeasurable f).enorm

theorem enorm_kernelFun_sq_le (x : X) (f : Lp 𝕜 2 ν) :
    ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ≤ (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 :=
  (pow_le_pow_left₀ (by positivity) (enorm_integral_le_lintegral_enorm _) 2).trans
    (lintegral_row_mul_sq_le k x f)

theorem aestronglyMeasurable_kernelFun (f : Lp 𝕜 2 ν) :
    AEStronglyMeasurable (kernelFun (ν := ν) k f) μ :=
  ((Lp.aestronglyMeasurable k).mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'

theorem lintegral_kernelFun_sq_le (f : Lp 𝕜 2 ν) :
    ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ ≤ ‖k‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
  calc ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν) * ‖f‖ₑ ^ 2 ∂μ :=
        lintegral_mono fun x => enorm_kernelFun_sq_le k x f
    _ = ‖k‖ₑ ^ 2 * ‖f‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ (measurable_rowSq k), lintegral_rowSq]

theorem memLp_kernelFun (f : Lp 𝕜 2 ν) : MemLp (kernelFun (ν := ν) k f) 2 μ := by
  refine ⟨aestronglyMeasurable_kernelFun k f, lt_top_of_sq_lt_top ?_⟩
  rw [eLpNorm_two_sq]
  exact (lintegral_kernelFun_sq_le k f).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) (ENNReal.pow_lt_top enorm_lt_top))

theorem ae_integrable_row_mul :
    ∀ᵐ x ∂μ, ∀ f : Lp 𝕜 2 ν, Integrable (fun y => k (x, y) * f y) ν := by
  filter_upwards [ae_rowSq_lt_top k] with x hx f
  refine ⟨(measurable_row k x).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f), ?_⟩
  refine lt_top_of_sq_lt_top ((lintegral_row_mul_sq_le k x f).trans_lt ?_)
  exact ENNReal.mul_lt_top hx (ENNReal.pow_lt_top enorm_lt_top)

def kernelOpₗ : Lp 𝕜 2 ν →ₗ[𝕜] Lp 𝕜 2 μ where
  toFun f := (memLp_kernelFun k f).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun k (f + g)).coeFn_toLp, (memLp_kernelFun k f).coeFn_toLp,
      (memLp_kernelFun k g).coeFn_toLp,
      Lp.coeFn_add ((memLp_kernelFun k f).toLp _) ((memLp_kernelFun k g).toLp _),
      ae_integrable_row_mul k] with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, kernelFun, kernelFun, kernelFun,
      ← integral_add (h5 f) (h5 g)]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [(memLp_kernelFun k (c • f)).coeFn_toLp, (memLp_kernelFun k f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_kernelFun k f).toLp _)] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, kernelFun, kernelFun, smul_eq_mul,
      ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm]

theorem kernelOpₗ_apply_ae (f : Lp 𝕜 2 ν) :
    kernelOpₗ k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  (memLp_kernelFun k f).coeFn_toLp

theorem enorm_kernelOpₗ_sq (f : Lp 𝕜 2 ν) :
    ‖kernelOpₗ k f‖ₑ ^ 2 = ∫⁻ x, ‖kernelFun (ν := ν) k f x‖ₑ ^ 2 ∂μ := by
  rw [Lp.enorm_def, eLpNorm_congr_ae (kernelOpₗ_apply_ae k f), eLpNorm_two_sq]
  rfl

theorem norm_kernelOpₗ_le (f : Lp 𝕜 2 ν) : ‖kernelOpₗ k f‖ ≤ ‖k‖ * ‖f‖ := by
  have h : ‖kernelOpₗ k f‖ₑ ^ 2 ≤ (‖k‖ₑ * ‖f‖ₑ) ^ 2 := by
    rw [enorm_kernelOpₗ_sq, mul_pow]
    exact lintegral_kernelFun_sq_le k f
  rw [ENNReal.pow_le_pow_left_iff two_ne_zero, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  exact h

def kernelOp : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ :=
  (kernelOpₗ k).mkContinuous ‖k‖ (norm_kernelOpₗ_le k)

theorem kernelOp_apply_ae (f : Lp 𝕜 2 ν) :
    kernelOp k f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν :=
  kernelOpₗ_apply_ae k f

theorem exists_row {x : X} (hx : ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν < ∞) :
    ∃ h : Lp 𝕜 2 ν, ‖h‖ₑ ^ 2 = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∧
      ∀ f : Lp 𝕜 2 ν, kernelFun (ν := ν) k f x = ⟪h, f⟫_𝕜 := by
  have hconj : ∀ y, ‖conj (k (x, y))‖ₑ = ‖k (x, y)‖ₑ := fun y => by
    rw [← ofReal_norm, ← ofReal_norm, RCLike.norm_conj]
  have hm : MemLp (fun y => conj (k (x, y))) 2 ν := by
    refine ⟨(RCLike.continuous_conj.comp_aestronglyMeasurable
      (measurable_row k x).aestronglyMeasurable), lt_top_of_sq_lt_top ?_⟩
    rw [eLpNorm_two_sq]
    simpa only [hconj] using hx
  refine ⟨hm.toLp _, ?_, fun f => ?_⟩
  · rw [Lp.enorm_def, eLpNorm_congr_ae hm.coeFn_toLp, eLpNorm_two_sq]
    simp only [hconj]
  · rw [MeasureTheory.L2.inner_def, kernelFun]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with y hy
    rw [RCLike.inner_apply, hy, RCLike.conj_conj, mul_comm]

theorem hsNormSq_kernelOp_le : hsNormSq (kernelOp k) ≤ ‖k‖ₑ ^ 2 := by
  let b := stdHilbertBasis 𝕜 (Lp 𝕜 2 ν)
  rw [hsNormSq]
  refine ENNReal.summable.tsum_le_of_sum_le fun s => ?_
  calc ∑ i ∈ s, ‖kernelOp k (b i)‖ₑ ^ 2
      = ∑ i ∈ s, ∫⁻ x, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2 ∂μ :=
        Finset.sum_congr rfl fun i _ => enorm_kernelOpₗ_sq k (b i)
    _ = ∫⁻ x, ∑ i ∈ s, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2 ∂μ :=
        (lintegral_finset_sum' s fun i _ =>
          ((aestronglyMeasurable_kernelFun k (b i)).enorm.pow_const 2)).symm
    _ ≤ ∫⁻ x, ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_rowSq_lt_top k] with x hx
        obtain ⟨h, hh, hK⟩ := exists_row k hx
        calc ∑ i ∈ s, ‖kernelFun (ν := ν) k (b i) x‖ₑ ^ 2
            = ∑ i ∈ s, ‖⟪b i, h⟫_𝕜‖ₑ ^ 2 :=
              Finset.sum_congr rfl fun i _ => by rw [hK, enorm_inner_comm]
          _ ≤ ∑' i, ‖⟪b i, h⟫_𝕜‖ₑ ^ 2 := ENNReal.sum_le_tsum s
          _ = ∫⁻ y, ‖k (x, y)‖ₑ ^ 2 ∂ν := by rw [← enorm_sq_eq_tsum b, hh]
    _ = ‖k‖ₑ ^ 2 := lintegral_rowSq k

theorem kernelOp_isHilbertSchmidt : IsHilbertSchmidt (kernelOp k) :=
  (hsNormSq_kernelOp_le k).trans_lt (ENNReal.pow_lt_top enorm_lt_top)

end Kernel

theorem kernelOp_toLp_apply_ae {k : X × Y → 𝕜} (hk : MemLp k 2 (μ.prod ν)) (f : Lp 𝕜 2 ν) :
    kernelOp (hk.toLp k) f =ᵐ[μ] fun x => ∫ y, k (x, y) * f y ∂ν := by
  filter_upwards [kernelOp_apply_ae (hk.toLp k) f, Measure.ae_ae_of_ae_prod hk.coeFn_toLp] with x h1 h2
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [h2] with y hy
  rw [hy]

end

end GroundTheory.Automorphic.L2Kernel

/- Adapted from Fermat Def_Mathlib_MeasureTheory_Function_L2KernelOperator.lean,
   through end Operator. The construction now assumes SFinite, not finite mass.
   No compactness or trace-class conclusion is asserted. -/

set_option autoImplicit false

open scoped ENNReal NNReal symmDiff
open MeasureTheory Set

noncomputable section

namespace MeasureTheory

namespace L2

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

def sigmaKernelIntegral (ν : Measure β) (K : α × β → ℂ) (f : β → ℂ) (x : α) : ℂ :=
  ∫ y, K (x, y) * f y ∂ν

omit [MeasurableSpace α] in
lemma sigmaKernelIntegral_def (K : α × β → ℂ) (f : β → ℂ) (x : α) :
    sigmaKernelIntegral ν K f x = ∫ y, K (x, y) * f y ∂ν := rfl

section SchurBound

variable [SFinite ν]

theorem lintegral_enorm_sigmaKernelIntegral_sq_le {K : α × β → ℂ} {f : β → ℂ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : AEStronglyMeasurable f ν) :
    ∫⁻ x, ‖sigmaKernelIntegral ν K f x‖ₑ ^ (2 : ℝ) ∂μ ≤
      (∫⁻ z, ‖K z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by

  have hslice : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => K (x, y)) ν :=
    hK.prodMk_left
  have key : ∀ᵐ x ∂μ, ‖sigmaKernelIntegral ν K f x‖ₑ ^ (2 : ℝ) ≤
      (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by
    filter_upwards [hslice] with x hx
    have h1 : ‖sigmaKernelIntegral ν K f x‖ₑ ≤ ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂ν := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      exact lintegral_congr fun y => by rw [enorm_mul]
    have h2 : ∫⁻ y, ‖K (x, y)‖ₑ * ‖f y‖ₑ ∂ν ≤
        (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
          (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
        hx.enorm hf.enorm
    calc ‖sigmaKernelIntegral ν K f x‖ₑ ^ (2 : ℝ)
        ≤ ((∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) *
            (∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
      _ = (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
            ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
          norm_num

  calc ∫⁻ x, ‖sigmaKernelIntegral ν K f x‖ₑ ^ (2 : ℝ) ∂μ
      ≤ ∫⁻ x, (∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν ∂μ :=
        lintegral_mono_ae key
    _ = (∫⁻ x, ∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν ∂μ) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν :=
        lintegral_mul_const'' _ (hK.enorm.pow_const _).lintegral_prod_right'
    _ = (∫⁻ z, ‖K z‖ₑ ^ (2 : ℝ) ∂(μ.prod ν)) * ∫⁻ y, ‖f y‖ₑ ^ (2 : ℝ) ∂ν := by
        rw [lintegral_prod _ (hK.enorm.pow_const _)]

theorem eLpNorm_sigmaKernelIntegral_le {K : α × β → ℂ} {f : β → ℂ}
    (hK : AEStronglyMeasurable K (μ.prod ν)) (hf : AEStronglyMeasurable f ν) :
    eLpNorm (sigmaKernelIntegral ν K f) 2 μ ≤ eLpNorm K 2 (μ.prod ν) * eLpNorm f 2 ν := by
  have h2 : ((2 : ℝ≥0∞)).toReal = (2 : ℝ) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num), h2,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1 / 2)]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_sigmaKernelIntegral_sq_le hK hf) (by norm_num)

theorem _root_.MeasureTheory.MemLp.sigmaKernelIntegral {K : α × β → ℂ} {f : β → ℂ}
    (hK : MemLp K 2 (μ.prod ν)) (hf : MemLp f 2 ν) :
    MemLp (sigmaKernelIntegral ν K f) 2 μ := by
  refine ⟨?_, ?_⟩
  · exact (hK.aestronglyMeasurable.mul (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd)).integral_prod_right'
  · exact (eLpNorm_sigmaKernelIntegral_le hK.aestronglyMeasurable hf.aestronglyMeasurable).trans_lt
      (ENNReal.mul_lt_top hK.eLpNorm_lt_top hf.eLpNorm_lt_top)

theorem _root_.MeasureTheory.MemLp.sigma_ae_memLp_prodMk_left {K : α × β → ℂ}
    (hK : MemLp K 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 ν := by
  have hmeas := hK.aestronglyMeasurable.prodMk_left
  have hfin : ∀ᵐ x ∂μ, ∫⁻ y, ‖K (x, y)‖ₑ ^ (2 : ℝ) ∂ν < ∞ := by
    have h2 := hK.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)] at h2
    have hfin' : ∫⁻ z, ‖K z‖ₑ ^ ((2 : ℝ≥0∞)).toReal ∂(μ.prod ν) ≠ ∞ := by
      intro hcon
      rw [hcon] at h2
      simp at h2
    rw [show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num] at hfin'
    rw [lintegral_prod _ (hK.aestronglyMeasurable.enorm.pow_const _)] at hfin'
    exact ae_lt_top' (hK.aestronglyMeasurable.enorm.pow_const _).lintegral_prod_right' hfin'
  filter_upwards [hmeas, hfin] with x hx1 hx2
  refine ⟨hx1, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    (by rw [show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num]; exact hx2.ne)

theorem ae_integrable_sigmaKernelIntegral {K : α × β → ℂ} (hK : MemLp K 2 (μ.prod ν))
    {f : β → ℂ} (hf : MemLp f 2 ν) :
    ∀ᵐ x ∂μ, Integrable (fun y => K (x, y) * f y) ν := by
  filter_upwards [hK.sigma_ae_memLp_prodMk_left] with x hx
  exact hx.integrable_mul hf

end SchurBound

section Operator

variable [SFinite μ] [SFinite ν]

def sigmaKernelIntegralLM (K : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ((Lp.memLp K).sigmaKernelIntegral (Lp.memLp f)).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [ae_integrable_sigmaKernelIntegral (Lp.memLp K) (Lp.memLp f),
      ae_integrable_sigmaKernelIntegral (Lp.memLp K) (Lp.memLp g)] with x hxf hxg
    simp only [Pi.add_apply, sigmaKernelIntegral_def]
    rw [← integral_add hxf hxg]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    refine .of_forall fun x => ?_
    simp only [Pi.smul_apply, sigmaKernelIntegral_def, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy, Pi.smul_apply, smul_eq_mul]; ring

omit [SFinite μ] in
@[simp]
lemma sigmaKernelIntegralLM_apply (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    sigmaKernelIntegralLM K f = ((Lp.memLp K).sigmaKernelIntegral (Lp.memLp f)).toLp _ := rfl

omit [SFinite μ] in
lemma sigmaKernelIntegralLM_coeFn (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    sigmaKernelIntegralLM K f =ᵐ[μ] sigmaKernelIntegral ν (K : α × β → ℂ) f :=
  MemLp.coeFn_toLp ((Lp.memLp K).sigmaKernelIntegral (Lp.memLp f))

omit [SFinite μ] in

theorem norm_sigmaKernelIntegralLM_apply_le (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    ‖sigmaKernelIntegralLM K f‖ ≤ ‖K‖ * ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top K)
    (Lp.eLpNorm_ne_top f)) ?_
  rw [eLpNorm_congr_ae (sigmaKernelIntegralLM_coeFn K f)]
  exact eLpNorm_sigmaKernelIntegral_le (Lp.aestronglyMeasurable K) (Lp.aestronglyMeasurable f)

omit [SFinite μ] in

theorem sigmaKernelIntegralLM_add_apply (K K' : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    sigmaKernelIntegralLM (K + K') f = sigmaKernelIntegralLM K f + sigmaKernelIntegralLM K' f := by
  simp only [sigmaKernelIntegralLM_apply]
  rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
  filter_upwards [ae_integrable_sigmaKernelIntegral (Lp.memLp K) (Lp.memLp f),
    ae_integrable_sigmaKernelIntegral (Lp.memLp K') (Lp.memLp f),
    Measure.ae_ae_of_ae_prod (Lp.coeFn_add K K')] with x hxK hxK' hxadd
  simp only [Pi.add_apply, sigmaKernelIntegral_def]
  rw [← integral_add hxK hxK']
  refine integral_congr_ae ?_
  filter_upwards [hxadd] with y hy
  rw [hy, Pi.add_apply, add_mul]

omit [SFinite μ] in

theorem sigmaKernelIntegralLM_smul_apply (c : ℂ) (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    sigmaKernelIntegralLM (c • K) f = c • sigmaKernelIntegralLM K f := by
  simp only [sigmaKernelIntegralLM_apply]
  rw [← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
  filter_upwards [Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c K)] with x hxsmul
  simp only [Pi.smul_apply, sigmaKernelIntegral_def, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hxsmul] with y hy
  rw [hy, Pi.smul_apply, smul_eq_mul]; ring

def sigmaKernelIntegralₗ : Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous₂
    { toFun := sigmaKernelIntegralLM
      map_add' := fun K K' => LinearMap.ext fun f => sigmaKernelIntegralLM_add_apply K K' f
      map_smul' := fun c K => LinearMap.ext fun f => sigmaKernelIntegralLM_smul_apply c K f }
    1 (fun K f => by simpa using norm_sigmaKernelIntegralLM_apply_le K f)

abbrev sigmaKernelIntegralCLM (K : Lp ℂ 2 (μ.prod ν)) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  sigmaKernelIntegralₗ K

omit [SFinite μ] in
lemma sigmaKernelIntegralCLM_apply (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    sigmaKernelIntegralCLM K f = sigmaKernelIntegralLM K f := rfl

omit [SFinite μ] in
lemma sigmaKernelIntegralCLM_coeFn (K : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
    sigmaKernelIntegralCLM K f =ᵐ[μ] fun x => ∫ y, (K : α × β → ℂ) (x, y) * f y ∂ν :=
  sigmaKernelIntegralLM_coeFn K f

omit [SFinite μ] in

theorem norm_sigmaKernelIntegralCLM_le (K : Lp ℂ 2 (μ.prod ν)) : ‖sigmaKernelIntegralCLM K‖ ≤ ‖K‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K) fun f =>
    norm_sigmaKernelIntegralLM_apply_le K f

omit [SFinite μ] in

theorem norm_sigmaKernelIntegralₗ_le :
    ‖(sigmaKernelIntegralₗ : Lp ℂ 2 (μ.prod ν) →L[ℂ] _)‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

end Operator

end L2
end MeasureTheory
end

#print axioms MeasureTheory.L2.norm_sigmaKernelIntegralCLM_le
#print axioms MeasureTheory.L2.sigmaKernelIntegralCLM_coeFn

namespace ActualKernelApplication
open MeasureTheory GroundTheory.Automorphic
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

/-- Fermat's bounded kernel construction realizes exactly ALPO's HS operator.
This is used for the differentiated compact kernel in ACTUAL_CUTOFF_R01.md. -/
theorem fermat_eq_alpo (K : Lp ℂ 2 (μ.prod ν)) :
    L2.sigmaKernelIntegralCLM K = L2Kernel.kernelOp K := by
  ext f
  exact (L2.sigmaKernelIntegralCLM_coeFn K f).trans
    (L2Kernel.kernelOp_apply_ae K f).symm

theorem fermat_kernel_isHilbertSchmidt (K : Lp ℂ 2 (μ.prod ν)) :
    IsHilbertSchmidt (L2.sigmaKernelIntegralCLM K) := by
  rw [fermat_eq_alpo]
  exact L2Kernel.kernelOp_isHilbertSchmidt K

end ActualKernelApplication
#print axioms ActualKernelApplication.fermat_eq_alpo
#print axioms ActualKernelApplication.fermat_kernel_isHilbertSchmidt

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

namespace ActualThetaShellR02
noncomputable section
open ContinuousLinearMap GroundTheory.Automorphic MeasureTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def shell (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W] : H →L[ℂ] H :=
  V.starProjection - W.starProjection

/-- The actual descending theta spaces give commuting nested projections. -/
theorem nested_left (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W]
    (hWV : W ≤ V) : V.starProjection.comp W.starProjection = W.starProjection := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr
    (hWV (W.starProjection_apply_mem x))

theorem nested_right (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W]
    (hWV : W ≤ V) : W.starProjection.comp V.starProjection = W.starProjection := by
  have h := congrArg adjoint (nested_left V W hWV)
  simpa only [adjoint_comp, (isSelfAdjoint_starProjection V).adjoint_eq,
    (isSelfAdjoint_starProjection W).adjoint_eq] using h

/-- Therefore this shell is an actual orthogonal projection, not a raw idele indicator. -/
theorem shell_idempotent (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W]
    (hWV : W ≤ V) : (shell V W).comp (shell V W) = shell V W := by
  have hvv := nested_left V V le_rfl
  have hww := nested_left W W le_rfl
  have hvw := nested_left V W hWV
  have hwv := nested_right V W hWV
  ext x
  have h1 := DFunLike.congr_fun hvv x
  have h2 := DFunLike.congr_fun hww x
  have h3 := DFunLike.congr_fun hvw x
  have h4 := DFunLike.congr_fun hwv x
  simp only [comp_apply] at h1 h2 h3 h4
  simp only [shell, comp_apply, sub_apply, map_sub, h1, h2, h3, h4]
  abel

theorem shell_selfadjoint (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W] :
    adjoint (shell V W) = shell V W := by
  simp only [shell, map_sub, (isSelfAdjoint_starProjection V).adjoint_eq,
    (isSelfAdjoint_starProjection W).adjoint_eq]

/-- Fixed-cutoff trace telescoping for genuine theta projections. -/
theorem shell_trace_step (V W : Submodule ℂ H) [CompleteSpace V] [CompleteSpace W]
    (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    trace (V.starProjection.comp T) =
      trace ((shell V W).comp T) + trace (W.starProjection.comp T) := by
  rw [← trace_add (hT.comp_left (shell V W)) (hT.comp_left W.starProjection)]
  congr 1
  ext x
  simp only [shell, add_apply, comp_apply, sub_apply]
  exact (sub_add_cancel _ _).symm

/-- ALPO is instantiated on Fermat's actual integral operators: the two L2
kernels give trace class without assuming the target trace identity. -/
theorem shell_trace_from_fermat
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (K L : Lp ℂ 2 (μ.prod μ))
    (V W : Submodule ℂ (Lp ℂ 2 μ)) [CompleteSpace V] [CompleteSpace W] :
    let T := (L2.sigmaKernelIntegralCLM K).comp (L2.sigmaKernelIntegralCLM L)
    IsTraceClass T ∧ trace (V.starProjection.comp T) =
      trace ((shell V W).comp T) + trace (W.starProjection.comp T) := by
  dsimp only
  have hT := isTraceClass_comp
    (ActualKernelApplication.fermat_kernel_isHilbertSchmidt K)
    (ActualKernelApplication.fermat_kernel_isHilbertSchmidt L)
  exact ⟨hT, shell_trace_step V W _ hT⟩
end
end ActualThetaShellR02
#print axioms ActualThetaShellR02.shell_idempotent
#print axioms ActualThetaShellR02.shell_selfadjoint
#print axioms ActualThetaShellR02.shell_trace_from_fermat


namespace ActualShellCouplingR06
open GroundTheory.Automorphic ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The internal coupling between adjacent actual shells is a block of the
whole finite-primary compression, whose nuclearity is constructed in B/R05. -/
theorem internal_block_traceClass (E F A : H →L[ℂ] H)
    (hEE : E * E = E) (hFF : F * F = F)
    (hFE : F * E = 0)
    (hT : IsTraceClass ((E+F)*A*(E+F))) :
    IsTraceClass (F*A*E) := by
  have h := (hT.comp_left F).comp_right E
  have hid : F * ((E+F)*A*(E+F)) * E = F*A*E := by
    calc
      F * ((E+F)*A*(E+F)) * E = (F*(E+F))*A*((E+F)*E) := by noncomm_ring
      _ = F*A*E := by simp only [mul_add, add_mul, hFE, hFF, hEE, zero_add, add_zero]
  change IsTraceClass (F * ((E+F)*A*(E+F)) * E) at h
  rwa [hid] at h

/-- Its uncut trace vanishes by the genuine orthogonality, not because
its operator vanishes. -/
theorem internal_block_trace_zero (E F A : H →L[ℂ] H)
    (hFF : F*F=F) (hEF : E*F=0) (hX : IsTraceClass (F*A*E)) :
    trace (F*A*E) = 0 := by
  have hleft : F * (F*A*E) = F*A*E := by rw [← mul_assoc, ← mul_assoc, hFF]
  have hright : (F*A*E)*F = 0 := by rw [mul_assoc, hEF, mul_zero]
  have hc := trace_comp_comm hX F
  change trace (F * (F*A*E)) = trace ((F*A*E)*F) at hc
  rw [hleft, hright] at hc
  simpa only [trace, zero_apply, inner_zero_right, tsum_zero] using hc

/-- The difference between adjacent-shell input couplings is exactly the
internal off-diagonal block. Q0 and Q1 are the actual nested theta projectors. -/
theorem adjacent_coupling_difference (Q0 Q1 F A R : H →L[ℂ] H) :
    F*A*(1-Q1)*R*F - F*A*(1-Q0)*R*F = F*A*(Q0-Q1)*R*F := by
  noncomm_ring

/-- Cutoff error expressed using R-1. This is the form to which the
constructed HS factors and strong-cutoff domination apply. -/
theorem internal_cutoff_error (E F A R : H →L[ℂ] H) (hEF : E*F=0) :
    F*A*E*R*F = F*A*E*(R-1)*F := by
  have hz : F*A*E*F = 0 := by rw [mul_assoc, hEF, mul_zero]
  calc
    F*A*E*R*F = F*A*E*R*F - F*A*E*F := by rw [hz, sub_zero]
    _ = F*A*E*(R-1)*F := by noncomm_ring
end
end ActualShellCouplingR06
#print axioms ActualShellCouplingR06.internal_block_traceClass
#print axioms ActualShellCouplingR06.internal_block_trace_zero
#print axioms ActualShellCouplingR06.adjacent_coupling_difference
#print axioms ActualShellCouplingR06.internal_cutoff_error
