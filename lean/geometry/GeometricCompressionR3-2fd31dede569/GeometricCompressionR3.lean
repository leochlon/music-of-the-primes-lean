/- Extracted from ALPO IsHilbertSchmidtOfFiniteDimensional.lean, Hilbert section.
Only the unrelated SmoothPartStable import and later representation sections were removed. -/
import Mathlib
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise

noncomputable section

namespace GlobalTheory.OpTrace

section Hilbert

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
  {ι κ : Type*}

variable (H) in

def stdIndex : Set H := (exists_hilbertBasis ℂ H).choose

variable (H) in

def stdBasis : HilbertBasis (stdIndex H) ℂ H := (exists_hilbertBasis ℂ H).choose_spec.choose

def IsHilbertSchmidt (T : H →L[ℂ] K) : Prop :=
  Summable fun i => ‖T (stdBasis H i)‖ ^ 2

def hsNormSq (T : H →L[ℂ] K) : ℝ := ∑' i, ‖T (stdBasis H i)‖ ^ 2

def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (n : ℕ) (B C : Fin n → (H →L[ℂ] H)),
    (∀ i, IsHilbertSchmidt (B i)) ∧ (∀ i, IsHilbertSchmidt (C i)) ∧ T = ∑ i, B i ∘L C i

def trace (T : H →L[ℂ] H) : ℂ := ∑' i, ⟪stdBasis H i, T (stdBasis H i)⟫_ℂ

def HasTrace (T : H →L[ℂ] H) (c : ℂ) : Prop := IsTraceClass T ∧ trace T = c

omit [CompleteSpace H] in

theorem hasSum_norm_inner_sq (e : HilbertBasis ι ℂ H) (x : H) :
    HasSum (fun i => ‖⟪e i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (e.repr x)
  simpa [e.repr_apply_apply] using h

omit [CompleteSpace H] [CompleteSpace K] in

theorem summable_matrix (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K) {T : H →L[ℂ] K}
    (h : Summable fun i => ‖T (e i)‖ ^ 2) :
    Summable fun p : ι × κ => ‖⟪f p.2, T (e p.1)⟫_ℂ‖ ^ 2 := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  refine ⟨fun i => (hasSum_norm_inner_sq f (T (e i))).summable, ?_⟩
  simpa only [(hasSum_norm_inner_sq f _).tsum_eq] using h

theorem hasSum_adjoint (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K) {T : H →L[ℂ] K} {s : ℝ}
    (h : HasSum (fun i => ‖T (e i)‖ ^ 2) s) : HasSum (fun j => ‖adjoint T (f j)‖ ^ 2) s := by
  have hF := (summable_matrix e f h.summable).hasSum
  have hs := h.unique (hF.prod_fiberwise fun i => hasSum_norm_inner_sq f (T (e i)))
  rw [← hs, ← (Equiv.prodComm κ ι).hasSum_iff] at hF
  refine hF.prod_fiberwise fun j => ?_
  have := hasSum_norm_inner_sq e (adjoint T (f j))
  simp only [adjoint_inner_right] at this
  simpa [Function.comp_def, norm_inner_symm (T _)] using this

theorem hasSum_basis (e : HilbertBasis ι ℂ H) (e' : HilbertBasis κ ℂ H) {T : H →L[ℂ] K} {s : ℝ}
    (h : HasSum (fun i => ‖T (e i)‖ ^ 2) s) : HasSum (fun j => ‖T (e' j)‖ ^ 2) s := by
  simpa using hasSum_adjoint (stdBasis K) e' (hasSum_adjoint e (stdBasis K) h)

theorem isHilbertSchmidt_iff (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] K} :
    IsHilbertSchmidt T ↔ Summable fun i => ‖T (e i)‖ ^ 2 :=
  ⟨fun h => (hasSum_basis _ e h.hasSum).summable, fun h => (hasSum_basis e _ h.hasSum).summable⟩

theorem IsHilbertSchmidt.hasSum {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ‖T (e i)‖ ^ 2) (hsNormSq T) :=
  hasSum_basis _ e (Summable.hasSum h)

theorem IsHilbertSchmidt.adjoint {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) :
    IsHilbertSchmidt (adjoint T) :=
  (hasSum_adjoint _ _ (Summable.hasSum h)).summable

omit [CompleteSpace K] [CompleteSpace L] in

theorem IsHilbertSchmidt.of_norm_le {T : H →L[ℂ] K} {S : H →L[ℂ] L} (h : IsHilbertSchmidt T)
    (c : ℝ) (hS : ∀ x, ‖S x‖ ≤ c * ‖T x‖) : IsHilbertSchmidt S := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_) (Summable.mul_left (c ^ 2) h)
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hS _) 2

omit [CompleteSpace K] [CompleteSpace L] in

theorem IsHilbertSchmidt.comp_left {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (A : K →L[ℂ] L) :
    IsHilbertSchmidt (A ∘L T) :=
  h.of_norm_le ‖A‖ fun x => A.le_opNorm _

theorem IsHilbertSchmidt.comp_right {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (A : L →L[ℂ] H) :
    IsHilbertSchmidt (T ∘L A) := by
  simpa using (h.adjoint.comp_left (ContinuousLinearMap.adjoint A)).adjoint

omit [CompleteSpace K] in

theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : H →L[ℂ] K) := by
  simp [IsHilbertSchmidt, summable_zero]

omit [CompleteSpace K] in

theorem IsHilbertSchmidt.add {S T : H →L[ℂ] K} (hS : IsHilbertSchmidt S) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (S + T) := by
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
    ((Summable.add hS hT).mul_left 2)
  have h1 := norm_add_le (S (stdBasis H i)) (T (stdBasis H i))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [add_apply]
  nlinarith [sq_nonneg (‖S (stdBasis H i)‖ - ‖T (stdBasis H i)‖)]

omit [CompleteSpace K] in

theorem IsHilbertSchmidt.smul {T : H →L[ℂ] K} (h : IsHilbertSchmidt T) (c : ℂ) :
    IsHilbertSchmidt (c • T) :=
  h.of_norm_le ‖c‖ fun x => by simp [norm_smul]

omit [CompleteSpace K] in

theorem isHilbertSchmidt_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] K) :
    IsHilbertSchmidt T := by
  have : Finite (stdIndex H) := (stdBasis H).orthonormal.linearIndependent.finite
  exact Summable.of_finite

theorem exists_hasSum_comp (e : HilbertBasis ι ℂ H) (f : HilbertBasis κ ℂ K)
    {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    ∃ s : ℂ, HasSum (fun i => ⟪e i, B (C (e i))⟫_ℂ) s ∧ HasSum (fun j => ⟪f j, C (B (f j))⟫_ℂ) s := by
  have h1 := summable_matrix e f ((isHilbertSchmidt_iff e).1 hC)
  have h2 := (Equiv.prodComm ι κ).summable_iff.2 (summable_matrix f e ((isHilbertSchmidt_iff f).1 hB))
  have hF : Summable fun p : ι × κ => ⟪e p.1, B (f p.2)⟫_ℂ * ⟪f p.2, C (e p.1)⟫_ℂ := by
    refine Summable.of_norm_bounded (h1.add h2) fun p => ?_
    simp only [Function.comp_def, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, norm_mul]
    nlinarith [sq_nonneg (‖⟪e p.1, B (f p.2)⟫_ℂ‖ - ‖⟪f p.2, C (e p.1)⟫_ℂ‖),
      mul_nonneg (norm_nonneg ⟪e p.1, B (f p.2)⟫_ℂ) (norm_nonneg ⟪f p.2, C (e p.1)⟫_ℂ)]
  refine ⟨_, hF.hasSum.prod_fiberwise fun i => ?_,
    ((Equiv.prodComm κ ι).hasSum_iff.2 hF.hasSum).prod_fiberwise fun j => ?_⟩
  · simpa only [adjoint_inner_left] using f.hasSum_inner_mul_inner (adjoint B (e i)) (C (e i))
  · have := e.hasSum_inner_mul_inner (adjoint C (f j)) (B (f j))
    simp only [adjoint_inner_left] at this
    simpa [Function.comp_def, mul_comm] using this

theorem hasSum_trace_comp (e : HilbertBasis ι ℂ H)
    {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) :
    HasSum (fun i => ⟪e i, (B ∘L C) (e i)⟫_ℂ) (trace (B ∘L C)) := by
  obtain ⟨s, h1, h2⟩ := exists_hasSum_comp e (stdBasis K) hB hC
  obtain ⟨t, h3, h4⟩ := exists_hasSum_comp (stdBasis H) (stdBasis K) hB hC
  have : trace (B ∘L C) = s := h3.tsum_eq.trans (h4.unique h2)
  rw [this]; exact h1

theorem trace_comp_comm {B : K →L[ℂ] H} {C : H →L[ℂ] K} (hB : IsHilbertSchmidt B)
    (hC : IsHilbertSchmidt C) : trace (B ∘L C) = trace (C ∘L B) := by
  obtain ⟨t, h3, h4⟩ := exists_hasSum_comp (stdBasis H) (stdBasis K) hB hC
  exact h3.tsum_eq.trans h4.tsum_eq.symm

theorem IsTraceClass.hasSum_trace {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    HasSum (fun i => ⟪e i, T (e i)⟫_ℂ) (trace T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have key : ∀ {κ : Type _} (f : HilbertBasis κ ℂ H),
      HasSum (fun i => ⟪f i, (∑ k, B k ∘L C k) (f i)⟫_ℂ) (∑ k, trace (B k ∘L C k)) := fun f => by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun k (_ : k ∈ Finset.univ) => hasSum_trace_comp f (hB k) (hC k)
  have h2 : HasSum (fun i => ⟪e i, (∑ k, B k ∘L C k) (e i)⟫_ℂ) (∑ k, trace (B k ∘L C k)) := by
    simpa only [ContinuousLinearMap.sum_apply, inner_sum] using
      hasSum_sum fun k (_ : k ∈ Finset.univ) => hasSum_trace_comp e (hB k) (hC k)
  rw [show trace (∑ k, B k ∘L C k) = _ from (key (stdBasis H)).tsum_eq]
  exact h2

theorem IsTraceClass.summable_norm {T : H →L[ℂ] H} (h : IsTraceClass T) (e : HilbertBasis ι ℂ H) :
    Summable fun i => ‖⟪e i, T (e i)⟫_ℂ‖ :=
  (h.hasSum_trace e).summable.norm

omit [CompleteSpace L] in

theorem exists_comp_eq_of_norm_le {C : H →L[ℂ] K} {A : H →L[ℂ] L} (h : ∀ x, ‖C x‖ ≤ ‖A x‖)
    [CompleteSpace L] : ∃ U : L →L[ℂ] K, U ∘L A = C := by
  let M : Submodule ℂ L := (LinearMap.range (A : H →ₗ[ℂ] L)).topologicalClosure
  have hM : ∀ x, A x ∈ M := fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩
  let a : H →ₗ[ℂ] M := (A : H →ₗ[ℂ] L).codRestrict M hM
  have hd : DenseRange a := by
    rw [DenseRange, Subtype.dense_iff]
    intro y hy
    refine closure_mono ?_ (show y ∈ closure (LinearMap.range (A : H →ₗ[ℂ] L) : Set L) from hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨a x, ⟨x, rfl⟩, rfl⟩
  refine ⟨(C : H →ₗ[ℂ] K).extendOfNorm a ∘L M.orthogonalProjection, ?_⟩
  ext x
  have h1 : M.orthogonalProjection (A x) = a x :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (a x)
  rw [comp_apply, comp_apply, h1]
  exact LinearMap.extendOfNorm_eq hd ⟨1, fun y => by simpa [a] using h y⟩ x

theorem norm_sqrt_apply (C : H →L[ℂ] K) (x : H) :
    ‖(CFC.sqrt (adjoint C ∘L C) : H →L[ℂ] H) x‖ = ‖C x‖ := by
  have hp : (0 : H →L[ℂ] H) ≤ adjoint C ∘L C :=
    (nonneg_iff_isPositive _).2 (isPositive_adjoint_comp_self C)
  set A : H →L[ℂ] H := CFC.sqrt (adjoint C ∘L C)
  have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
  have h2 : A * A = adjoint C ∘L C := CFC.sqrt_mul_sqrt_self _ hp
  have h3 : ⟪A x, A x⟫_ℂ = ⟪C x, C x⟫_ℂ := by
    rw [← adjoint_inner_right, hA.adjoint_eq, ← adjoint_inner_right C]
    exact congrArg (fun S : H →L[ℂ] H => ⟪x, S x⟫_ℂ) h2
  rw [@norm_eq_sqrt_re_inner ℂ, h3, ← @norm_eq_sqrt_re_inner ℂ]

theorem IsHilbertSchmidt.isTraceClass_comp {B : K →L[ℂ] H} {C : H →L[ℂ] K}
    (hB : IsHilbertSchmidt B) (hC : IsHilbertSchmidt C) : IsTraceClass (B ∘L C) := by
  obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (norm_sqrt_apply C x).ge
  refine ⟨1, fun _ => B ∘L U, fun _ => CFC.sqrt (ContinuousLinearMap.adjoint C ∘L C),
    fun _ => hB.comp_right U,
    fun _ => hC.of_norm_le 1 fun x => by rw [norm_sqrt_apply, one_mul], ?_⟩
  rw [Fin.sum_univ_one, comp_assoc, hU]

theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) :=
  ⟨0, fun _ => 0, fun _ => 0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem IsTraceClass.add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := hS
  obtain ⟨m, B', C', hB', hC', rfl⟩ := hT
  refine ⟨n + m, Fin.append B B', Fin.append C C', fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hB, hB']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hC, hC']
  · simp [Fin.sum_univ_add]

theorem isTraceClass_sum {α : Type*} (s : Finset α) {T : α → (H →L[ℂ] H)}
    (h : ∀ a ∈ s, IsTraceClass (T a)) : IsTraceClass (∑ a ∈ s, T a) :=
  Finset.sum_induction T IsTraceClass (fun _ _ => IsTraceClass.add) isTraceClass_zero h

theorem IsTraceClass.comp_comp {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] K)
    (A' : K →L[ℂ] H) : IsTraceClass (A ∘L T ∘L A') := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have : A ∘L (∑ i, B i ∘L C i) ∘L A' = ∑ i, (A ∘L B i) ∘L (C i ∘L A') := by
    ext x; simp
  rw [this]
  exact isTraceClass_sum _ fun i _ => ((hB i).comp_left A).isTraceClass_comp ((hC i).comp_right A')

theorem IsTraceClass.comp_left {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] H) :
    IsTraceClass (A ∘L T) := by simpa using h.comp_comp A (ContinuousLinearMap.id ℂ H)

theorem IsTraceClass.comp_right {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] H) :
    IsTraceClass (T ∘L A) := by simpa using h.comp_comp (ContinuousLinearMap.id ℂ H) A

theorem IsTraceClass.smul {T : H →L[ℂ] H} (h : IsTraceClass T) (c : ℂ) : IsTraceClass (c • T) := by
  simpa using h.comp_left (c • ContinuousLinearMap.id ℂ H)

theorem IsTraceClass.adjoint {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsTraceClass (adjoint T) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  exact ⟨n, fun i => ContinuousLinearMap.adjoint (C i), fun i => ContinuousLinearMap.adjoint (B i),
    fun i => (hC i).adjoint, fun i => (hB i).adjoint, by simp [map_sum]⟩

theorem IsTraceClass.isHilbertSchmidt {T : H →L[ℂ] H} (h : IsTraceClass T) :
    IsHilbertSchmidt T := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  exact Finset.sum_induction _ IsHilbertSchmidt (fun _ _ => IsHilbertSchmidt.add)
    isHilbertSchmidt_zero fun i _ => (hC i).comp_left _

@[simp] theorem trace_zero : trace (0 : H →L[ℂ] H) = 0 := by simp [trace]

theorem trace_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    trace (S + T) = trace S + trace T := by
  have := (hS.hasSum_trace (stdBasis H)).add (hT.hasSum_trace (stdBasis H))
  simpa only [trace, add_apply, inner_add_right] using this.tsum_eq

theorem trace_sum {α : Type*} (s : Finset α) {T : α → (H →L[ℂ] H)}
    (h : ∀ a ∈ s, IsTraceClass (T a)) : trace (∑ a ∈ s, T a) = ∑ a ∈ s, trace (T a) := by
  have := hasSum_sum fun a (ha : a ∈ s) => (h a ha).hasSum_trace (stdBasis H)
  simpa only [trace, ContinuousLinearMap.sum_apply, inner_sum] using this.tsum_eq

theorem trace_smul (c : ℂ) (T : H →L[ℂ] H) : trace (c • T) = c * trace T := by
  simp [trace, inner_smul_right, tsum_mul_left]

theorem IsTraceClass.trace_comp_comp {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H →L[ℂ] K)
    (A' : K →L[ℂ] H) : trace (A ∘L T ∘L A') = trace (T ∘L A' ∘L A) := by
  obtain ⟨n, B, C, hB, hC, rfl⟩ := h
  have h1 : A ∘L (∑ i, B i ∘L C i) ∘L A' = ∑ i, (A ∘L B i) ∘L (C i ∘L A') := by
    ext x; simp
  have h2 : (∑ i, B i ∘L C i) ∘L A' ∘L A = ∑ i, B i ∘L (C i ∘L A' ∘L A) := by
    ext x; simp
  rw [h1, h2, trace_sum _ fun i _ => ((hB i).comp_left A).isTraceClass_comp ((hC i).comp_right A'),
    trace_sum _ fun i _ => (hB i).isTraceClass_comp ((hC i).comp_right _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_comp_comm ((hB i).comp_left A) ((hC i).comp_right A'),
    trace_comp_comm (hB i) ((hC i).comp_right _)]
  rfl

theorem IsTraceClass.trace_conj {T : H →L[ℂ] H} (h : IsTraceClass T) (A : H ≃L[ℂ] K) :
    trace ((A : H →L[ℂ] K) ∘L T ∘L (A.symm : K →L[ℂ] H)) = trace T := by
  rw [h.trace_comp_comp]
  congr 1
  ext x; simp

theorem isTraceClass_iff_abs (e : HilbertBasis ι ℂ H) {T : H →L[ℂ] H} :
    IsTraceClass T ↔ Summable fun i => ⟪e i, CFC.abs T (e i)⟫_ℂ := by
  have hn : ∀ x, ‖CFC.abs T x‖ = ‖T x‖ := norm_sqrt_apply T
  constructor
  · intro h
    obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (hn x).le
    rw [← hU]
    exact ((h.comp_left U).hasSum_trace e).summable
  · intro h
    obtain ⟨U, hU⟩ := exists_comp_eq_of_norm_le fun x => (hn x).ge
    set A : H →L[ℂ] H := CFC.sqrt (CFC.abs T)
    have hA : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)
    have h2 : A ∘L A = CFC.abs T := CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)
    have hHS : IsHilbertSchmidt A := by
      rw [isHilbertSchmidt_iff e]
      refine h.norm.congr fun i => ?_
      rw [← h2, comp_apply, ← adjoint_inner_left, hA.adjoint_eq, inner_self_eq_norm_sq_to_K]
      simp
    rw [← hU, ← h2]
    exact (hHS.isTraceClass_comp hHS).comp_left U

theorem isTraceClass_of_finiteDimensional [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    IsTraceClass T := by
  simpa using (isHilbertSchmidt_of_finiteDimensional T).isTraceClass_comp
    (isHilbertSchmidt_of_finiteDimensional (ContinuousLinearMap.id ℂ H))

theorem trace_eq_linearMap_trace [FiniteDimensional ℂ H] (T : H →L[ℂ] H) :
    trace T = LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  let b := stdOrthonormalBasis ℂ H
  rw [LinearMap.trace_eq_sum_inner _ b,
    ← ((isTraceClass_of_finiteDimensional T).hasSum_trace b.toHilbertBasis).tsum_eq, tsum_fintype]
  simp

example (n : ℕ) : HasTrace (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n))) n :=
  ⟨isTraceClass_of_finiteDimensional _, by simp [trace_eq_linearMap_trace]⟩

example : trace (Complex.I • ContinuousLinearMap.id ℂ ℂ) = Complex.I := by
  simp [trace_smul, trace_eq_linearMap_trace]

end Hilbert


end GlobalTheory.OpTrace
end


noncomputable section
open ContinuousLinearMap GlobalTheory.OpTrace
namespace GeometricTrace
variable {H Q : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- Quotient lifting: the two identities are application hypotheses, not the target theorem. -/
theorem projection_factorization
    (A P : H →L[ℂ] H) (q : H →L[ℂ] Q) (j : Q →L[ℂ] H) (B : Q →L[ℂ] Q)
    (hP : j ∘L q = P) (hdesc : q ∘L A = B ∘L q) :
    P ∘L A = j ∘L B ∘L q := by
  rw [← hP, ContinuousLinearMap.comp_assoc, hdesc]

/-- A proved implication. Constructing B and establishing its trace class remain separate. -/
theorem projection_trace_transfer
    (A P : H →L[ℂ] H) (q : H →L[ℂ] Q) (j : Q →L[ℂ] H) (B : Q →L[ℂ] Q)
    (hP : j ∘L q = P) (hdesc : q ∘L A = B ∘L q)
    (hqj : q ∘L j = ContinuousLinearMap.id ℂ Q) (hB : IsTraceClass B) :
    IsTraceClass (P ∘L A) ∧ trace (P ∘L A) = trace B := by
  rw [projection_factorization A P q j B hP hdesc]
  refine ⟨hB.comp_comp j q, ?_⟩
  rw [hB.trace_comp_comp, hqj]
  simp
end GeometricTrace
#print axioms GeometricTrace.projection_trace_transfer

/- Post-derivation peer adaptation: F/ProjectionBridge.lean. This supplies the
 genuine orthogonal-projection identity alongside the trace transfer above. -/
namespace GeometricTrace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem spectral_compression_of_invariant
    (V : Submodule ℂ H) [CompleteSpace V] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ V, A x ∈ V) :
    (1 - V.starProjection) ∘L A ∘L (1 - V.starProjection) =
      (1 - V.starProjection) ∘L A := by
  ext x
  have h : V.starProjection (A (V.starProjection x)) = A (V.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hA _ (V.starProjection_apply_mem x))
  change A (x - V.starProjection x) -
      V.starProjection (A (x - V.starProjection x)) =
    A x - V.starProjection (A x)
  rw [map_sub, map_sub, h]
  abel

theorem spectral_kills_geometric
    (V : Submodule ℂ H) [CompleteSpace V] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ V, A x ∈ V) :
    (1 - V.starProjection) ∘L A ∘L V.starProjection = 0 := by
  ext x
  have h : V.starProjection (A (V.starProjection x)) = A (V.starProjection x) :=
    Submodule.starProjection_eq_self_iff.mpr
      (hA _ (V.starProjection_apply_mem x))
  change A (V.starProjection x) - V.starProjection (A (V.starProjection x)) = 0
  rw [h, sub_self]

end GeometricTrace

#print axioms GeometricTrace.spectral_compression_of_invariant
#print axioms GeometricTrace.spectral_kills_geometric


namespace GeometricTraceR3
open ContinuousLinearMap GlobalTheory.OpTrace
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option linter.unusedSectionVars false

def spectralToPerp (M : Submodule ℂ H) [CompleteSpace M] : H →L[ℂ] Mᗮ :=
  (ContinuousLinearMap.id ℂ H - M.starProjection).codRestrict Mᗮ
    (fun x => M.sub_starProjection_mem_orthogonal x)

/-- Actual orthogonal compression. Trace class is required only for the explicitly
constructed compressed convolution, and is not asserted for the arithmetic application. -/
theorem actual_geometric_trace_transfer
    (M : Submodule ℂ H) [CompleteSpace M] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ M, A x ∈ M)
    (hB : IsTraceClass ((spectralToPerp M).comp (A.comp Mᗮ.subtypeL))) :
    IsTraceClass ((ContinuousLinearMap.id ℂ H - M.starProjection).comp A) ∧
    trace ((ContinuousLinearMap.id ℂ H - M.starProjection).comp A) =
      trace ((spectralToPerp M).comp (A.comp Mᗮ.subtypeL)) := by
  let q := spectralToPerp M
  let j := Mᗮ.subtypeL
  let B := q.comp (A.comp j)
  have hP : j.comp q = ContinuousLinearMap.id ℂ H - M.starProjection := by
    ext x
    rfl
  have hqj : q.comp j = ContinuousLinearMap.id ℂ Mᗮ := by
    ext x
    change (x : H) - M.starProjection (x : H) = (x : H)
    rw [M.starProjection_apply_eq_zero_iff.mpr x.property, sub_zero]
  have hd : q.comp A = B.comp q := by
    ext x
    change A x - M.starProjection (A x) =
      A (x - M.starProjection x) - M.starProjection (A (x - M.starProjection x))
    have hm : M.starProjection (A (M.starProjection x)) = A (M.starProjection x) :=
      M.starProjection_eq_self_iff.mpr (hA _ (M.starProjection_apply_mem x))
    rw [map_sub, map_sub, hm]
    abel
  exact GeometricTrace.projection_trace_transfer A _ q j B hP hd hqj hB
end
end GeometricTraceR3
#print axioms GeometricTraceR3.actual_geometric_trace_transfer
