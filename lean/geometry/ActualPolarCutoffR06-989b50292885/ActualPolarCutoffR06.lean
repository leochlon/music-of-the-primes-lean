-- Extracted from original ALPO IsHilbertSchmidtOfFiniteDimensional.lean, Hilbert section only.
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
open ContinuousLinearMap Filter
open scoped Topology InnerProductSpace
namespace GeometricTraceRound4
open GlobalTheory.OpTrace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {α : Type*} {F : Filter α}

/-- Uniformly bounded strong cutoffs preserve the trace limit of a product
of Hilbert--Schmidt operators, for the actual left-cutoff order. -/
theorem tendsto_trace_left_hs
    {A B : H →L[ℂ] H} (hA : IsHilbertSchmidt A) (hB : IsHilbertSchmidt B)
    (M : α → H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a x, ‖M a x‖ ≤ C * ‖x‖)
    (hstrong : ∀ x, Tendsto (fun a => M a x) F (𝓝 x)) :
    Tendsto (fun a => trace ((M a).comp (A.comp B))) F (𝓝 (trace (A.comp B))) := by
  let e := stdBasis H
  have hrepr (U : H →L[ℂ] H) :
      trace (U.comp (A.comp B)) =
        ∑' i, ⟪adjoint B (e i), U (A (e i))⟫_ℂ := by
    have heq : U.comp (A.comp B) = (U.comp A).comp B := rfl
    rw [heq, trace_comp_comm (hA.comp_left U) hB]
    simp only [trace, comp_apply, adjoint_inner_left, e]
  have htarget : trace (A.comp B) =
      ∑' i, ⟪adjoint B (e i), A (e i)⟫_ℂ := by
    simpa using hrepr (ContinuousLinearMap.id ℂ H)
  simp_rw [hrepr]
  rw [htarget]
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun i => C * (‖adjoint B (e i)‖ ^ 2 + ‖A (e i)‖ ^ 2))
  · exact ((hB.adjoint.hasSum e).summable.add (hA.hasSum e).summable).mul_left C
  · intro i
    exact tendsto_const_nhds.inner (hstrong (A (e i)))
  · apply Eventually.of_forall
    intro a i
    have hp : ‖adjoint B (e i)‖ * ‖A (e i)‖ ≤
        ‖adjoint B (e i)‖ ^ 2 + ‖A (e i)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖adjoint B (e i)‖ - ‖A (e i)‖)]
    calc
      ‖⟪adjoint B (e i), M a (A (e i))⟫_ℂ‖
          ≤ ‖adjoint B (e i)‖ * ‖M a (A (e i))‖ := norm_inner_le_norm _ _
      _ ≤ ‖adjoint B (e i)‖ * (C * ‖A (e i)‖) :=
        mul_le_mul_of_nonneg_left (hbound a _) (norm_nonneg _)
      _ = C * (‖adjoint B (e i)‖ * ‖A (e i)‖) := by ring
      _ ≤ C * (‖adjoint B (e i)‖ ^ 2 + ‖A (e i)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hp hC

/-- The generic cutoff bridge assumes trace class of the actual T.
It neither assumes nor asserts geometric nuclearity. -/
theorem tendsto_trace_left
    {T : H →L[ℂ] H} (hT : IsTraceClass T)
    (M : α → H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ a x, ‖M a x‖ ≤ C * ‖x‖)
    (hstrong : ∀ x, Tendsto (fun a => M a x) F (𝓝 x)) :
    Tendsto (fun a => trace ((M a).comp T)) F (𝓝 (trace T)) := by
  obtain ⟨n, A, B, hA, hB, rfl⟩ := hT
  have heq (a : α) : (M a).comp (∑ i, (A i).comp (B i)) =
      ∑ i, (M a).comp ((A i).comp (B i)) := by
    ext x
    simp
  simp_rw [heq, trace_sum _ (fun i _ => ((hA i).isTraceClass_comp (hB i)).comp_left _)]
  rw [trace_sum _ (fun i _ => (hA i).isTraceClass_comp (hB i))]
  exact tendsto_finset_sum _ (fun i _ => tendsto_trace_left_hs (hA i) (hB i)
    M C hC hbound hstrong)
end GeometricTraceRound4
end
#print axioms GeometricTraceRound4.tendsto_trace_left_hs
#print axioms GeometricTraceRound4.tendsto_trace_left

namespace ActualPolarCutoffR06
noncomputable section
open ContinuousLinearMap GlobalTheory.OpTrace Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The inverse Gram map of the actual polar graph changes the compressed
cutoff by an explicitly finite-rank term. See APPLICATION_R06.md. -/
theorem effective_cutoff (C D R : H →L[ℂ] H)
    (hR : (ContinuousLinearMap.id ℂ H + D).comp R = ContinuousLinearMap.id ℂ H) :
    (C + D).comp R = C + (ContinuousLinearMap.id ℂ H - C).comp (D.comp R) := by
  ext x
  have hx : R x + D (R x) = x := DFunLike.congr_fun hR x
  change C (R x) + D (R x) = C x + (D (R x) - C (D (R x)))
  calc
    C (R x) + D (R x) = C (R x + D (R x)) + (D (R x) - C (D (R x))) := by
      rw [map_add]
      abel
    _ = _ := by rw [hx]

theorem trace_cyclic {F : H →L[ℂ] H} (hF : IsTraceClass F) (T : H →L[ℂ] H) :
    trace (T.comp F) = trace (F.comp T) := by
  simpa using hF.trace_comp_comp T (ContinuousLinearMap.id ℂ H)

/-- No trace-class hypothesis is imposed on the spectral convolution T.
Only the constructed finite-rank polar correction F needs trace class. -/
theorem trace_defect {F : H →L[ℂ] H} (hF : IsTraceClass F)
    (T C : H →L[ℂ] H) :
    trace (T.comp ((ContinuousLinearMap.id ℂ H - C).comp F)) =
      trace (F.comp T) - trace (C.comp (F.comp T)) := by
  have hFT := hF.comp_right T
  have hcyc : trace (T.comp ((ContinuousLinearMap.id ℂ H - C).comp F)) =
      trace ((ContinuousLinearMap.id ℂ H - C).comp (F.comp T)) := by
    calc
      _ = trace (F.comp (T.comp (ContinuousLinearMap.id ℂ H - C))) := by
        simpa only [comp_assoc] using trace_cyclic hF (T.comp (ContinuousLinearMap.id ℂ H - C))
      _ = _ := by
        simpa only [comp_assoc] using
          (trace_cyclic hFT (ContinuousLinearMap.id ℂ H - C)).symm
  rw [hcyc]
  have he : (ContinuousLinearMap.id ℂ H - C).comp (F.comp T) =
      F.comp T + (-1 : ℂ) • (C.comp (F.comp T)) := by
    ext x
    simp [sub_eq_add_neg]
  rw [he, trace_add hFT ((hFT.comp_left C).smul (-1)), trace_smul]
  ring

theorem tendsto_trace_defect {ι : Type*} {l : Filter ι}
    {F : H →L[ℂ] H} (hF : IsTraceClass F) (T : H →L[ℂ] H)
    (C : ι → H →L[ℂ] H) (b : ℝ) (hb : 0 ≤ b)
    (hbound : ∀ i x, ‖C i x‖ ≤ b * ‖x‖)
    (hstrong : ∀ x, Tendsto (fun i => C i x) l (𝓝 x)) :
    Tendsto (fun i => trace (T.comp ((ContinuousLinearMap.id ℂ H - C i).comp F)))
      l (𝓝 0) := by
  simp_rw [trace_defect hF]
  have ht := GeometricTraceRound4.tendsto_trace_left (hF.comp_right T)
    C b hb hbound hstrong
  have hc : Tendsto (fun _ : ι => trace (F.comp T)) l (𝓝 (trace (F.comp T))) :=
    tendsto_const_nhds
  simpa using hc.sub ht

end
end ActualPolarCutoffR06
#print axioms ActualPolarCutoffR06.effective_cutoff
#print axioms ActualPolarCutoffR06.trace_defect
#print axioms ActualPolarCutoffR06.tendsto_trace_defect
