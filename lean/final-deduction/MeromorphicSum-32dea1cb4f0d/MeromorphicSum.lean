import Mathlib

namespace MasulloGRH.ConditionalMoment

/-- C.SPECTRAL.TAIL: discharges the uniform large-zero kernel estimate for
the proposed first-moment Laplace tests. This is a scalar inequality, not a
zero-counting theorem or an identification of a Hecke zero divisor. -/
theorem square_resolvent_tail (z w : ℂ) (R : ℝ) (hR : 0 < R)
    (hz : ‖z‖ ≤ R) (hw : 2 * R ≤ ‖w‖) :
    ‖((z - w)⁻¹) ^ 2‖ ≤ 4 / ‖w‖ ^ 2 := by
  have hn : 0 < ‖w‖ := by linarith
  have hd : ‖w‖ / 2 ≤ ‖z - w‖ := by
    have h := norm_sub_norm_le w z
    rw [norm_sub_rev] at h
    linarith
  have hdpos : 0 < ‖z - w‖ := lt_of_lt_of_le (by positivity) hd
  rw [norm_pow, norm_inv, inv_pow, inv_eq_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hdpos) (sq_pos_of_pos hn)).2
  have hm := mul_nonneg (sub_nonneg.mpr hd)
    (show 0 ≤ ‖z - w‖ + ‖w‖ / 2 by positivity)
  nlinarith

#check square_resolvent_tail
#print axioms square_resolvent_tail

end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open Filter

/-- C.SPECTRAL.NORMAL: the inverse-square weighted counting premise implies
absolute summability and uniform convergence of the large-zero resolvent tail
on a closed disc. This proves the analytic M-test step only. The counting
premise and identification with the actual Hecke divisor remain obligations. -/
theorem weighted_square_resolvent_tail_uniform
    {ι : Type*} (w m : ι → ℂ) (R : ℝ) (hR : 0 < R)
    (hw : ∀ i, 2 * R ≤ ‖w i‖)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    (∀ z : ℂ, ‖z‖ ≤ R →
      Summable (fun i => ‖m i * ((z - w i)⁻¹) ^ 2‖)) ∧
    TendstoUniformlyOn
      (fun S : Finset ι => fun z : ℂ => ∑ i ∈ S, m i * ((z - w i)⁻¹) ^ 2)
      (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹) ^ 2)
      atTop {z : ℂ | ‖z‖ ≤ R} := by
  have hbound : ∀ i (z : ℂ), ‖z‖ ≤ R →
      ‖m i * ((z - w i)⁻¹) ^ 2‖ ≤ 4 * (‖m i‖ / ‖w i‖ ^ 2) := by
    intro i z hz
    rw [norm_mul]
    calc
      ‖m i‖ * ‖((z - w i)⁻¹) ^ 2‖ ≤ ‖m i‖ * (4 / ‖w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (square_resolvent_tail z (w i) R hR hz (hw i)) (norm_nonneg _)
      _ = 4 * (‖m i‖ / ‖w i‖ ^ 2) := by ring
  constructor
  · intro z hz
    exact (hweight.mul_left 4).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun i => hbound i z hz)
  · exact tendstoUniformlyOn_tsum (hweight.mul_left 4) hbound

#check weighted_square_resolvent_tail_uniform
#print axioms weighted_square_resolvent_tail_uniform
end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open Filter Topology Metric

/-- C.CONTINUE.TAIL: proves holomorphy of the large-zero squared-resolvent
tail from the explicit inverse-square summability premise. The genuine Hecke
divisor and its summability still have to be supplied; neither is postulated
as part of the arithmetic trace identity. -/
theorem weighted_square_resolvent_tail_holomorphic
    {ι : Type*} (w m : ι → ℂ) (R : ℝ) (hR : 0 < R)
    (hw : ∀ i, 2 * R ≤ ‖w i‖)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹) ^ 2)
      {z : ℂ | ‖z‖ < R} := by
  have hU : IsOpen {z : ℂ | ‖z‖ < R} :=
    isOpen_lt continuous_norm continuous_const
  refine Complex.differentiableOn_tsum_of_summable_norm
    (hweight.mul_left 4) (fun i => ?_) hU (fun i z hz => ?_)
  · intro z hz
    have hn : ‖z‖ < ‖w i‖ := by
      have hz' : ‖z‖ < R := hz
      linarith [hw i]
    have hne : z - w i ≠ 0 :=
      sub_ne_zero.mpr (fun he => (ne_of_lt hn) (congrArg norm he))
    exact ((((differentiableAt_id.sub_const (w i)).inv hne).pow 2).const_mul
      (m i)).differentiableWithinAt
  · rw [norm_mul]
    calc
      ‖m i‖ * ‖((z - w i)⁻¹) ^ 2‖ ≤ ‖m i‖ * (4 / ‖w i‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (square_resolvent_tail z (w i) R hR (le_of_lt hz) (hw i))
          (norm_nonneg _)
      _ = 4 * (‖m i‖ / ‖w i‖ ^ 2) := by ring

/-- C.COUNT.LOCAL: the compact-finiteness premise for a genuine completed
zero divisor follows from entire regularization and one nonzero value.
Those arithmetic inputs remain separate obligations. Port of the finite-zero
argument inspected in the pinned Fermat Hadamard source, using only Mathlib. -/
theorem entire_zeros_finite_on_closedBall (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (z₀ : ℂ) (hz₀ : f z₀ ≠ 0) (R : ℝ) :
    ({s : ℂ | f s = 0} ∩ closedBall 0 R).Finite := by
  by_contra h
  obtain ⟨w, _, hAcc⟩ :=
    Set.Infinite.exists_accPt_of_subset_isCompact h (isCompact_closedBall 0 R)
      Set.inter_subset_right
  have hfreq : ∃ᶠ y in 𝓝[≠] w, f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hAcc).mono fun _ hy => hy.1
  have hAn : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  exact hz₀ <| hAn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (Set.mem_univ w) hfreq (Set.mem_univ z₀)

/-- C.COUNT.INDEX: the genuine zero set is countable once the entire,
nonzero regularization has been constructed. No enumeration is stipulated. -/
theorem entire_zeros_countable (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (z₀ : ℂ) (hz₀ : f z₀ ≠ 0) :
    {s : ℂ | f s = 0}.Countable := by
  have hcover : {s : ℂ | f s = 0} ⊆
      ⋃ n : ℕ, ({s : ℂ | f s = 0} ∩ closedBall 0 (n : ℝ)) := by
    intro s hs
    exact Set.mem_iUnion.mpr
      ⟨⌈‖s‖⌉₊, hs, mem_closedBall_zero_iff.mpr (Nat.le_ceil _)⟩
  exact Set.Countable.mono hcover <| Set.countable_iUnion fun n =>
    (entire_zeros_finite_on_closedBall f hf z₀ hz₀ n).countable

#check weighted_square_resolvent_tail_holomorphic
#print axioms weighted_square_resolvent_tail_holomorphic
#check entire_zeros_finite_on_closedBall
#print axioms entire_zeros_finite_on_closedBall
#check entire_zeros_countable
#print axioms entire_zeros_countable
end MasulloGRH.ConditionalMoment

namespace MasulloGRH.ConditionalMoment
open Filter Topology

/-- C.CONTINUE.SUM: compact-finite locations and the explicit weighted
inverse-square bound give summability of the full resolvent, including at
locations themselves under Lean's totalized inverse. Genuine Hecke counting
and arithmetic identification remain separate obligations. -/
theorem weighted_square_resolvent_summable
    {ι : Type*} (w m : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) (z : ℂ) :
    Summable (fun i => m i * ((z - w i)⁻¹)^2) := by
  classical
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let S : Finset ι := (hfinite (2 * R)).toFinset
  have hw : ∀ i : {i // i ∉ S}, 2 * R ≤ ‖w i‖ := by
    intro i
    have hn : ¬ ‖w i.val‖ < 2 * R := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using i.property
    exact le_of_not_gt hn
  have ht := (weighted_square_resolvent_tail_uniform
    (fun i : {i // i ∉ S} => w i) (fun i => m i) R hR hw
    (hweight.subtype _)).1 z (by dsimp [R]; linarith)
  exact (summable_subtype_and_compl (s := (S : Set ι))).mp
    ⟨(hasSum_fintype _).summable, ht.of_norm⟩

/-- C.CONTINUE.MEROMORPHIC: constructs global meromorphy from compact
finiteness and the explicit weighted estimate by a proved finite-head/tail
split. No meromorphy or convergence of the sum is assumed. This is an
analytic auxiliary, not the arithmetic trace-to-Hecke-GRH theorem. -/
theorem weighted_square_resolvent_meromorphic
    {ι : Type*} (w m : ι → ℂ)
    (hfinite : ∀ R : ℝ, {i | ‖w i‖ < R}.Finite)
    (hweight : Summable (fun i => ‖m i‖ / ‖w i‖ ^ 2)) :
    MeromorphicOn (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹)^2) Set.univ := by
  classical
  intro p _
  let R : ℝ := ‖p‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let S : Finset ι := (hfinite (2 * R)).toFinset
  have hw : ∀ i : {i // i ∉ S}, 2 * R ≤ ‖w i‖ := by
    intro i
    have hn : ¬ ‖w i.val‖ < 2 * R := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using i.property
    exact le_of_not_gt hn
  have ht := weighted_square_resolvent_tail_holomorphic
    (fun i : {i // i ∉ S} => w i) (fun i => m i) R hR hw
    (hweight.subtype _)
  have hh : MeromorphicAt (fun z : ℂ => ∑ j ∈ S, m j * ((z - w j)⁻¹)^2) p := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      simp only [Finset.sum_insert hj]
      exact ((analyticAt_const (v := m j)).meromorphicAt.mul
        (((analyticAt_id.sub (analyticAt_const (v := w j))).meromorphicAt.inv).pow 2)).add ih
  have he : (fun z : ℂ => ∑' i, m i * ((z - w i)⁻¹)^2) =
      (fun z : ℂ => (∑ j ∈ S, m j * ((z - w j)⁻¹)^2) +
        ∑' i : {i // i ∉ S}, m i * ((z - w i)⁻¹)^2) := by
    funext z
    exact ((weighted_square_resolvent_summable w m hfinite hweight z).sum_add_tsum_subtype_compl S).symm
  rw [he]
  exact hh.add (ht.analyticAt
    ((isOpen_lt continuous_norm continuous_const).mem_nhds
      (show ‖p‖ < R by dsimp [R]; linarith))).meromorphicAt

#check weighted_square_resolvent_summable
#print axioms weighted_square_resolvent_summable
#check weighted_square_resolvent_meromorphic
#print axioms weighted_square_resolvent_meromorphic
end MasulloGRH.ConditionalMoment
