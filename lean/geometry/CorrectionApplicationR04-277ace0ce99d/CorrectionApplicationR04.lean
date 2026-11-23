import Mathlib

/-! Conditional trace identities and the Riemann-hypothesis implication. Arithmetic data, trace identities, regularized limits and correction control remain explicit hypotheses. -/
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

open scoped InnerProductSpace
namespace Masullo.NuclearDiagonal

theorem rankOne_diagonal_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : ι → H) (hb : Orthonormal ℂ b) (u v : H) :
    Summable (fun i => ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ∧
    (∑' i, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
  have key (S : Finset ι) :
      ∑ i ∈ S, ‖⟪u, b i⟫_ℂ * ⟪b i, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := by
    have hn (i : ι) : ‖⟪u, b i⟫_ℂ‖ = ‖⟪b i, u⟫_ℂ‖ := norm_inner_symm _ _
    simp only [norm_mul, hn]
    calc
      _ ≤ Real.sqrt (∑ i ∈ S, ‖⟪b i, u⟫_ℂ‖ ^ 2) *
          Real.sqrt (∑ i ∈ S, ‖⟪b i, v⟫_ℂ‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (‖u‖ ^ 2) * Real.sqrt (‖v‖ ^ 2) :=
        mul_le_mul (Real.sqrt_le_sqrt (hb.sum_inner_products_le u))
          (Real.sqrt_le_sqrt (hb.sum_inner_products_le v))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = ‖u‖ * ‖v‖ := by simp
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) key,
    le_of_tendsto (summable_of_sum_le (fun _ => norm_nonneg _) key).hasSum
      (Filter.Eventually.of_forall key)⟩

theorem nuclear_diagonal_interchange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (u v : ℕ → H)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖)) :
    Summable (fun p : ℕ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) ∧
    (∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) =
      ∑' n, ⟪u n, v n⟫_ℂ := by
  have hf (n : ℕ) := rankOne_diagonal_bound b b.orthonormal (u n) (v n)
  have hs : Summable (fun n => ∑' i, ‖⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ‖) :=
    Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
      (fun n => (hf n).2) hc
  have hp : Summable (fun p : ℕ × ι => ‖⟪u p.1, b p.2⟫_ℂ * ⟪b p.2, v p.1⟫_ℂ‖) := by
    exact (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      ⟨fun n => (hf n).1, hs⟩
  refine ⟨hp, ?_⟩
  calc
    _ = ∑' n, ∑' i, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ := hp.of_norm.tsum_comm
    _ = _ := tsum_congr (fun n => (b.hasSum_inner_mul_inner (u n) (v n)).tsum_eq)

theorem nuclear_operator_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    (∑' i, ⟪b i, T (b i)⟫_ℂ) = ∑' n, ⟪u n, v n⟫_ℂ := by
  have hd (i : ι) :
      (∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [inner_smul_right] using hh.tsum_eq
  calc
    _ = ∑' i, ∑' n, ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ :=
      tsum_congr (fun i => (hd i).symm)
    _ = _ := (nuclear_diagonal_interchange b u v hc).2

end Masullo.NuclearDiagonal

set_option maxHeartbeats 400000
namespace Masullo.NuclearSeries
open scoped InnerProductSpace

/-- Absolute convergence is derived from the existing operator expansion.
Both summable costs and the genuine HasSum equation are indispensable. -/
theorem nuclear_diagonal_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    Summable (fun i => ‖⟪b i, T (b i)⟫_ℂ‖) := by
  let c : ℕ → ι → ℂ := fun n i => ⟪u n, b i⟫_ℂ * ⟪b i, v n⟫_ℂ
  have hp : Summable (fun p : ℕ × ι => ‖c p.1 p.2‖) :=
    (Masullo.NuclearDiagonal.nuclear_diagonal_interchange b u v hc).1
  have hs : Summable (fun p : ι × ℕ => ‖c p.2 p.1‖) := hp.prod_symm
  have hr : (∀ i, Summable (fun n => ‖c n i‖)) ∧
      Summable (fun i => ∑' n, ‖c n i‖) :=
    (summable_prod_of_nonneg (fun p : ι × ℕ => norm_nonneg (c p.2 p.1))).1 hs
  have hd (i : ι) : (∑' n, c n i) = ⟪b i, T (b i)⟫_ℂ := by
    have hh := (hT (b i)).map (innerSL ℂ (b i)).toAddMonoidHom
      (innerSL ℂ (b i)).continuous
    simpa [c, inner_smul_right] using hh.tsum_eq
  have hbound (i : ι) : ‖⟪b i, T (b i)⟫_ℂ‖ ≤ ∑' n, ‖c n i‖ := by
    calc
      ‖⟪b i, T (b i)⟫_ℂ‖ = ‖∑' n, c n i‖ := congrArg norm (hd i).symm
      _ ≤ ∑' n, ‖c n i‖ := norm_tsum_le_tsum_norm (hr.1 i)
  exact Summable.of_nonneg_of_le
    (fun i => norm_nonneg (⟪b i, T (b i)⟫_ℂ)) hbound hr.2

/-- The native application sets T = P.comp (A h). The theorem does not
assume summability of a prescribed zero sum or reverse the operator order. -/
theorem nuclear_diagonal_hasSum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (b : HilbertBasis ι ℂ H) (T : H →L[ℂ] H)
    (u v : ℕ → H) (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)) :
    HasSum (fun i => ⟪b i, T (b i)⟫_ℂ) (∑' n, ⟪u n, v n⟫_ℂ) := by
  have hs := (nuclear_diagonal_summable b T u v hc hT).of_norm.hasSum
  rwa [Masullo.NuclearDiagonal.nuclear_operator_diagonal b T u v hc hT] at hs

end Masullo.NuclearSeries

namespace Masullo.TateDivisibility
open Filter Topology
theorem local_tate_derivative_zero (L D Z : ℂ → ℂ) (rho : ℂ) (m : ℕ)
    (hL : AnalyticAt ℂ L rho) (hD : AnalyticAt ℂ D rho)
    (hfinite : analyticOrderAt L rho ≠ ⊤)
    (hm : m < analyticOrderNatAt L rho)
    (hdiv : Z =ᶠ[𝓝 rho] (fun z => L z * D z)) :
    iteratedDeriv m Z rho = 0 := by
  rw [hdiv.iteratedDeriv_eq m]
  have hle : (analyticOrderNatAt L rho : ℕ∞) ≤
      analyticOrderAt (fun z => L z * D z) rho := by
    change (analyticOrderNatAt L rho : ℕ∞) ≤ analyticOrderAt (L * D) rho
    rw [analyticOrderAt_mul hL hD, Nat.cast_analyticOrderNatAt hfinite]
    exact le_add_of_nonneg_right (zero_le _)
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hL.mul hD)).mp hle m hm

end Masullo.TateDivisibility

namespace Masullo.GramProjection
open scoped InnerProductSpace Matrix BigOperators
noncomputable instance finiteSpan_finiteDim
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} [Fintype ι] (r : ι → H) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range r)) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range r)

/-- Explicit inverse-Gram coefficients determine the genuine orthogonal
projection, with the complex inner product linear in the second argument. -/
theorem inverseGram_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → H)
    (hG : IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j)))) (v : H) :
    (Submodule.span ℂ (Set.range r)).starProjection v =
      ∑ j, (((fun i j => inner ℂ (r i) (r j)) : Matrix ι ι ℂ)⁻¹ *ᵥ
        (fun i => inner ℂ (r i) v)) j • r j := by
  classical
  let E := Submodule.span ℂ (Set.range r)
  let G : Matrix ι ι ℂ := fun i j => inner ℂ (r i) (r j)
  let c := G⁻¹ *ᵥ (fun i => inner ℂ (r i) v)
  let p := ∑ j, c j • r j
  have hp : p ∈ E := by
    apply Submodule.sum_mem
    intro j hj
    exact E.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
  have heq : G *ᵥ c = (fun i => inner ℂ (r i) v) := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
  have hi : ∀ i, inner ℂ (r i) (v-p) = 0 := by
    intro i
    rw [inner_sub_right]
    apply sub_eq_zero.mpr
    have hh := congrFun heq i
    simpa [p, inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, G, mul_comm] using hh.symm
  have ho : ∀ w ∈ E, inner ℂ w (v-p) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨i, rfl⟩ := hw; exact hi i
    | zero => simp
    | add x y hx hy hpx hpy => simp only [inner_add_left, hpx, hpy, add_zero]
    | smul a x hx hpx => simp only [inner_smul_left, hpx, mul_zero]
  exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp
    (fun w hw => inner_eq_zero_symm.mpr (ho w hw)))

end Masullo.GramProjection

namespace Masullo.ZetaLocalAnalysis

theorem logDeriv_eq_order_div_add_analytic :
    ∀ (f : ℂ → ℂ) (p : ℂ), AnalyticAt ℂ f p → (¬ ∀ᶠ s in 𝓝 p, f s = 0) →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, f s ≠ 0 ∧
        deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  intro f p hf hne
  have htop : analyticOrderAt f p ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact hne
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderNatAt_eq_iff htop (n := analyticOrderNatAt f p)).mp rfl
  set m := analyticOrderNatAt f p with hm
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have h1 : ∀ᶠ s in 𝓝 p, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have h2 : ∀ᶠ s in 𝓝 p, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have h3 := hfg.eventually_nhds
  have h4 : ∀ᶠ s in 𝓝[≠] p, s ≠ p := self_mem_nhdsWithin
  filter_upwards [h4, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3]
    with s hsp hs1 hs2 hs3
  have hsub : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hev : f =ᶠ[𝓝 s] fun z => (z - p) ^ m * g z := by
    filter_upwards [hs3] with z hz
    rw [hz, smul_eq_mul]
  have hfs : f s = (s - p) ^ m * g s := hev.eq_of_nhds
  have hd : HasDerivAt (fun z => (z - p) ^ m * g z)
      ((m : ℂ) * (s - p) ^ (m - 1) * 1 * g s + (s - p) ^ m * deriv g s) s :=
    (((hasDerivAt_id s).sub_const p).pow m).mul hs2.differentiableAt.hasDerivAt
  have hdf : deriv f s = (m : ℂ) * (s - p) ^ (m - 1) * 1 * g s + (s - p) ^ m * deriv g s := by
    rw [hev.deriv_eq, hd.deriv]
  refine ⟨by rw [hfs]; exact mul_ne_zero (pow_ne_zero _ hsub) hs1, ?_⟩
  rw [hdf, hfs]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · rw [h0]; simp
  · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    field_simp
    ring

/-- A nonzero simple-pole coefficient cannot be represented by a continuous germ.
Adapted from Fermat's integer-residue lemma; the coefficient may be complex. -/
theorem pole_coefficient_zero_of_continuous_extension {c p : ℂ} {g : ℂ → ℂ}
    (hg : ContinuousAt g p)
    (heq : ∀ᶠ z in 𝓝[≠] p, c / (z - p) = g z) : c = 0 := by
  have h1 : Tendsto (fun z : ℂ => g z * (z - p)) (𝓝[≠] p)
      (𝓝 (g p * (p - p))) :=
    (hg.tendsto.mono_left nhdsWithin_le_nhds).mul
      ((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds)
  rw [sub_self, mul_zero] at h1
  have h2 : Tendsto (fun _ : ℂ => c) (𝓝[≠] p) (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hzp
    rw [← hz, div_mul_cancel₀ _ (sub_ne_zero.mpr hzp)]
  exact tendsto_nhds_unique tendsto_const_nhds h2

theorem analyticAt_riemannZeta {p : ℂ} (hp : p ≠ 1) :
    AnalyticAt ℂ riemannZeta p := by
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_compl_singleton p hp

/-- Finite order is proved for genuine zeta using analytic continuation on C\{1}
and its known nonzero value at 2. No RH input occurs. -/
theorem riemannZeta_analyticOrder_ne_top {p : ℂ} (hp : p ≠ 1) :
    analyticOrderAt riemannZeta p ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    fun z hz => analyticAt_riemannZeta hz
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
  have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    have hz : analyticOrderAt riemannZeta 2 = 0 :=
      analyticOrderAt_eq_zero.2
        (Or.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num)))
    simp [hz]
  exact han.analyticOrderAt_ne_top_of_isPreconnected hconn
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) hp h2

theorem riemannZeta_order_pos_of_zero {p : ℂ} (hp : p ≠ 1)
    (hz : riemannZeta p = 0) : 0 < analyticOrderNatAt riemannZeta p := by
  have htop := riemannZeta_analyticOrder_ne_top hp
  have hne : analyticOrderAt riemannZeta p ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨analyticAt_riemannZeta hp, hz⟩
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  have hn' : analyticOrderNatAt riemannZeta p = n := by
    simp [analyticOrderNatAt, ← hn]
  rw [hn']
  rcases Nat.eq_zero_or_pos n with h | h
  · exact False.elim (hne (by rw [← hn, h]; rfl))
  · exact h

/-- Exact local zeta linkage: the residue is its actual analytic zero order. -/
theorem riemannZeta_logDeriv_local {p : ℂ} (hp : p ≠ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ z in 𝓝[≠] p,
      riemannZeta z ≠ 0 ∧
      deriv riemannZeta z / riemannZeta z =
        (analyticOrderNatAt riemannZeta p : ℂ) / (z - p) + g z := by
  apply logDeriv_eq_order_div_add_analytic riemannZeta p (analyticAt_riemannZeta hp)
  intro he
  exact riemannZeta_analyticOrder_ne_top hp (analyticOrderAt_eq_top.mpr he)

/-- A genuine zero is incompatible even with a continuous extension of zeta'/zeta.
This is the local contradiction required after, but not in place of, trace analysis. -/
theorem riemannZeta_zero_no_continuous_logDeriv_extension {p : ℂ}
    (hp : p ≠ 1) (hz : riemannZeta p = 0) :
    ¬ ∃ H : ℂ → ℂ, ContinuousAt H p ∧ ∀ᶠ z in 𝓝[≠] p,
      deriv riemannZeta z / riemannZeta z = H z := by
  rintro ⟨H, hH, heq⟩
  obtain ⟨g, hg, hlocal⟩ := riemannZeta_logDeriv_local hp
  have hc : (analyticOrderNatAt riemannZeta p : ℂ) = 0 := by
    apply pole_coefficient_zero_of_continuous_extension (hH.sub hg.continuousAt)
    filter_upwards [heq, hlocal] with z hzH hzg
    rw [hzg.2] at hzH
    exact eq_sub_of_add_eq hzH
  have hn : analyticOrderNatAt riemannZeta p = 0 := by exact_mod_cast hc
  exact (Nat.ne_of_gt (riemannZeta_order_pos_of_zero hp hz)) hn

/-- Differentiating a punctured identity retains the pole and its sign. -/
theorem deriv_logDeriv_riemannZeta_local {p : ℂ} (hp : p ≠ 1) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ z in 𝓝[≠] p,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z =
        -(analyticOrderNatAt riemannZeta p : ℂ) / (z - p)^2 + g z := by
  obtain ⟨g, hg, hlocal⟩ := riemannZeta_logDeriv_local hp
  refine ⟨deriv g, hg.deriv, ?_⟩
  have he : ∀ᶠ z in 𝓝 p, z ≠ p →
      deriv riemannZeta z / riemannZeta z =
        (analyticOrderNatAt riemannZeta p : ℂ) / (z - p) + g z :=
    eventually_nhdsWithin_iff.mp (hlocal.mono fun _ h => h.2)
  filter_upwards [nhdsWithin_le_nhds he.eventually_nhds,
    nhdsWithin_le_nhds hg.eventually_analyticAt, self_mem_nhdsWithin]
    with z hez hgz hzp
  have hez' : (fun w => deriv riemannZeta w / riemannZeta w) =ᶠ[𝓝 z]
      (fun w => (analyticOrderNatAt riemannZeta p : ℂ) / (w-p) + g w) := by
    filter_upwards [hez, (continuousAt_id.eventually_ne hzp)] with w hw hwp
    exact hw hwp
  rw [hez'.deriv_eq]
  have hd := ((hasDerivAt_const z (analyticOrderNatAt riemannZeta p : ℂ)).div
    ((hasDerivAt_id z).sub_const p) (sub_ne_zero.mpr hzp)).add
      hgz.differentiableAt.hasDerivAt
  simpa using hd.deriv

theorem double_pole_coefficient_zero_of_continuous_extension {c p : ℂ} {g : ℂ → ℂ}
    (hg : ContinuousAt g p)
    (heq : ∀ᶠ z in 𝓝[≠] p, c / (z - p)^2 = g z) : c = 0 := by
  have h1 : Tendsto (fun z : ℂ => g z * (z - p)^2) (𝓝[≠] p)
      (𝓝 (g p * (p-p)^2)) :=
    (hg.tendsto.mono_left nhdsWithin_le_nhds).mul
      (((continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds).pow 2)
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero] at h1
  have h2 : Tendsto (fun _ : ℂ => c) (𝓝[≠] p) (𝓝 0) := by
    refine h1.congr' ?_
    filter_upwards [heq, self_mem_nhdsWithin] with z hz hzp
    rw [← hz, div_mul_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr hzp))]
  exact tendsto_nhds_unique tendsto_const_nhds h2

/-- The logged test produces the derivative of the logarithmic derivative.
Its double pole has coefficient minus the actual positive multiplicity. -/
theorem riemannZeta_zero_no_continuous_deriv_logDeriv_extension {p : ℂ}
    (hp : p ≠ 1) (hz : riemannZeta p = 0) :
    ¬ ∃ H : ℂ → ℂ, ContinuousAt H p ∧ ∀ᶠ z in 𝓝[≠] p,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z = H z := by
  rintro ⟨H, hH, heq⟩
  obtain ⟨g, hg, hlocal⟩ := deriv_logDeriv_riemannZeta_local hp
  have hc : -(analyticOrderNatAt riemannZeta p : ℂ) = 0 := by
    apply double_pole_coefficient_zero_of_continuous_extension (hH.sub hg.continuousAt)
    filter_upwards [heq, hlocal] with z hzH hzg
    rw [hzg] at hzH
    exact eq_sub_of_add_eq hzH
  have hn : analyticOrderNatAt riemannZeta p = 0 := by
    exact_mod_cast (neg_eq_zero.mp hc)
  exact (Nat.ne_of_gt (riemannZeta_order_pos_of_zero hp hz)) hn

/-- The genuine functional equation reflects zeros in the open critical strip. -/
theorem riemannZeta_zero_reflect {p : ℂ} (hpos : 0 < p.re) (hlt : p.re < 1)
    (hz : riemannZeta p = 0) : riemannZeta (1-p) = 0 := by
  have hn : ∀ n : ℕ, p ≠ -n := by
    intro n he
    have hr := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.natCast_re] at hr
    have hnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hp : p ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  rw [riemannZeta_one_sub hn hp, hz, mul_zero]

/-- Concrete backwards endpoint: an off-line nontrivial zero supplies a
right-hand genuine zero with a nonremovable logged-trace double pole.
No trace identity, correction vanishing or zero-free region is assumed. -/
theorem off_line_zero_forces_right_double_pole {p : ℂ}
    (hpos : 0 < p.re) (hlt : p.re < 1) (hz : riemannZeta p = 0)
    (hoff : p.re ≠ 1/2) :
    ∃ q : ℂ, 1/2 < q.re ∧ q.re < 1 ∧ riemannZeta q = 0 ∧
      ¬ ∃ H : ℂ → ℂ, ContinuousAt H q ∧ ∀ᶠ z in 𝓝[≠] q,
        deriv (fun w => deriv riemannZeta w / riemannZeta w) z = H z := by
  have make (q : ℂ) (hqr : 1/2 < q.re) (hq1 : q.re < 1)
      (hqz : riemannZeta q = 0) :
      ¬ ∃ H : ℂ → ℂ, ContinuousAt H q ∧ ∀ᶠ z in 𝓝[≠] q,
        deriv (fun w => deriv riemannZeta w / riemannZeta w) z = H z := by
    apply riemannZeta_zero_no_continuous_deriv_logDeriv_extension ?_ hqz
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · have hqr : 1/2 < (1-p).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hq1 : (1-p).re < 1 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hqz := riemannZeta_zero_reflect hpos hlt hz
    exact ⟨1-p, hqr, hq1, hqz, make (1-p) hqr hq1 hqz⟩
  · exact ⟨p, hright, hlt, hz, make p hright hlt hz⟩

/-- The cross-multiplied logged identity is analytic through unknown zeros;
division is used only at points already known to be nonzero. -/
theorem deriv_logDeriv_riemannZeta_eq {p : ℂ} (hp : p ≠ 1)
    (hz : riemannZeta p ≠ 0) :
    deriv (fun w => deriv riemannZeta w / riemannZeta w) p =
      (deriv (deriv riemannZeta) p * riemannZeta p - (deriv riemannZeta p)^2) /
        (riemannZeta p)^2 := by
  have ha := analyticAt_riemannZeta hp
  have hd := (ha.deriv.differentiableAt.hasDerivAt.div
    ha.differentiableAt.hasDerivAt hz).deriv
  simpa only [pow_two] using hd

theorem riemannZeta_ne_zero_of_cross_multiplied_logged_identity {p : ℂ}
    (hp : p ≠ 1) {H : ℂ → ℂ} (hH : ContinuousAt H p)
    (heq : ∀ᶠ z in 𝓝 p,
      deriv (deriv riemannZeta) z * riemannZeta z - (deriv riemannZeta z)^2 =
        H z * (riemannZeta z)^2) : riemannZeta p ≠ 0 := by
  intro hz
  apply riemannZeta_zero_no_continuous_deriv_logDeriv_extension hp hz
  refine ⟨H, hH, ?_⟩
  obtain ⟨g, hg, hlocal⟩ := riemannZeta_logDeriv_local hp
  filter_upwards [nhdsWithin_le_nhds heq,
    nhdsWithin_le_nhds (continuousAt_id.eventually_ne hp), hlocal]
    with z hez hz1 hzn
  rw [deriv_logDeriv_riemannZeta_eq (p := z) (by simpa using hz1) hzn.1]
  exact (div_eq_iff (pow_ne_zero 2 hzn.1)).mpr hez

/-- The sign in the logged corrected trace is L'=H-D. At a genuine zero,
the surviving correction D therefore has positive double-pole coefficient m. -/
theorem correction_double_pole_at_zeta_zero {p : ℂ} (hp : p ≠ 1)
    (hz : riemannZeta p = 0) {H D : ℂ → ℂ} (hH : ContinuousAt H p)
    (heq : ∀ᶠ z in 𝓝[≠] p,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z = H z - D z) :
    0 < analyticOrderNatAt riemannZeta p ∧
      Tendsto (fun z => (z-p)^2 * D z) (𝓝[≠] p)
        (𝓝 (analyticOrderNatAt riemannZeta p : ℂ)) := by
  refine ⟨riemannZeta_order_pos_of_zero hp hz, ?_⟩
  obtain ⟨g, hg, hlocal⟩ := deriv_logDeriv_riemannZeta_local hp
  have ht : Tendsto
      (fun z : ℂ => (analyticOrderNatAt riemannZeta p : ℂ) +
        (z-p)^2 * (H z - g z)) (𝓝[≠] p)
      (𝓝 ((analyticOrderNatAt riemannZeta p : ℂ) + (p-p)^2 * (H p-g p))) :=
    tendsto_const_nhds.add
      ((((continuousAt_id.sub continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds).pow 2).mul
        ((hH.sub hg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds))
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [heq, hlocal, self_mem_nhdsWithin] with z hez hgz hzp
  have hzp' : z-p ≠ 0 := sub_ne_zero.mpr hzp
  have hrel : D z = (analyticOrderNatAt riemannZeta p : ℂ) / (z-p)^2 + H z - g z := by
    rw [hgz] at hez
    linear_combination hez
  rw [hrel]
  field_simp
  ring

/-- Noncircular analytic continuation: the identity theorem is applied to the
cross-multiplied analytic functions, without first deleting unknown zeros.
This is an assembly lemma; construction of H from actual traces is separate. -/
theorem zeta_ne_zero_on_of_local_cross_identity
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (hU1 : ∀ z ∈ U, z ≠ 1) {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H U)
    {q : ℂ} (hq : q ∈ U)
    (heq : ∀ᶠ z in 𝓝 q,
      deriv (deriv riemannZeta) z * riemannZeta z - (deriv riemannZeta z)^2 =
        H z * (riemannZeta z)^2) : ∀ p ∈ U, riemannZeta p ≠ 0 := by
  have hZ : AnalyticOnNhd ℂ riemannZeta U := fun z hz => analyticAt_riemannZeta (hU1 z hz)
  have hF : AnalyticOnNhd ℂ
      (fun z => deriv (deriv riemannZeta) z * riemannZeta z - (deriv riemannZeta z)^2) U :=
    fun z hz => (((hZ z hz).deriv.deriv).mul (hZ z hz)).sub ((hZ z hz).deriv.pow 2)
  have hG : AnalyticOnNhd ℂ (fun z => H z * (riemannZeta z)^2) U :=
    fun z hz => (hH z hz).mul ((hZ z hz).pow 2)
  have he := hF.eqOn_of_preconnected_of_eventuallyEq hG hc hq heq
  intro p hp
  apply riemannZeta_ne_zero_of_cross_multiplied_logged_identity (hU1 p hp)
    (hH p hp).continuousAt
  filter_upwards [hU.mem_nhds hp] with z hz
  exact he hz

end Masullo.ZetaLocalAnalysis

namespace ManuscriptRH
open scoped InnerProductSpace
open MeasureTheory Filter Topology

structure Parameters where
  width : ℝ
  weight : ℝ
  width_pos : 0 < width

structure HilbertData where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℂ Carrier]
  [complete : CompleteSpace Carrier]
  spectralSubspace : Submodule ℂ Carrier
  [projectionExists : spectralSubspace.HasOrthogonalProjection]
  BasisIndex : Type
  basis : HilbertBasis BasisIndex ℂ Carrier

attribute [instance] HilbertData.normed HilbertData.inner HilbertData.complete
  HilbertData.projectionExists

/-- Original-object integration contract; see the explicit construction hole.
The finite/trivial character specialization is part of that construction.
The logged limit functions below are to be constructed from the actual cutoffs;
their relationships to the finite-test traces are NOT supplied by this record. -/
structure RationalTraceData where
  IdeleClass : Type
  [ideleMeasurable : MeasurableSpace IdeleClass]
  haar : Measure IdeleClass
  module : IdeleClass → ℝ
  module_pos : ∀ g, 0 < module g
  Adele : Type
  [adeleZero : Zero Adele]
  Bruhat : Type
  [bruhatTopology : TopologicalSpace Bruhat]
  bruhatValue : Bruhat → Adele → ℂ
  fourier : Bruhat → Bruhat
  theta : Bruhat → IdeleClass → ℂ
  continuedZetaIntegral : Bruhat → ℂ → ℂ
  Test : Type
  testValue : Test → IdeleClass → ℂ
  logMul : Test → Test
  logMul_value : ∀ φ g, testValue (logMul φ) g =
    (Real.log (module g) : ℂ) * testValue φ g
  sharp : Test → Test
  allowed : Parameters → Prop
  space : Parameters → HilbertData
  convolution : ∀ p, Test → ((space p).Carrier →L[ℂ] (space p).Carrier)
  residueVector : ∀ p, ℂ → ℕ → (space p).Carrier
  Place : Type
  localOrbitalTerm : Place → Test → ℂ
  loggedRegularPart : Parameters → ℂ → ℂ
  loggedCorrection : Parameters → ℂ → ℂ

attribute [instance] RationalTraceData.ideleMeasurable RationalTraceData.adeleZero
  RationalTraceData.bruhatTopology

def originalS0 (D : RationalTraceData) (f : D.Bruhat) : Prop :=
  D.bruhatValue f 0 = 0 ∧ D.bruhatValue (D.fourier f) 0 = 0

/-- The test vanishes on the ENTIRE norm-one subgroup. -/
def Admissible (D : RationalTraceData) (φ : D.Test) : Prop :=
  ∀ g, D.module g = 1 → D.testValue φ g = 0

inductive TestFamily | plain | logged

def familyTest (D : RationalTraceData) (k : TestFamily) (φ : D.Test) : D.Test :=
  match k with
  | .plain => φ
  | .logged => D.logMul φ

theorem familyTest_admissible (D : RationalTraceData) (k : TestFamily)
    (φ : D.Test) (hφ : Admissible D φ) : Admissible D (familyTest D k φ) := by
  cases k with
  | plain => exact hφ
  | logged =>
      intro g hg
      change D.testValue (D.logMul φ) g = 0
      rw [D.logMul_value, hφ g hg, mul_zero]

/-- Actual geometric orthogonal projection OF THE SUPPLIED SUBSPACE.
Attaching that subspace to the manuscript is the original-object placeholder. -/
noncomputable def geometricProjection (D : RationalTraceData) (p : Parameters) :
    (D.space p).Carrier →L[ℂ] (D.space p).Carrier :=
  (D.space p).spectralSubspace.starProjection

/-- PA, never AP: convolution first, projection second. -/
noncomputable def leadingOperator (D : RationalTraceData) (p : Parameters)
    (k : TestFamily) (φ : D.Test) : (D.space p).Carrier →L[ℂ] (D.space p).Carrier :=
  (geometricProjection D p).comp (D.convolution p (D.sharp (familyTest D k φ)))

/-- A quantitative nuclear expansion converging to the actual supplied operator.
This is the requested Hilbert-space rank-one criterion, not merely boundedness. -/
def HasNuclearExpansion (S : HilbertData) (T : S.Carrier →L[ℂ] S.Carrier) : Prop :=
  ∃ (u v : ℕ → S.Carrier) (C : ℝ), 0 ≤ C ∧
    Summable (fun n => ‖u n‖ * ‖v n‖) ∧
    (∑' n, ‖u n‖ * ‖v n‖) ≤ C ∧
    ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (T x)

/-- Basis diagonal. Its identification with the canonical nuclear trace is
explicitly required by SpectralIdentification; it is not assumed for all T. -/
noncomputable def operatorTrace (D : RationalTraceData) (p : Parameters)
    (k : TestFamily) (φ : D.Test) : ℂ :=
  ∑' i, ⟪(D.space p).basis i, leadingOperator D p k φ ((D.space p).basis i)⟫_ℂ

/-- Discharged using the saved spectral trace/interchange proof: the nuclear
trace clause is no longer an arithmetic spectral-identification assumption. -/
theorem operatorTrace_eq_nuclear_sum (D : RationalTraceData) (p : Parameters)
    (k : TestFamily) (φ : D.Test) (u v : ℕ → (D.space p).Carrier)
    (hc : Summable (fun n => ‖u n‖ * ‖v n‖))
    (hT : ∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (leadingOperator D p k φ x)) :
    operatorTrace D p k φ = ∑' n, ⟪u n, v n⟫_ℂ :=
  Masullo.NuclearDiagonal.nuclear_operator_diagonal (D.space p).basis (leadingOperator D p k φ) u v hc hT

theorem leadingOperator_diagonal_summable (D : RationalTraceData) (p : Parameters)
    (k : TestFamily) (φ : D.Test)
    (hn : HasNuclearExpansion (D.space p) (leadingOperator D p k φ)) :
    Summable (fun i => ‖⟪(D.space p).basis i,
      leadingOperator D p k φ ((D.space p).basis i)⟫_ℂ‖) := by
  obtain ⟨u, v, C, hC, hc, hbound, hT⟩ := hn
  exact Masullo.NuclearSeries.nuclear_diagonal_summable (D.space p).basis
    (leadingOperator D p k φ) u v hc hT

/-- Saved geometry applied to this assembly's PA operator at a finite stage.
The finite-span identity and invertible Gram matrix remain explicit. This is
not a claim that the full geometric spectral space is finite-dimensional. -/
theorem leadingOperator_finite_Gram (D : RationalTraceData) (p : Parameters)
    (k : TestFamily) (φ : D.Test) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → (D.space p).Carrier)
    (hspan : (D.space p).spectralSubspace = Submodule.span ℂ (Set.range r))
    (hG : IsUnit (Matrix.det (fun i j => inner ℂ (r i) (r j))))
    (x : (D.space p).Carrier) :
    leadingOperator D p k φ x =
      ∑ j, (Matrix.mulVec (((fun i j => inner ℂ (r i) (r j)) : Matrix ι ι ℂ)⁻¹)
        (fun i => inner ℂ (r i) (D.convolution p (D.sharp (familyTest D k φ)) x))) j • r j := by
  simpa only [leadingOperator, geometricProjection, ContinuousLinearMap.comp_apply, hspan]
    using Masullo.GramProjection.inverseGram_projection r hG
      (D.convolution p (D.sharp (familyTest D k φ)) x)

/-- Genuine completed-zeta zeros, without assuming the critical-line conclusion. -/
def GenuineZero := {ρ : ℂ // completedRiemannZeta ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1}

noncomputable def zeroOrder (ρ : GenuineZero) : ℕ :=
  analyticOrderNatAt completedRiemannZeta ρ.val

def AdmittedJet (p : Parameters) (ρ : GenuineZero) (m : ℕ) : Prop :=
  m < zeroOrder ρ ∧
    (|ρ.val.re - 1/2| < p.width ∨
      (|ρ.val.re - 1/2| = p.width ∧ (2 : ℝ) * m + 1 < p.weight))

noncomputable def interiorMultiplicity (p : Parameters) (ρ : GenuineZero) : ℕ :=
  if |ρ.val.re - 1/2| < p.width then zeroOrder ρ else 0

noncomputable def boundaryMultiplicity (p : Parameters) (ρ : GenuineZero) : ℕ := by
  classical
  exact if |ρ.val.re - 1/2| = p.width then
    ((Finset.range (zeroOrder ρ)).filter (fun m => (2 : ℝ) * m + 1 < p.weight)).card
    else 0

noncomputable def mellin (D : RationalTraceData) (φ : D.Test) (z : ℂ) : ℂ :=
  ∫ g, D.testValue φ g * (D.module g : ℂ) ^ z ∂D.haar

noncomputable def zeroTest (D : RationalTraceData) (φ : D.Test) (ρ : GenuineZero) : ℂ :=
  mellin D φ (ρ.val - 1/2)

noncomputable def nativeTerm (D : RationalTraceData) (p : Parameters)
    (φ : D.Test) (ρ : GenuineZero) : ℂ :=
  ((interiorMultiplicity p ρ + boundaryMultiplicity p ρ : ℕ) : ℂ) * zeroTest D φ ρ

noncomputable def nativeSum (D : RationalTraceData) (p : Parameters) (φ : D.Test) : ℂ :=
  ∑' ρ : GenuineZero, nativeTerm D p φ ρ

noncomputable def omittedTerm (D : RationalTraceData) (p : Parameters)
    (φ : D.Test) (ρ : GenuineZero) : ℂ :=
  ((zeroOrder ρ - interiorMultiplicity p ρ : ℕ) : ℂ) * zeroTest D φ ρ

noncomputable def edgeTerm (D : RationalTraceData) (p : Parameters)
    (φ : D.Test) (ρ : GenuineZero) : ℂ :=
  (boundaryMultiplicity p ρ : ℂ) * zeroTest D φ ρ

/-- The omitted-zero correction is retained with its sign. -/
noncomputable def stripCorrection (D : RationalTraceData) (p : Parameters)
    (φ : D.Test) : ℂ :=
  (∑' ρ : GenuineZero, omittedTerm D p φ ρ) -
    (∑' ρ : GenuineZero, edgeTerm D p φ ρ)

noncomputable def poleTerm (D : RationalTraceData) (φ : D.Test) : ℂ :=
  mellin D φ (-1/2) + mellin D φ (1/2)

noncomputable def arithmeticTerm (D : RationalTraceData) (φ : D.Test) : ℂ :=
  poleTerm D φ - ∑' v : D.Place, D.localOrbitalTerm v φ

/-- The needed Q/trivial-character consequence of the Hecke/Tate integral
theorem. The local factorization ranges over every original test; S0 retains
BOTH zero constraints for the unfolded pairing and zero-derivative consequence.
The full distribution topology must be supplied when replacing this interface. -/
def HeckeIntegral (D : RationalTraceData) : Prop :=
  (∀ f, originalS0 D f → ∀ z : ℂ, 1 < z.re →
    D.continuedZetaIntegral f z =
      ∫ g, D.theta f g * (D.module g : ℂ) ^ z ∂D.haar) ∧
  (∀ ρ : GenuineZero, ∃ deltaRatio : D.Bruhat → ℂ → ℂ,
    (∀ z, Continuous (fun f => deltaRatio f z)) ∧
    ∀ f, AnalyticAt ℂ (deltaRatio f) ρ.val ∧ ∀ᶠ z in 𝓝 ρ.val,
      D.continuedZetaIntegral f z = completedRiemannZeta z * deltaRatio f z) ∧
  (∀ ρ : GenuineZero, ∀ f, originalS0 D f → ∀ m : ℕ, m < zeroOrder ρ →
    iteratedDeriv m (D.continuedZetaIntegral f) ρ.val = 0)

/-- Only unfolding and actual local all-test factorization remain supplied.
The derivative-zero consequence is proved below, not assumed separately. -/
def HeckeFactorization (D : RationalTraceData) : Prop :=
  (∀ f, originalS0 D f → ∀ z : ℂ, 1 < z.re →
    D.continuedZetaIntegral f z =
      ∫ g, D.theta f g * (D.module g : ℂ) ^ z ∂D.haar) ∧
  (∀ ρ : GenuineZero, ∃ deltaRatio : D.Bruhat → ℂ → ℂ,
    (∀ z, Continuous (fun f => deltaRatio f z)) ∧
    ∀ f, AnalyticAt ℂ (deltaRatio f) ρ.val ∧ ∀ᶠ z in 𝓝 ρ.val,
      D.continuedZetaIntegral f z = completedRiemannZeta z * deltaRatio f z)

theorem analyticAt_completedZeta_genuineZero (ρ : GenuineZero) :
    AnalyticAt ℂ completedRiemannZeta ρ.val := by
  have hd : DifferentiableOn ℂ completedRiemannZeta
      ({0, 1}ᶜ : Set ℂ) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro e
      apply hz
      simp [e]
    have hz1 : z ≠ 1 := by
      intro e
      apply hz
      simp [e]
    exact (differentiableAt_completedZeta hz0 hz1).differentiableWithinAt
  have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := by
    have he : ({0, 1}ᶜ : Set ℂ) = ({0}ᶜ : Set ℂ) ∩ ({1}ᶜ : Set ℂ) := by
      ext z
      simp
    rw [he]
    exact isOpen_compl_singleton.inter isOpen_compl_singleton
  apply hd.analyticOnNhd hopen ρ.val
  simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨ρ.property.2.1, ρ.property.2.2⟩

/-- Actual completed-zeta zero orders now feed the saved Tate derivative proof. -/
theorem heckeIntegral_of_factorization (D : RationalTraceData)
    (hf : HeckeFactorization D) : HeckeIntegral D := by
  refine ⟨hf.1, hf.2, ?_⟩
  intro ρ f _ m hm
  obtain ⟨delta, hcontinuous, hdelta⟩ := hf.2 ρ
  have hfinite : analyticOrderAt completedRiemannZeta ρ.val ≠ ⊤ := by
    intro ht
    have hzero : zeroOrder ρ = 0 := by simp [zeroOrder, analyticOrderNatAt, ht]
    rw [hzero] at hm
    exact Nat.not_lt_zero m hm
  exact Masullo.TateDivisibility.local_tate_derivative_zero completedRiemannZeta (delta f)
    (D.continuedZetaIntegral f) ρ.val m (analyticAt_completedZeta_genuineZero ρ)
    (hdelta f).1 hfinite hm (hdelta f).2

def LeadingNuclearity (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
    HasNuclearExpansion (D.space p) (leadingOperator D p k φ)

def ResidueExhaustion (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p →
    closure (↑(Submodule.span ℂ {x : (D.space p).Carrier |
      ∃ (ρ : GenuineZero) (m : ℕ), AdmittedJet p ρ m ∧
        x = D.residueVector p ρ.val m}) : Set (D.space p).Carrier) =
      ((D.space p).spectralSubspace : Set (D.space p).Carrier)

def SpectralIdentification (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
    Summable (fun ρ : GenuineZero => ‖nativeTerm D p (familyTest D k φ) ρ‖) ∧
    operatorTrace D p k φ = nativeSum D p (familyTest D k φ) ∧
    (∀ u v : ℕ → (D.space p).Carrier,
      Summable (fun n => ‖u n‖ * ‖v n‖) →
      (∀ x, HasSum (fun n => ⟪u n, x⟫_ℂ • v n) (leadingOperator D p k φ x)) →
      operatorTrace D p k φ = ∑' n, ⟪u n, v n⟫_ℂ)

/-- Absolute zero-sum convergence and spectral trace identity. -/
def SpectralZeroTrace (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
    Summable (fun ρ : GenuineZero => ‖nativeTerm D p (familyTest D k φ) ρ‖) ∧
    operatorTrace D p k φ = nativeSum D p (familyTest D k φ)

theorem spectralIdentification_of_zeroTrace (D : RationalTraceData)
    (hz : SpectralZeroTrace D) : SpectralIdentification D := by
  intro p hp φ hφ k
  exact ⟨(hz p hp φ hφ k).1, (hz p hp φ hφ k).2,
    fun u v hc hT => operatorTrace_eq_nuclear_sum D p k φ u v hc hT⟩

/-- Geometric trace identity with the omitted-zero and boundary correction retained. -/
def GeometricTrace (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
    Summable (fun v : D.Place => ‖D.localOrbitalTerm v (familyTest D k φ)‖) ∧
    Summable (fun ρ : GenuineZero => ‖omittedTerm D p (familyTest D k φ) ρ‖) ∧
    Summable (fun ρ : GenuineZero => ‖edgeTerm D p (familyTest D k φ) ρ‖) ∧
    operatorTrace D p k φ = arithmeticTerm D (familyTest D k φ) -
      stripCorrection D p (familyTest D k φ)

def MatchedTraces (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
    nativeSum D p (familyTest D k φ) = arithmeticTerm D (familyTest D k φ) -
      stripCorrection D p (familyTest D k φ)

/-- Match the spectral and geometric formulas for the same PA operator. -/
theorem match_traces (D : RationalTraceData)
    (hs : SpectralIdentification D) (hg : GeometricTrace D) : MatchedTraces D := by
  intro p hp φ hφ k
  exact (hs p hp φ hφ k).2.1.symm.trans (hg p hp φ hφ k).2.2.2

/-- Regularized logarithmic cutoff-limit identity, retaining reference constants
and the omitted-zero and boundary correction. The width is below Re(q) − 1/2. -/
def Chapter13RegularizedLimit (D : RationalTraceData) : Prop :=
  ∀ q : ℂ, 1/2 < q.re → q ≠ 1 → ∃ p : Parameters,
    D.allowed p ∧ p.width < q.re - 1/2 ∧
    ContinuousAt (D.loggedRegularPart p) q ∧
    ∀ᶠ z in 𝓝[≠] q,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z =
        D.loggedRegularPart p z - D.loggedCorrection p z

/-- Correction-control hypothesis: the scaled correction tends to zero
at each point to the right of the retained strip. -/
def Chapter13CorrectionControl (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ q : ℂ, p.width < q.re - 1/2 → q ≠ 1 →
    Tendsto (fun z => (z-q)^2 * D.loggedCorrection p z) (𝓝[≠] q) (𝓝 0)

theorem right_half_plane_nonvanishing (D : RationalTraceData)
    (hlimit : Chapter13RegularizedLimit D) (hcorr : Chapter13CorrectionControl D) :
    ∀ q : ℂ, 1/2 < q.re → q ≠ 1 → riemannZeta q ≠ 0 := by
  intro q hq hq1 hz
  obtain ⟨p, hp, hwidth, hreg, heq⟩ := hlimit q hq hq1
  have hres := Masullo.ZetaLocalAnalysis.correction_double_pole_at_zeta_zero hq1 hz hreg heq
  have hzero := hcorr p hp q hwidth hq1
  have hn : (analyticOrderNatAt riemannZeta q : ℂ) = 0 :=
    tendsto_nhds_unique hres.2 hzero
  have hn' : analyticOrderNatAt riemannZeta q = 0 := by exact_mod_cast hn
  exact (Nat.ne_of_gt (Masullo.ZetaLocalAnalysis.riemannZeta_order_pos_of_zero hq1 hz)) hn'

/-- Standard Mathlib RH, including exclusion of the trivial zeros.
Functional-equation/Gamma argument adapted from the inspected alpo source;
no alpo conclusion or unverified transitive import is assumed. -/
theorem riemannHypothesis_of_right_nonvanishing
    (h : ∀ s : ℂ, 1/2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hs hn h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hs
      norm_num at hs
    have h1s : (1-s) ≠ 1 := fun e => hs0 (by simpa using e)
    have hz : riemannZeta (1-s) ≠ 0 := h (1-s) (by simp; linarith) h1s
    have hc : completedRiemannZeta s = completedRiemannZeta (1-s) :=
      (completedRiemannZeta_one_sub s).symm
    have h1s0 : (1-s) ≠ 0 := fun e => h1 (by linear_combination -e)
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · exact hz (by rw [riemannZeta_def_of_ne_zero h1s0, ← hc, hs, zero_div])
    · obtain ⟨n, hn'⟩ := Complex.Gammaℝ_eq_zero_iff.1 hs
      rcases n with _ | n
      · exact hs0 (by simpa using hn')
      · exact hn ⟨n, by rw [hn']; push_cast; ring⟩
  · exact h s hgt h1 hs

/-- RH from the regularized-limit and correction-control hypotheses. -/
theorem riemannHypothesis_of_chapter13 (D : RationalTraceData)
    (hlimit : Chapter13RegularizedLimit D) (hcorr : Chapter13CorrectionControl D) :
    RiemannHypothesis :=
  riemannHypothesis_of_right_nonvanishing (right_half_plane_nonvanishing D hlimit hcorr)

end ManuscriptRH

namespace Masullo.CorrectionControl
open Complex Filter Topology
theorem correction_scaled_limit_all_points {p : ℂ} (hp : p ≠ 1)
    {H D : ℂ → ℂ} (hH : ContinuousAt H p)
    (heq : ∀ᶠ z in 𝓝[≠] p,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z = H z - D z) :
    Tendsto (fun z => (z-p)^2 * D z) (𝓝[≠] p)
        (𝓝 (analyticOrderNatAt riemannZeta p : ℂ)) := by
  obtain ⟨g, hg, hlocal⟩ := Masullo.ZetaLocalAnalysis.deriv_logDeriv_riemannZeta_local hp
  have ht : Tendsto
      (fun z : ℂ => (analyticOrderNatAt riemannZeta p : ℂ) +
        (z-p)^2 * (H z - g z)) (𝓝[≠] p)
      (𝓝 ((analyticOrderNatAt riemannZeta p : ℂ) + (p-p)^2 * (H p-g p))) :=
    tendsto_const_nhds.add
      ((((continuousAt_id.sub continuousAt_const).tendsto.mono_left
        nhdsWithin_le_nhds).pow 2).mul
        ((hH.sub hg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds))
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_mul, add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [heq, hlocal, self_mem_nhdsWithin] with z hez hgz hzp
  have hzp' : z-p ≠ 0 := sub_ne_zero.mpr hzp
  have hrel : D z = (analyticOrderNatAt riemannZeta p : ℂ) / (z-p)^2 + H z - g z := by
    rw [hgz] at hez
    linear_combination hez
  rw [hrel]
  field_simp
  ring

/-- The true finite order is zero exactly at a nonzero value of genuine zeta. -/
theorem zeta_order_zero_iff {p : ℂ} (hp : p ≠ 1) :
    analyticOrderNatAt riemannZeta p = 0 ↔ riemannZeta p ≠ 0 := by
  constructor
  · intro h0 hz
    have hm := Masullo.ZetaLocalAnalysis.riemannZeta_order_pos_of_zero hp hz
    omega
  · intro hn
    have ha : analyticOrderAt riemannZeta p = 0 :=
      (Masullo.ZetaLocalAnalysis.analyticAt_riemannZeta hp).analyticOrderAt_eq_zero.mpr hn
    have hn' : (analyticOrderNatAt riemannZeta p : ℕ∞) = 0 := by
      rw [Nat.cast_analyticOrderNatAt (Masullo.ZetaLocalAnalysis.riemannZeta_analyticOrder_ne_top hp), ha]
    exact_mod_cast hn'

/-- Under the local identity, correction control is equivalent to zeta nonvanishing. -/
theorem correction_control_iff_zeta_ne_zero {p : ℂ} (hp : p ≠ 1)
    {H D : ℂ → ℂ} (hH : ContinuousAt H p)
    (heq : ∀ᶠ z in 𝓝[≠] p,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z = H z - D z) :
    Tendsto (fun z => (z-p)^2 * D z) (𝓝[≠] p) (𝓝 0) ↔ riemannZeta p ≠ 0 := by
  have ht := correction_scaled_limit_all_points hp hH heq
  constructor
  · intro h0
    have hc : (analyticOrderNatAt riemannZeta p : ℂ) = 0 :=
      tendsto_nhds_unique ht h0
    have hm : analyticOrderNatAt riemannZeta p = 0 := by exact_mod_cast hc
    exact (zeta_order_zero_iff hp).mp hm
  · intro hn
    have hm := (zeta_order_zero_iff hp).mpr hn
    simpa [hm] using ht

end Masullo.CorrectionControl

namespace ManuscriptRH
open Complex Filter Topology

/-- One exact witness of the EXISTENTIAL regularized-limit interface.
This definition changes no original test, operator, measure or multiplicity. -/
def Chapter13Witness (D : RationalTraceData) (p : Parameters) (q : ℂ) : Prop :=
  D.allowed p ∧ p.width < q.re - 1/2 ∧
    ContinuousAt (D.loggedRegularPart p) q ∧
    ∀ᶠ z in 𝓝[≠] q,
      deriv (fun w => deriv riemannZeta w / riemannZeta w) z =
        D.loggedRegularPart p z - D.loggedCorrection p z

/-- A smaller paired-witness target: the SAME width must provide both
continuation and correction control. This is an OPEN mathematical obligation,
not a proved replacement for the scaffold's correction-control placeholder. -/
def Chapter13PairedControl (D : RationalTraceData) : Prop :=
  ∀ q : ℂ, 1/2 < q.re → q ≠ 1 → ∃ p : Parameters,
    Chapter13Witness D p q ∧
    Tendsto (fun z => (z-q)^2 * D.loggedCorrection p z) (𝓝[≠] q) (𝓝 0)

theorem chapter13_witness_coefficient (D : RationalTraceData)
    {p : Parameters} {q : ℂ} (hq : q ≠ 1) (hw : Chapter13Witness D p q) :
    Tendsto (fun z => (z-q)^2 * D.loggedCorrection p z) (𝓝[≠] q)
      (𝓝 (analyticOrderNatAt riemannZeta q : ℂ)) :=
  Masullo.CorrectionControl.correction_scaled_limit_all_points hq hw.2.2.1 hw.2.2.2

theorem chapter13_witness_control_iff (D : RationalTraceData)
    {p : Parameters} {q : ℂ} (hq : q ≠ 1) (hw : Chapter13Witness D p q) :
    Tendsto (fun z => (z-q)^2 * D.loggedCorrection p z) (𝓝[≠] q) (𝓝 0) ↔
      riemannZeta q ≠ 0 :=
  Masullo.CorrectionControl.correction_control_iff_zeta_ne_zero hq hw.2.2.1 hw.2.2.2

/-- The original all-width control suffices, but is stronger in its
quantifiers than needed for the conditional endpoint. -/
theorem chapter13_paired_of_original (D : RationalTraceData)
    (hl : Chapter13RegularizedLimit D) (hc : Chapter13CorrectionControl D) :
    Chapter13PairedControl D := by
  intro q hq hq1
  obtain ⟨p, hp, hw, hH, heq⟩ := hl q hq hq1
  exact ⟨p, ⟨hp, hw, hH, heq⟩, hc p hp q hw hq1⟩

/-- Paired correction control is equivalent to right-half-plane nonvanishing. -/
theorem chapter13_paired_iff_right_nonvanishing (D : RationalTraceData)
    (hl : Chapter13RegularizedLimit D) :
    Chapter13PairedControl D ↔
      ∀ q : ℂ, 1/2 < q.re → q ≠ 1 → riemannZeta q ≠ 0 := by
  constructor
  · intro hc q hq hq1
    obtain ⟨p, hw, hzero⟩ := hc q hq hq1
    exact (chapter13_witness_control_iff D hq1 hw).mp hzero
  · intro hn q hq hq1
    obtain ⟨p, hp, hw, hH, heq⟩ := hl q hq hq1
    have hwit : Chapter13Witness D p q := ⟨hp, hw, hH, heq⟩
    exact ⟨p, hwit, (chapter13_witness_control_iff D hq1 hwit).mpr (hn q hq hq1)⟩

theorem right_nonvanishing_of_riemannHypothesis (hrh : RiemannHypothesis) :
    ∀ q : ℂ, 1/2 < q.re → q ≠ 1 → riemannZeta q ≠ 0 := by
  intro q hq hq1 hz
  have hnt : ¬ ∃ n : ℕ, q = -2 * (n+1) := by
    rintro ⟨n, hn⟩
    have he := congrArg Complex.re hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    norm_num at he
    linarith
  have he := hrh q hz hnt hq1
  linarith

/-- Under the regularized-limit hypothesis, paired correction control
is equivalent to RH. -/
theorem chapter13_paired_control_iff_riemannHypothesis (D : RationalTraceData)
    (hl : Chapter13RegularizedLimit D) :
    Chapter13PairedControl D ↔ RiemannHypothesis := by
  rw [chapter13_paired_iff_right_nonvanishing D hl]
  exact ⟨riemannHypothesis_of_right_nonvanishing, right_nonvanishing_of_riemannHypothesis⟩

theorem riemannHypothesis_of_paired_chapter13 (D : RationalTraceData)
    (hc : Chapter13PairedControl D) : RiemannHypothesis := by
  apply riemannHypothesis_of_right_nonvanishing
  intro q hq hq1
  obtain ⟨p, hw, hzero⟩ := hc q hq hq1
  exact (chapter13_witness_control_iff D hq1 hw).mp hzero

/-- Matching the same arithmetic expression at two widths transports the
correction by the native-trace difference; it does not erase that difference. -/
theorem stripCorrection_width_difference (D : RationalTraceData)
    (hm : MatchedTraces D) {p r : Parameters}
    (hp : D.allowed p) (hr : D.allowed r) {φ : D.Test}
    (hφ : Admissible D φ) (k : TestFamily) :
    stripCorrection D p (familyTest D k φ) - stripCorrection D r (familyTest D k φ) =
      nativeSum D r (familyTest D k φ) - nativeSum D p (familyTest D k φ) := by
  have h1 := hm p hp φ hφ k
  have h2 := hm r hr φ hφ k
  linear_combination h1 - h2

/-- Width-independent corrections would force width-independent native
traces. Neither assertion is supplied by boundary-free width selection. -/
theorem stripCorrection_width_eq_iff_native_eq (D : RationalTraceData)
    (hm : MatchedTraces D) {p r : Parameters}
    (hp : D.allowed p) (hr : D.allowed r) {φ : D.Test}
    (hφ : Admissible D φ) (k : TestFamily) :
    stripCorrection D p (familyTest D k φ) = stripCorrection D r (familyTest D k φ) ↔
      nativeSum D p (familyTest D k φ) = nativeSum D r (familyTest D k φ) := by
  have hd := stripCorrection_width_difference D hm hp hr hφ k
  constructor <;> intro he <;> linear_combination hd - he

/-- Among widths whose regular part is continuous at the SAME point, the
correction's quadratic coefficient is the same true zeta order, not zero. -/
theorem paired_width_correction_difference (D : RationalTraceData)
    {p r : Parameters} {q : ℂ} (hq : q ≠ 1)
    (hp : Chapter13Witness D p q) (hr : Chapter13Witness D r q) :
    Tendsto (fun z => (z-q)^2 *
      (D.loggedCorrection p z - D.loggedCorrection r z)) (𝓝[≠] q) (𝓝 0) := by
  have ht := (chapter13_witness_coefficient D hq hp).sub
    (chapter13_witness_coefficient D hq hr)
  simpa only [mul_sub, sub_self] using ht

#print axioms chapter13_witness_coefficient
#print axioms chapter13_paired_control_iff_riemannHypothesis
#print axioms riemannHypothesis_of_paired_chapter13
#print axioms stripCorrection_width_difference
#print axioms stripCorrection_width_eq_iff_native_eq
#print axioms paired_width_correction_difference
end ManuscriptRH

open Complex MeasureTheory Filter Topology Set
open scoped ContDiff

namespace MasulloGRH.ConditionalMoment

/-- the scalar compact tests used before subtracting
two widths of the arithmetic trace. This is not an idelic admissibility claim. -/
noncomputable def positiveCutoff (t x : ℝ) : ℝ :=
  Real.smoothTransition (t * x - 1) * Real.smoothTransition (2 - x / t)

theorem positiveCutoff_smooth (t : ℝ) : ContDiff ℝ ∞ (positiveCutoff t) := by
  exact (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_id.div_const t)))

theorem positiveCutoff_bounds (t x : ℝ) :
    0 ≤ positiveCutoff t x ∧ positiveCutoff t x ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact mul_le_one₀ (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem positiveCutoff_eq_one (t x : ℝ) (hleft : 2 ≤ t * x) (hright : x ≤ t)
    (ht : 0 < t) : positiveCutoff t x = 1 := by
  unfold positiveCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t * x - 1)]
  rw [Real.smoothTransition.one_of_one_le (by
    have h : x / t ≤ 1 := (div_le_one ht).mpr hright
    linarith : 1 ≤ 2 - x / t)]
  simp

theorem positiveCutoff_support (t : ℝ) (ht : 0 < t) :
    Function.support (positiveCutoff t) ⊆ Icc (1 / t) (2 * t) := by
  intro x hx
  have hne : positiveCutoff t x ≠ 0 := hx
  have hleft : 0 < t * x - 1 := by
    by_contra h
    exact hne (by simp [positiveCutoff,
      Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)])
  have hright : 0 < 2 - x / t := by
    by_contra h
    exact hne (by simp [positiveCutoff,
      Real.smoothTransition.zero_of_nonpos (le_of_not_gt h)])
  constructor
  · apply (div_le_iff₀ ht).mpr
    nlinarith
  · apply (div_le_iff₀ ht).mp
    linarith

theorem positiveCutoff_compact (t : ℝ) (ht : 0 < t) :
    HasCompactSupport (positiveCutoff t) := by
  apply isCompact_Icc.of_isClosed_subset isClosed_closure
  exact closure_minimal (positiveCutoff_support t ht) isClosed_Icc

theorem positiveCutoff_tsupport_positive (t : ℝ) (ht : 0 < t) :
    tsupport (positiveCutoff t) ⊆ Ioi 0 := by
  have hs : tsupport (positiveCutoff t) ⊆ Icc (1 / t) (2 * t) :=
    closure_minimal (positiveCutoff_support t ht) isClosed_Icc
  intro x hx
  exact lt_of_lt_of_le (one_div_pos.mpr ht) (hs hx).1

/-- exact eventual agreement, rather than an assumed
limit, at every positive logarithmic norm coordinate. -/
theorem positiveCutoff_eventually_one (x : ℝ) (hx : 0 < x) :
    ∀ᶠ n : ℕ in atTop, positiveCutoff ((n : ℝ) + 1) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max x (2 / x))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnx : x < (n : ℝ) + 1 := by
    have := le_max_left x (2 / x)
    linarith
  have hnq : 2 / x < (n : ℝ) + 1 := by
    have := le_max_right x (2 / x)
    linarith
  apply positiveCutoff_eq_one
  · have := (div_lt_iff₀ hx).mp hnq
    linarith
  · exact hnx.le
  · positivity

theorem positiveCutoff_tendsto (x : ℝ) (hx : 0 < x) :
    Tendsto (fun n : ℕ => positiveCutoff ((n : ℝ) + 1) x) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [positiveCutoff_eventually_one x hx] with n hn
  exact hn.symm

end MasulloGRH.ConditionalMoment

namespace Masullo.LaplaceCutoff
open MasulloGRH.ConditionalMoment

theorem uniform_integral_cutoff_ae_bound
    {X Z : Type*} [MeasurableSpace X] (μ : Measure X) (S : Set Z)
    (q : ℕ → X → ℝ) (F : Z → X → ℂ) (B : X → ℝ)
    (hq : ∀ n, AEStronglyMeasurable (q n) μ)
    (hqbound : ∀ n x, 0 ≤ q n x ∧ q n x ≤ 1)
    (hqlim : ∀ᵐ x ∂μ, Tendsto (fun n => q n x) atTop (𝓝 1))
    (hB : Integrable B μ) (hBpos : ∀ x, 0 ≤ B x)
    (hF : ∀ z ∈ S, AEStronglyMeasurable (F z) μ)
    (hbound : ∀ z ∈ S, ∀ᵐ x ∂μ, ‖F z x‖ ≤ B x) :
    TendstoUniformlyOn (fun n z => ∫ x, (q n x : ℂ) * F z x ∂μ)
      (fun z => ∫ x, F z x ∂μ) atTop S := by
  have herrbd (n : ℕ) (x : X) : ‖(1 - q n x) * B x‖ ≤ B x := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr
      (hqbound n x).2) (hBpos x))]
    nlinarith [(hqbound n x).1, (hqbound n x).2, hBpos x]
  have herrmeas (n : ℕ) : AEStronglyMeasurable (fun x => (1-q n x)*B x) μ :=
    (aestronglyMeasurable_const.sub (hq n)).mul hB.aestronglyMeasurable
  have herrint (n : ℕ) : Integrable (fun x => (1-q n x)*B x) μ :=
    hB.mono' (herrmeas n) (Eventually.of_forall (herrbd n))
  have herrlim : Tendsto (fun n => ∫ x, (1-q n x)*B x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence B herrmeas hB
      (fun n => Eventually.of_forall (herrbd n)) (by
        filter_upwards [hqlim] with x hx
        simpa using (tendsto_const_nhds.sub hx).mul_const (B x))
    simpa using h
  have hFi (z : Z) (hz : z ∈ S) : Integrable (F z) μ :=
    hB.mono' (hF z hz) (hbound z hz)
  have hqi (n : ℕ) (z : Z) (hz : z ∈ S) :
      Integrable (fun x => (q n x : ℂ) * F z x) μ := by
    refine hB.mono' ?_ ?_
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable (hq n)).mul (hF z hz)
    · filter_upwards [hbound z hz] with x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hqbound n x).1]
      exact (mul_le_mul_of_nonneg_left hx (hqbound n x).1).trans
        (by nlinarith [(hqbound n x).2, hBpos x])
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [herrlim.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm, ← integral_sub (hFi z hz) (hqi n z hz)]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le (herrint n) ?_) hn
  filter_upwards [hbound z hz] with x hx
  have he : F z x - (q n x : ℂ) * F z x = ((1-q n x : ℝ) : ℂ) * F z x := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (hqbound n x).2)]
  exact mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr (hqbound n x).2)

theorem norm_pow_mul_cexp_neg (n : ℕ) (r : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ n * Complex.exp (-(r * t))‖ = t ^ (n : ℝ) * Real.exp (-r.re * t ^ (1 : ℝ)) := by
  rw [norm_mul, norm_pow, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.rpow_natCast, Real.rpow_one]
  congr 2
  simp

theorem integrableOn_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := r.re)
    (by have := n.cast_nonneg (α := ℝ); linarith) le_rfl hr
  refine h.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_pow_mul_cexp_neg n r ht]

theorem tendsto_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ n * Complex.exp (-(r * t))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) r.re hr
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [norm_pow_mul_cexp_neg n r ht, Real.rpow_one]

theorem integral_pow_mul_cexp_neg (n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * Complex.exp (-(r * t)) = (n.factorial : ℂ) / r ^ (n + 1) := by
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr
  induction n with
  | zero =>
    have h := integral_exp_mul_complex_Ioi (a := -r) (by simpa using hr) 0
    simp only [pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
    simp_rw [← neg_mul]
    rw [h]; simp
  | succ n ih =>
    have h1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
    have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => Complex.exp (-(r * t)) / (-r))
        (Complex.exp (-(r * t))) t := by
      intro t _
      have h2 : HasDerivAt (fun t : ℝ => -(r * (t : ℂ))) (-r) t := by
        simpa using ((h1 t).const_mul (-r))
      have hv' := h2.cexp.div_const (-r)
      rwa [mul_div_assoc, div_self (neg_ne_zero.mpr hr0), mul_one] at hv'
    have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1))
        (((n : ℂ) + 1) * (t : ℂ) ^ n) t := by
      intro t _
      convert (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal using 1
      simp
    have hint := integrableOn_pow_mul_cexp_neg n hr
    have hibp := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0) hu hv
      (integrableOn_pow_mul_cexp_neg (n + 1) hr)
      (by
        refine IntegrableOn.congr_fun (hint.const_mul (-((n : ℂ) + 1) / r)) (fun t _ => ?_) measurableSet_Ioi
        simp only [Pi.mul_apply]; field_simp)
      (by
        have hc : Continuous (fun t : ℝ => (t : ℂ) ^ (n + 1) * (Complex.exp (-(r * t)) / (-r))) := by
          fun_prop
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        convert this using 2; simp)
      (by
        have := (tendsto_pow_mul_cexp_neg (n + 1) hr).const_mul (-1 / r)
        rw [mul_zero] at this
        refine this.congr (fun t => ?_)
        simp only [Pi.mul_apply]; field_simp)
    rw [hibp]
    have e : (fun t : ℝ => ((n : ℂ) + 1) * (t : ℂ) ^ n * (Complex.exp (-(r * t)) / (-r))) =
        fun t : ℝ => (-((n : ℂ) + 1) / r) * ((t : ℂ) ^ n * Complex.exp (-(r * t))) := by
      funext t; field_simp
    rw [e, integral_const_mul, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- Original common smooth cutoffs tend UNIFORMLY to the actual Laplace
moment on the whole half-plane Re(r)>=delta>0. This identifies each native
zero transform, but does not by itself dominate the infinite zero sum. -/
theorem smooth_laplace_moment_uniform (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    TendstoUniformlyOn
      (fun (n : ℕ) (r : ℂ) => ∫ x in Ioi (0 : ℝ),
        (positiveCutoff ((n:ℝ)+1) x : ℂ) *
          ((x : ℂ)^k * Complex.exp (-(r*x))))
      (fun r : ℂ => (k.factorial : ℂ) / r^(k+1)) atTop {r : ℂ | δ ≤ r.re} := by
  have hu := uniform_integral_cutoff_ae_bound (volume.restrict (Ioi (0:ℝ)))
    {r : ℂ | δ ≤ r.re}
    (fun n x => positiveCutoff ((n:ℝ)+1) x)
    (fun r x => (x:ℂ)^k * Complex.exp (-(r*x)))
    (fun x => ‖(x:ℂ)^k * Complex.exp (-((δ:ℂ)*x))‖)
    (fun n => (positiveCutoff_smooth _).continuous.aestronglyMeasurable)
    (fun n x => positiveCutoff_bounds _ _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact positiveCutoff_tendsto x hx)
    ((integrableOn_pow_mul_cexp_neg k (by simpa using hδ : 0 < (δ:ℂ).re)).norm)
    (fun x => norm_nonneg _)
    (fun r _ => (show Continuous (fun x : ℝ => (x:ℂ)^k * Complex.exp (-(r*x))) by
      fun_prop).aestronglyMeasurable)
    (by
      intro r hr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_pow_mul_cexp_neg k r hx, norm_pow_mul_cexp_neg k (δ:ℂ) hx,
        Complex.ofReal_re, Real.rpow_one]
      apply mul_le_mul_of_nonneg_left
      · apply Real.exp_le_exp.mpr
        change δ ≤ r.re at hr
        change 0 < x at hx
        nlinarith
      · exact Real.rpow_nonneg (le_of_lt hx) _)
  apply hu.congr_right
  intro r hr
  exact integral_pow_mul_cexp_neg k (lt_of_lt_of_le hδ hr)

/-- In the manuscript's centered coordinate z=s-1/2, the logged transform
at a genuine zero rho is exactly 1/(s-rho)^2. No spectral relabeling occurs. -/
theorem logged_zero_transform_limit (ρ s : ℂ) (hs : ρ.re < s.re) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ),
      (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        ((x:ℂ) * Complex.exp (-((s-ρ)*x)))) atTop (𝓝 (1/(s-ρ)^2)) := by
  have hd : 0 < (s-ρ).re := by simp; linarith
  have hu := (smooth_laplace_moment_uniform 1 hd).tendsto_at
    (show (s-ρ) ∈ {r : ℂ | (s-ρ).re ≤ r.re} from by simp)
  simpa using hu

/-- The fixed reference value survives the common-cutoff subtraction. -/
theorem anchored_zero_transform_limit (ρ s w : ℂ)
    (hs : ρ.re < s.re) (hw : ρ.re < w.re) :
    Tendsto (fun n : ℕ =>
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        Complex.exp (-((s-ρ)*x))) -
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        Complex.exp (-((w-ρ)*x)))) atTop (𝓝 (1/(s-ρ)-1/(w-ρ))) := by
  have hs' : 0 < (s-ρ).re := by simp; linarith
  have hw' : 0 < (w-ρ).re := by simp; linarith
  have h1 := (smooth_laplace_moment_uniform 0 hs').tendsto_at
    (show (s-ρ) ∈ {r : ℂ | (s-ρ).re ≤ r.re} from by simp)
  have h2 := (smooth_laplace_moment_uniform 0 hw').tendsto_at
    (show (w-ρ) ∈ {r : ℂ | (w-ρ).re ≤ r.re} from by simp)
  simpa using h1.sub h2

/-- Each exact smooth-cutoff Laplace moment is integrable on the original
positive logarithmic half-line. This justifies taking subtraction inside. -/
theorem cutoff_moment_integrable (k n : ℕ) {r : ℂ} (hr : 0 < r.re) :
    IntegrableOn (fun x : ℝ => (positiveCutoff ((n:ℝ)+1) x : ℂ) *
      ((x:ℂ)^k * Complex.exp (-(r*x)))) (Ioi 0) := by
  refine (integrableOn_pow_mul_cexp_neg k hr).norm.mono' ?_ ?_
  · have hc : Continuous (fun x : ℝ => (positiveCutoff ((n:ℝ)+1) x : ℂ)) :=
      Complex.continuous_ofReal.comp (positiveCutoff_smooth _).continuous
    exact (hc.mul (by fun_prop)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (positiveCutoff_bounds _ _).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (positiveCutoff_bounds _ _).2

/-- One actual anchored test integral, with its reference term retained. -/
theorem anchored_zero_transform_single_integral (ρ s w : ℂ)
    (hs : ρ.re < s.re) (hw : ρ.re < w.re) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ),
      (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        (Complex.exp (-((s-ρ)*x)) - Complex.exp (-((w-ρ)*x))))
      atTop (𝓝 (1/(s-ρ)-1/(w-ρ))) := by
  have hs' : 0 < (s-ρ).re := by simp; linarith
  have hw' : 0 < (w-ρ).re := by simp; linarith
  have hi (n : ℕ) :
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        (Complex.exp (-((s-ρ)*x)) - Complex.exp (-((w-ρ)*x)))) =
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        Complex.exp (-((s-ρ)*x))) -
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        Complex.exp (-((w-ρ)*x))) := by
    simp only [mul_sub]
    apply integral_sub
    · simpa using cutoff_moment_integrable 0 n hs'
    · simpa using cutoff_moment_integrable 0 n hw'
  simpa only [hi] using anchored_zero_transform_limit ρ s w hs hw

/-- Original centered Mellin normalization for the logged test. Its actual
finite-zeta analytic multiplicity stays outside this scalar integral. -/
theorem logged_centered_mellin_limit (ρ z : ℂ) (hz : ρ.re - 1/2 < z.re) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ),
      (positiveCutoff ((n:ℝ)+1) x : ℂ) * (x:ℂ) * Complex.exp (-z*x) *
        Complex.exp ((ρ-1/2)*x)) atTop (𝓝 (1/(z+1/2-ρ)^2)) := by
  have hs : ρ.re < (z+1/2).re := by simp; linarith
  have h := logged_zero_transform_limit ρ (z+1/2) hs
  have he (n : ℕ) :
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) * (x:ℂ) *
        Complex.exp (-z*x) * Complex.exp ((ρ-1/2)*x)) =
      (∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
        ((x:ℂ) * Complex.exp (-((z+1/2-ρ)*x)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [mul_assoc]
    rw [← Complex.exp_add]
    congr 3
    ring
  simpa only [he] using h

theorem genuine_order_logged_mellin_limit (ρ z : ℂ)
    (hz : ρ.re - 1/2 < z.re) :
    Tendsto (fun n : ℕ => (analyticOrderNatAt riemannZeta ρ : ℂ) *
      ∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) * (x:ℂ) *
        Complex.exp (-z*x) * Complex.exp ((ρ-1/2)*x))
      atTop (𝓝 ((analyticOrderNatAt riemannZeta ρ : ℂ)/(z+1/2-ρ)^2)) := by
  simpa only [mul_one_div] using
    (logged_centered_mellin_limit ρ z hz).const_mul (analyticOrderNatAt riemannZeta ρ : ℂ)

#print axioms cutoff_moment_integrable
#print axioms anchored_zero_transform_single_integral
#print axioms logged_centered_mellin_limit
#print axioms genuine_order_logged_mellin_limit
#print axioms integral_pow_mul_cexp_neg
#print axioms smooth_laplace_moment_uniform
#print axioms logged_zero_transform_limit
#print axioms anchored_zero_transform_limit
end Masullo.LaplaceCutoff

namespace ManuscriptRH
open Complex Filter Topology Set MeasureTheory MasulloGRH.ConditionalMoment

theorem completedZeta_order_eq_finite {p : ℂ} (hpos : 0 < p.re) (hp1 : p ≠ 1) :
    analyticOrderNatAt completedRiemannZeta p = analyticOrderNatAt riemannZeta p := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hpos
  have hC : AnalyticAt ℂ completedRiemannZeta p := by
    have hd : DifferentiableOn ℂ completedRiemannZeta ({0, 1}ᶜ : Set ℂ) := by
      intro z hz
      have hz' : z ≠ 0 ∧ z ≠ 1 := by simpa using hz
      exact (differentiableAt_completedZeta hz'.1 hz'.2).differentiableWithinAt
    have hopen : IsOpen ({0, 1}ᶜ : Set ℂ) := by
      have he : ({0, 1}ᶜ : Set ℂ) = ({0}ᶜ : Set ℂ) ∩ ({1}ᶜ : Set ℂ) := by
        ext z
        simp
      rw [he]
      exact isOpen_compl_singleton.inter isOpen_compl_singleton
    exact hd.analyticOnNhd hopen p (by simpa using And.intro hp0 hp1)
  have hGamma : AnalyticAt ℂ (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) p :=
    Complex.differentiable_Gammaℝ_inv.analyticAt p
  have hGamma0 : (Complex.Gammaℝ p)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hpos)
  have he : riemannZeta =ᶠ[𝓝 p]
      completedRiemannZeta * (fun z => (Complex.Gammaℝ z)⁻¹) := by
    filter_upwards [continuousAt_id.eventually_ne hp0] with z hz
    change riemannZeta z = completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹
    rw [riemannZeta_def_of_ne_zero (by simpa using hz), div_eq_mul_inv]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hC hGamma,
    hGamma.analyticOrderAt_eq_zero.mpr hGamma0, add_zero]

/-- Main scaffold's GENUINE completed-zero labels and exact multiplicities
now attach to the ORIGINAL centered smooth logged Mellin transforms.
This is a single-zero scalar attachment, not the infinite trace interchange. -/
theorem genuineZero_logged_cutoff_limit (ρ : GenuineZero) (hpos : 0 < ρ.val.re)
    (z : ℂ) (hz : ρ.val.re - 1/2 < z.re) :
    Tendsto (fun n : ℕ => (zeroOrder ρ : ℂ) *
      ∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) * (x:ℂ) *
        Complex.exp (-z*x) * Complex.exp ((ρ.val-1/2)*x))
      atTop (𝓝 ((zeroOrder ρ : ℂ)/(z+1/2-ρ.val)^2)) := by
  unfold zeroOrder
  rw [completedZeta_order_eq_finite hpos ρ.property.2.2]
  exact Masullo.LaplaceCutoff.genuine_order_logged_mellin_limit ρ.val z hz

#print axioms completedZeta_order_eq_finite
#print axioms genuineZero_logged_cutoff_limit
end ManuscriptRH

open ArithmeticFunction LSeries
open scoped LSeries.notation
namespace Masullo.PrimeSeries
noncomputable def mangoldt : ℕ → ℂ := fun n => (vonMangoldt n : ℂ)
noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

/-- The finite-prime series has the MINUS logarithmic-derivative sign. -/
theorem prime_series_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries mangoldt s = -logDerivZeta s := by
  simpa [mangoldt, logDerivZeta, neg_div] using
    LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs

/-- Subtraction preserves the actual reference value at w. -/
theorem anchored_prime_series_eq {s w : ℂ} (hs : 1 < s.re) (hw : 1 < w.re) :
    (∑' n, (LSeries.term mangoldt s n - LSeries.term mangoldt w n)) =
      -logDerivZeta s + logDerivZeta w := by
  have hss : Summable (LSeries.term mangoldt s) := LSeriesSummable_vonMangoldt hs
  have hws : Summable (LSeries.term mangoldt w) := LSeriesSummable_vonMangoldt hw
  rw [hss.tsum_sub hws]
  change LSeries mangoldt s - LSeries mangoldt w = _
  rw [prime_series_eq hs, prime_series_eq hw]
  ring

/-- Exact Mathlib abscissa input for differentiating the prime series. -/
theorem mangoldt_abscissa_lt {s : ℂ} (hs : 1 < s.re) :
    abscissaOfAbsConv mangoldt < s.re := by
  have h : abscissaOfAbsConv mangoldt ≤ ((1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      LSeriesSummable_vonMangoldt (by simpa using hy)
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr hs)

/-- The logged prime series has the POSITIVE derivative-log-derivative sign. -/
theorem logged_prime_series_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (logMul mangoldt) s = deriv logDerivZeta s := by
  have he : (fun z => -LSeries mangoldt z) =ᶠ[𝓝 s] logDerivZeta := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    rw [prime_series_eq hz, neg_neg]
  have hd := (LSeries_hasDerivAt (mangoldt_abscissa_lt hs)).neg
  have hd' : deriv (fun z => -LSeries mangoldt z) s = LSeries (logMul mangoldt) s := by
    simpa using hd.deriv
  rw [← hd', he.deriv_eq]

/-- The manuscript Mellin parameter is shifted by exactly one half. -/
theorem shifted_prime_identities {z w : ℂ} (hz : 1/2 < z.re) (hw : 1/2 < w.re) :
    LSeries mangoldt (z+1/2) = -logDerivZeta (z+1/2) ∧
    (∑' n, (LSeries.term mangoldt (z+1/2) n - LSeries.term mangoldt (w+1/2) n)) =
      -logDerivZeta (z+1/2) + logDerivZeta (w+1/2) ∧
    LSeries (logMul mangoldt) (z+1/2) = deriv logDerivZeta (z+1/2) := by
  have hz' : 1 < (z+(1:ℂ)/2).re := by simp only [Complex.add_re]; norm_num; linarith
  have hw' : 1 < (w+(1:ℂ)/2).re := by simp only [Complex.add_re]; norm_num; linarith
  exact ⟨prime_series_eq hz', anchored_prime_series_eq hz' hw', logged_prime_series_eq hz'⟩

end Masullo.PrimeSeries

namespace Masullo.PrimeSeries
open Set

/-- Uniform dominated convergence for a common bounded series cutoff. -/
theorem uniform_series_cutoff {Z : Type*} (S : Set Z)
    (q : ℕ → ℕ → ℝ) (F : Z → ℕ → ℂ) (B : ℕ → ℝ)
    (hq : ∀ n k, 0 ≤ q n k ∧ q n k ≤ 1)
    (hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 1))
    (hB : Summable B) (hBpos : ∀ k, 0 ≤ B k)
    (hbound : ∀ z ∈ S, ∀ k, ‖F z k‖ ≤ B k) :
    TendstoUniformlyOn (fun n z => ∑' k : ℕ, (q n k : ℂ) * F z k)
      (fun z => ∑' k : ℕ, F z k) atTop S := by
  have heB (n k : ℕ) : 0 ≤ (1-q n k)*B k ∧ (1-q n k)*B k ≤ B k := by
    constructor
    · exact mul_nonneg (sub_nonneg.mpr (hq n k).2) (hBpos k)
    · nlinarith [(hq n k).1, (hq n k).2, hBpos k]
  have hes (n : ℕ) : Summable (fun k => (1-q n k)*B k) :=
    Summable.of_nonneg_of_le (fun k => (heB n k).1) (fun k => (heB n k).2) hB
  have ht : Tendsto (fun n => ∑' k : ℕ, (1-q n k)*B k) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence hB
      (fun k => (tendsto_const_nhds.sub (hqlim k)).mul_const (B k))
      (Eventually.of_forall fun n k => show ‖(1-q n k)*B k‖ ≤ B k by
        rw [Real.norm_eq_abs, abs_of_nonneg (heB n k).1]; exact (heB n k).2)
    simpa using h
  have hs (z : Z) (hz : z ∈ S) : Summable (F z) :=
    Summable.of_norm_bounded hB (hbound z hz)
  have hqs (n : ℕ) (z : Z) (hz : z ∈ S) :
      Summable (fun k => (q n k : ℂ) * F z k) := by
    refine Summable.of_norm_bounded hB fun k => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hq n k).1]
    exact (mul_le_mul_of_nonneg_left (hbound z hz k) (hq n k).1).trans
      (by nlinarith [(hq n k).2, hBpos k])
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn z hz
  rw [dist_eq_norm, ← (hs z hz).tsum_sub (hqs n z hz)]
  apply lt_of_le_of_lt (tsum_of_norm_bounded (hes n).hasSum fun k => ?_) hn
  have he : F z k - (q n k : ℂ) * F z k = ((1-q n k : ℝ) : ℂ) * F z k := by
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (hq n k).2)]
  exact mul_le_mul_of_nonneg_left (hbound z hz k) (sub_nonneg.mpr (hq n k).2)

/-- One convergent real Dirichlet series dominates a whole closed right
half-plane, uniformly even with unbounded imaginary parameter. -/
theorem term_norm_le_real {a : ℕ → ℂ} {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) (n : ℕ) :
    ‖LSeries.term a s n‖ ≤ ‖LSeries.term a (σ : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  split_ifs with hn
  · rfl
  · simp only [Complex.ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 hs)

/-- Applies to the genuine prime and logged prime series once their
arithmetic absolute convergence at σ>1 is supplied by Mathlib. -/
theorem LSeries_cutoff_uniform {a : ℕ → ℂ} {σ : ℝ}
    (ha : LSeriesSummable a (σ : ℂ))
    (q : ℕ → ℕ → ℝ) (hq : ∀ n k, 0 ≤ q n k ∧ q n k ≤ 1)
    (hqlim : ∀ k, Tendsto (fun n => q n k) atTop (𝓝 1)) :
    TendstoUniformlyOn (fun (n : ℕ) s => ∑' k : ℕ, (q n k : ℂ) * LSeries.term a s k)
      (LSeries a) atTop {s : ℂ | σ ≤ s.re} := by
  exact uniform_series_cutoff {s : ℂ | σ ≤ s.re} q (fun s k => LSeries.term a s k)
    (fun k => ‖LSeries.term a (σ : ℂ) k‖) hq hqlim ha.norm
    (fun k => norm_nonneg _) (fun s hs k => term_norm_le_real hs k)

#print axioms uniform_series_cutoff
#print axioms LSeries_cutoff_uniform

#print axioms prime_series_eq
#print axioms anchored_prime_series_eq
#print axioms logged_prime_series_eq
#print axioms shifted_prime_identities
end Masullo.PrimeSeries

namespace Masullo.PrimeSeries
open Set MasulloGRH.ConditionalMoment

/-- Changing the cutoff at n=0,1 is invisible for either genuine prime
coefficient family. It permits uniform use of the common cutoff theorem. -/
noncomputable def naturalCutoff (n k : ℕ) : ℝ :=
  if k ≤ 1 then 1 else positiveCutoff ((n : ℝ)+1) (Real.log k)

theorem naturalCutoff_bounds (n k : ℕ) :
    0 ≤ naturalCutoff n k ∧ naturalCutoff n k ≤ 1 := by
  unfold naturalCutoff
  split_ifs
  · exact ⟨zero_le_one, le_rfl⟩
  · exact positiveCutoff_bounds _ _

theorem naturalCutoff_tendsto (k : ℕ) :
    Tendsto (fun n => naturalCutoff n k) atTop (𝓝 1) := by
  by_cases hk : k ≤ 1
  · simp [naturalCutoff, hk]
  · have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast (lt_of_not_ge hk))
    simpa [naturalCutoff, hk] using positiveCutoff_tendsto (Real.log k) hlog

/-- The ORIGINAL smooth radial cutoff evaluated at log(n), with no raw
limit hypothesis. The n=0,1 terms vanish by the actual coefficient input. -/
theorem smooth_LSeries_cutoff_uniform {a : ℕ → ℂ} {σ : ℝ}
    (h1 : a 1 = 0) (ha : LSeriesSummable a (σ : ℂ)) :
    TendstoUniformlyOn
      (fun (n : ℕ) s => ∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term a s k)
      (LSeries a) atTop {s : ℂ | σ ≤ s.re} := by
  have hg := LSeries_cutoff_uniform ha naturalCutoff naturalCutoff_bounds naturalCutoff_tendsto
  have he : (fun (n : ℕ) s => ∑' k : ℕ, (naturalCutoff n k : ℂ) * LSeries.term a s k) =
      (fun (n : ℕ) s => ∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term a s k) := by
    funext n s
    apply tsum_congr
    intro k
    by_cases hk : k ≤ 1
    · interval_cases k <;> simp [LSeries.term, h1]
    · simp [naturalCutoff, hk]
  rwa [he] at hg

theorem logged_mangoldt_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (logMul mangoldt) s := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  change abscissaOfAbsConv ((logMul^[1]) mangoldt) < s.re
  rw [LSeries.absicssaOfAbsConv_logPowMul]
  exact mangoldt_abscissa_lt hs

/-- Both ACTUAL prime coefficient families have whole-sequence uniform
smooth-cutoff limits on every closed half-plane Re(s)>=σ>1. Their finite-zeta
identifications, signs, reference subtraction and 1/2 shift are proved above. -/
theorem prime_and_logged_smooth_cutoff_uniform {σ : ℝ} (hσ : 1 < σ) :
    TendstoUniformlyOn
      (fun (n : ℕ) s => ∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term mangoldt s k)
      (LSeries mangoldt) atTop {s : ℂ | σ ≤ s.re} ∧
    TendstoUniformlyOn
      (fun (n : ℕ) s => ∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term (logMul mangoldt) s k)
      (LSeries (logMul mangoldt)) atTop {s : ℂ | σ ≤ s.re} := by
  constructor
  · apply smooth_LSeries_cutoff_uniform
    · simp [mangoldt]
    · exact LSeriesSummable_vonMangoldt (by simpa using hσ)
  · apply smooth_LSeries_cutoff_uniform
    · simp [LSeries.logMul, mangoldt]
    · exact logged_mangoldt_summable (by simpa using hσ)

#print axioms smooth_LSeries_cutoff_uniform
#print axioms prime_and_logged_smooth_cutoff_uniform
end Masullo.PrimeSeries

namespace ManuscriptRH
open Complex Filter Topology

/-- A genuine full-zero term, with exactly the main scaffold's Mellin value. -/
noncomputable def fullZeroTerm (D : RationalTraceData) (φ : D.Test)
    (ρ : GenuineZero) : ℂ := (zeroOrder ρ : ℂ) * zeroTest D φ ρ

theorem interiorMultiplicity_le_order (p : Parameters) (ρ : GenuineZero) :
    interiorMultiplicity p ρ ≤ zeroOrder ρ := by
  unfold interiorMultiplicity
  split_ifs <;> omega

theorem actual_term_balance (D : RationalTraceData) (p : Parameters)
    (φ : D.Test) (ρ : GenuineZero) :
    nativeTerm D p φ ρ + (omittedTerm D p φ ρ - edgeTerm D p φ ρ) =
      fullZeroTerm D φ ρ := by
  unfold nativeTerm omittedTerm edgeTerm fullZeroTerm
  rw [Nat.cast_add, Nat.cast_sub (interiorMultiplicity_le_order p ρ)]
  ring

/-- The exact corrected trace already supplies the full explicit formula.
This is valid for BOTH original sharp families and the identical PA operator.
It is not an uncorrected native formula or a zero-exclusion theorem. -/
theorem actual_matched_traces_full_formula (D : RationalTraceData)
    (hs : SpectralIdentification D) (hg : GeometricTrace D)
    {p : Parameters} (hp : D.allowed p) {φ : D.Test} (hφ : Admissible D φ)
    (k : TestFamily) :
    Summable (fun ρ => ‖fullZeroTerm D (familyTest D k φ) ρ‖) ∧
      (∑' ρ, fullZeroTerm D (familyTest D k φ) ρ) =
        arithmeticTerm D (familyTest D k φ) := by
  have hN := (hs p hp φ hφ k).1
  have hR := (hg p hp φ hφ k).2.1
  have hB := (hg p hp φ hφ k).2.2.1
  have hFn : Summable (fun ρ => ‖fullZeroTerm D (familyTest D k φ) ρ‖) := by
    apply Summable.of_nonneg_of_le (fun ρ => norm_nonneg _)
      (fun ρ => ?_) (hN.add (hR.add hB))
    rw [← actual_term_balance D p (familyTest D k φ) ρ]
    exact (norm_add_le _ _).trans
      (add_le_add (le_refl _) (norm_sub_le _ _))
  refine ⟨hFn, ?_⟩
  have hsum : nativeSum D p (familyTest D k φ) +
      stripCorrection D p (familyTest D k φ) =
      ∑' ρ, fullZeroTerm D (familyTest D k φ) ρ := by
    unfold nativeSum stripCorrection
    rw [← hR.of_norm.tsum_sub hB.of_norm,
      ← hN.of_norm.tsum_add (hR.of_norm.sub hB.of_norm)]
    exact tsum_congr (actual_term_balance D p (familyTest D k φ))
  have hm := match_traces D hs hg p hp φ hφ k
  linear_combination hm - hsum

/-- A bounded punctured germ cannot carry a quadratic pole. No holomorphy
or assumed convergence of the correction is needed for this elementary step. -/
theorem bounded_germ_quadratic_limit {q : ℂ} {C : ℂ → ℂ} {M : ℝ}
    (hb : ∀ᶠ z in 𝓝[≠] q, ‖C z‖ ≤ M) :
    Tendsto (fun z => (z-q)^2 * C z) (𝓝[≠] q) (𝓝 0) := by
  have hz : Tendsto (fun z : ℂ => (z-q)^2) (𝓝[≠] q) (𝓝 0) := by
    simpa using (((continuousAt_id.sub continuousAt_const).pow 2 :
      ContinuousAt (fun z : ℂ => (z-q)^2) q).tendsto.mono_left nhdsWithin_le_nhds)
  have ht : Tendsto (fun z : ℂ => ‖(z-q)^2‖ * M) (𝓝[≠] q) (𝓝 0) := by
    simpa using hz.norm.mul_const M
  refine squeeze_zero_norm' ?_ ht
  filter_upwards [hb] with z hzb
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hzb (norm_nonneg _)

/-- The corrected identity forces actual local unboundedness at every
genuine zero. Boundary freedom, subtraction and native holomorphy do not
supply the missing common bound. -/
theorem chapter13_witness_correction_unbounded (D : RationalTraceData)
    {p : Parameters} {q : ℂ} (hq : q ≠ 1) (hz : riemannZeta q = 0)
    (hw : Chapter13Witness D p q) :
    ¬ ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] q, ‖D.loggedCorrection p z‖ ≤ M := by
  rintro ⟨M, hM⟩
  exact ((chapter13_witness_control_iff D hq hw).mp
    (bounded_germ_quadratic_limit hM)) hz

/-- Precise Montel attack: if a cutoff family converges pointwise to the
actual correction on a punctured neighborhood of an omitted genuine zero,
then NO cutoff-independent local bound can hold there. The conclusion does
not assert that the actual cutoffs have such a punctured limit. -/
theorem chapter13_no_bounded_correction_approximants (D : RationalTraceData)
    {p : Parameters} {q : ℂ} (hq : q ≠ 1) (hz : riemannZeta q = 0)
    (hw : Chapter13Witness D p q) (C : ℕ → ℂ → ℂ)
    (hc : ∀ᶠ z in 𝓝[≠] q,
      Tendsto (fun n => C n z) atTop (𝓝 (D.loggedCorrection p z))) :
    ¬ ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] q, ∀ n : ℕ, ‖C n z‖ ≤ M := by
  rintro ⟨M, hM⟩
  apply chapter13_witness_correction_unbounded D hq hz hw
  refine ⟨M, ?_⟩
  filter_upwards [hc, hM] with z hzc hzb
  exact le_of_tendsto' hzc.norm hzb

/-- Strongest connected conclusion from the corrected ACTUAL trace
interfaces and their regularized germs. The explicit formula is obtained;
the surviving pole-control premise is characterized, not assumed proved. -/
theorem trace_formula_and_correction_condition (D : RationalTraceData)
    (hs : SpectralIdentification D) (hg : GeometricTrace D)
    (hl : Chapter13RegularizedLimit D) :
    (∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
      Summable (fun ρ => ‖fullZeroTerm D (familyTest D k φ) ρ‖) ∧
      (∑' ρ, fullZeroTerm D (familyTest D k φ) ρ) =
        arithmeticTerm D (familyTest D k φ)) ∧
    (Chapter13PairedControl D ↔ RiemannHypothesis) ∧
    (∀ q : ℂ, 1/2 < q.re → q ≠ 1 → riemannZeta q = 0 →
      ∃ p : Parameters, Chapter13Witness D p q ∧
        ¬ ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] q, ‖D.loggedCorrection p z‖ ≤ M) := by
  refine ⟨fun _ hp _ hφ k => actual_matched_traces_full_formula D hs hg hp hφ k,
    chapter13_paired_control_iff_riemannHypothesis D hl, ?_⟩
  intro q hq hq1 hz
  obtain ⟨p, hp, hw, hH, he⟩ := hl q hq hq1
  have hwit : Chapter13Witness D p q := ⟨hp, hw, hH, he⟩
  exact ⟨p, hwit, chapter13_witness_correction_unbounded D hq1 hz hwit⟩

#print axioms actual_matched_traces_full_formula
#print axioms bounded_germ_quadratic_limit
#print axioms chapter13_no_bounded_correction_approximants
#print axioms trace_formula_and_correction_condition
end ManuscriptRH

namespace Masullo.PrimeSeries
open Set MasulloGRH.ConditionalMoment

/-- Actual smooth prime cutoffs converge UNIFORMLY directly to genuine
finite-zeta derivatives, with the negative unlogged and positive logged signs. -/
theorem genuine_zeta_prime_cutoffs_uniform {σ : ℝ} (hσ : 1 < σ) :
    TendstoUniformlyOn
      (fun (n : ℕ) s => ∑' k : ℕ,
        (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term mangoldt s k)
      (fun s => -logDerivZeta s) atTop {s : ℂ | σ ≤ s.re} ∧
    TendstoUniformlyOn
      (fun (n : ℕ) s => ∑' k : ℕ,
        (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term (logMul mangoldt) s k)
      (deriv logDerivZeta) atTop {s : ℂ | σ ≤ s.re} := by
  have h := prime_and_logged_smooth_cutoff_uniform hσ
  constructor
  · apply h.1.congr_right
    intro s hs
    exact prime_series_eq (lt_of_lt_of_le hσ hs)
  · apply h.2.congr_right
    intro s hs
    exact logged_prime_series_eq (lt_of_lt_of_le hσ hs)

theorem cutoff_prime_summable (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun k : ℕ =>
      (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term mangoldt s k) := by
  have hsum : Summable (LSeries.term mangoldt s) := LSeriesSummable_vonMangoldt hs
  apply Summable.of_norm_bounded hsum.norm
  intro k
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (positiveCutoff_bounds _ _).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (positiveCutoff_bounds _ _).2

/-- A SINGLE common-cutoff anchored prime sum has the exact fixed-reference
limit. This avoids subtracting divergent raw archimedean quantities. -/
theorem genuine_zeta_anchored_prime_cutoff {s w : ℂ}
    (hs : 1 < s.re) (hw : 1 < w.re) :
    Tendsto (fun n : ℕ => ∑' k : ℕ,
      (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) *
        (LSeries.term mangoldt s k - LSeries.term mangoldt w k))
      atTop (𝓝 (-logDerivZeta s + logDerivZeta w)) := by
  have hS := (genuine_zeta_prime_cutoffs_uniform hs).1.tendsto_at (x := s) (by change s.re ≤ s.re; exact le_rfl)
  have hW := (genuine_zeta_prime_cutoffs_uniform hw).1.tendsto_at (x := w) (by change w.re ≤ w.re; exact le_rfl)
  have h := hS.sub hW
  have he (n : ℕ) :
      (∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) *
        (LSeries.term mangoldt s k - LSeries.term mangoldt w k)) =
      (∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term mangoldt s k) -
      (∑' k : ℕ, (positiveCutoff ((n:ℝ)+1) (Real.log k) : ℂ) * LSeries.term mangoldt w k) := by
    simp_rw [mul_sub]
    exact (cutoff_prime_summable n hs).tsum_sub (cutoff_prime_summable n hw)
  simpa only [he, sub_neg_eq_add] using h

#print axioms genuine_zeta_prime_cutoffs_uniform
#print axioms genuine_zeta_anchored_prime_cutoff
end Masullo.PrimeSeries


/-! D correction application R01. The preceding review definitions are preserved
verbatim. New declarations below use those actual definitions. -/
namespace DCorrectionApplication
open Complex Filter Topology ManuscriptRH
theorem fermat_eventually_large_norm {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, R ≤ ‖ρ j‖ := by
  have _em := Classical.em
  have h0 := hsum.tendsto_atTop_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]


theorem reciprocal_square_tail_bound {rho z : ℂ} (hrho : rho ≠ 0)
    (hlarge : 2 * ‖z‖ ≤ ‖rho‖) :
    ‖(1 : ℂ) / (z-rho)^2‖ ≤ 4 / ‖rho‖^2 := by
  have hn : 0 < ‖rho‖ := norm_pos_iff.mpr hrho
  have ht : ‖rho‖ - ‖z‖ ≤ ‖z-rho‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  have hd : ‖rho‖ / 2 ≤ ‖z-rho‖ := by linarith
  have hd0 : 0 < ‖z-rho‖ := by linarith
  rw [norm_div, norm_one, norm_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (sq_pos_of_pos hn)).2
  nlinarith [sq_nonneg (‖z-rho‖ - ‖rho‖ / 2)]

theorem square_resolvent_summable {rho : ℕ → ℂ}
    (hrho : ∀ j, rho j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (rho j))⁻¹) (z : ℂ) :
    Summable (fun j => (1 : ℂ) / (z-rho j)^2) := by
  apply (hsum.mul_left 4).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [fermat_eventually_large_norm hrho hsum
    (show (0:ℝ) < 2 * (‖z‖+1) by positivity)] with j hj
  have hh := reciprocal_square_tail_bound (hrho j)
    (show 2 * ‖z‖ ≤ ‖rho j‖ by linarith)
  simpa only [Complex.normSq_eq_norm_sq, div_eq_mul_inv] using hh

/-- At an actual zero strictly right of the retained strip, every jet is
omitted. Both original boundary and interior definitions are used. -/
theorem actual_right_deficit (p : Parameters) (rho : GenuineZero)
    (hright : p.width < rho.val.re - 1/2) :
    interiorMultiplicity p rho = 0 ∧ boundaryMultiplicity p rho = 0 := by
  have hpos : 0 < rho.val.re - 1/2 := lt_trans p.width_pos hright
  have hi : ¬ |rho.val.re - 1/2| < p.width := by
    rw [abs_of_pos hpos]
    linarith
  have he : ¬ |rho.val.re - 1/2| = p.width := by
    rw [abs_of_pos hpos]
    linarith
  constructor
  · unfold interiorMultiplicity
    exact if_neg hi
  · unfold boundaryMultiplicity
    exact if_neg he

/-- The actual omitted-minus-edge coefficient, not a replacement trace. -/
theorem actual_right_correction_term (D : RationalTraceData) (p : Parameters)
    (phi : D.Test) (rho : GenuineZero)
    (hright : p.width < rho.val.re - 1/2) :
    omittedTerm D p phi rho - edgeTerm D p phi rho =
      (zeroOrder rho : ℂ) * zeroTest D phi rho := by
  obtain ⟨hi, he⟩ := actual_right_deficit p rho hright
  simp [omittedTerm, edgeTerm, hi, he]

/-- Exact original smooth logged Mellin cutoff for the missing coefficient.
This is a scalar attachment; the infinite cutoff interchange is proved on paper. -/
theorem actual_right_logged_cutoff (p : Parameters) (rho : GenuineZero)
    (hright : p.width < rho.val.re - 1/2) (z : ℂ)
    (hz : rho.val.re - 1/2 < z.re) :
    Tendsto (fun n : ℕ =>
      (((zeroOrder rho - interiorMultiplicity p rho : ℕ) : ℂ) -
        (boundaryMultiplicity p rho : ℂ)) *
      ∫ x in Set.Ioi (0:ℝ),
        (MasulloGRH.ConditionalMoment.positiveCutoff ((n:ℝ)+1) x : ℂ) *
        (x:ℂ) * Complex.exp (-z*x) * Complex.exp ((rho.val-1/2)*x))
      atTop (𝓝 ((zeroOrder rho : ℂ)/(z+1/2-rho.val)^2)) := by
  obtain ⟨hi, he⟩ := actual_right_deficit p rho hright
  have hpos : 0 < rho.val.re := by linarith [p.width_pos]
  simpa only [hi, he, Nat.sub_zero, Nat.cast_zero, sub_zero] using
    genuineZero_logged_cutoff_limit rho hpos z hz

#print axioms fermat_eventually_large_norm
#print axioms square_resolvent_summable
#print axioms actual_right_correction_term
#print axioms actual_right_logged_cutoff
end DCorrectionApplication

/-! R02: infinite original logged-cutoff sum, with the actual missing-jet mask.
The integration-by-parts majorant is a PAPER input, explicitly exposed below;
neither correction control nor a nonvanishing conclusion is a premise. -/
namespace DCorrectionApplicationR02
open Complex Filter Topology MeasureTheory Set ManuscriptRH
open DCorrectionApplication MasulloGRH.ConditionalMoment

theorem square_resolvent_norm_summable {rho : ℕ → ℂ}
    (hrho : ∀ j, rho j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (rho j))⁻¹) (z : ℂ) :
    Summable (fun j => ‖(1 : ℂ) / (z-rho j)^2‖) := by
  apply (hsum.mul_left 4).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [fermat_eventually_large_norm hrho hsum
    (show (0:ℝ) < 2 * (‖z‖+1) by positivity)] with j hj
  rw [norm_norm]
  have hh := reciprocal_square_tail_bound (hrho j)
    (show 2 * ‖z‖ ≤ ‖rho j‖ by linarith)
  simpa only [Complex.normSq_eq_norm_sq, div_eq_mul_inv] using hh

noncomputable def missingCopy (p : Parameters) (rho : GenuineZero) (k : ℕ) : ℂ := by
  classical
  exact if AdmittedJet p rho k then 0 else 1

theorem missingCopy_norm_le (p : Parameters) (rho : GenuineZero) (k : ℕ) :
    ‖missingCopy p rho k‖ ≤ 1 := by
  classical
  unfold missingCopy
  split_ifs <;> simp

noncomputable def originalLoggedMoment (n : ℕ) (rho z : ℂ) : ℂ :=
  ∫ x in Ioi (0:ℝ), (positiveCutoff ((n:ℝ)+1) x : ℂ) *
    ((x:ℂ) * Complex.exp (-((z-rho)*x)))

/-- The exact common smooth-cutoff correction over the multiplicity enumeration.
The source supplies reciprocal-square summability. The explicit hbound is the
uniform two-integration-by-parts estimate proved in CORRECTION_APPLICATION_R02.
No finite-test trace equality or zero location right of 1/2 is assumed here. -/
theorem actual_logged_copy_series_limit (p : Parameters)
    (rho : ℕ → GenuineZero) (jet : ℕ → ℕ)
    (hsource : Summable fun j => (Complex.normSq (rho j).val)⁻¹)
    (z : ℂ) (hz : ∀ j, (rho j).val.re < z.re)
    (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ n j, ‖originalLoggedMoment n (rho j).val z‖ ≤
      C * ‖(1 : ℂ)/(z-(rho j).val)^2‖) :
    Tendsto (fun n => ∑' j, missingCopy p (rho j) (jet j) *
      originalLoggedMoment n (rho j).val z) atTop
      (𝓝 (∑' j, missingCopy p (rho j) (jet j) *
        ((1 : ℂ)/(z-(rho j).val)^2))) := by
  have hs := (square_resolvent_norm_summable
    (fun j => (rho j).property.2.1) hsource z).mul_left C
  apply tendsto_tsum_of_dominated_convergence hs
  · intro j
    exact (Masullo.LaplaceCutoff.logged_zero_transform_limit
      (rho j).val z (hz j)).const_mul (missingCopy p (rho j) (jet j))
  · exact Eventually.of_forall fun n j => by
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖originalLoggedMoment n (rho j).val z‖ :=
          mul_le_mul_of_nonneg_right (missingCopy_norm_le p (rho j) (jet j))
            (norm_nonneg _)
        _ ≤ _ := by simpa using hbound n j

/-- Both original logged sharp tests, anchored with the SAME fixed reference.
This is subtraction of the two genuine common-cutoff limits, not deletion
of the reference value. -/
theorem actual_anchored_logged_copy_series_limit (p : Parameters)
    (rho : ℕ → GenuineZero) (jet : ℕ → ℕ)
    (hsource : Summable fun j => (Complex.normSq (rho j).val)⁻¹)
    (z w : ℂ) (hz : ∀ j, (rho j).val.re < z.re)
    (hw : ∀ j, (rho j).val.re < w.re)
    (C : ℝ) (hC : 0 ≤ C)
    (hzbound : ∀ n j, ‖originalLoggedMoment n (rho j).val z‖ ≤
      C * ‖(1 : ℂ)/(z-(rho j).val)^2‖)
    (hwbound : ∀ n j, ‖originalLoggedMoment n (rho j).val w‖ ≤
      C * ‖(1 : ℂ)/(w-(rho j).val)^2‖) :
    Tendsto (fun n =>
      (∑' j, missingCopy p (rho j) (jet j) * originalLoggedMoment n (rho j).val z) -
      (∑' j, missingCopy p (rho j) (jet j) * originalLoggedMoment n (rho j).val w))
      atTop (𝓝 ((∑' j, missingCopy p (rho j) (jet j) * ((1:ℂ)/(z-(rho j).val)^2)) -
        (∑' j, missingCopy p (rho j) (jet j) * ((1:ℂ)/(w-(rho j).val)^2)))) :=
  (actual_logged_copy_series_limit p rho jet hsource z hz C hC hzbound).sub
    (actual_logged_copy_series_limit p rho jet hsource w hw C hC hwbound)

#print axioms square_resolvent_norm_summable
#print axioms actual_logged_copy_series_limit
#print axioms actual_anchored_logged_copy_series_limit
end DCorrectionApplicationR02

/-! One common physical cutoff for the four actual trace families.
The hypotheses expose the uniform cutoff estimate, not correction control.
Its application to PA on the two original weighted spaces is in R03.md. -/
namespace DCorrectionApplicationR03
open Filter Topology

theorem common_physical_diagonal
    (cut : ℕ → ℕ → Fin 2 → Fin 2 → ℂ → ℂ)
    (uncut : ℕ → Fin 2 → Fin 2 → ℂ → ℂ)
    (K : ℕ → Set ℂ) (err : ℕ → ℝ)
    (hphysical : ∀ n, ∃ cutoffBound : ℕ, ∀ R, cutoffBound ≤ R → ∀ b j z, z ∈ K n →
      ‖cut n R b j z - uncut n b j z‖ ≤ err n) :
    ∃ R : ℕ → ℕ, (∀ n, n ≤ R n) ∧
      ∀ n b j z, z ∈ K n →
        ‖cut n (R n) b j z - uncut n b j z‖ ≤ err n := by
  classical
  choose cutoffBound hBound using hphysical
  refine ⟨fun n => max n (cutoffBound n), fun n => le_max_left _ _, ?_⟩
  intro n b j z hz
  exact hBound n _ (le_max_right _ _) b j z hz

/-- Error for wide minus narrow traces, for either sharp test. -/
theorem correction_diagonal_error (a b c d : ℂ) (e : ℝ)
    (ha : ‖a-b‖ ≤ e) (hc : ‖c-d‖ ≤ e) :
    ‖(a-c)-(b-d)‖ ≤ 2*e := by
  have he : (a-c)-(b-d) = (a-b)-(c-d) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The selected actual physical traces inherit the independently proved
Fermat cutoff-series limit. No zero-limit correction premise is present. -/
theorem correction_diagonal_limit
    (physical exactValue : ℕ → ℂ) (target : ℂ) (err : ℕ → ℝ)
    (herr : Tendsto err atTop (𝓝 0))
    (hcut : ∀ n, ‖physical n - exactValue n‖ ≤ 2 * err n)
    (hexact : Tendsto exactValue atTop (𝓝 target)) :
    Tendsto physical atTop (𝓝 target) := by
  have hnorm : Tendsto (fun n => ‖physical n-exactValue n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hcut (by simpa using herr.const_mul 2)
  have hdiff : Tendsto (fun n => physical n-exactValue n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa using hdiff.add hexact

#print axioms common_physical_diagonal
#print axioms correction_diagonal_error
#print axioms correction_diagonal_limit
end DCorrectionApplicationR03

/-! The actual wide Riesz block lies in the geometric correction kernel.
In the application B and C are the shifted wide and narrow convolution
operators, and J is the actual dense quotient map. No assertion about a
zero-free half-plane or a zero correction is a premise. -/
namespace DCorrectionApplicationR04
open Filter Topology

theorem root_block_in_geometric_kernel
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (B : E →L[ℂ] E) (C : F →L[ℂ] F) (J : E →L[ℂ] F)
    (hJC : ∀ x, J (B x) = C (J x)) (hC : Function.Injective C)
    (n : ℕ) (x : E) (hx : (fun y => B y)^[n] x = 0) : J x = 0 := by
  induction n generalizing x with
  | zero => simpa using congrArg J hx
  | succ n ih =>
    have hBx : (fun y => B y)^[n] (B x) = 0 := by
      simpa only [Function.iterate_succ_apply] using hx
    have hJx : J (B x) = 0 := ih (B x) hBx
    apply hC
    simpa only [_root_.map_zero, ← hJC] using hJx

/-- Negative sharp support places the pole at the reflected zero 1-rho. -/
theorem reflected_negative_exponent (z q : ℂ) :
    (z-(1/2:ℂ)) + ((1-q)-(1/2:ℂ)) = z-q := by ring

/-- A genuine finite root block has the full multiplicity trace, despite
its possible nonorthogonal Jordan coordinates. This is a matrix trace
identity, not an identification of the ambient operator with a zero model. -/
theorem root_block_trace {m : ℕ} (a : ℂ)
    (N : Matrix (Fin m) (Fin m) ℂ) (hN : ∀ i, N i i = 0) :
    Matrix.trace (a • (1 : Matrix (Fin m) (Fin m) ℂ) + N) = (m:ℂ)*a := by
  classical
  simp [Matrix.trace, Matrix.diag, hN, mul_comm]

/-- Both anchored scalar block transforms keep the SAME reference. -/
theorem anchored_block_scaled_limit (m : ℕ) (q b : ℂ)
    (hq : q ≠ b) :
    Tendsto (fun z => (z-q)^2 * ((m:ℂ) *
      ((1:ℂ)/(z-q)^2 - (1:ℂ)/(b-q)^2))) (𝓝[≠] q) (𝓝 (m:ℂ)) := by
  have ht : Tendsto (fun z : ℂ => (m:ℂ) - (z-q)^2 * ((m:ℂ)/(b-q)^2))
      (𝓝[≠] q) (𝓝 (m:ℂ)) := by
    have hc : ContinuousAt (fun z : ℂ =>
        (m:ℂ) - (z-q)^2 * ((m:ℂ)/(b-q)^2)) q := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzq : z-q ≠ 0 := sub_ne_zero.mpr hz
  have hbq : b-q ≠ 0 := sub_ne_zero.mpr hq.symm
  field_simp [hzq, hbq]

#print axioms root_block_in_geometric_kernel
#print axioms root_block_trace
#print axioms anchored_block_scaled_limit
end DCorrectionApplicationR04
