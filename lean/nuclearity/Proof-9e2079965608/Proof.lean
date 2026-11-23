import Mathlib

open Complex Filter Set
open scoped Topology

namespace MasulloGRH

/-- Twice the genuine Riemann xi function, with arbitrary unitary norm twist.
The removable pole values are filled using Mathlib's entire completed kernel. -/
noncomputable def rationalHeckeXi (τ : ℝ) (s : ℂ) : ℂ :=
  (s + Complex.I * τ) * (s + Complex.I * τ - 1) *
    completedRiemannZeta₀ (s + Complex.I * τ) + 1

/-- The actual completed Hecke function for the pure norm family over Q. -/
noncomputable def rationalHeckeCompleted (τ : ℝ) (s : ℂ) : ℂ :=
  completedRiemannZeta (s + Complex.I * τ)

noncomputable def rationalHeckeFinite (τ : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + Complex.I * τ)

/-- The genuine zeros, not an unconstrained sequence or a critical-line subset. -/
def RationalHeckeZero (τ : ℝ) := {s : ℂ // rationalHeckeXi τ s = 0}

noncomputable def rationalHeckeMultiplicity (τ : ℝ) (s : ℂ) : ℕ :=
  analyticOrderNatAt (rationalHeckeXi τ) s

/-- Each genuine zero is repeated its analytic multiplicity many times. -/
def RationalHeckeDivisor (τ : ℝ) :=
  (s : RationalHeckeZero τ) × Fin (rationalHeckeMultiplicity τ s.val)

theorem rationalHeckeXi_at_pole (τ : ℝ) :
    rationalHeckeXi τ (-Complex.I * τ) = 1 := by
  simp [rationalHeckeXi]

theorem rationalHeckeXi_eq_completed (τ : ℝ) (s : ℂ)
    (h0 : s + Complex.I * τ ≠ 0) (h1 : s + Complex.I * τ ≠ 1) :
    rationalHeckeXi τ s =
      (s + Complex.I * τ) * (s + Complex.I * τ - 1) *
        rationalHeckeCompleted τ s := by
  unfold rationalHeckeXi rationalHeckeCompleted
  rw [completedRiemannZeta_eq]
  have h10 : 1 - (s + Complex.I * τ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp [h0, h10]
  ring

theorem rationalHeckeXi_zero_iff (τ : ℝ) (s : ℂ)
    (h0 : s + Complex.I * τ ≠ 0) (h1 : s + Complex.I * τ ≠ 1) :
    rationalHeckeXi τ s = 0 ↔ rationalHeckeCompleted τ s = 0 := by
  rw [rationalHeckeXi_eq_completed τ s h0 h1]
  simp [mul_eq_zero, h0, sub_ne_zero.mpr h1]

#check rationalHeckeXi_at_pole
#print axioms rationalHeckeXi_at_pole
#check rationalHeckeXi_eq_completed
#print axioms rationalHeckeXi_eq_completed
#check rationalHeckeXi_zero_iff
#print axioms rationalHeckeXi_zero_iff

/-- Entirety is inherited from the actual theta-integral completed zeta kernel. -/
theorem rationalHeckeXi_analytic (τ : ℝ) :
    AnalyticOnNhd ℂ (rationalHeckeXi τ) Set.univ := by
  have hd : Differentiable ℂ (rationalHeckeXi τ) := by
    unfold rationalHeckeXi
    exact (((differentiable_id.add_const (Complex.I * τ)).mul
      ((differentiable_id.add_const (Complex.I * τ)).sub_const 1)).mul
      (differentiable_completedZeta₀.comp
        (differentiable_id.add_const (Complex.I * τ)))).add_const 1
  intro s hs
  exact hd.analyticAt s

/-- Local finiteness for the genuine pole-cancelled zeta divisor, all norm twists. -/
theorem rationalHeckeXi_zeros_locally_finite (τ : ℝ) (s : ℂ) :
    ∃ U ∈ nhds s, Set.Finite (U ∩ {z | rationalHeckeXi τ z = 0}) := by
  have hn : rationalHeckeXi τ (-Complex.I * τ) ≠ 0 := by
    rw [rationalHeckeXi_at_pole]
    exact one_ne_zero
  have h := (rationalHeckeXi_analytic τ).preimage_zero_mem_codiscreteWithin
    hn (Set.mem_univ _) isConnected_univ
  have hlocal := codiscreteWithin_iff_locallyFiniteComplementWithin.mp h s (Set.mem_univ _)
  simpa using hlocal

/-- No genuine zero has infinite analytic order; no nonvanishing premise is assumed. -/
theorem rationalHeckeXi_order_finite (τ : ℝ) (s : ℂ) :
    analyticOrderAt (rationalHeckeXi τ) s ≠ ⊤ := by
  have hA := rationalHeckeXi_analytic τ
  have hbase : analyticOrderAt (rationalHeckeXi τ) (-Complex.I * τ) = 0 :=
    (hA _ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr (by
      rw [rationalHeckeXi_at_pole]; exact one_ne_zero)
  exact hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ _) (by rw [hbase]; simp)

theorem rationalHeckeXi_zero_order_positive (τ : ℝ) (s : ℂ)
    (hs : rationalHeckeXi τ s = 0) :
    0 < analyticOrderAt (rationalHeckeXi τ) s := by
  exact bot_lt_iff_ne_bot.mpr (analyticOrderAt_ne_zero.mpr
    ⟨rationalHeckeXi_analytic τ s (Set.mem_univ _), hs⟩)

#check rationalHeckeXi_analytic
#print axioms rationalHeckeXi_analytic
#check rationalHeckeXi_zeros_locally_finite
#print axioms rationalHeckeXi_zeros_locally_finite
#check rationalHeckeXi_order_finite
#print axioms rationalHeckeXi_order_finite
#check rationalHeckeXi_zero_order_positive
#print axioms rationalHeckeXi_zero_order_positive

/-! Round 6: actual finite/completed divisor identification, adapting the
untwisted argument in frozen r05/final/B/Proof.lean to every norm twist. -/

theorem rationalHeckeMultiplicity_pos_iff (τ : ℝ) (s : ℂ) :
    0 < rationalHeckeMultiplicity τ s ↔ rationalHeckeXi τ s = 0 := by
  have hc := Nat.cast_analyticOrderNatAt (rationalHeckeXi_order_finite τ s)
  rw [Nat.pos_iff_ne_zero]
  change analyticOrderNatAt (rationalHeckeXi τ) s ≠ 0 ↔ _
  rw [← Nat.cast_ne_zero (R := ℕ∞), hc]
  exact (rationalHeckeXi_analytic τ s (Set.mem_univ _)).analyticOrderAt_ne_zero

theorem rationalHeckeXi_at_other_pole (τ : ℝ) :
    rationalHeckeXi τ (1 - Complex.I * τ) = 1 := by
  simp [rationalHeckeXi]

theorem rationalHeckeXi_zero_iff_finite (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    rationalHeckeXi τ s = 0 ↔ rationalHeckeFinite τ s = 0 := by
  have hre : (s + Complex.I * τ).re = s.re := by simp [Complex.mul_re]
  have hp : 0 < (s + Complex.I * τ).re := by rwa [hre]
  have h0 : s + Complex.I * τ ≠ 0 := by intro h; simp [h] at hp
  have h1 : s + Complex.I * τ ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [← hre, h]; simp
    linarith
  rw [rationalHeckeXi_zero_iff τ s h0 h1]
  unfold rationalHeckeFinite rationalHeckeCompleted
  rw [riemannZeta_def_of_ne_zero h0]
  simp [div_eq_zero_iff, Complex.Gammaℝ_ne_zero_of_re_pos hp]

theorem rationalHeckeXi_zeros_compact_finite (τ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) :
    {s ∈ K | rationalHeckeXi τ s = 0}.Finite := by
  have hn : rationalHeckeXi τ (-Complex.I * τ) ≠ 0 := by
    rw [rationalHeckeXi_at_pole]; exact one_ne_zero
  have hd := (rationalHeckeXi_analytic τ).preimage_zero_mem_codiscrete hn
  have hm := Filter.codiscreteWithin.mono (Set.subset_univ K) hd
  have hh : (K \ ((rationalHeckeXi τ) ⁻¹' {0}ᶜ)).Finite := by
    by_contra hi
    obtain ⟨x, hx, ha⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hi hK
      (fun _ h => h.1)
    exact (mem_codiscreteWithin_accPt.mp hm) x hx ha
  exact hh.subset (by intro s hs; exact ⟨hs.1, fun hz => hz hs.2⟩)

/-- The multiplicity is that of the actual finite L-function germ. -/
theorem rationalHeckeFinite_order_eq (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt (rationalHeckeFinite τ) s =
      analyticOrderAt (rationalHeckeXi τ) s := by
  let T : ℂ → ℂ := fun z => z + Complex.I * τ
  have hT : AnalyticAt ℂ T s := analyticAt_id.add analyticAt_const
  have hre : (T s).re = s.re := by simp [T, Complex.mul_re]
  have hp : 0 < (T s).re := by rwa [hre]
  have h0 : T s ≠ 0 := by intro h; simp [h] at hp
  have h1 : T s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [← hre, h]; simp
    linarith
  let G : ℂ → ℂ := fun z => (T z * (T z - 1))⁻¹ * (Complex.Gammaℝ (T z))⁻¹
  have hG : AnalyticAt ℂ G s :=
    ((hT.mul (hT.sub analyticAt_const)).inv
      (mul_ne_zero h0 (sub_ne_zero.mpr h1))).mul
      ((Complex.differentiable_Gammaℝ_inv.analyticAt (T s)).comp hT)
  have hGn : G s ≠ 0 := mul_ne_zero
    (inv_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)))
    (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hp))
  have he : rationalHeckeFinite τ =ᶠ[𝓝 s] G * rationalHeckeXi τ := by
    filter_upwards [hT.continuousAt.eventually_ne h0,
      hT.continuousAt.eventually_ne h1] with z hz0 hz1
    change riemannZeta (T z) = G z * rationalHeckeXi τ z
    rw [riemannZeta_def_of_ne_zero hz0, rationalHeckeXi_eq_completed τ z hz0 hz1]
    dsimp [G, T, rationalHeckeCompleted]
    dsimp [T] at hz0 hz1
    field_simp [hz0, sub_ne_zero.mpr hz1]
  rw [analyticOrderAt_congr he,
    analyticOrderAt_mul hG (rationalHeckeXi_analytic τ s (Set.mem_univ _)),
    hG.analyticOrderAt_eq_zero.mpr hGn, zero_add]

theorem rationalHeckeFinite_multiplicity_eq (τ : ℝ) (s : ℂ)
    (hpos : 0 < s.re) (hlt : s.re < 1) :
    rationalHeckeMultiplicity τ s = analyticOrderNatAt (rationalHeckeFinite τ) s := by
  unfold rationalHeckeMultiplicity analyticOrderNatAt
  rw [rationalHeckeFinite_order_eq τ s hpos hlt]

theorem rationalHeckeFinite_zeros_compact_finite (τ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) :
    {s ∈ K | 0 < s.re ∧ s.re < 1 ∧ rationalHeckeFinite τ s = 0}.Finite := by
  apply (rationalHeckeXi_zeros_compact_finite τ K hK).subset
  rintro s ⟨hs, hpos, hlt, hz⟩
  exact ⟨hs, (rationalHeckeXi_zero_iff_finite τ s hpos hlt).mpr hz⟩

theorem rationalHecke_occurrences_finite (τ : ℝ)
    (K : Set ℂ) (hK : IsCompact K) :
    Finite (Σ s : {s : ℂ // s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧
      rationalHeckeFinite τ s = 0}, Fin (rationalHeckeMultiplicity τ s.1)) := by
  letI : Finite {s : ℂ // s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧
      rationalHeckeFinite τ s = 0} :=
    (rationalHeckeFinite_zeros_compact_finite τ K hK).to_subtype
  infer_instance

#check rationalHeckeMultiplicity_pos_iff
#print axioms rationalHeckeMultiplicity_pos_iff
#check rationalHeckeXi_at_other_pole
#print axioms rationalHeckeXi_at_other_pole
#check rationalHeckeXi_zero_iff_finite
#print axioms rationalHeckeXi_zero_iff_finite
#check rationalHeckeXi_zeros_compact_finite
#print axioms rationalHeckeXi_zeros_compact_finite
#check rationalHeckeFinite_order_eq
#print axioms rationalHeckeFinite_order_eq
#check rationalHeckeFinite_multiplicity_eq
#print axioms rationalHeckeFinite_multiplicity_eq
#check rationalHeckeFinite_zeros_compact_finite
#print axioms rationalHeckeFinite_zeros_compact_finite
#check rationalHecke_occurrences_finite
#print axioms rationalHecke_occurrences_finite

/-! Round 7: identify the WHOLE xi divisor with genuine finite nontrivial zeros.
This closes the support obligation raised in frozen r06 B/C attacks, needed
before this actual divisor can be used by bounded-strip resolvent machinery. -/

theorem rationalHeckeXi_ne_zero_right (τ : ℝ) (s : ℂ)
    (hs : 1 ≤ s.re) : rationalHeckeXi τ s ≠ 0 := by
  have hre : (s + Complex.I * τ).re = s.re := by simp [Complex.mul_re]
  have h0 : s + Complex.I * τ ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    rw [hre] at hh
    norm_num at hh
    linarith
  by_cases h1 : s + Complex.I * τ = 1
  · have he : s = 1 - Complex.I * τ := by linear_combination h1
    rw [he, rationalHeckeXi_at_other_pole]
    exact one_ne_zero
  · intro hz
    have hc := (rationalHeckeXi_zero_iff τ s h0 h1).mp hz
    have hfinite : riemannZeta (s + Complex.I * τ) = 0 := by
      rw [riemannZeta_def_of_ne_zero h0]
      change rationalHeckeCompleted τ s / Complex.Gammaℝ (s + Complex.I * τ) = 0
      rw [hc, zero_div]
    exact (riemannZeta_ne_zero_of_one_le_re (by rwa [hre])) hfinite

theorem rationalHeckeXi_reflection (τ : ℝ) (s : ℂ) :
    rationalHeckeXi τ (1 - s - 2 * Complex.I * τ) = rationalHeckeXi τ s := by
  have he : 1 - s - 2 * Complex.I * τ + Complex.I * τ =
      1 - (s + Complex.I * τ) := by ring
  unfold rationalHeckeXi
  rw [he, completedRiemannZeta₀_one_sub]
  ring

theorem rationalHeckeXi_zero_strip (τ : ℝ) (s : ℂ)
    (hz : rationalHeckeXi τ s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hn
    have hr : 1 ≤ (1 - s - 2 * Complex.I * τ).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      linarith
    apply rationalHeckeXi_ne_zero_right τ (1 - s - 2 * Complex.I * τ) hr
    rw [rationalHeckeXi_reflection, hz]
  · exact lt_of_not_ge (fun h => rationalHeckeXi_ne_zero_right τ s h hz)

/-- Global support equality, with no strip assumption on the queried point. -/
theorem rationalHeckeXi_zero_iff_genuine (τ : ℝ) (s : ℂ) :
    rationalHeckeXi τ s = 0 ↔
      0 < s.re ∧ s.re < 1 ∧ rationalHeckeFinite τ s = 0 := by
  constructor
  · intro hz
    obtain ⟨hp, hl⟩ := rationalHeckeXi_zero_strip τ s hz
    exact ⟨hp, hl, (rationalHeckeXi_zero_iff_finite τ s hp hl).mp hz⟩
  · rintro ⟨hp, hl, hz⟩
    exact (rationalHeckeXi_zero_iff_finite τ s hp hl).mpr hz

/-- Every occurrence of the unrestricted xi divisor is a genuine finite zero
with exactly its finite-function analytic multiplicity, in the open strip. -/
theorem rationalHeckeDivisor_genuine (τ : ℝ) (d : RationalHeckeDivisor τ) :
    0 < d.1.val.re ∧ d.1.val.re < 1 ∧
      rationalHeckeFinite τ d.1.val = 0 ∧
      rationalHeckeMultiplicity τ d.1.val =
        analyticOrderNatAt (rationalHeckeFinite τ) d.1.val := by
  obtain ⟨hp, hl, hz⟩ := (rationalHeckeXi_zero_iff_genuine τ d.1.val).mp d.1.property
  exact ⟨hp, hl, hz, rationalHeckeFinite_multiplicity_eq τ d.1.val hp hl⟩

#check rationalHeckeXi_ne_zero_right
#print axioms rationalHeckeXi_ne_zero_right
#check rationalHeckeXi_reflection
#print axioms rationalHeckeXi_reflection
#check rationalHeckeXi_zero_strip
#print axioms rationalHeckeXi_zero_strip
#check rationalHeckeXi_zero_iff_genuine
#print axioms rationalHeckeXi_zero_iff_genuine
#check rationalHeckeDivisor_genuine
#print axioms rationalHeckeDivisor_genuine

/-! Round 8: genuine norm twists require shifted pole-clearing factors.
This is the concrete normalization prerequisite for manuscript (10.4.3.1)
and its spectral quotient, not a proof of the trace identity. -/

noncomputable def unshiftedCompletedFactor (τ : ℝ) (s : ℂ) : ℂ :=
  s * (s - 1) * rationalHeckeCompleted τ s

/-- The unshifted factor inserts a zero at a regular nonzero point of the
actual completed function, for every nonzero unitary norm twist. -/
theorem unshiftedClearing_spurious_zero (τ : ℝ) (hτ : τ ≠ 0) :
    DifferentiableAt ℂ (rationalHeckeCompleted τ) 0 ∧
    rationalHeckeCompleted τ 0 ≠ 0 ∧
    unshiftedCompletedFactor τ 0 = 0 ∧ rationalHeckeXi τ 0 ≠ 0 := by
  have h0 : (0 : ℂ) + Complex.I * τ ≠ 0 := by
    simpa using mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hτ)
  have h1 : (0 : ℂ) + Complex.I * τ ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [Complex.mul_re] at hh
  have hx : rationalHeckeXi τ 0 ≠ 0 := by
    intro hz
    have hh := (rationalHeckeXi_zero_strip τ 0 hz).1
    norm_num at hh
  refine ⟨?_, ?_, by simp [unshiftedCompletedFactor], hx⟩
  · exact (differentiableAt_completedZeta h0 h1).comp 0
      (differentiableAt_id.add_const (Complex.I * τ))
  · exact fun hz => hx ((rationalHeckeXi_zero_iff τ 0 h0 h1).mpr hz)

/-- The same wrong factor fails to clear the genuine shifted pole. -/
theorem unshiftedClearing_not_continuous (τ : ℝ) (hτ : τ ≠ 0) :
    ¬ ContinuousAt (unshiftedCompletedFactor τ) (-Complex.I * τ) := by
  intro hB
  let p : ℂ := -Complex.I * τ
  have hp0 : p ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hτ)
  have hp1 : p ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    norm_num [p, Complex.mul_re] at hh
  have hT : ContinuousAt (fun z : ℂ => z + Complex.I * τ) p :=
    continuousAt_id.add_const _
  have hT1 : p + Complex.I * τ ≠ 1 := by simp [p]
  have he : (fun z : ℂ => (z + Complex.I * τ) * (z + Complex.I * τ - 1) *
      unshiftedCompletedFactor τ z) =ᶠ[𝓝[≠] p]
      (fun z => z * (z - 1) * rationalHeckeXi τ z) := by
    filter_upwards [self_mem_nhdsWithin,
      (hT.eventually_ne hT1).filter_mono nhdsWithin_le_nhds] with z hz hz1
    have hz0 : z + Complex.I * τ ≠ 0 := by
      intro hh
      have hz' : z = p := by dsimp [p]; linear_combination hh
      exact hz hz'
    rw [rationalHeckeXi_eq_completed τ z hz0 hz1]
    unfold unshiftedCompletedFactor
    ring
  have hleft := ((hT.mul (hT.sub_const 1)).mul hB).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] p ≤ 𝓝 p)
  have hright := (((continuousAt_id.mul (continuousAt_id.sub_const 1)).mul
    ((rationalHeckeXi_analytic τ p (Set.mem_univ _)).continuousAt))).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] p ≤ 𝓝 p)
  have hh := tendsto_nhds_unique (hleft.congr' he) hright
  have hval : rationalHeckeXi τ p = 1 := rationalHeckeXi_at_pole τ
  simp only [show p + Complex.I * τ = 0 by simp [p], zero_mul, hval, mul_one] at hh
  exact (mul_ne_zero hp0 (sub_ne_zero.mpr hp1)) hh.symm

#check unshiftedClearing_spurious_zero
#print axioms unshiftedClearing_spurious_zero
#check unshiftedClearing_not_continuous
#print axioms unshiftedClearing_not_continuous

end MasulloGRH
