import Mathlib

/-! Round 5, B. Genuine zeta divisor work for the rational trivial-Hecke
case. This is NOT the full Hecke divisor theorem or a trace identity.
The Mathlib functions below are the actual continued zeta functions.
No arbitrary spectrum, assumed GRH, or assumed trace conclusion is used. -/
open Filter Set Complex
open scoped Topology
namespace MasulloGRH

/-- Twice the classical xi function, defined everywhere by pole removal. -/
noncomputable def genuineZetaXi (s : ℂ) : ℂ :=
  1 + s * (s - 1) * completedRiemannZeta₀ s

theorem genuineZetaXi_analytic (s : ℂ) : AnalyticAt ℂ genuineZetaXi s := by
  exact analyticAt_const.add
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
      (differentiable_completedZeta₀.analyticAt s))

theorem genuineZetaXi_zero : genuineZetaXi 0 = 1 := by
  simp [genuineZetaXi]

theorem genuineZetaXi_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    genuineZetaXi s = s * (s - 1) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold genuineZetaXi
  field_simp [h0, sub_ne_zero.mpr h1, sub_ne_zero.mpr (Ne.symm h1)]
  ring

theorem genuineZetaXi_zero_iff_completed (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    genuineZetaXi s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [genuineZetaXi_completed s h0 h1]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero h0 (sub_ne_zero.mpr h1)))

theorem genuineZetaXi_order_finite (s : ℂ) :
    analyticOrderAt genuineZetaXi s ≠ ⊤ := by
  intro h
  have hf : AnalyticOnNhd ℂ genuineZetaXi Set.univ := fun z _ => genuineZetaXi_analytic z
  have he : ∀ᶠ z in 𝓝[≠] s, genuineZetaXi z = 0 :=
    (analyticOrderAt_eq_top.mp h).filter_mono nhdsWithin_le_nhds
  have ha := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isPreconnected_univ (mem_univ s) he.frequently
  have hh := ha (mem_univ (0 : ℂ))
  simp [genuineZetaXi] at hh

/-- Actual local vanishing order, with no assumed spectral enumeration. -/
noncomputable def genuineZetaMultiplicity (s : ℂ) : ℕ :=
  analyticOrderNatAt genuineZetaXi s

theorem genuineZetaXi_local_factor (s : ℂ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧ g s ≠ 0 ∧
      genuineZetaXi =ᶠ[𝓝 s] fun z => (z-s)^genuineZetaMultiplicity s * g z := by
  simpa only [genuineZetaMultiplicity, smul_eq_mul] using
    (genuineZetaXi_analytic s).analyticOrderAt_ne_top.mp (genuineZetaXi_order_finite s)

theorem genuineZetaMultiplicity_pos_iff (s : ℂ) :
    0 < genuineZetaMultiplicity s ↔ genuineZetaXi s = 0 := by
  have hc := Nat.cast_analyticOrderNatAt (genuineZetaXi_order_finite s)
  rw [Nat.pos_iff_ne_zero]
  change analyticOrderNatAt genuineZetaXi s ≠ 0 ↔ _
  rw [← Nat.cast_ne_zero (R := ℕ∞), hc]
  exact (genuineZetaXi_analytic s).analyticOrderAt_ne_zero

/-- Genuine finite and completed zeros agree inside the critical strip. -/
theorem genuineZetaXi_zero_iff_zeta (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    genuineZetaXi s = 0 ↔ riemannZeta s = 0 := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hpos
  have h1 : s ≠ 1 := by intro h; simp [h] at hlt
  rw [genuineZetaXi_zero_iff_completed s h0 h1, riemannZeta_def_of_ne_zero h0]
  simp [div_eq_zero_iff, Complex.Gammaℝ_ne_zero_of_re_pos hpos]

theorem genuineZetaXi_zeros_compact_finite (K : Set ℂ) (hK : IsCompact K) :
    {s ∈ K | genuineZetaXi s = 0}.Finite := by
  have hf : AnalyticOnNhd ℂ genuineZetaXi Set.univ := fun z _ => genuineZetaXi_analytic z
  have h0 : genuineZetaXi 0 ≠ 0 := by rw [genuineZetaXi_zero]; exact one_ne_zero
  have hd := hf.preimage_zero_mem_codiscrete h0
  have hm := Filter.codiscreteWithin.mono (Set.subset_univ K) hd
  have hh : (K \ (genuineZetaXi ⁻¹' {0}ᶜ)).Finite := by
    by_contra hi
    obtain ⟨x, hx, ha⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hi hK
      (fun _ h => h.1)
    exact (mem_codiscreteWithin_accPt.mp hm) x hx ha
  exact hh.subset (by intro s hs; exact ⟨hs.1, fun hz => hz hs.2⟩)

/-- Local finiteness for the ACTUAL zeta zeros, not a chosen sequence. -/
theorem genuineZeta_zeros_compact_finite (K : Set ℂ) (hK : IsCompact K) :
    {s ∈ K | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0}.Finite := by
  apply (genuineZetaXi_zeros_compact_finite K hK).subset
  rintro s ⟨hs, hpos, hlt, hz⟩
  exact ⟨hs, (genuineZetaXi_zero_iff_zeta s hpos hlt).mpr hz⟩

/-- The natural multiplicity equals the order of the genuine finite zeta germ. -/
theorem genuineZeta_order_eq (s : ℂ) (hpos : 0 < s.re) (hlt : s.re < 1) :
    analyticOrderAt riemannZeta s = analyticOrderAt genuineZetaXi s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hpos
  have h1 : s ≠ 1 := by intro h; simp [h] at hlt
  let G : ℂ → ℂ := fun z => (z * (z-1))⁻¹ * (Complex.Gammaℝ z)⁻¹
  have hG : AnalyticAt ℂ G s :=
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).inv
      (mul_ne_zero h0 (sub_ne_zero.mpr h1))).mul
      (Complex.differentiable_Gammaℝ_inv.analyticAt s)
  have hGn : G s ≠ 0 := mul_ne_zero
    (inv_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)))
    (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hpos))
  have he : riemannZeta =ᶠ[𝓝 s] G * genuineZetaXi := by
    filter_upwards [eventually_ne_nhds h0, eventually_ne_nhds h1] with z hz0 hz1
    change riemannZeta z = G z * genuineZetaXi z
    rw [riemannZeta_def_of_ne_zero hz0, genuineZetaXi_completed z hz0 hz1]
    dsimp [G]
    field_simp [hz0, sub_ne_zero.mpr hz1]
  rw [analyticOrderAt_congr he, analyticOrderAt_mul hG (genuineZetaXi_analytic s),
    hG.analyticOrderAt_eq_zero.mpr hGn, zero_add]

/-- A finite occurrence type repeats each genuine zero its actual natural order. -/
theorem genuineZeta_occurrences_finite (K : Set ℂ) (hK : IsCompact K) :
    Finite (Σ s : {s : ℂ // s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0},
      Fin (genuineZetaMultiplicity s.1)) := by
  letI : Finite {s : ℂ // s ∈ K ∧ 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0} :=
    (genuineZeta_zeros_compact_finite K hK).to_subtype
  infer_instance

/-- Compact local finiteness also holds for every imaginary norm shift. -/
theorem genuineNormTwistZeta_zeros_compact_finite (t : ℝ)
    (K : Set ℂ) (hK : IsCompact K) :
    {s ∈ K | 0 < s.re ∧ s.re < 1 ∧
      riemannZeta (s + (t : ℂ) * Complex.I) = 0}.Finite := by
  let shift : ℂ → ℂ := fun s => s + (t : ℂ) * Complex.I
  have hcont : Continuous shift := continuous_id.add continuous_const
  have hi : Function.Injective shift := fun _ _ h => add_right_cancel h
  have hf := genuineZeta_zeros_compact_finite (shift '' K) (hK.image hcont)
  have hp := hf.preimage hi.injOn
  apply hp.subset
  rintro s ⟨hs, hpos, hlt, hz⟩
  refine ⟨⟨s, hs, rfl⟩, ?_, ?_, hz⟩
  · simpa [shift, Complex.mul_re] using hpos
  · simpa [shift, Complex.mul_re] using hlt

end MasulloGRH
#check MasulloGRH.genuineZetaXi_analytic
#print axioms MasulloGRH.genuineZetaXi_analytic
#check MasulloGRH.genuineZetaXi_zero
#print axioms MasulloGRH.genuineZetaXi_zero
#check MasulloGRH.genuineZetaXi_completed
#print axioms MasulloGRH.genuineZetaXi_completed
#check MasulloGRH.genuineZetaXi_zero_iff_completed
#print axioms MasulloGRH.genuineZetaXi_zero_iff_completed
#check MasulloGRH.genuineZetaXi_order_finite
#print axioms MasulloGRH.genuineZetaXi_order_finite
#check MasulloGRH.genuineZetaXi_local_factor
#print axioms MasulloGRH.genuineZetaXi_local_factor
#check MasulloGRH.genuineZetaMultiplicity_pos_iff
#print axioms MasulloGRH.genuineZetaMultiplicity_pos_iff

#check MasulloGRH.genuineZetaXi_zero_iff_zeta
#print axioms MasulloGRH.genuineZetaXi_zero_iff_zeta

#check MasulloGRH.genuineZetaXi_zeros_compact_finite
#print axioms MasulloGRH.genuineZetaXi_zeros_compact_finite

#check MasulloGRH.genuineZeta_zeros_compact_finite
#print axioms MasulloGRH.genuineZeta_zeros_compact_finite

#check MasulloGRH.genuineZeta_order_eq
#print axioms MasulloGRH.genuineZeta_order_eq

#check MasulloGRH.genuineZeta_occurrences_finite
#print axioms MasulloGRH.genuineZeta_occurrences_finite

#check MasulloGRH.genuineNormTwistZeta_zeros_compact_finite
#print axioms MasulloGRH.genuineNormTwistZeta_zeros_compact_finite
