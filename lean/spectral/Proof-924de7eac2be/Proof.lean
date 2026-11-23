import Mathlib
open Filter Topology
namespace MasulloGRH.Round15F

/-- Discharges D7 of the critical-line route: the local logarithmic derivative
of a supplied genuine meromorphic function has residue its SIGNED intrinsic
order. No zero set, zero-free region, or summability is assumed. Applying this
to completed Hecke L still requires its independently constructed continuation. -/
theorem logDeriv_regular_part_of_order (f : ℂ → ℂ) (a : ℂ) (m : ℤ)
    (hf : MeromorphicAt f a) (hm : meromorphicOrderAt f a = m) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧
      logDeriv f =ᶠ[𝓝[≠] a] fun z => (m : ℂ) / (z-a) + r z := by
  obtain ⟨u, hu, hu0, he⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hm
  refine ⟨logDeriv u, ?_, ?_⟩
  · exact hu.deriv.div hu hu0
  have hnear : ∀ᶠ z in 𝓝 a, u z ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hlocal := eventually_eventually_nhdsWithin.mpr he
  filter_upwards [hlocal, self_mem_nhdsWithin,
    hu.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds] with z hez hz huz huz0
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  rw [isOpen_compl_singleton.nhdsWithin_eq hz] at hez
  have hlin : HasDerivAt (fun t : ℂ => t-a) 1 z :=
    (hasDerivAt_id z).sub_const a
  have hp := hasDerivAt_zpow m (z-a) (Or.inl hza)
  have hpow : logDeriv (fun t : ℂ => (t-a)^m) z = (m : ℂ)/(z-a) := by
    have h := logDeriv_comp (f := fun t : ℂ => t^m) (g := fun t : ℂ => t-a)
      (x := z) hp.differentiableAt hlin.differentiableAt
    simpa only [Function.comp_def, logDeriv_zpow, hlin.deriv, mul_one] using h
  have hpd : DifferentiableAt ℂ (fun t : ℂ => (t-a)^m) z := by
    exact DifferentiableAt.comp (f := fun t : ℂ => t-a) (g := fun t : ℂ => t^m)
      z hp.differentiableAt hlin.differentiableAt
  have hprod := logDeriv_mul (f := fun t : ℂ => (t-a)^m) (g := u)
    z (zpow_ne_zero m hza) huz0
    hpd huz.differentiableAt
  change f =ᶠ[𝓝 z] (fun t => (t-a)^m * u t) at hez
  change deriv f z / f z = _
  rw [hez.deriv_eq, hez.eq_of_nhds]
  exact hprod.trans (congrArg (fun v => v + logDeriv u z) hpow)

/-- Discharges the residue-identification premise of D7, including simple
poles m=-1 and genuine positive-order zeros. -/
theorem logDeriv_residue_limit (f : ℂ → ℂ) (a : ℂ) (m : ℤ)
    (hf : MeromorphicAt f a) (hm : meromorphicOrderAt f a = m) :
    Tendsto (fun z => (z-a) * logDeriv f z) (𝓝[≠] a) (𝓝 (m : ℂ)) := by
  obtain ⟨r, hr, he⟩ := logDeriv_regular_part_of_order f a m hf hm
  have heq : (fun z => (z-a) * logDeriv f z) =ᶠ[𝓝[≠] a]
      fun z => (m : ℂ) + (z-a) * r z := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hza
    rw [hz]
    have hne : z-a ≠ 0 := sub_ne_zero.mpr hza
    field_simp [hne]
  have ht : Tendsto (fun z => (m : ℂ) + (z-a) * r z) (𝓝 a) (𝓝 (m : ℂ)) := by
    have h := (tendsto_const_nhds (x := (m : ℂ)) (f := 𝓝 a)).add
      ((tendsto_id.sub (tendsto_const_nhds (x := a))).mul hr.continuousAt)
    simpa using h
  exact (ht.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Discharges D7's local nonremovability implication. This supplies no global
holomorphic trace limit: it proves that any such independently obtained limit
cannot agree locally with a logarithmic derivative at nonzero intrinsic order. -/
theorem nonzero_order_no_continuous_logDeriv_extension
    (f : ℂ → ℂ) (a : ℂ) (m : ℤ) (hf : MeromorphicAt f a)
    (hm : meromorphicOrderAt f a = m) (hm0 : m ≠ 0) :
    ¬ ∃ H : ℂ → ℂ, ContinuousAt H a ∧ logDeriv f =ᶠ[𝓝[≠] a] H := by
  rintro ⟨H, hH, he⟩
  have ht : Tendsto (fun z => (z-a) * H z) (𝓝 a) (𝓝 (0 : ℂ)) := by
    have h : Tendsto (fun z => (z-a) * H z) (𝓝 a) (𝓝 ((a-a) * H a)) :=
      (tendsto_id.sub tendsto_const_nhds).mul hH
    simpa using h
  have heq : (fun z => (z-a) * logDeriv f z) =ᶠ[𝓝[≠] a]
      fun z => (z-a) * H z := by
    filter_upwards [he] with z hz
    rw [hz]
  have hz := (ht.mono_left nhdsWithin_le_nhds).congr' heq.symm
  have hzero := tendsto_nhds_unique (logDeriv_residue_limit f a m hf hm) hz
  apply hm0
  exact_mod_cast hzero

#check nonzero_order_no_continuous_logDeriv_extension
#print axioms nonzero_order_no_continuous_logDeriv_extension

#check logDeriv_regular_part_of_order
#print axioms logDeriv_regular_part_of_order
#check logDeriv_residue_limit
#print axioms logDeriv_residue_limit
end MasulloGRH.Round15F

namespace MasulloGRH.Round16F
open MasulloGRH.Round15F

/-- D7 of the assigned critical-line route: a continuous corrected logarithmic
 derivative determines the SIGNED intrinsic order, including at a known pole.
 The correction/extension must be independently obtained from the trace limit. -/
theorem order_eq_neg_correction (f H : ℂ → ℂ) (a : ℂ) (m : ℤ) (c : ℂ)
    (hf : MeromorphicAt f a) (hm : meromorphicOrderAt f a = m)
    (hH : ContinuousAt H a)
    (he : (fun z => logDeriv f z + c / (z-a)) =ᶠ[𝓝[≠] a] H) :
    (m : ℂ) = -c := by
  have ht : Tendsto (fun z => (z-a) * H z) (𝓝[≠] a) (𝓝 (0 : ℂ)) := by
    have h : Tendsto (fun z => (z-a) * H z) (𝓝 a) (𝓝 ((a-a)*H a)) :=
      (tendsto_id.sub tendsto_const_nhds).mul hH
    simpa using h.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun z => (z-a) * logDeriv f z + c)
      (𝓝[≠] a) (𝓝 ((m : ℂ) + c)) :=
    (logDeriv_residue_limit f a m hf hm).add tendsto_const_nhds
  have heq : (fun z => (z-a) * logDeriv f z + c) =ᶠ[𝓝[≠] a]
      fun z => (z-a) * H z := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hza
    rw [← hz]
    have hne : z-a ≠ 0 := sub_ne_zero.mpr hza
    field_simp [hne]
  have hz := tendsto_nhds_unique hleft (ht.congr' heq.symm)
  exact eq_neg_of_add_eq_zero_left hz

/-- D7: both known simple-pole corrections are retained. This classifies
 intrinsic orders from a supplied regular part, without prescribing zeros.
 No arithmetic continuation or global trace-limit identity is supplied here. -/
theorem order_from_two_pole_extension (f H : ℂ → ℂ) (a p q : ℂ) (m : ℤ)
    (hpq : p ≠ q) (hf : MeromorphicAt f a)
    (hm : meromorphicOrderAt f a = m) (hH : ContinuousAt H a)
    (he : (fun z => logDeriv f z + (1 / (z-p) + 1 / (z-q)))
      =ᶠ[𝓝[≠] a] H) :
    m = if a = p ∨ a = q then -1 else 0 := by
  classical
  by_cases hap : a = p
  · subst a
    have hR : ContinuousAt (fun z : ℂ => H z - 1 / (z-q)) p :=
      hH.sub (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hpq))
    have h := order_eq_neg_correction f (fun z => H z - 1 / (z-q)) p m 1 hf hm hR (by
      filter_upwards [he] with z hz
      linear_combination hz)
    have hi : m = -1 := by exact_mod_cast h
    simp [hi]
  · by_cases haq : a = q
    · subst a
      have hR : ContinuousAt (fun z : ℂ => H z - 1 / (z-p)) q :=
        hH.sub (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
          (sub_ne_zero.mpr hpq.symm))
      have h := order_eq_neg_correction f (fun z => H z - 1 / (z-p)) q m 1 hf hm hR (by
        filter_upwards [he] with z hz
        linear_combination hz)
      have hi : m = -1 := by exact_mod_cast h
      simp [hi]
    · have hR : ContinuousAt (fun z : ℂ => H z - (1 / (z-p) + 1 / (z-q))) a :=
        hH.sub ((continuousAt_const.div (continuousAt_id.sub continuousAt_const)
          (sub_ne_zero.mpr hap)).add
          (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
          (sub_ne_zero.mpr haq)))
      have h := order_eq_neg_correction f (fun z => H z - (1 / (z-p) + 1 / (z-q)))
        a m 0 hf hm hR (by
          filter_upwards [he] with z hz
          simp only [zero_div, add_zero]
          linear_combination hz)
      have hi : m = 0 := by exact_mod_cast h
      simpa [hap, haq] using hi

/-- D7 with the full unitary norm-twist parameter: in the Euler convention
 L(s,norm^(i*tau))=zeta_K(s+i*tau), known completed poles are -i*tau and
 1-i*tau. This is a CONDITIONAL local classification, not the arithmetic
 assertion that these poles or this regular part have been constructed. -/
theorem normTwist_order_classification (f H : ℂ → ℂ) (a : ℂ) (m : ℤ) (τ : ℝ)
    (hf : MeromorphicAt f a) (hm : meromorphicOrderAt f a = m)
    (hH : ContinuousAt H a)
    (he : (fun z => logDeriv f z +
        (1 / (z - (-(Complex.I * (τ : ℂ)))) +
         1 / (z - (1 - Complex.I * (τ : ℂ))))) =ᶠ[𝓝[≠] a] H) :
    m = if a = -(Complex.I * (τ : ℂ)) ∨ a = 1 - Complex.I * (τ : ℂ)
      then -1 else 0 := by
  apply order_from_two_pole_extension f H a _ _ m _ hf hm hH he
  intro h
  have h10 : (1 : ℂ) = 0 := by linear_combination -h
  exact one_ne_zero h10

/-- D7 on the exact right half-plane, with every real norm twist retained.
 The left completed pole has real part zero and is outside this domain.
 This removes the exceptional-right-pole ambiguity: its order is negative. -/
theorem normTwist_rightHalfPlane_order (f H : ℂ → ℂ) (a : ℂ) (m : ℤ) (τ : ℝ)
    (ha : (1 / 2 : ℝ) < a.re)
    (hf : MeromorphicAt f a) (hm : meromorphicOrderAt f a = m)
    (hH : ContinuousAt H a)
    (he : (fun z => logDeriv f z +
        (1 / (z - (-(Complex.I * (τ : ℂ)))) +
         1 / (z - (1 - Complex.I * (τ : ℂ))))) =ᶠ[𝓝[≠] a] H) :
    m = (if a = 1 - Complex.I * (τ : ℂ) then -1 else 0) ∧ m ≤ 0 := by
  have h := normTwist_order_classification f H a m τ hf hm hH he
  have hp : a ≠ -(Complex.I * (τ : ℂ)) := by
    intro heq
    have hr := congrArg Complex.re heq
    simp at hr
    linarith
  simp only [hp, false_or] at h
  refine ⟨h, ?_⟩
  rw [h]
  split_ifs <;> norm_num

/-- D6 -> D7: propagate the corrected trace identity from ONE overlap germ
 across a connected meromorphic domain before using local order classification.
 Meromorphicity of the actual corrected quotient and an analytic trace limit
 are explicit analytic premises; no zero-free domain is assumed. -/
theorem order_from_connected_trace_germ (f H : ℂ → ℂ) (U : Set ℂ)
    (a b p q : ℂ) (m : ℤ) (hpq : p ≠ q) (hU : IsPreconnected U)
    (ha : a ∈ U) (hb : b ∈ U) (hf : MeromorphicAt f a)
    (hm : meromorphicOrderAt f a = m) (hH : AnalyticOnNhd ℂ H U)
    (hD : MeromorphicOn
      (fun z => logDeriv f z + (1 / (z-p) + 1 / (z-q))) U)
    (he : (fun z => logDeriv f z + (1 / (z-p) + 1 / (z-q)))
      =ᶠ[𝓝[≠] b] H) :
    m = if a = p ∨ a = q then -1 else 0 := by
  let D : ℂ → ℂ := fun z => logDeriv f z + (1 / (z-p) + 1 / (z-q))
  have hd : MeromorphicOn (fun z => D z - H z) U :=
    hD.fun_sub (fun z hz => (hH z hz).meromorphicAt)
  have hl : (fun z => D z - H z) =ᶠ[𝓝[≠] b] (fun _ => 0) := by
    filter_upwards [he] with z hz
    exact sub_eq_zero.mpr hz
  have hbt : meromorphicOrderAt (fun z => D z - H z) b = ⊤ := by
    rw [meromorphicOrderAt_congr hl]
    simp [meromorphicOrderAt_const]
  have hat : meromorphicOrderAt (fun z => D z - H z) a = ⊤ := by
    by_contra hn
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected hU ha hb hn) hbt
  apply order_from_two_pole_extension f H a p q m hpq hf hm (hH a ha).continuousAt
  filter_upwards [meromorphicOrderAt_eq_top_iff.mp hat] with z hz
  exact sub_eq_zero.mp hz

#check order_from_connected_trace_germ
#print axioms order_from_connected_trace_germ
#check normTwist_rightHalfPlane_order
#print axioms normTwist_rightHalfPlane_order
#check order_eq_neg_correction
#print axioms order_eq_neg_correction
#check order_from_two_pole_extension
#print axioms order_from_two_pole_extension
#check normTwist_order_classification
#print axioms normTwist_order_classification
end MasulloGRH.Round16F
