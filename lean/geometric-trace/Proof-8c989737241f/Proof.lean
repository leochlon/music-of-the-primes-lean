import Mathlib
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
open Filter Topology
namespace MasulloGRH.Round12A
attribute [local instance] Classical.propDecidable
/-- Supplies the local simple-root premise for the two norm-twist polar
clearing factors in manuscript Proposition 3.2.1.3. -/
theorem linear_polar_factor_order (a x : ℂ) :
    meromorphicOrderAt (fun z : ℂ => z - a) x =
      if x = a then (1 : WithTop ℤ) else 0 := by
  by_cases hx : x = a
  · subst x
    rw [if_pos rfl]
    apply (meromorphicOrderAt_eq_int_iff
      ((analyticAt_id.sub analyticAt_const).meromorphicAt)).2
    refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall ?_⟩
    intro z
    simp
  · rw [if_neg hx]
    have he := meromorphicOrderAt_mul_of_ne_zero (f := fun _ : ℂ => (1 : ℂ))
      (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hx)
    change meromorphicOrderAt (fun z : ℂ => (z - a) * 1) x =
      meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) x at he
    simpa [meromorphicOrderAt_const] using he

/-- Exact polar-clearing divisor for chi=norm^(i*tau). The manuscript uses
t0=-tau. This supplies the two polar corrections without assuming either
is a genuine pole of a supplied continuation. -/
theorem norm_twist_polar_divisor (τ : ℝ) (x : ℂ) :
    meromorphicOrderAt (fun z : ℂ =>
      (z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I))) x =
      (if x = -(τ : ℂ) * Complex.I then (1 : WithTop ℤ) else 0) +
      (if x = 1 - (τ : ℂ) * Complex.I then (1 : WithTop ℤ) else 0) := by
  have he (z : ℂ) : z + (τ : ℂ) * Complex.I = z - (-(τ : ℂ) * Complex.I) := by ring
  simp_rw [he]
  have h0 : MeromorphicAt (fun z : ℂ => z - (-(τ : ℂ) * Complex.I)) x :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have h1 : MeromorphicAt (fun z : ℂ => z - (1 - (τ : ℂ) * Complex.I)) x :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have hh := meromorphicOrderAt_mul h0 h1
  rw [linear_polar_factor_order, linear_polar_factor_order] at hh
  exact hh

/-- Supplies the reciprocal simple-root premise for undoing precisely the
norm-twist clearing polynomial; no assumed L-function zero set is used. -/
theorem reciprocal_linear_polar_order (a x : ℂ) :
    meromorphicOrderAt (fun z : ℂ => (z - a)⁻¹) x =
      if x = a then (-1 : WithTop ℤ) else 0 := by
  by_cases hx : x = a
  · subst x
    rw [if_pos rfl]
    have hm : MeromorphicAt (fun z : ℂ => (z - a)⁻¹) a :=
      ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
    apply (meromorphicOrderAt_eq_int_iff hm).2
    refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall ?_⟩
    intro z
    simp
  · rw [if_neg hx]
    have ha : AnalyticAt ℂ (fun z : ℂ => (z - a)⁻¹) x :=
      (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hx)
    have he := meromorphicOrderAt_mul_of_ne_zero (f := fun _ : ℂ => (1 : ℂ))
      ha (inv_ne_zero (sub_ne_zero.mpr hx))
    change meromorphicOrderAt (fun z : ℂ => (z - a)⁻¹ * 1) x =
      meromorphicOrderAt (fun _ : ℂ => (1 : ℂ)) x at he
    simpa [meromorphicOrderAt_const] using he

/-- CONDITIONAL removal of the actual norm-twist clearing polynomial. Z is
supplied, not a newly defined L-function; its arithmetic attachment remains
unproved. This isolates the exact divisor correction required by the target. -/
theorem uncleared_norm_twist_order (Z : ℂ → ℂ) (τ : ℝ) (x : ℂ)
    (hZ : MeromorphicAt Z x) :
    meromorphicOrderAt (fun z : ℂ => Z z /
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I)))) x =
      meromorphicOrderAt Z x +
      (if x = -(τ : ℂ) * Complex.I then (-1 : WithTop ℤ) else 0) +
      (if x = 1 - (τ : ℂ) * Complex.I then (-1 : WithTop ℤ) else 0) := by
  have h0 : MeromorphicAt (fun z : ℂ => (z - (-(τ : ℂ) * Complex.I))⁻¹) x :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
  have h1 : MeromorphicAt (fun z : ℂ => (z - (1 - (τ : ℂ) * Complex.I))⁻¹) x :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).inv
  have hh := meromorphicOrderAt_mul (hZ.mul h0) h1
  rw [meromorphicOrderAt_mul hZ h0,
    reciprocal_linear_polar_order, reciprocal_linear_polar_order] at hh
  have heq : (fun z : ℂ => Z z /
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I)))) =
      (fun z : ℂ => (Z z * (z - (-(τ : ℂ) * Complex.I))⁻¹) *
        (z - (1 - (τ : ℂ) * Complex.I))⁻¹) := by
    funext z
    simp only [neg_mul, sub_neg_eq_add, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  exact hh

/-- CONDITIONAL genuine simple poles after clearing: nonzero analytic values
of Z at BOTH distinct polar roots are required. This is the missing nonzero
residue premise, not a proof that an arbitrary entire Z has these poles. -/
theorem norm_twist_simple_poles (Z : ℂ → ℂ) (τ : ℝ)
    (hZ0 : AnalyticAt ℂ Z (-(τ : ℂ) * Complex.I))
    (hZ1 : AnalyticAt ℂ Z (1 - (τ : ℂ) * Complex.I))
    (hne0 : Z (-(τ : ℂ) * Complex.I) ≠ 0)
    (hne1 : Z (1 - (τ : ℂ) * Complex.I) ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => Z z /
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I))))
        (-(τ : ℂ) * Complex.I) = -1 ∧
    meromorphicOrderAt (fun z : ℂ => Z z /
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I))))
        (1 - (τ : ℂ) * Complex.I) = -1 := by
  have hsep : -(τ : ℂ) * Complex.I ≠ 1 - (τ : ℂ) * Complex.I := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
  have hu0 := meromorphicOrderAt_mul_of_ne_zero (f := fun _ : ℂ => (1 : ℂ)) hZ0 hne0
  have hu1 := meromorphicOrderAt_mul_of_ne_zero (f := fun _ : ℂ => (1 : ℂ)) hZ1 hne1
  have ho0 : meromorphicOrderAt Z (-(τ : ℂ) * Complex.I) = 0 := by
    change meromorphicOrderAt (fun z => Z z * 1) _ = _ at hu0
    simpa [meromorphicOrderAt_const] using hu0
  have ho1 : meromorphicOrderAt Z (1 - (τ : ℂ) * Complex.I) = 0 := by
    change meromorphicOrderAt (fun z => Z z * 1) _ = _ at hu1
    simpa [meromorphicOrderAt_const] using hu1
  constructor
  · rw [uncleared_norm_twist_order Z τ _ hZ0.meromorphicAt, ho0]
    rw [if_pos rfl, if_neg hsep]
    norm_num
  · rw [uncleared_norm_twist_order Z τ _ hZ1.meromorphicAt, ho1]
    rw [if_neg (Ne.symm hsep), if_pos rfl]
    norm_num
#check linear_polar_factor_order
#print axioms linear_polar_factor_order
#check norm_twist_polar_divisor
#print axioms norm_twist_polar_divisor
#check reciprocal_linear_polar_order
#print axioms reciprocal_linear_polar_order
#check uncleared_norm_twist_order
#print axioms uncleared_norm_twist_order
#check norm_twist_simple_poles
#print axioms norm_twist_simple_poles
end MasulloGRH.Round12A

namespace MasulloGRH.Round13A
/-- CONDITIONAL continuation uniqueness for the genuine completed-divisor
bridge: half-plane agreement of supplied meromorphic continuations forces
agreement of every punctured germ. No zero set or continuation is defined. -/
theorem meromorphic_germ_eq_of_rightHalfPlane (F G : ℂ → ℂ)
    (hF : MeromorphicOn F Set.univ) (hG : MeromorphicOn G Set.univ)
    (h : ∀ z : ℂ, 1 < z.re → F z = G z) (x : ℂ) :
    F =ᶠ[𝓝[≠] x] G := by
  have hd := hF.fun_sub hG
  have hl : (fun z => F z - G z) =ᶠ[𝓝[≠] (2 : ℂ)] (fun _ => 0) := by
    have ho : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have ht : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    exact ((ho.eventually_mem ht).filter_mono nhdsWithin_le_nhds).mono
      (fun z hz => sub_eq_zero.mpr (h z hz))
  have htwo : meromorphicOrderAt (fun z => F z - G z) (2 : ℂ) = ⊤ := by
    rw [meromorphicOrderAt_congr hl]
    simp [meromorphicOrderAt_const]
  have hx : meromorphicOrderAt (fun z => F z - G z) x = ⊤ := by
    by_contra hn
    exact (hd.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ x) (Set.mem_univ (2 : ℂ)) hn) htwo
  have he := meromorphicOrderAt_eq_top_iff.mp hx
  filter_upwards [he] with z hz
  exact sub_eq_zero.mp hz
#check meromorphic_germ_eq_of_rightHalfPlane
#print axioms meromorphic_germ_eq_of_rightHalfPlane
end MasulloGRH.Round13A

namespace MasulloGRH.Round13A
/-- CONDITIONAL attachment of the norm-twist divisor to a supplied actual
continuation Lambda. Discharges the previously missing germ-transport premise:
a right-half-plane clearing identity suffices; global quotient equality and
pointwise values at poles are not assumed. Arithmetic existence and the
half-plane identity still must be proved for the genuine completed L. -/
theorem attached_norm_twist_divisor (Λ Z : ℂ → ℂ) (τ : ℝ)
    (hΛ : MeromorphicOn Λ Set.univ) (hZ : MeromorphicOn Z Set.univ)
    (hh : ∀ z : ℂ, 1 < z.re → Z z =
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I))) * Λ z)
    (x : ℂ) :
    meromorphicOrderAt Λ x = meromorphicOrderAt Z x +
      (if x = -(τ : ℂ) * Complex.I then (-1 : WithTop ℤ) else 0) +
      (if x = 1 - (τ : ℂ) * Complex.I then (-1 : WithTop ℤ) else 0) := by
  have hQ : MeromorphicOn (fun z : ℂ => Z z /
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I)))) Set.univ := by
    intro z hz
    exact (hZ z hz).div
      (((analyticAt_id.add analyticAt_const).mul
        (analyticAt_id.sub analyticAt_const)).meromorphicAt)
  have he := meromorphic_germ_eq_of_rightHalfPlane Λ _ hΛ hQ (by
    intro z hz
    have h0 : z + (τ : ℂ) * Complex.I ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith
    have h1 : z - (1 - (τ : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp at hr
      linarith
    apply (eq_div_iff (mul_ne_zero h0 h1)).2
    rw [hh z hz]
    ring) x
  exact (meromorphicOrderAt_congr he).trans
    (MasulloGRH.Round12A.uncleared_norm_twist_order Z τ x (hZ x (Set.mem_univ x)))
#check attached_norm_twist_divisor
#print axioms attached_norm_twist_divisor
end MasulloGRH.Round13A

namespace MasulloGRH.Round13A
/-- CONDITIONAL nondegeneracy of the genuine completed divisor. An analytic,
nonzero Euler-half-plane model at 2 excludes identically zero germs everywhere
on the connected continuation plane, so all zero/pole orders are finite. This
is the finite-multiplicity premise needed before any genuine zero enumeration. -/
theorem finite_order_of_nonzero_halfPlane_model (Λ E : ℂ → ℂ)
    (hΛ : MeromorphicOn Λ Set.univ) (hE : AnalyticAt ℂ E (2 : ℂ))
    (hne : E 2 ≠ 0) (hh : ∀ z : ℂ, 1 < z.re → Λ z = E z) (x : ℂ) :
    meromorphicOrderAt Λ x ≠ ⊤ := by
  have hl : Λ =ᶠ[𝓝[≠] (2 : ℂ)] E := by
    have ho : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have ht : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    exact ((ho.eventually_mem ht).filter_mono nhdsWithin_le_nhds).mono hh
  have he := meromorphicOrderAt_mul_of_ne_zero
    (f := fun _ : ℂ => (1 : ℂ)) hE hne
  have he0 : meromorphicOrderAt E (2 : ℂ) = 0 := by
    change meromorphicOrderAt (fun z => E z * 1) (2 : ℂ) = _ at he
    simpa [meromorphicOrderAt_const] using he
  apply hΛ.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) (Set.mem_univ x)
  rw [meromorphicOrderAt_congr hl, he0]
  simp
#check finite_order_of_nonzero_halfPlane_model
#print axioms finite_order_of_nonzero_halfPlane_model
end MasulloGRH.Round13A

namespace MasulloGRH.Round15A
/-- Supplies the meromorphic-continuation premise for the completed-Hecke
bridge from a genuine theta FE-pair, once that arithmetic pair is attached.
This uses Mathlib's existing Mellin continuation; it defines no new L-function. -/
theorem weakFE_norm_twist_meromorphic (P : WeakFEPair ℂ) (τ : ℝ) :
    MeromorphicOn (fun z : ℂ => P.Λ (z + (τ : ℂ) * Complex.I)) Set.univ := by
  have hm (x : ℂ) : MeromorphicAt P.Λ x := by
    unfold WeakFEPair.Λ
    simp only [smul_eq_mul]
    exact ((P.differentiable_Λ₀.analyticAt x).meromorphicAt.sub
      ((analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt).mul
        analyticAt_const.meromorphicAt)).sub
      ((analyticAt_const.meromorphicAt.div
        ((analyticAt_const.sub analyticAt_id).meromorphicAt)).mul
          analyticAt_const.meromorphicAt)
  intro x _
  exact (hm _).comp_analyticAt ((differentiable_id.add_const _).analyticAt x)

/-- Discharges the nonzero-cleared-value premise of A12 from actual FE-pair
constant terms. Arithmetic realization of P as the genuine norm-character
theta pair remains an explicit dependency. All real norm shifts are included. -/
theorem weakFE_norm_twist_simple_poles (P : WeakFEPair ℂ) (hk : P.k = 1)
    (hf : P.f₀ ≠ 0) (hg : P.g₀ ≠ 0) (τ : ℝ) :
    meromorphicOrderAt (fun z : ℂ => P.Λ (z + (τ : ℂ) * Complex.I))
      (-(τ : ℂ) * Complex.I) = -1 ∧
    meromorphicOrderAt (fun z : ℂ => P.Λ (z + (τ : ℂ) * Complex.I))
      (1 - (τ : ℂ) * Complex.I) = -1 := by
  let t : ℂ := (τ : ℂ) * Complex.I
  let Z : ℂ → ℂ := fun z =>
    (z + t) * (z + t - 1) * P.Λ₀ (z + t) -
      (z + t - 1) * P.f₀ + (z + t) * P.ε * P.g₀
  have hZ : Differentiable ℂ Z := by
    dsimp [Z]
    have h := P.differentiable_Λ₀
    fun_prop
  have hhalf : ∀ z : ℂ, 1 < z.re → Z z =
      ((z + (τ : ℂ) * Complex.I) * (z - (1 - (τ : ℂ) * Complex.I))) *
        P.Λ (z + (τ : ℂ) * Complex.I) := by
    intro z hz
    have h0 : z + t ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp [t] at hr
      linarith
    have h1 : (1 : ℂ) - (z + t) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp [t] at hr
      linarith
    dsimp [Z, WeakFEPair.Λ]
    simp only [hk, Complex.ofReal_one, smul_eq_mul]
    change (z + t) * (z + t - 1) * P.Λ₀ (z + t) -
      (z + t - 1) * P.f₀ + (z + t) * P.ε * P.g₀ =
      ((z + t) * (z - (1 - t))) *
      (P.Λ₀ (z + t) - (1 / (z + t)) * P.f₀ -
        (P.ε / (1 - (z + t))) * P.g₀)
    field_simp
    ring
  have hz0 : Z (-(τ : ℂ) * Complex.I) ≠ 0 := by
    simpa [Z, t] using hf
  have hz1 : Z (1 - (τ : ℂ) * Complex.I) ≠ 0 := by
    simpa [Z, t] using mul_ne_zero P.hε hg
  have hsep : -(τ : ℂ) * Complex.I ≠ 1 - (τ : ℂ) * Complex.I := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
  have ho (x : ℂ) (hne : Z x ≠ 0) : meromorphicOrderAt Z x = 0 := by
    have he := meromorphicOrderAt_mul_of_ne_zero
      (f := fun _ : ℂ => (1 : ℂ)) (hZ.analyticAt x) hne
    change meromorphicOrderAt (fun z => Z z * 1) x = _ at he
    simpa [meromorphicOrderAt_const] using he
  have hattach := MasulloGRH.Round13A.attached_norm_twist_divisor
    (fun z => P.Λ (z + (τ : ℂ) * Complex.I)) Z τ
    (weakFE_norm_twist_meromorphic P τ)
    (fun x _ => (hZ.analyticAt x).meromorphicAt) hhalf
  constructor
  · rw [hattach, ho _ hz0, if_pos rfl, if_neg hsep]
    norm_num
  · rw [hattach, ho _ hz1, if_neg (Ne.symm hsep), if_pos rfl]
    norm_num
#check weakFE_norm_twist_meromorphic
#print axioms weakFE_norm_twist_meromorphic
#check weakFE_norm_twist_simple_poles
#print axioms weakFE_norm_twist_simple_poles
/-- CONDITIONAL transport of genuine pole multiplicities from a theta Mellin
identity. Premise discharged: both norm-twist poles are genuine simple poles
once the actual completed function agrees with this FE-pair Mellin transform
on Re(s)>1 and the theta constants are nonzero. No zero set is supplied. -/
theorem attached_mellin_simple_poles (P : WeakFEPair ℂ) (hk : P.k = 1)
    (hf : P.f₀ ≠ 0) (hg : P.g₀ ≠ 0) (τ : ℝ) (L : ℂ → ℂ)
    (hL : MeromorphicOn L Set.univ)
    (hM : ∀ z : ℂ, 1 < z.re →
      HasMellin (fun x => P.f x - P.f₀) (z + (τ : ℂ) * Complex.I) (L z)) :
    meromorphicOrderAt L (-(τ : ℂ) * Complex.I) = -1 ∧
    meromorphicOrderAt L (1 - (τ : ℂ) * Complex.I) = -1 := by
  have hh (z : ℂ) (hz : 1 < z.re) :
      L z = P.Λ (z + (τ : ℂ) * Complex.I) := by
    have hs : P.k < (z + (τ : ℂ) * Complex.I).re := by simpa [hk] using hz
    exact (hM z hz).2.symm.trans (P.hasMellin hs).2
  have he (x : ℂ) := meromorphicOrderAt_congr
    (MasulloGRH.Round13A.meromorphic_germ_eq_of_rightHalfPlane L _ hL
      (weakFE_norm_twist_meromorphic P τ) hh x)
  simpa only [he] using weakFE_norm_twist_simple_poles P hk hf hg τ
#check attached_mellin_simple_poles
#print axioms attached_mellin_simple_poles
end MasulloGRH.Round15A
