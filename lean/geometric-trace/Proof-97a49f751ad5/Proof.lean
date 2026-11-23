import Mathlib

open scoped NumberField
namespace GeometricC

abbrev Ideles (K : Type*) [Field K] [NumberField K] :=
  (NumberField.AdeleRing (𝓞 K) K)ˣ
noncomputable def principal (K : Type*) [Field K] [NumberField K] : Kˣ →* Ideles K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom
abbrev Classes (K : Type*) [Field K] [NumberField K] :=
  Ideles K ⧸ (principal K).range

/-- Discharges the discrete-norm estimate in 12.5.1.1: no nonzero valuation
lies in the support annulus once the residue norm exceeds its radius. -/
lemma pow_succ_lower {q : ℝ} (hq : 1 < q) (n : ℕ) : q ≤ q ^ (n + 1) := by
  have h : 1 ≤ q ^ n := one_le_pow₀ hq.le
  calc
    q = 1 * q := by ring
    _ ≤ q ^ n * q := mul_le_mul_of_nonneg_right h (by linarith)
    _ = q ^ (n + 1) := (pow_succ q n).symm

/-- CONDITIONAL arithmetic attachment: N must be the genuine class norm.
The conclusion discharges pointwise vanishing on a local norm shell; it does
not assert the orbital trace formula or the global-to-local kernel bridge. -/
theorem local_shell_vanish (K : Type*) [Field K] [NumberField K]
    (N : Classes K → ℝ) (φ : Classes K → ℂ) (T q : ℝ)
    (hT : 0 < T) (hq : 1 < q) (hTq : T < q)
    (hunit : ∀ x, N x = 1 → φ x = 0)
    (hsupport : ∀ x, φ x ≠ 0 → T⁻¹ < N x ∧ N x < T)
    (x : Classes K) (k : ℤ) (hx : N x = q ^ k) : φ x = 0 := by
  by_contra hn
  obtain ⟨hlo, hhi⟩ := hsupport x hn
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact hn (hunit x (by simpa using hx))
    | succ n =>
      have hb := pow_succ_lower hq n
      have he : N x = q ^ (n + 1) := by simpa using hx
      rw [he] at hhi
      linarith
  | negSucc n =>
    have hb := pow_succ_lower hq n
    have hp : 0 < q ^ (n + 1) := pow_pos (by linarith) _
    have hi : (q ^ (n + 1))⁻¹ < T⁻¹ :=
      (inv_lt_inv₀ hp hT).2 (lt_of_lt_of_le hTq hb)
    have he : N x = (q ^ (n + 1))⁻¹ := by simpa using hx
    rw [he] at hlo
    linarith

/-- Exact finite telescoping for the sign convention of (11.3.1.4).
With d_j=(α_(j+1)-α_j)k, the initial kernel equals the final carving MINUS
its differences. This is a finite identity, not a nuclearity assertion. -/
theorem carving_telescopes (α : ℕ → ℂ) (k : ℂ) (n : ℕ) :
    α n * k = α 0 * k + ∑ j ∈ Finset.range n, (α (j + 1) - α j) * k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [← add_assoc, ← ih]
    ring

/-- The limit algebra required by the missing section 12.3. Actual carving
convergence is an explicit premise; no nuclearity or infinite trace sum is assumed. -/
theorem carving_limit (α : ℕ → ℂ) (k a : ℂ)
    (hα : Filter.Tendsto α Filter.atTop (nhds a)) :
    Filter.Tendsto (fun n => ∑ j ∈ Finset.range n, (α (j + 1) - α j) * k)
      Filter.atTop (nhds (a * k - α 0 * k)) := by
  have he : (fun n => ∑ j ∈ Finset.range n, (α (j + 1) - α j) * k) =
      (fun n => α n * k - α 0 * k) := by
    funext n
    have h := carving_telescopes α k n
    linear_combination -h
  rw [he]
  exact (hα.mul_const k).sub_const (α 0 * k)

#check GeometricC.carving_limit
#print axioms GeometricC.carving_limit
#check GeometricC.local_shell_vanish
#print axioms GeometricC.local_shell_vanish
#check GeometricC.carving_telescopes
#print axioms GeometricC.carving_telescopes
end GeometricC


namespace GeometricC
open MeasureTheory Filter Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum (𝓞 K)

/-- The genuine componentwise unit restrictions in (11.3.1.2).
These are not inverse images under a field norm. -/
def unitCarving (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K) (n : ℕ) :
    Set (Ideles K) :=
  {a | ∀ j < n, v j ∉ S → Valued.v (a.val.2 (v j)) = 1}

/-- The genuine standard S-ideles: unit at every finite place outside S. -/
def sIdeleLocus (S : Set (FinitePlace K)) : Set (Ideles K) :=
  {a | ∀ w, w ∉ S → Valued.v (a.val.2 w) = 1}

/-- Discharges pointwise convergence of the actual coordinate carvings in
§12.3. Surjectivity is the precise exhaustion premise. -/
theorem unitCarving_eventually (S : Set (FinitePlace K))
    (v : ℕ → FinitePlace K) (hv : Function.Surjective v) (a : Ideles K) :
    ∀ᶠ n in atTop, (a ∈ unitCarving K S v n ↔ a ∈ sIdeleLocus K S) := by
  classical
  by_cases ha : a ∈ sIdeleLocus K S
  · exact Eventually.of_forall fun n => ⟨fun _ => ha, fun _ j _ hj => ha (v j) hj⟩
  · have hh : ∃ w, w ∉ S ∧ Valued.v (a.val.2 w) ≠ 1 := by
      by_contra h
      apply ha
      intro w hwS
      by_contra hw
      exact h ⟨w, hwS, hw⟩
    obtain ⟨w, hwS, hw⟩ := hh
    obtain ⟨j, rfl⟩ := hv w
    filter_upwards [eventually_ge_atTop (j + 1)] with n hn
    have hc : a ∉ unitCarving K S v n := by
      intro hc
      apply hw
      exact hc j (by omega) hwS
    exact iff_of_false hc ha

/-- Skew diagonal used by Proposition 12.2.2.2, with the actual principal idele. -/
def skewIdele (p : Ideles K × Kˣ) : Ideles K :=
  (principal K p.2)⁻¹ * p.1

/-- The supplied indentation times the supplied quotient diagonal, evaluated
on the genuine idele/principal-unit skew diagonal. Kernel attachment is open. -/
def liftedDiagonal (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (p : Ideles K × Kˣ) : ℂ :=
  u p.1 (skewIdele K p) * d (QuotientGroup.mk p.1)

/-- CONDITIONAL integrated carving limit for §12.3. The exhaustion and
coordinate cutoffs are actual; integrability of the SAME lifted arithmetic
kernel and measurability under the supplied measure remain explicit premises.
No shell summability, trace equality or nuclearity is assumed or concluded. -/
theorem lifted_diagonal_carving_limit
    [MeasurableSpace (Ideles K × Kˣ)]
    (mu : Measure (Ideles K × Kˣ))
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Function.Surjective v)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (hF : Integrable (liftedDiagonal K u d) mu)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    Tendsto (fun n => ∫ p, Set.indicator
        {p | skewIdele K p ∈ unitCarving K S v n} (liftedDiagonal K u d) p ∂mu)
      atTop (𝓝 (∫ p, Set.indicator
        {p | skewIdele K p ∈ sIdeleLocus K S} (liftedDiagonal K u d) p ∂mu)) := by
  classical
  apply tendsto_integral_of_dominated_convergence (fun p => ‖liftedDiagonal K u d p‖)
  · intro n
    exact hF.aestronglyMeasurable.indicator (hmeas n)
  · exact hF.norm
  · intro n
    exact Eventually.of_forall fun p => by
      by_cases hp : skewIdele K p ∈ unitCarving K S v n
      · simp [Set.indicator, hp]
      · simp [Set.indicator, hp, norm_nonneg]
  · exact Eventually.of_forall fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [unitCarving_eventually K S v hv (skewIdele K p)] with n hn
      simp only [Set.indicator, Set.mem_setOf_eq, hn]

#check GeometricC.unitCarving_eventually
#print axioms GeometricC.unitCarving_eventually
#check GeometricC.lifted_diagonal_carving_limit
#print axioms GeometricC.lifted_diagonal_carving_limit

/-- Discharges the integrated telescoping premise of §12.3 for the actual
componentwise carvings. Paper-sign shell masses tend to residual minus global;
therefore global equals residual MINUS their sum. This is still conditional
on identifying u,d,mu with the arithmetic indentation and diagonal measure. -/
theorem lifted_diagonal_shell_mass_limit
    [MeasurableSpace (Ideles K × Kˣ)]
    (mu : Measure (Ideles K × Kˣ))
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Function.Surjective v)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (hF : Integrable (liftedDiagonal K u d) mu)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    Tendsto (fun n => ∑ j ∈ Finset.range n, ∫ p,
      (Set.indicator {p | skewIdele K p ∈ unitCarving K S v (j+1)}
        (liftedDiagonal K u d) p -
       Set.indicator {p | skewIdele K p ∈ unitCarving K S v j}
        (liftedDiagonal K u d) p) ∂mu)
      atTop (𝓝 ((∫ p, Set.indicator {p | skewIdele K p ∈ sIdeleLocus K S}
        (liftedDiagonal K u d) p ∂mu) - ∫ p, liftedDiagonal K u d p ∂mu)) := by
  classical
  let A : ℕ → ℂ := fun n => ∫ p, Set.indicator
    {p | skewIdele K p ∈ unitCarving K S v n} (liftedDiagonal K u d) p ∂mu
  have hzero : A 0 = ∫ p, liftedDiagonal K u d p ∂mu := by
    simp [A, unitCarving]
  have ht := carving_limit A 1
    (∫ p, Set.indicator {p | skewIdele K p ∈ sIdeleLocus K S}
      (liftedDiagonal K u d) p ∂mu)
    (lifted_diagonal_carving_limit K mu S v hv u d hF hmeas)
  simp only [mul_one, hzero] at ht
  have he (j : ℕ) : (∫ p,
      (Set.indicator {p | skewIdele K p ∈ unitCarving K S v (j+1)}
        (liftedDiagonal K u d) p -
       Set.indicator {p | skewIdele K p ∈ unitCarving K S v j}
        (liftedDiagonal K u d) p) ∂mu) = A (j+1) - A j :=
    integral_sub (hF.indicator (hmeas (j+1))) (hF.indicator (hmeas j))
  simpa only [he] using ht

#check GeometricC.lifted_diagonal_shell_mass_limit
#print axioms GeometricC.lifted_diagonal_shell_mass_limit

end
end GeometricC


namespace GeometricC
open MeasureTheory Filter Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- Supplies nestedness for the actual coordinate-shell absolute convergence
premise of the global-to-local decomposition in §12.3 and 12.5.1.1. -/
theorem unitCarving_antitone (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K) :
    Antitone (unitCarving K S v) := by
  intro m n hmn a ha j hj hS
  exact ha j (lt_of_lt_of_le hj hmn) hS

def carvedDiagonal (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (n : ℕ) (p : Ideles K × Kˣ) : ℂ :=
  Set.indicator {p | skewIdele K p ∈ unitCarving K S v n}
    (liftedDiagonal K u d) p

def diagonalShell (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (n : ℕ) (p : Ideles K × Kˣ) : ℂ :=
  carvedDiagonal K S v u d (n+1) p - carvedDiagonal K S v u d n p

/-- The absolute shell mass is the loss of absolute carved mass, because
these are nested indicators, not arbitrary bounded multipliers. This is the
pointwise premise for absolute integrated shell convergence in §12.3. -/
theorem norm_diagonalShell (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (n : ℕ) (p : Ideles K × Kˣ) :
    ‖diagonalShell K S v u d n p‖ =
      ‖carvedDiagonal K S v u d n p‖ - ‖carvedDiagonal K S v u d (n+1) p‖ := by
  classical
  by_cases hn : skewIdele K p ∈ unitCarving K S v (n+1)
  · have hm := unitCarving_antitone K S v (Nat.le_succ n) hn
    simp [diagonalShell, carvedDiagonal, Set.indicator, hn, hm]
  · by_cases hm : skewIdele K p ∈ unitCarving K S v n
    · simp [diagonalShell, carvedDiagonal, Set.indicator, hn, hm]
    · simp [diagonalShell, carvedDiagonal, Set.indicator, hn, hm]

#check GeometricC.norm_diagonalShell
#print axioms GeometricC.norm_diagonalShell

/-- Discharges absolute integrated shell summability in §12.3 from the SAME
L1 lifted diagonal as round 3. Summability is a conclusion, not a premise.
No arithmetic nuclearity or orbital trace identification is asserted. -/
theorem lifted_diagonal_shell_absolute_summable
    [MeasurableSpace (Ideles K × Kˣ)]
    (mu : Measure (Ideles K × Kˣ))
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (hF : Integrable (liftedDiagonal K u d) mu)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    Summable (fun n => ∫ p, ‖diagonalShell K S v u d n p‖ ∂mu) ∧
    Summable (fun n => ‖∫ p, diagonalShell K S v u d n p ∂mu‖) := by
  classical
  let A : ℕ → ℝ := fun n => ∫ p, ‖carvedDiagonal K S v u d n p‖ ∂mu
  have hi (n : ℕ) : Integrable (carvedDiagonal K S v u d n) mu :=
    hF.indicator (hmeas n)
  have hn (n : ℕ) : 0 ≤ A n := integral_nonneg (fun p => norm_nonneg _)
  have hid (n : ℕ) : (∫ p, ‖diagonalShell K S v u d n p‖ ∂mu) =
      A n - A (n+1) := by
    simp_rw [norm_diagonalShell]
    exact integral_sub (hi n).norm (hi (n+1)).norm
  have htel (n : ℕ) : (∑ j ∈ Finset.range n,
      ∫ p, ‖diagonalShell K S v u d j p‖ ∂mu) = A 0 - A n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, hid]
      ring
  have hs : Summable (fun n => ∫ p, ‖diagonalShell K S v u d n p‖ ∂mu) :=
    summable_of_sum_range_le (fun n => integral_nonneg (fun p => norm_nonneg _))
      (fun n => by rw [htel]; exact sub_le_self _ (hn n))
  exact ⟨hs, Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => norm_integral_le_integral_norm _) hs⟩

/-- CONDITIONAL unordered complex shell sum for the actual componentwise
carvings. Together with absolute summability this removes the scalar series
convergence premise of the global-to-local decomposition in §12.3. -/
theorem lifted_diagonal_shell_hasSum
    [MeasurableSpace (Ideles K × Kˣ)]
    (mu : Measure (Ideles K × Kˣ))
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Function.Surjective v)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (hF : Integrable (liftedDiagonal K u d) mu)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    HasSum (fun n => ∫ p, diagonalShell K S v u d n p ∂mu)
      ((∫ p, Set.indicator {p | skewIdele K p ∈ sIdeleLocus K S}
        (liftedDiagonal K u d) p ∂mu) - ∫ p, liftedDiagonal K u d p ∂mu) := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm
    (lifted_diagonal_shell_absolute_summable K mu S v u d hF hmeas).2).2
  simpa only [diagonalShell, carvedDiagonal] using
    lifted_diagonal_shell_mass_limit K mu S v hv u d hF hmeas

#check GeometricC.unitCarving_antitone
#print axioms GeometricC.unitCarving_antitone
#check GeometricC.lifted_diagonal_shell_absolute_summable
#print axioms GeometricC.lifted_diagonal_shell_absolute_summable
#check GeometricC.lifted_diagonal_shell_hasSum
#print axioms GeometricC.lifted_diagonal_shell_hasSum
end
end GeometricC

namespace GeometricC
open MeasureTheory Filter Topology
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- CONDITIONAL premise of 12.2.2.3--7: a nonnegative, normalized genuine
skew-diagonal indentation preserves both the diagonal value and its absolute
mass. The normalization/construction of the manuscript indentation is separate. -/
theorem indentation_fiber_mass
    (w : Ideles K → Ideles K → ℝ) (d : Classes K → ℂ)
    (hw : ∀ x h, 0 ≤ w x (skewIdele K (x,h)))
    (hpart : ∀ x, HasSum (fun h : Kˣ => w x (skewIdele K (x,h))) 1)
    (x : Ideles K) :
    HasSum (fun h : Kˣ => ‖liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,h)‖)
      ‖d (QuotientGroup.mk x)‖ ∧
    HasSum (fun h : Kˣ => liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,h))
      (d (QuotientGroup.mk x)) := by
  constructor
  · have H := (hpart x).mul_right ‖d (QuotientGroup.mk x)‖
    simpa [liftedDiagonal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hw x _)] using H
  · have H := (hpart x).smul_const (d (QuotientGroup.mk x))
    simpa [liftedDiagonal, Complex.real_smul] using H

#check GeometricC.indentation_fiber_mass
#print axioms GeometricC.indentation_fiber_mass

/-- Discharges the L1 lifted-diagonal hypothesis in the checked §12.3 shell
reduction, from base diagonal integrability and nonnegative normalized weights.
Here mu is intended to be Haar restricted to the SAME fundamental domain. -/
theorem indentation_lift_integrable
    [MeasurableSpace (Ideles K)] [MeasurableSpace Kˣ]
    [MeasurableSingletonClass Kˣ]
    (mu : Measure (Ideles K))
    (w : Ideles K → Ideles K → ℝ) (d : Classes K → ℂ)
    (hw : ∀ x h, 0 ≤ w x (skewIdele K (x,h)))
    (hpart : ∀ x, HasSum (fun h : Kˣ => w x (skewIdele K (x,h))) 1)
    (hm : AEStronglyMeasurable (liftedDiagonal K (fun x y => (w x y : ℂ)) d)
      (mu.prod Measure.count))
    (hd : Integrable (fun x : Ideles K => d (QuotientGroup.mk x)) mu) :
    Integrable (liftedDiagonal K (fun x y => (w x y : ℂ)) d)
      (mu.prod Measure.count) := by
  letI : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  apply (integrable_prod_iff hm).2
  constructor
  · exact Filter.Eventually.of_forall fun x => integrable_count_iff.mpr
      (indentation_fiber_mass K w d hw hpart x).1.summable
  · convert hd.norm using 1
    funext x
    have hi : Integrable (fun y : Kˣ =>
        ‖liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y)‖) Measure.count :=
      (integrable_count_iff.mpr
        (indentation_fiber_mass K w d hw hpart x).1.summable).norm
    have H := integral_countable (μ := Measure.count)
      (fun y : Kˣ => ‖liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y)‖)
      Set.countable_univ hi.integrableOn
    calc
      _ = ∑' y : Kˣ, ‖liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y)‖ := by
        let e : (Set.univ : Set Kˣ) ≃ Kˣ :=
          { toFun := Subtype.val
            invFun := fun a => ⟨a, Set.mem_univ a⟩
            left_inv := fun a => rfl
            right_inv := fun a => rfl }
        simp [Measure.real] at H
        exact H.trans (e.tsum_eq (fun y : Kˣ =>
          ‖liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y)‖))
      _ = _ := (indentation_fiber_mass K w d hw hpart x).1.tsum_eq

/-- CONDITIONAL full mass-preserving skew lift in 12.2.2.3--7. This supplies
both absolute integrability and Fubini for the actual idele/principal-unit
indexing. Constructing w=u0^Delta and transferring Haar from D to C_K remain. -/
theorem indentation_lift_integral
    [MeasurableSpace (Ideles K)] [MeasurableSpace Kˣ]
    [MeasurableSingletonClass Kˣ]
    (mu : Measure (Ideles K)) [SFinite mu]
    (w : Ideles K → Ideles K → ℝ) (d : Classes K → ℂ)
    (hw : ∀ x h, 0 ≤ w x (skewIdele K (x,h)))
    (hpart : ∀ x, HasSum (fun h : Kˣ => w x (skewIdele K (x,h))) 1)
    (hm : AEStronglyMeasurable (liftedDiagonal K (fun x y => (w x y : ℂ)) d)
      (mu.prod Measure.count))
    (hd : Integrable (fun x : Ideles K => d (QuotientGroup.mk x)) mu) :
    (∫ p, liftedDiagonal K (fun x y => (w x y : ℂ)) d p ∂(mu.prod Measure.count)) =
      ∫ x, d (QuotientGroup.mk x) ∂mu := by
  letI : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  rw [integral_prod _ (indentation_lift_integrable K mu w d hw hpart hm hd)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    have hi : Integrable (fun y : Kˣ =>
        liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y)) Measure.count :=
      integrable_count_iff.mpr (indentation_fiber_mass K w d hw hpart x).1.summable
    have H := integral_countable (μ := Measure.count)
      (fun y : Kˣ => liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y))
      Set.countable_univ hi.integrableOn
    calc
      _ = ∑' y : Kˣ, liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y) := by
        let e : (Set.univ : Set Kˣ) ≃ Kˣ :=
          { toFun := Subtype.val
            invFun := fun a => ⟨a, Set.mem_univ a⟩
            left_inv := fun a => rfl
            right_inv := fun a => rfl }
        simp [Measure.real] at H
        exact H.trans (e.tsum_eq (fun y : Kˣ =>
          liftedDiagonal K (fun x y => (w x y : ℂ)) d (x,y)))
      _ = _ := (indentation_fiber_mass K w d hw hpart x).2.tsum_eq

/-- Repairs the still-unchecked r04 shell-series/interchange step of §12.3
using the proved absolute integral series, with no summability assumption. -/
theorem lifted_diagonal_shell_integral_tsum
    [MeasurableSpace (Ideles K × Kˣ)]
    (mu : Measure (Ideles K × Kˣ))
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (u : Ideles K → Ideles K → ℂ) (d : Classes K → ℂ)
    (hF : Integrable (liftedDiagonal K u d) mu)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    (∫ p, ∑' n, diagonalShell K S v u d n p ∂mu) =
      ∑' n, ∫ p, diagonalShell K S v u d n p ∂mu := by
  have hi (n : ℕ) : Integrable (carvedDiagonal K S v u d n) mu :=
    hF.indicator (hmeas n)
  exact (integral_tsum_of_summable_integral_norm
    (fun n => (hi (n+1)).sub (hi n))
    (lifted_diagonal_shell_absolute_summable K mu S v u d hF hmeas).1).symm

#check GeometricC.indentation_lift_integrable
#print axioms GeometricC.indentation_lift_integrable
#check GeometricC.indentation_lift_integral
#print axioms GeometricC.indentation_lift_integral
#check GeometricC.lifted_diagonal_shell_integral_tsum
#print axioms GeometricC.lifted_diagonal_shell_integral_tsum
end
end GeometricC


namespace GeometricC
open MeasureTheory
noncomputable section
/-- CONDITIONAL §12.3 decomposition on genuine ideles. Discharges the lifted
L1 and count-integral premises using nonnegative normalized indentation weights.
The residual's S-local operator identity and each orbital identification remain
separate. The minus sign follows the shell convention of (11.3.1.4). -/
theorem indentation_global_to_local (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [MeasurableSpace Kˣ]
    [MeasurableSingletonClass Kˣ]
    (mu : Measure (Ideles K)) [SFinite mu]
    (w : Ideles K → Ideles K → ℝ) (d : Classes K → ℂ)
    (hw : ∀ x h, 0 ≤ w x (skewIdele K (x,h)))
    (hpart : ∀ x, HasSum (fun h : Kˣ => w x (skewIdele K (x,h))) 1)
    (hm : AEStronglyMeasurable (liftedDiagonal K (fun x y => (w x y : ℂ)) d)
      (mu.prod Measure.count))
    (hd : Integrable (fun x : Ideles K => d (QuotientGroup.mk x)) mu)
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Function.Surjective v)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    Summable (fun n => ∫ p,
      ‖diagonalShell K S v (fun x y => (w x y : ℂ)) d n p‖ ∂(mu.prod Measure.count)) ∧
    (∫ x, d (QuotientGroup.mk x) ∂mu) =
      (∫ p, Set.indicator {p | skewIdele K p ∈ sIdeleLocus K S}
        (liftedDiagonal K (fun x y => (w x y : ℂ)) d) p ∂(mu.prod Measure.count)) -
      ∑' n, ∫ p, diagonalShell K S v (fun x y => (w x y : ℂ)) d n p
        ∂(mu.prod Measure.count) := by
  have hF := indentation_lift_integrable K mu w d hw hpart hm hd
  refine ⟨(lifted_diagonal_shell_absolute_summable K (mu.prod Measure.count)
    S v (fun x y => (w x y : ℂ)) d hF hmeas).1, ?_⟩
  have H := (lifted_diagonal_shell_hasSum K (mu.prod Measure.count) S v hv
    (fun x y => (w x y : ℂ)) d hF hmeas).tsum_eq
  rw [indentation_lift_integral K mu w d hw hpart hm hd] at H
  linear_combination H

#check GeometricC.indentation_global_to_local
#print axioms GeometricC.indentation_global_to_local
end
end GeometricC

namespace GeometricC
noncomputable section
/-- The correlation in manuscript (12.2.2.1), using the genuine principal
idele action and counting measure. Existence of a suitable u0 is separate. -/
def indentationCorrelation (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (x y : Ideles K) : ℝ :=
  ∑' h : Kˣ, u0 (skewIdele K (x,h)) * u0 (skewIdele K (y,h))

/-- Discharges exactly the nonnegative normalized weight premises of
indentation_global_to_local for the correlation of (12.2.2.1). The input is
normalization of the underlying indentation, not shell/trace summability. -/
theorem indentation_correlation_normalized (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (hu : ∀ x, 0 ≤ u0 x)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1) :
    (∀ x y, 0 ≤ indentationCorrelation K u0 x y) ∧
    ∀ x, HasSum (fun h : Kˣ =>
      indentationCorrelation K u0 x (skewIdele K (x,h))) 1 := by
  constructor
  · intro x y
    exact tsum_nonneg fun h => mul_nonneg
      (hu (skewIdele K (x,h))) (hu (skewIdele K (y,h)))
  · intro x
    let f : Kˣ → ℝ := fun h => u0 (skewIdele K (x,h))
    have hf : HasSum f 1 := hpart x
    have hp : Summable (fun p : Kˣ × Kˣ => f p.1 * f p.2) :=
      hf.summable.mul_of_nonneg hf.summable
        (fun h => hu (skewIdele K (x,h))) (fun h => hu (skewIdele K (x,h)))
    have hh : HasSum (fun p : Kˣ × Kˣ => f p.1 * f p.2) 1 := by
      simpa using hf.mul hf hp
    let e : (Kˣ × Kˣ) ≃ (Kˣ × Kˣ) :=
      { toFun := fun p => (p.2, p.1 * p.2)
        invFun := fun p => (p.2 * p.1⁻¹, p.1)
        left_inv := by intro p; ext <;> simp
        right_inv := by intro p; ext <;> simp [mul_assoc] }
    have hs : HasSum (fun p : Kˣ × Kˣ => f p.2 * f (p.1 * p.2)) 1 := by
      simpa [Function.comp_def, e] using (e.hasSum_iff.mpr hh)
    have H := hs.prod_fiberwise (fun h => (hs.summable.prod_factor h).hasSum)
    simpa [indentationCorrelation, f, skewIdele, map_mul, mul_inv_rev, mul_assoc] using H

#check GeometricC.indentation_correlation_normalized
#print axioms GeometricC.indentation_correlation_normalized
end
end GeometricC

namespace GeometricC
/-- Discharges pointwise absolute convergence of the genuine correlation
series in (12.2.2.1); no summability of operator traces is assumed. -/
theorem indentation_correlation_summable (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (hu : ∀ x, 0 ≤ u0 x)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (x y : Ideles K) :
    Summable (fun h : Kˣ =>
      ‖u0 (skewIdele K (x,h)) * u0 (skewIdele K (y,h))‖) := by
  have hp := (hpart x).summable.mul_of_nonneg (hpart y).summable
    (fun h => hu (skewIdele K (x,h))) (fun h => hu (skewIdele K (y,h)))
  have hi : Function.Injective (fun h : Kˣ => (h,h)) := by
    intro a b h
    exact congrArg Prod.fst h
  have H := hp.comp_injective hi
  exact H.norm
#check GeometricC.indentation_correlation_summable
#print axioms GeometricC.indentation_correlation_summable
end GeometricC

namespace GeometricC
open Filter Topology

/-- Discharges the diagonal principal-action invariance premise in
Proposition 12.2.2.2(1) for the SAME arithmetic correlation (12.2.2.1).
This does not identify the correlation with an operator kernel. -/
theorem indentation_correlation_invariant (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (a : Kˣ) (x y : Ideles K) :
    indentationCorrelation K u0 (principal K a * x) (principal K a * y) =
      indentationCorrelation K u0 x y := by
  let e : Kˣ ≃ Kˣ :=
    { toFun := fun h => a * h
      invFun := fun h => a⁻¹ * h
      left_inv := by intro h; simp
      right_inv := by intro h; simp }
  simpa [indentationCorrelation, e, skewIdele, map_mul, mul_inv_rev, mul_assoc]
    using (e.tsum_eq (fun h =>
      u0 (skewIdele K (principal K a * x, h)) *
      u0 (skewIdele K (principal K a * y, h)))).symm

set_option maxHeartbeats 800000 in
/-- Discharges correlation continuity in Proposition 12.2.2.2(1), conditional
on local finiteness of the translates of the SAME continuous indentation.
The local finiteness premise must still be obtained from its proper support. -/
theorem indentation_correlation_continuous (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (hu : Continuous u0)
    (hlocal : ∀ x : Ideles K, ∃ s : Finset Kˣ,
      ∀ᶠ z in 𝓝 x, ∀ h ∉ s, u0 (skewIdele K (z,h)) = 0) :
    Continuous (fun p : Ideles K × Ideles K => indentationCorrelation K u0 p.1 p.2) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨s, hs⟩ := hlocal p.1
  have hc : Continuous (fun q : Ideles K × Ideles K =>
      ∑ h ∈ s, u0 (skewIdele K (q.1,h)) * u0 (skewIdele K (q.2,h))) := by
    exact continuous_finset_sum s fun h _ =>
      (hu.comp ((continuous_const : Continuous (fun _ : Ideles K × Ideles K =>
        (principal K h)⁻¹)).mul continuous_fst)).mul
      (hu.comp ((continuous_const : Continuous (fun _ : Ideles K × Ideles K =>
        (principal K h)⁻¹)).mul continuous_snd))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [(continuous_fst.continuousAt :
    Tendsto (Prod.fst : Ideles K × Ideles K → Ideles K) (𝓝 p) (𝓝 p.1)).eventually hs] with q hq
  unfold indentationCorrelation
  exact tsum_eq_sum (fun h hh => by rw [hq h hh, zero_mul])

#check GeometricC.indentation_correlation_invariant
#print axioms GeometricC.indentation_correlation_invariant
#check GeometricC.indentation_correlation_continuous
#print axioms GeometricC.indentation_correlation_continuous
end GeometricC

namespace GeometricC
open MeasureTheory

/-- Discharges the measurability premise of Proposition 12.2.2.2(2) and of
indentation_global_to_local for the exact correlation (12.2.2.1).
Continuity and locally finite translates of u0, second countability, and
Borel measurability of the pulled-back quotient
DIAGONAL are used: no product-a.e. statement is restricted to a null diagonal.
The measure, indentation construction and arithmetic kernel attachment remain separate. -/
theorem indentation_correlation_lift_measurable (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [BorelSpace (Ideles K)]
    [SecondCountableTopology (Ideles K)]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    (u0 : Ideles K → ℝ) (hu : Continuous u0)
    (hlocal : ∀ x : Ideles K, ∃ s : Finset Kˣ,
      ∀ᶠ z in nhds x, ∀ h ∉ s, u0 (skewIdele K (z,h)) = 0)
    (d : Classes K → ℂ)
    (hd : Measurable (fun x : Ideles K => d (QuotientGroup.mk x))) :
    Measurable (liftedDiagonal K
      (fun x y => (indentationCorrelation K u0 x y : ℂ)) d) := by
  letI : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  have hp : Measurable (principal K) := measurable_of_countable _
  have hs : Measurable (skewIdele K) :=
    (hp.comp measurable_snd).inv.mul measurable_fst
  have hc := (indentation_correlation_continuous K u0 hu hlocal).measurable
  exact (Complex.measurable_ofReal.comp
    (hc.comp (measurable_fst.prodMk hs))).mul (hd.comp measurable_fst)

/-- Discharges the lifted L1 premise of the global-to-local decomposition
for the SAME continuous nonnegative normalized indentation correlation.
This removes the previously supplied lifted AEStronglyMeasurable premise;
base diagonal L1 and its Borel representative remain explicit. -/
theorem continuous_indentation_lift_integrable (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [BorelSpace (Ideles K)]
    [SecondCountableTopology (Ideles K)]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    (mu : Measure (Ideles K)) (u0 : Ideles K → ℝ)
    (hu : Continuous u0)
    (hlocal : ∀ x : Ideles K, ∃ s : Finset Kˣ,
      ∀ᶠ z in nhds x, ∀ h ∉ s, u0 (skewIdele K (z,h)) = 0)
    (hn : ∀ x, 0 ≤ u0 x)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (d : Classes K → ℂ)
    (hdm : Measurable (fun x : Ideles K => d (QuotientGroup.mk x)))
    (hd : Integrable (fun x : Ideles K => d (QuotientGroup.mk x)) mu) :
    Integrable (liftedDiagonal K
      (fun x y => (indentationCorrelation K u0 x y : ℂ)) d) (mu.prod Measure.count) := by
  obtain ⟨hw, hp⟩ := indentation_correlation_normalized K u0 hn hpart
  exact indentation_lift_integrable K mu (indentationCorrelation K u0) d
    (fun x h => hw x (skewIdele K (x,h))) hp
    (indentation_correlation_lift_measurable K u0 hu hlocal d hdm).aestronglyMeasurable hd

#check GeometricC.indentation_correlation_lift_measurable
#print axioms GeometricC.indentation_correlation_lift_measurable
#check GeometricC.continuous_indentation_lift_integrable
#print axioms GeometricC.continuous_indentation_lift_integrable
end GeometricC

namespace GeometricC
open MeasureTheory

/-- CONDITIONAL quotient-Haar transport for (12.2.2.3--7) and §12.3.
Discharges the base-domain L1 and mass-identification premises from a Borel
L1 diagonal on the genuine idele class group. The domain D and its normalized
Haar pushforward are explicit inputs; their arithmetic construction is OPEN.
No operator trace, shell summability, or diagonal product-a.e. restriction is
assumed. The residual and shell terms use the SAME correlation and measure. -/
theorem quotient_diagonal_indentation_decomposition
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [BorelSpace (Ideles K)]
    [SecondCountableTopology (Ideles K)]
    [MeasurableSpace (Classes K)]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    (muG : Measure (Ideles K)) [SFinite muG]
    (muC : Measure (Classes K)) (D : Set (Ideles K))
    (hquot : MeasurePreserving (QuotientGroup.mk : Ideles K → Classes K)
      (muG.restrict D) muC)
    (u0 : Ideles K → ℝ) (hu : Continuous u0)
    (hlocal : ∀ x : Ideles K, ∃ s : Finset Kˣ,
      ∀ᶠ z in nhds x, ∀ h ∉ s, u0 (skewIdele K (z,h)) = 0)
    (hn : ∀ x, 0 ≤ u0 x)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (d : Classes K → ℂ) (hdm : Measurable d) (hd : Integrable d muC)
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Function.Surjective v)
    (hmeas : ∀ n, MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n}) :
    Integrable (liftedDiagonal K
      (fun x y => (indentationCorrelation K u0 x y : ℂ)) d)
        ((muG.restrict D).prod Measure.count) ∧
    Summable (fun n => ∫ p,
      ‖diagonalShell K S v (fun x y => (indentationCorrelation K u0 x y : ℂ)) d n p‖
        ∂((muG.restrict D).prod Measure.count)) ∧
    (∫ c, d c ∂muC) =
      (∫ p, Set.indicator {p | skewIdele K p ∈ sIdeleLocus K S}
        (liftedDiagonal K (fun x y => (indentationCorrelation K u0 x y : ℂ)) d) p
          ∂((muG.restrict D).prod Measure.count)) -
      ∑' n, ∫ p,
        diagonalShell K S v (fun x y => (indentationCorrelation K u0 x y : ℂ)) d n p
          ∂((muG.restrict D).prod Measure.count) := by
  have hdm' : Measurable (fun x : Ideles K => d (QuotientGroup.mk x)) :=
    hdm.comp hquot.measurable
  have hd' : Integrable (fun x : Ideles K => d (QuotientGroup.mk x))
      (muG.restrict D) := (hquot.integrable_comp hdm.aestronglyMeasurable).mpr hd
  have he : (∫ x, d (QuotientGroup.mk x) ∂(muG.restrict D)) = ∫ c, d c ∂muC :=
    calc
      _ = ∫ c, d c ∂Measure.map
          (QuotientGroup.mk : Ideles K → Classes K) (muG.restrict D) :=
        (integral_map hquot.measurable.aemeasurable hdm.aestronglyMeasurable).symm
      _ = _ := by rw [hquot.map_eq]
  obtain ⟨hw, hp⟩ := indentation_correlation_normalized K u0 hn hpart
  have hdec := indentation_global_to_local K (muG.restrict D)
    (indentationCorrelation K u0) d (fun x h => hw x (skewIdele K (x,h))) hp
    (indentation_correlation_lift_measurable K u0 hu hlocal d hdm').aestronglyMeasurable
    hd' S v hv hmeas
  rw [he] at hdec
  exact ⟨continuous_indentation_lift_integrable K (muG.restrict D)
    u0 hu hlocal hn hpart d hdm' hd', hdec⟩

#check GeometricC.quotient_diagonal_indentation_decomposition
#print axioms GeometricC.quotient_diagonal_indentation_decomposition
end GeometricC

namespace GeometricC
noncomputable section
/-- The two-variable lift in (12.2.2.2), on genuine arithmetic groups.
The supplied k must still be identified as the correctly ordered canonical
geometric kernel; this definition makes no such operator assertion. -/
def indentedKernel (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (k : Classes K → Classes K → ℂ)
    (x y : Ideles K) : ℂ :=
  (indentationCorrelation K u0 x y : ℂ) * k (QuotientGroup.mk x) (QuotientGroup.mk y)

/-- Discharges the quotient-skew identity needed to identify the actual
indented kernel integrand in (12.2.2.7) with liftedDiagonal. -/
theorem principal_skew_class (K : Type*) [Field K] [NumberField K]
    (x : Ideles K) (h : Kˣ) :
    (QuotientGroup.mk (skewIdele K (x,h)) : Classes K) = QuotientGroup.mk x := by
  apply QuotientGroup.eq.mpr
  refine ⟨h, ?_⟩
  simp [skewIdele, mul_inv_rev, mul_comm]

/-- Exact-source arithmetic kernel/diagonal bridge for (12.2.2.7).
This is pointwise for an actual chosen quotient representative, and never
restricts an ambient product-a.e. equality to its null diagonal. -/
theorem indentedKernel_skew_eq_liftedDiagonal
    (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (k : Classes K → Classes K → ℂ)
    (p : Ideles K × Kˣ) :
    indentedKernel K u0 k p.1 (skewIdele K p) =
      liftedDiagonal K (fun x y => (indentationCorrelation K u0 x y : ℂ))
        (fun c => k c c) p := by
  unfold indentedKernel liftedDiagonal
  rw [principal_skew_class K p.1 p.2]

#check GeometricC.principal_skew_class
#print axioms GeometricC.principal_skew_class
#check GeometricC.indentedKernel_skew_eq_liftedDiagonal
#print axioms GeometricC.indentedKernel_skew_eq_liftedDiagonal
end
end GeometricC

namespace GeometricC
open MeasureTheory

/-- Precise premise of (12.2.2.4--7): the two principal skew orientations
agree for the genuine correlation lift, without requiring symmetry of k. -/
theorem indentedKernel_skew_swap
    (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (k : Classes K → Classes K → ℂ)
    (x : Ideles K) (h : Kˣ) :
    indentedKernel K u0 k (skewIdele K (x,h)) x =
      indentedKernel K u0 k x (skewIdele K (x,h)) := by
  have hs : indentationCorrelation K u0 (skewIdele K (x,h)) x =
      indentationCorrelation K u0 x (skewIdele K (x,h)) := by
    unfold indentationCorrelation
    apply tsum_congr
    intro a
    exact mul_comm _ _
  unfold indentedKernel
  rw [principal_skew_class K x h, hs]

/-- CONDITIONAL arithmetic kernel transport for (12.2.2.3--7).
Discharges absolute convergence and both Fubini orders for the SAME supplied
quotient kernel and genuine principal-action correlation. Haar normalization,
indentation existence, and identification of k with the correctly ordered
geometric operator's canonical representative remain separate obligations. -/
theorem quotient_indentedKernel_integral
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [BorelSpace (Ideles K)]
    [SecondCountableTopology (Ideles K)] [MeasurableSpace (Classes K)]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    (muG : Measure (Ideles K)) [SFinite muG]
    (muC : Measure (Classes K)) (D : Set (Ideles K))
    (hquot : MeasurePreserving (QuotientGroup.mk : Ideles K → Classes K)
      (muG.restrict D) muC)
    (u0 : Ideles K → ℝ) (hu : Continuous u0)
    (hlocal : ∀ x : Ideles K, ∃ s : Finset Kˣ,
      ∀ᶠ z in nhds x, ∀ h ∉ s, u0 (skewIdele K (z,h)) = 0)
    (hn : ∀ x, 0 ≤ u0 x)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (k : Classes K → Classes K → ℂ)
    (hkm : Measurable (fun c => k c c)) (hk : Integrable (fun c => k c c) muC) :
    Integrable (fun p : Ideles K × Kˣ =>
      indentedKernel K u0 k p.1 (skewIdele K p))
        ((muG.restrict D).prod Measure.count) ∧
    (∫ c, k c c ∂muC) =
      (∫ x, ∫ h : Kˣ, indentedKernel K u0 k x (skewIdele K (x,h))
        ∂Measure.count ∂(muG.restrict D)) ∧
    (∫ c, k c c ∂muC) =
      (∫ h : Kˣ, ∫ x, indentedKernel K u0 k (skewIdele K (x,h)) x
        ∂(muG.restrict D) ∂Measure.count) := by
  letI : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  let f : Ideles K × Kˣ → ℂ := fun p =>
    indentedKernel K u0 k p.1 (skewIdele K p)
  have hf : f = liftedDiagonal K
      (fun x y => (indentationCorrelation K u0 x y : ℂ)) (fun c => k c c) := by
    funext p
    exact indentedKernel_skew_eq_liftedDiagonal K u0 k p
  have hm := hkm.comp hquot.measurable
  have hd := (hquot.integrable_comp hkm.aestronglyMeasurable).mpr hk
  have hi : Integrable f ((muG.restrict D).prod Measure.count) := by
    rw [hf]
    exact continuous_indentation_lift_integrable K (muG.restrict D)
      u0 hu hlocal hn hpart (fun c => k c c) hm hd
  have he : (∫ p, f p ∂((muG.restrict D).prod Measure.count)) = ∫ c, k c c ∂muC := by
    rw [hf]
    obtain ⟨hw, hp⟩ := indentation_correlation_normalized K u0 hn hpart
    rw [indentation_lift_integral K (muG.restrict D) (indentationCorrelation K u0)
      (fun c => k c c) (fun x h => hw x (skewIdele K (x,h))) hp
      (indentation_correlation_lift_measurable K u0 hu hlocal (fun c => k c c) hm).aestronglyMeasurable hd]
    calc
      _ = ∫ c, k c c ∂Measure.map
          (QuotientGroup.mk : Ideles K → Classes K) (muG.restrict D) :=
        (integral_map hquot.measurable.aemeasurable hkm.aestronglyMeasurable).symm
      _ = _ := by rw [hquot.map_eq]
  refine ⟨hi, ?_, ?_⟩
  · exact he.symm.trans (integral_prod f hi)
  · calc
      _ = ∫ h : Kˣ, ∫ x, f (x,h) ∂(muG.restrict D) ∂Measure.count :=
        he.symm.trans (integral_prod_symm f hi)
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h => by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x =>
            (indentedKernel_skew_swap K u0 k x h).symm

#check GeometricC.indentedKernel_skew_swap
#print axioms GeometricC.indentedKernel_skew_swap
#check GeometricC.quotient_indentedKernel_integral
#print axioms GeometricC.quotient_indentedKernel_integral
end GeometricC


namespace GeometricC
open MeasureTheory

/-- Discharges the coordinate-measurability premise of the genuine
(11.3.1.2) divisorial cutoffs. The valuation is that of the actual completion,
and the coordinate map is the actual restricted-product projection. -/
theorem local_unit_locus_isClosed (K : Type*) [Field K] [NumberField K]
    (v : FinitePlace K) :
    IsClosed {a : Ideles K | Valued.v (a.val.2 v) = 1} := by
  exact (Valued.isClopen_sphere (v.adicCompletion K)
    (by exact one_ne_zero : (1 : WithZero (Multiplicative ℤ)) ≠ 0)).isClosed.preimage
      ((RestrictedProduct.continuous_eval v).comp
        (continuous_snd.comp Units.continuous_val))

/-- Discharges Borel measurability of every finite arithmetic carving in
§11.3.1 and §12.3 without assuming valuation measurability. -/
theorem unitCarving_isClosed (K : Type*) [Field K] [NumberField K]
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K) (n : ℕ) :
    IsClosed (unitCarving K S v n) := by
  have he : unitCarving K S v n =
      ⋂ (j : ℕ) (_ : j < n) (_ : v j ∉ S),
        {a : Ideles K | Valued.v (a.val.2 (v j)) = 1} := by
    ext a
    simp [unitCarving]
  rw [he]
  exact isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => local_unit_locus_isClosed K (v j)

/-- Discharges measurability of the limiting S-idele residual in §12.3.
No finite-place enumeration or surjectivity premise is needed here. -/
theorem sIdeleLocus_isClosed (K : Type*) [Field K] [NumberField K]
    (S : Set (FinitePlace K)) : IsClosed (sIdeleLocus K S) := by
  have he : sIdeleLocus K S = ⋂ (v : FinitePlace K) (_ : v ∉ S),
      {a : Ideles K | Valued.v (a.val.2 v) = 1} := by
    ext a
    simp [sIdeleLocus]
  rw [he]
  exact isClosed_iInter fun v => isClosed_iInter fun _ => local_unit_locus_isClosed K v

/-- Discharges the exact hmeas premise in the r12 quotient decomposition:
actual coordinate cutoffs pulled back along the principal skew diagonal. -/
theorem skew_unitCarving_measurable (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [BorelSpace (Ideles K)]
    [SecondCountableTopology (Ideles K)]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K) (n : ℕ) :
    MeasurableSet {p | skewIdele K p ∈ unitCarving K S v n} := by
  letI : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  letI : Countable Kˣ := Units.val_injective.countable
  have hp : Measurable (principal K) := measurable_of_countable _
  have hs : Measurable (skewIdele K) :=
    (hp.comp measurable_snd).inv.mul measurable_fst
  exact (unitCarving_isClosed K S v n).measurableSet.preimage hs

/-- CONDITIONAL arithmetic application to §12.3 and Theorem 12.5.1.1.
The new ingredient proves the actual coordinate-cutoff measurability,
removing r12's hmeas hypothesis. Quotient Haar normalization, a continuous
normalized indentation and the SAME measurable L1 geometric diagonal still
need arithmetic construction; no trace or nuclearity is asserted. -/
theorem quotient_diagonal_arithmetic_decomposition
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (Ideles K)] [BorelSpace (Ideles K)]
    [SecondCountableTopology (Ideles K)]
    [MeasurableSpace (Classes K)]
    [MeasurableSpace Kˣ] [MeasurableSingletonClass Kˣ]
    (muG : Measure (Ideles K)) [SFinite muG]
    (muC : Measure (Classes K)) (D : Set (Ideles K))
    (hquot : MeasurePreserving (QuotientGroup.mk : Ideles K → Classes K)
      (muG.restrict D) muC)
    (u0 : Ideles K → ℝ) (hu : Continuous u0)
    (hlocal : ∀ x : Ideles K, ∃ s : Finset Kˣ,
      ∀ᶠ z in nhds x, ∀ h ∉ s, u0 (skewIdele K (z,h)) = 0)
    (hn : ∀ x, 0 ≤ u0 x)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (d : Classes K → ℂ) (hdm : Measurable d) (hd : Integrable d muC)
    (S : Set (FinitePlace K)) (v : ℕ → FinitePlace K)
    (hv : Function.Surjective v) :
    Integrable (liftedDiagonal K
      (fun x y => (indentationCorrelation K u0 x y : ℂ)) d)
        ((muG.restrict D).prod Measure.count) ∧
    Summable (fun n => ∫ p,
      ‖diagonalShell K S v (fun x y => (indentationCorrelation K u0 x y : ℂ)) d n p‖
        ∂((muG.restrict D).prod Measure.count)) ∧
    (∫ c, d c ∂muC) =
      (∫ p, Set.indicator {p | skewIdele K p ∈ sIdeleLocus K S}
        (liftedDiagonal K (fun x y => (indentationCorrelation K u0 x y : ℂ)) d) p
          ∂((muG.restrict D).prod Measure.count)) -
      ∑' n, ∫ p,
        diagonalShell K S v (fun x y => (indentationCorrelation K u0 x y : ℂ)) d n p
          ∂((muG.restrict D).prod Measure.count) := by
  exact quotient_diagonal_indentation_decomposition K muG muC D hquot u0 hu
    hlocal hn hpart d hdm hd S v hv (skew_unitCarving_measurable K S v)

#check GeometricC.local_unit_locus_isClosed
#print axioms GeometricC.local_unit_locus_isClosed
#check GeometricC.unitCarving_isClosed
#print axioms GeometricC.unitCarving_isClosed
#check GeometricC.sIdeleLocus_isClosed
#print axioms GeometricC.sIdeleLocus_isClosed
#check GeometricC.skew_unitCarving_measurable
#print axioms GeometricC.skew_unitCarving_measurable
#check GeometricC.quotient_diagonal_arithmetic_decomposition
#print axioms GeometricC.quotient_diagonal_arithmetic_decomposition
end GeometricC
