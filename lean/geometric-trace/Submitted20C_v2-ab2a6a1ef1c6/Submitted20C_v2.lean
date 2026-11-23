import Mathlib
open scoped NumberField
open Filter

/-! C19: corrected global-to-local shell premise for Theorem 12.5.1.1.
The masks below are the genuine finite-place unit conditions of 11.3.1.
The result identifies the surviving S-local SUPPORT, not its arithmetic kernel.
No trace, nuclearity, quotient descent, or zero identification is assumed proved.
-/
namespace Geometric19C
variable (K : Type*) [Field K] [NumberField K]
abbrev Ideles := (NumberField.AdeleRing (𝓞 K) K)ˣ
abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
def UnitStratum (P : Finset (FinitePlace K)) (g : Ideles K) : Prop :=
  ∀ v ∈ P, Valued.v (g.val.2 v) = 1
noncomputable def unitMask (P : Finset (FinitePlace K)) (g : Ideles K) : ℂ := by
  classical
  exact if UnitStratum K P g then 1 else 0
def OutsideUnits (S : Finset (FinitePlace K)) (g : Ideles K) : Prop :=
  ∀ v, v ∉ S → Valued.v (g.val.2 v) = 1
noncomputable def outsideMask (S : Finset (FinitePlace K)) (g : Ideles K) : ℂ := by
  classical
  exact if OutsideUnits K S g then 1 else 0

/-- Premise discharged: the limiting mask is exactly the actual unit
condition outside S. Exhaustion is explicit, not inferred from compactness. -/
theorem unitMask_eventually_eq_outsideMask
    (S : Finset (FinitePlace K)) (P : ℕ → Finset (FinitePlace K))
    (hmono : Monotone P)
    (hcover : ∀ v, v ∉ S ↔ ∃ n, v ∈ P n) (g : Ideles K) :
    ∀ᶠ n in atTop, unitMask K (P n) g = outsideMask K S g := by
  classical
  by_cases hg : OutsideUnits K S g
  · filter_upwards [] with n
    have hp : UnitStratum K (P n) g := by
      intro v hv
      exact hg v ((hcover v).mpr ⟨n, hv⟩)
    simp [unitMask, outsideMask, hp, hg]
  · have hex : ∃ v, v ∉ S ∧ Valued.v (g.val.2 v) ≠ 1 := by
      by_contra hn
      apply hg
      intro v hvS
      by_contra hv
      exact hn ⟨v, hvS, hv⟩
    obtain ⟨v, hvS, hv⟩ := hex
    obtain ⟨N, hN⟩ := (hcover v).mp hvS
    filter_upwards [eventually_ge_atTop N] with n hn
    have hp : ¬ UnitStratum K (P n) g := by
      intro hp
      exact hv (hp v (hmono hn hN))
    simp [unitMask, outsideMask, hp, hg]

/-- Premise discharged: correct sign and exact finite remainder in the
shell split of the actual pulled-back kernel, before diagonal integration. -/
theorem corrected_shell_partial_sum
    (P : ℕ → Finset (FinitePlace K)) (hzero : P 0 = ∅)
    (kernel : Ideles K → Ideles K → ℂ) (x y : Ideles K) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (unitMask K (P n) y - unitMask K (P (n+1)) y) * kernel x y) =
      (1 - unitMask K (P N) y) * kernel x y := by
  classical
  induction N with
  | zero => simp [hzero, unitMask, UnitStratum]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- New exported result: exact eventual shell reconstruction on genuine
ideles, with the nonzero outside-S-unit remnant retained. The actual
indented arithmetic kernel can be substituted only after constructing it.
This discharges the pointwise signed decomposition premise of 11.3/12.3;
L1 interchange, quotient descent and the S-local trace remain separate. -/
theorem corrected_geometric_shell_eventually_reconstructs
    (S : Finset (FinitePlace K)) (P : ℕ → Finset (FinitePlace K))
    (hzero : P 0 = ∅) (hmono : Monotone P)
    (hcover : ∀ v, v ∉ S ↔ ∃ n, v ∈ P n)
    (kernel : Ideles K → Ideles K → ℂ) (x y : Ideles K) :
    ∀ᶠ N in atTop,
      outsideMask K S y * kernel x y +
        (∑ n ∈ Finset.range N,
          (unitMask K (P n) y - unitMask K (P (n+1)) y) * kernel x y) =
        kernel x y := by
  filter_upwards [unitMask_eventually_eq_outsideMask K S P hmono hcover y] with N hN
  rw [corrected_shell_partial_sum K P hzero kernel x y N, hN]
  ring

/-- Premise discharged: dominated cutoff passage for the corrected shell
sum along an actual idele diagonal. This is CONDITIONAL on integrability and
measurability of the pulled-back diagonal. It supplies neither of those
arithmetic attachments and does not assert any operator trace identity. -/
theorem corrected_shell_diagonal_integral_limit
    [MeasurableSpace (Ideles K)] (μ : MeasureTheory.Measure (Ideles K))
    (S : Finset (FinitePlace K)) (P : ℕ → Finset (FinitePlace K))
    (hzero : P 0 = ∅) (hmono : Monotone P)
    (hcover : ∀ v, v ∉ S ↔ ∃ n, v ∈ P n)
    (kernel : Ideles K → Ideles K → ℂ)
    (hint : MeasureTheory.Integrable (fun y => kernel y y) μ)
    (hmeas : ∀ N, MeasureTheory.AEStronglyMeasurable
      (fun y => (1 - unitMask K (P N) y) * kernel y y) μ) :
    Tendsto (fun N => ∫ y,
      (∑ n ∈ Finset.range N,
        (unitMask K (P n) y - unitMask K (P (n+1)) y) * kernel y y) ∂μ)
      atTop (nhds (∫ y, (1 - outsideMask K S y) * kernel y y ∂μ)) := by
  classical
  simp_rw [corrected_shell_partial_sum K P hzero kernel]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun y => ‖kernel y y‖) hmeas hint.norm
  · intro N
    filter_upwards [] with y
    by_cases h : UnitStratum K (P N) y
    · simp [unitMask, h]
    · simp [unitMask, h]
  · filter_upwards [] with y
    apply tendsto_const_nhds.congr'
    filter_upwards [unitMask_eventually_eq_outsideMask K S P hmono hcover y] with N hN
    rw [hN]


/-- The actual principal-idele action in the skewered diagonals of 12.2. -/
noncomputable def principalIdele (a : Kˣ) : Ideles K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom a

/-- Direct indentation premise: the same corrected shell limit on the
GENUINE pairs (x, principalIdele(a)*x). The measure and integrable indented
kernel are explicit hypotheses; matching the fundamental-domain measure and
constructing the canonical arithmetic kernel remain unresolved. -/
theorem corrected_indented_shell_integral_limit
    [MeasurableSpace (Ideles K × Kˣ)]
    (μ : MeasureTheory.Measure (Ideles K × Kˣ))
    (S : Finset (FinitePlace K)) (P : ℕ → Finset (FinitePlace K))
    (hzero : P 0 = ∅) (hmono : Monotone P)
    (hcover : ∀ v, v ∉ S ↔ ∃ n, v ∈ P n)
    (kernel : Ideles K → Ideles K → ℂ)
    (hint : MeasureTheory.Integrable
      (fun z : Ideles K × Kˣ => kernel z.1 (principalIdele K z.2 * z.1)) μ)
    (hmeas : ∀ N, MeasureTheory.AEStronglyMeasurable
      (fun z : Ideles K × Kˣ =>
        (1 - unitMask K (P N) (principalIdele K z.2 * z.1)) *
          kernel z.1 (principalIdele K z.2 * z.1)) μ) :
    Tendsto (fun N => ∫ z : Ideles K × Kˣ,
      (∑ n ∈ Finset.range N,
        (unitMask K (P n) (principalIdele K z.2 * z.1) -
          unitMask K (P (n+1)) (principalIdele K z.2 * z.1)) *
            kernel z.1 (principalIdele K z.2 * z.1)) ∂μ)
      atTop (nhds (∫ z : Ideles K × Kˣ,
        (1 - outsideMask K S (principalIdele K z.2 * z.1)) *
          kernel z.1 (principalIdele K z.2 * z.1) ∂μ)) := by
  classical
  simp_rw [corrected_shell_partial_sum K P hzero kernel]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun z : Ideles K × Kˣ => ‖kernel z.1 (principalIdele K z.2 * z.1)‖)
    hmeas hint.norm
  · intro N
    filter_upwards [] with z
    by_cases h : UnitStratum K (P N) (principalIdele K z.2 * z.1)
    · simp [unitMask, h]
    · simp [unitMask, h]
  · filter_upwards [] with z
    apply tendsto_const_nhds.congr'
    filter_upwards [unitMask_eventually_eq_outsideMask K S P hmono hcover
      (principalIdele K z.2 * z.1)] with N hN
    rw [hN]

end Geometric19C
#check Geometric19C.corrected_geometric_shell_eventually_reconstructs
#print axioms Geometric19C.corrected_geometric_shell_eventually_reconstructs
#check Geometric19C.unitMask_eventually_eq_outsideMask
#print axioms Geometric19C.unitMask_eventually_eq_outsideMask

#check Geometric19C.corrected_shell_diagonal_integral_limit
#print axioms Geometric19C.corrected_shell_diagonal_integral_limit

#check Geometric19C.corrected_indented_shell_integral_limit
#print axioms Geometric19C.corrected_indented_shell_integral_limit

namespace Geometric20C
open Geometric19C
variable (K : Type*) [Field K] [NumberField K]

/-- The actual subgroup of principal ideles, not a prescribed equivalence. -/
noncomputable def principalSubgroup : Subgroup (Ideles K) :=
  (Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom).range

/-- Named premise of 11.3/12.3: outside-S unit support survives multiplication
by an actual idele which is a unit at each place outside S. In particular this
applies to principal S-units. It does not assert invariance under all K-units. -/
theorem outsideUnits_mul_iff (S : Finset (FinitePlace K))
    (a g : Ideles K) (ha : OutsideUnits K S a) :
    OutsideUnits K S (a * g) ↔ OutsideUnits K S g := by
  constructor
  · intro h v hv
    have he := h v hv
    change Valued.v (a.val.2 v * g.val.2 v) = 1 at he
    simpa only [map_mul, ha v hv, one_mul] using he
  · intro h v hv
    change Valued.v (a.val.2 v * g.val.2 v) = 1
    rw [map_mul, ha v hv, h v hv, one_mul]

/-- Exact quotient-descent obstruction for the remnant in the corrected
11.3 shell split. A principal idele nonunit outside S identifies two ideles
with different masks. Thus the raw mask cannot itself be a class function.
This names the missing theta/indentation bridge; it is not a refutation of
an indented or automorphized kernel construction. -/
theorem outsideMask_no_ideleClass_descent
    (S : Finset (FinitePlace K)) (v : FinitePlace K) (hvS : v ∉ S)
    (a : Kˣ) (hv : Valued.v ((principalIdele K a).val.2 v) ≠ 1) :
    ¬ ∃ f : (Ideles K ⧸ principalSubgroup K) → ℂ,
      ∀ g : Ideles K, f (QuotientGroup.mk g) = outsideMask K S g := by
  classical
  have h1 : outsideMask K S (1 : Ideles K) = 1 := by
    have hone : OutsideUnits K S (1 : Ideles K) := by
      intro w hw
      change Valued.v (1 : w.adicCompletion K) = 1
      exact map_one _
    simp [outsideMask, hone]
  have ha : outsideMask K S (principalIdele K a) = 0 := by
    have hn : ¬ OutsideUnits K S (principalIdele K a) := fun h => hv (h v hvS)
    simp [outsideMask, hn]
  have hmem : principalIdele K a ∈ principalSubgroup K := ⟨a, rfl⟩
  have heq : (QuotientGroup.mk (principalIdele K a) :
      Ideles K ⧸ principalSubgroup K) = QuotientGroup.mk (1 : Ideles K) := by
    simpa using QuotientGroup.mk_mul_of_mem (1 : Ideles K) hmem
  rintro ⟨f, hf⟩
  have hh := hf (principalIdele K a)
  rw [heq, hf 1, h1, ha] at hh
  exact one_ne_zero hh

end Geometric20C
#check Geometric20C.outsideUnits_mul_iff
#print axioms Geometric20C.outsideUnits_mul_iff
#check Geometric20C.outsideMask_no_ideleClass_descent
#print axioms Geometric20C.outsideMask_no_ideleClass_descent
