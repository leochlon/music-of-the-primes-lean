import Mathlib

open scoped NumberField

/-!
Participant C, round 18. Direct audit of manuscript (11.3.1.4) and
(11.3.2.3), a premise of the global-to-local diagonal decomposition in
Theorem 12.5.1.1. These are the genuine number-field ideles and the actual
finite-place valuation-unit strata. No operator, zero set, or trace is
replaced by these definitions. The result applies to any pulled-back kernel,
including the manuscript kernel once that pullback is constructed.

This checks that multiplication in the SAME second variable by a later
unit-stratum indicator kills the displayed shell. It does not prove the
geometric trace formula, diagonal convergence, or nuclearity.
-/
namespace GeometricReview18C

variable (K : Type*) [Field K] [NumberField K]

abbrev Ideles := (NumberField.AdeleRing (𝓞 K) K)ˣ
abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum (𝓞 K)

/-- The manuscript's finite set of local valuation-unit conditions. -/
def UnitStratum (P : Finset (FinitePlace K)) (g : Ideles K) : Prop :=
  ∀ v ∈ P, Valued.v (g.val.2 v) = 1

/-- Pullback multiplier on the actual ideles, before any quotient descent. -/
noncomputable def unitMask (P : Finset (FinitePlace K)) (g : Ideles K) : ℂ :=
  by
    classical
    exact if UnitStratum K P g then 1 else 0

/-- Premise discharged: orientation of the nested actual unit strata used
in (11.3.1.4); adding places imposes more unit conditions. -/
theorem unitStratum_antitone {P Q : Finset (FinitePlace K)} (hPQ : P ⊆ Q)
    {g : Ideles K} (hQ : UnitStratum K Q g) : UnitStratum K P g := by
  intro v hv
  exact hQ v (hPQ hv)

/-- Direct audit premise for (11.3.2.3): a later unit mask in the second
variable annihilates the shell displayed in (11.3.1.4). This is independent
of regularity or nuclearity of the actual pulled-back geometric kernel. -/
theorem later_unitMask_annihilates_geometric_shell
    {P Q R : Finset (FinitePlace K)} (hPQ : P ⊆ Q) (hQR : Q ⊆ R)
    (kernel : Ideles K → Ideles K → ℂ) (x y : Ideles K) :
    ((unitMask K Q y - unitMask K P y) * kernel x y) * unitMask K R y = 0 := by
  classical
  by_cases hR : UnitStratum K R y
  · have hQ : UnitStratum K Q y := unitStratum_antitone K hQR hR
    have hP : UnitStratum K P y := unitStratum_antitone K hPQ hQ
    simp [unitMask, hQ, hP]
  · simp [unitMask, hR]

/-- Consequently the printed claim that this later cutoff preserves the
shell is possible only when that shell was already zero at the point.
This identifies the precise failed implication rather than presuming a
nonzero arithmetic trace. -/
theorem later_unitMask_preserves_geometric_shell_iff_zero
    {P Q R : Finset (FinitePlace K)} (hPQ : P ⊆ Q) (hQR : Q ⊆ R)
    (kernel : Ideles K → Ideles K → ℂ) (x y : Ideles K) :
    ((unitMask K Q y - unitMask K P y) * kernel x y) * unitMask K R y =
        (unitMask K Q y - unitMask K P y) * kernel x y ↔
      (unitMask K Q y - unitMask K P y) * kernel x y = 0 := by
  rw [later_unitMask_annihilates_geometric_shell K hPQ hQR kernel x y]
  exact eq_comm

end GeometricReview18C

#check GeometricReview18C.later_unitMask_preserves_geometric_shell_iff_zero
#print axioms GeometricReview18C.later_unitMask_preserves_geometric_shell_iff_zero
#check GeometricReview18C.later_unitMask_annihilates_geometric_shell
#print axioms GeometricReview18C.later_unitMask_annihilates_geometric_shell
