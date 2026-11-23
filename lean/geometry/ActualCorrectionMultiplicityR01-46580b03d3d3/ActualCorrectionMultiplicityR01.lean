import Mathlib
open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace Masullo.ManuscriptRH
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

/-- Number of actual jets retained by the weighted geometric quotient. -/
noncomputable def retainedCount (p : Parameters) (ρ : GenuineZero) : ℕ :=
  interiorMultiplicity p ρ + boundaryMultiplicity p ρ

/-- Boundary jets and interior jets cannot both contribute. -/
theorem retainedCount_le_order (p : Parameters) (ρ : GenuineZero) :
    retainedCount p ρ ≤ zeroOrder ρ := by
  classical
  by_cases hi : |ρ.val.re - 1/2| < p.width
  · have hn : |ρ.val.re - 1/2| ≠ p.width := ne_of_lt hi
    simp only [retainedCount, interiorMultiplicity, boundaryMultiplicity, if_pos hi, if_neg hn, add_zero, le_refl]
  · by_cases hb : |ρ.val.re - 1/2| = p.width
    · simp only [retainedCount, interiorMultiplicity, if_neg hi,
        boundaryMultiplicity, if_pos hb, zero_add]
      exact le_trans (Finset.card_filter_le _ _) (by simpa using (Finset.card_image_le (s := Finset.range (zeroOrder ρ)) (f := fun n : ℕ => (n : ℝ))))
    · simp only [retainedCount, interiorMultiplicity, boundaryMultiplicity, if_neg hi, if_neg hb, zero_add, Nat.zero_le]

/-- The exact missing coefficient includes the strict boundary deficit. -/
noncomputable def missingCount (p : Parameters) (ρ : GenuineZero) : ℕ :=
  zeroOrder ρ - retainedCount p ρ

theorem missing_add_retained (p : Parameters) (ρ : GenuineZero) :
    missingCount p ρ + retainedCount p ρ = zeroOrder ρ :=
  Nat.sub_add_cancel (retainedCount_le_order p ρ)

theorem actual_correction_coefficient (D : RationalTraceData)
    (p : Parameters) (φ : D.Test) (ρ : GenuineZero) :
    omittedTerm D p φ ρ - edgeTerm D p φ ρ =
      (missingCount p ρ : ℂ) * zeroTest D φ ρ := by
  have hb := retainedCount_le_order p ρ
  have hi : interiorMultiplicity p ρ ≤ zeroOrder ρ := by
    unfold retainedCount at hb
    omega
  have hm := missing_add_retained p ρ
  have hc : (zeroOrder ρ : ℂ) - (interiorMultiplicity p ρ : ℂ) -
      (boundaryMultiplicity p ρ : ℂ) = (missingCount p ρ : ℂ) := by
    have he := congrArg (fun n : ℕ => (n : ℂ)) hm
    push_cast at he
    unfold retainedCount at he
    push_cast at he
    linear_combination -he
  simp only [omittedTerm, edgeTerm, Nat.cast_sub hi]
  rw [← sub_mul, hc]

/-- A single series for the ACTUAL correction; both original series are retained
until the justified summable subtraction. Applies to either familyTest. -/
theorem stripCorrection_eq_missing (D : RationalTraceData)
    (p : Parameters) (φ : D.Test)
    (ho : Summable (omittedTerm D p φ)) (he : Summable (edgeTerm D p φ)) :
    stripCorrection D p φ =
      ∑' ρ : GenuineZero, (missingCount p ρ : ℂ) * zeroTest D φ ρ := by
  rw [stripCorrection, ← ho.tsum_sub he]
  exact tsum_congr (actual_correction_coefficient D p φ)

/-- Every genuine zero outside the width contributes its FULL order. -/
theorem missingCount_of_exterior (p : Parameters) (ρ : GenuineZero)
    (h : p.width < |ρ.val.re - 1/2|) : missingCount p ρ = zeroOrder ρ := by
  have hi : ¬ |ρ.val.re - 1/2| < p.width := not_lt_of_ge h.le
  have hb : |ρ.val.re - 1/2| ≠ p.width := ne_of_gt h
  simp only [missingCount, retainedCount, interiorMultiplicity, boundaryMultiplicity, if_neg hi, if_neg hb, zero_add, Nat.sub_zero]

/-- The exact boundary loss, including the equality case 2j+1=weight. -/
theorem missingCount_of_boundary (p : Parameters) (ρ : GenuineZero)
    (h : |ρ.val.re - 1/2| = p.width) :
    missingCount p ρ = zeroOrder ρ -
      (((Finset.range (zeroOrder ρ)).image (fun n : ℕ => (n : ℝ))).filter (fun j => 2*j+1 < p.weight)).card := by
  classical
  have hi : ¬ |ρ.val.re - 1/2| < p.width := by rw [h]; exact lt_irrefl _
  simp only [missingCount, retainedCount, interiorMultiplicity, boundaryMultiplicity, if_neg hi, if_pos h, zero_add]
  simp

#print axioms retainedCount_le_order
#print axioms actual_correction_coefficient
#print axioms stripCorrection_eq_missing
#print axioms missingCount_of_exterior
#print axioms missingCount_of_boundary
end Masullo.ManuscriptRH
