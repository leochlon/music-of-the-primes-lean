import Mathlib
/- Exact current review-core definitions, extracted without alteration.
The new result uses the existing spectral trace obligation explicitly;
it does not assume or prove geometric trace equality or correction control. -/
open Complex Filter Topology MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace ManuscriptRH
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

def SpectralZeroTrace (D : RationalTraceData) : Prop :=
  ∀ p, D.allowed p → ∀ φ, Admissible D φ → ∀ k,
    Summable (fun ρ : GenuineZero => ‖nativeTerm D p (familyTest D k φ) ρ‖) ∧
    operatorTrace D p k φ = nativeSum D p (familyTest D k φ)


theorem full_width_native (D : RationalTraceData) (r : Parameters)
    (hf : ∀ ρ : GenuineZero, |ρ.val.re - 1/2| < r.width)
    (φ : D.Test) (ρ : GenuineZero) :
    nativeTerm D r φ ρ = (zeroOrder ρ : ℂ) * zeroTest D φ ρ := by
  unfold nativeTerm interiorMultiplicity boundaryMultiplicity
  rw [if_pos (hf ρ), if_neg (ne_of_lt (hf ρ))]
  simp

theorem actual_term_balance_r02 (D : RationalTraceData) (p : Parameters)
    (φ : D.Test) (ρ : GenuineZero) :
    nativeTerm D p φ ρ + (omittedTerm D p φ ρ - edgeTerm D p φ ρ) =
      (zeroOrder ρ : ℂ) * zeroTest D φ ρ := by
  have hi : interiorMultiplicity p ρ ≤ zeroOrder ρ := by
    unfold interiorMultiplicity
    split_ifs <;> omega
  unfold nativeTerm omittedTerm edgeTerm
  rw [Nat.cast_add, Nat.cast_sub hi]
  ring

/-- The correction is exactly a difference of traces of the original PA
operators, on their respective weighted spaces; no cross-space subtraction
of operators or identification of their orthogonal projections is made. -/
theorem actual_correction_as_trace_difference (D : RationalTraceData)
    (hs : SpectralZeroTrace D) {p r : Parameters}
    (hp : D.allowed p) (hr : D.allowed r)
    (hf : ∀ ρ : GenuineZero, |ρ.val.re - 1/2| < r.width)
    {φ : D.Test} (hφ : Admissible D φ) (k : TestFamily)
    (ho : Summable (fun ρ => omittedTerm D p (familyTest D k φ) ρ))
    (he : Summable (fun ρ => edgeTerm D p (familyTest D k φ) ρ)) :
    stripCorrection D p (familyTest D k φ) =
      operatorTrace D r k φ - operatorTrace D p k φ := by
  have hn := (hs p hp φ hφ k).1.of_norm
  have hb : nativeSum D p (familyTest D k φ) +
      stripCorrection D p (familyTest D k φ) =
      nativeSum D r (familyTest D k φ) := by
    unfold nativeSum stripCorrection
    rw [← ho.tsum_sub he, ← hn.tsum_add (ho.sub he)]
    apply tsum_congr
    intro ρ
    rw [actual_term_balance_r02, full_width_native D r hf]
  rw [(hs r hr φ hφ k).2, (hs p hp φ hφ k).2]
  linear_combination hb

end ManuscriptRH
#print axioms ManuscriptRH.actual_correction_as_trace_difference
