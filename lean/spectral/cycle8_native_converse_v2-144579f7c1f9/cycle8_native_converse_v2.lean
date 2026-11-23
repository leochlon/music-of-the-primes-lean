import Mathlib
attribute [local instance] Classical.propDecidable

namespace SpectralRound1B

/-- The finite set of boundary jets satisfying the STRICT numerical condition
in Proposition 9.1.2.5. This is an index set, not a spectrum or an L-function.
The unresolved analytic bridge is that these are exactly the continuous jets
of the actual weighted idele-class quotient. -/
noncomputable def boundaryJetOrders (N : ℕ) (s : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (2 : ℝ) * j + 1 < s)

/-- Discharges the finite counting premise for boundary multiplicities:
at odd integral weight 2*k+1, the strict cutoff retains min(N,k) jets. -/
theorem boundaryJetOrders_odd (N k : ℕ) :
    boundaryJetOrders N (2 * (k : ℝ) + 1) = Finset.range (min N k) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range, Nat.lt_min]
  constructor
  · intro h
    have hj : (j : ℝ) < (k : ℝ) := by linarith [h.2]
    exact ⟨h.1, by exact_mod_cast hj⟩
  · rintro ⟨hN, hk⟩
    have hj : (j : ℝ) < (k : ℝ) := by exact_mod_cast hk
    exact ⟨hN, by linarith⟩

/-- Conditional finite-block trace reduction for the binomial jet action
printed at (10.3.1.17). Discharges only its finite trace calculation; the
hypothesis must be proved for the genuine quotient operator before use. -/
theorem trace_of_binomial_jet_action (n : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    Matrix.trace M = (n : ℂ) * a 0 := by
  have hd (i : Fin n) : M i i = a 0 := by simp [hM]
  simp [Matrix.trace, Matrix.diag, hd, nsmul_eq_mul]

/-- Combined exact finite-count and conditional finite-trace step toward the
correct spectral multiplicity. No assertion of analytic jet admissibility,
zero identification, completeness, nuclearity, or infinite summability. -/
theorem boundary_jet_trace_at_odd_weight (N k : ℕ) (a : ℕ → ℂ)
    (M : Matrix (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card)
      (Fin (boundaryJetOrders N (2 * (k : ℝ) + 1)).card) ℂ)
    (hM : ∀ i j, M i j = if j.val ≤ i.val then
      (Nat.choose i.val j.val : ℂ) * a (i.val - j.val) else 0) :
    (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k ∧
      Matrix.trace M = ((min N k : ℕ) : ℂ) * a 0 := by
  have hc : (boundaryJetOrders N (2 * (k : ℝ) + 1)).card = min N k := by
    rw [boundaryJetOrders_odd, Finset.card_range]
  refine ⟨hc, ?_⟩
  simpa only [hc] using trace_of_binomial_jet_action _ a M hM

#print axioms boundaryJetOrders_odd
#print axioms trace_of_binomial_jet_action
#print axioms boundary_jet_trace_at_odd_weight
/-- Numerical boundary multiplicity for every real Sobolev parameter.
This discharges counting only; continuous native jet attachment is unresolved. -/
theorem boundaryJetOrders_all_real (N : ℕ) (s : ℝ) :
    boundaryJetOrders N s = Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  ext j
  simp only [boundaryJetOrders, Finset.mem_filter, Finset.mem_range,
    Nat.lt_min, Nat.lt_ceil]
  constructor
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩

#print axioms boundaryJetOrders_all_real
end SpectralRound1B

namespace SpectralRound3B
open MeasureTheory Set
/-- The actual polynomial part of the radial squared dual norm in
Proposition 9.1.2.5; no spectrum or L-function is defined here. -/
noncomputable def radialJetDensity (m : ℕ) (s : ℝ) (x : ℝ) : ℝ :=
  x ^ (2 * m) * (1 + x ^ 2) ^ (-s / 2)

/-- Power comparison needed for the native boundary-jet continuity premise. -/
theorem radialJetDensity_tail_comparison (m : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (x : ℝ) (hx : 1 < x) :
    radialJetDensity m s x ≤ x ^ ((2 : ℝ) * m - s) ∧
    (2 : ℝ) ^ (-s / 2) * x ^ ((2 : ℝ) * m - s) ≤ radialJetDensity m s x := by
  have hp : 0 < x := by linarith
  have hsq : 0 < x ^ 2 := sq_pos_of_pos hp
  have he : x ^ (2 * m) * (x ^ 2) ^ (-s / 2) =
      x ^ ((2 : ℝ) * m - s) := by
    rw [← Real.rpow_natCast x (2 * m), ← Real.rpow_natCast x 2,
      ← Real.rpow_mul (le_of_lt hp), ← Real.rpow_add hp]
    congr 1
    push_cast
    ring
  have hnon : 0 ≤ x ^ (2 * m) := pow_nonneg (le_of_lt hp) _
  have hq : -s / 2 ≤ 0 := by linarith
  constructor
  · unfold radialJetDensity
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hsq (by linarith) hq) hnon
  · have hbase : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
    have hb := Real.rpow_le_rpow_of_nonpos
      (show 0 < 1 + x ^ 2 by positivity) hbase hq
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hsq)] at hb
    have hh := mul_le_mul_of_nonneg_left hb hnon
    rw [← he]
    unfold radialJetDensity
    nlinarith

/-- Exact positive-tail criterion for the radial native Mellin-jet norm.
Discharges the boundary power-tail integrability premise, not the genuine
idele Haar decomposition or the weighted dual representation. -/
theorem radialJetDensity_integrable_tail_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (radialJetDensity m s) (Ioi 1) ↔ (2 : ℝ) * m + 1 < s := by
  have hm : AEStronglyMeasurable (radialJetDensity m s) (volume.restrict (Ioi 1)) := by
    apply Continuous.aestronglyMeasurable
    unfold radialJetDensity
    exact (continuous_id.pow _).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (by positivity)))
  have hn (x : ℝ) : 0 ≤ radialJetDensity m s x := by
    unfold radialJetDensity
    exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
      (Real.rpow_nonneg (by positivity) _)
  have hpow : IntegrableOn (fun x : ℝ => x ^ ((2 : ℝ) * m - s)) (Ioi 1) ↔
      (2 : ℝ) * m + 1 < s := by
    rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    constructor <;> intro h <;> linarith
  constructor
  · intro h
    apply hpow.mp
    apply (h.const_mul ((2 : ℝ) ^ (s / 2))).mono'
      ((measurable_id.pow_const _).aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp : 0 < x := by exact lt_trans zero_lt_one hx
    simp only [id_eq]
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hp _)]
    have hb := mul_le_mul_of_nonneg_left
      (radialJetDensity_tail_comparison m s hs x hx).2
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (s / 2))
    have hc : (2 : ℝ) ^ (s / 2) * 2 ^ (-s / 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show s / 2 + -s / 2 = 0 by ring, Real.rpow_zero]
    simpa only [← mul_assoc, hc, one_mul] using hb
  · intro h
    apply (hpow.mpr h).mono' hm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
    exact (radialJetDensity_tail_comparison m s hs x hx).1

#print axioms radialJetDensity_tail_comparison
#print axioms radialJetDensity_integrable_tail_iff
end SpectralRound3B

namespace SpectralRound3B
open MeasureTheory Set
/-- Includes the compact part of the actual radial density, so the only
obstruction on the positive half-line is the strict boundary jet cutoff. -/
theorem radialJetDensity_integrable_halfLine_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (radialJetDensity m s) (Ici 0) ↔ (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    apply (radialJetDensity_integrable_tail_iff m s hs).mp
    exact h.mono_set (by intro x hx; change 1 < x at hx; change 0 ≤ x; linarith)
  · intro h
    have hc : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
      ext x
      simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro hx
        by_cases h1 : x ≤ 1
        · exact Or.inl ⟨hx, h1⟩
        · exact Or.inr (lt_of_not_ge h1)
    have hi := (hc.integrableOn_Icc (a := 0) (b := 1)).union
      ((radialJetDensity_integrable_tail_iff m s hs).mpr h)
    rwa [hu] at hi
#print axioms radialJetDensity_integrable_halfLine_iff
end SpectralRound3B

namespace SpectralRound3B
open MeasureTheory Set
/-- At the right boundary b=alpha the exponential weight cancels on x>=0.
This discharges that precise tail of the actual weighted jet dual-norm test. -/
theorem boundaryRadialJet_integrable_halfLine_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x)
      (Ici 0) ↔ (2 : ℝ) * m + 1 < s := by
  have he : EqOn (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x)
      (radialJetDensity m s) (Ici 0) := by
    intro x hx
    change 0 ≤ x at hx
    dsimp only
    rw [abs_of_nonneg hx, sub_self, Real.exp_zero, one_mul]
  constructor
  · intro h
    exact (radialJetDensity_integrable_halfLine_iff m s hs).mp
      (h.congr_fun he measurableSet_Ici)
  · intro h
    exact ((radialJetDensity_integrable_halfLine_iff m s hs).mpr h).congr_fun
      (fun x hx => (he hx).symm) measurableSet_Ici
#print axioms boundaryRadialJet_integrable_halfLine_iff
end SpectralRound3B

namespace SpectralRound4B
open MeasureTheory Set SpectralRound3B
/-- Discharges reflection symmetry of the squared radial jet norm, needed
for the negative-tail part of the native boundary multiplicity criterion. -/
theorem radialJetDensity_even (m : ℕ) (s x : ℝ) :
    radialJetDensity m s (-x) = radialJetDensity m s x := by
  simp [radialJetDensity, pow_mul]
#print axioms radialJetDensity_even

/-- Full radial norm criterion: closes the negative-tail premise left open
by the positive-half-line calculation in round 3. -/
theorem radialJetDensity_integrable_iff (m : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (radialJetDensity m s) ↔ (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    exact (radialJetDensity_integrable_halfLine_iff m s hs).mp h.integrableOn
  · intro h
    have hp := (radialJetDensity_integrable_halfLine_iff m s hs).mpr h
    have hn : IntegrableOn (radialJetDensity m s) (Iic 0) := by
      simpa [radialJetDensity_even] using hp.comp_neg
    have hu : Ici (0 : ℝ) ∪ Iic 0 = univ := by
      ext x
      simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
      exact le_total 0 x
    simpa only [hu, integrableOn_univ] using hp.union hn

/-- Full right-boundary squared radial norm, including the decaying tail.
This discharges the analytic boundary cutoff premise for spectral jet
multiplicities; the genuine Haar and weighted-dual bridges remain separate. -/
theorem rightBoundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    exact (boundaryRadialJet_integrable_halfLine_iff m s alpha hs).mp h.integrableOn
  · intro h
    have hc : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    have hw : Continuous (fun x : ℝ =>
        Real.exp (2 * alpha * x - 2 * alpha * |x|) * radialJetDensity m s x) :=
      (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
        (continuous_const.mul continuous_abs))).mul hc
    apply ((radialJetDensity_integrable_iff m s hs).mpr h).mono'
      hw.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hn : 0 ≤ radialJetDensity m s x := by
      unfold radialJetDensity
      exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
        (Real.rpow_nonneg (by positivity) _)
    have he : Real.exp (2 * alpha * x - 2 * alpha * |x|) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [le_abs_self x]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hn)]
    exact (mul_le_mul_of_nonneg_right he hn).trans_eq (one_mul _)

#print axioms radialJetDensity_integrable_iff
#print axioms rightBoundaryRadialJet_integrable_iff

/-- Reflection proves the same sharp cutoff at the other strip boundary. -/
theorem leftBoundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * (-alpha) * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  constructor
  · intro h
    apply (rightBoundaryRadialJet_integrable_iff m s alpha hs ha).mp
    simpa only [mul_neg, neg_mul, neg_neg, abs_neg, radialJetDensity_even] using h.comp_neg
  · intro h
    have hr := (rightBoundaryRadialJet_integrable_iff m s alpha hs ha).mpr h
    simpa only [mul_neg, neg_mul, neg_neg, abs_neg, radialJetDensity_even] using hr.comp_neg

/-- Uniform statement for either genuine strip edge (including alpha=0).
It does not assume a prescribed zero set or any spectral summability. -/
theorem boundaryRadialJet_integrable_iff
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    Integrable (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x) ↔
      (2 : ℝ) * m + 1 < s := by
  rcases le_total 0 beta with h | h
  · have he : beta = alpha := by simpa only [abs_of_nonneg h] using hb
    subst beta
    exact rightBoundaryRadialJet_integrable_iff m s alpha hs ha
  · have he : beta = -alpha := by rw [abs_of_nonpos h] at hb; linarith
    subst beta
    exact leftBoundaryRadialJet_integrable_iff m s alpha hs ha

#print axioms leftBoundaryRadialJet_integrable_iff
#print axioms boundaryRadialJet_integrable_iff
end SpectralRound4B

namespace SpectralRound4B
open MeasureTheory Set SpectralRound3B SpectralRound1B
attribute [local instance] Classical.propDecidable
/-- Converts the proven full-line integrability condition into the exact
number of surviving orders below N. This discharges only analytic counting;
N still has to be identified with a genuine Hecke zero's order. -/
theorem boundary_integrable_orders
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => Integrable (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x)) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  rw [← boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, boundaryJetOrders,
    boundaryRadialJet_integrable_iff m s alpha beta hs ha hb]
#print axioms boundary_integrable_orders
end SpectralRound4B

namespace SpectralRound5B
open MeasureTheory SpectralRound3B SpectralRound4B

/-- CONDITIONAL measure bridge for the actual log-norm map: a nonzero finite
Haar scaling preserves the sharp radial boundary criterion. Discharges the
measure-transport premise, not the genuine idele-class pushforward identity. -/
theorem boundary_density_integrable_pullback_iff
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (hell : AEMeasurable ell mu) (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    Integrable (fun x => Real.exp (2 * beta * ell x - 2 * alpha * |ell x|) *
      radialJetDensity m s (ell x)) mu ↔ (2 : ℝ) * m + 1 < s := by
  let d : ℝ → ℝ := fun x =>
    Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x
  have hc : Continuous (radialJetDensity m s) := by
    unfold radialJetDensity
    exact (continuous_id.pow _).mul
      ((continuous_const.add (continuous_id.pow 2)).rpow_const
        (fun x => Or.inl (by positivity)))
  have hd : Continuous d :=
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hc
  have ht := integrable_map_measure
    (μ := mu) (f := ell) (g := d) hd.aestronglyMeasurable hell
  rw [hmap, integrable_smul_measure hc0 hct] at ht
  exact ht.symm.trans (boundaryRadialJet_integrable_iff m s alpha beta hs ha hb)

/-- The scalar weight-normalized Mellin jet. The phase is any Circle-valued
function, including an actual unitary character times its imaginary norm twist.
This defines no operator, spectrum, or L-function. -/
noncomputable def weightedMellinJet {X : Type*} (ell : X → ℝ)
    (phase : X → Circle) (m : ℕ) (s alpha beta : ℝ) (x : X) : ℂ :=
  (phase x : ℂ) * ((Real.exp (beta * ell x - alpha * |ell x|) *
    (ell x)^m * (1 + (ell x)^2)^(-s / 4) : ℝ) : ℂ)

/-- Discharges the pointwise squared-norm identity for the explicit weighted
jet; no integrability assumption or zero enumeration enters the identity. -/
theorem weightedMellinJet_sq_norm {X : Type*} (ell : X → ℝ)
    (phase : X → Circle) (m : ℕ) (s alpha beta : ℝ) (x : X) :
    ‖weightedMellinJet ell phase m s alpha beta x‖^2 =
      Real.exp (2 * beta * ell x - 2 * alpha * |ell x|) *
        radialJetDensity m s (ell x) := by
  unfold weightedMellinJet radialJetDensity
  rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, mul_pow, ← Real.exp_nat_mul, ← pow_mul,
    ← Real.rpow_natCast ((1 + (ell x)^2)^(-s / 4)) 2,
    ← Real.rpow_mul (by positivity : 0 ≤ 1 + (ell x)^2)]
  ring_nf

/-- CONDITIONAL native-membership bridge: for an explicit weighted jet and
an actual log-norm pushforward, square integrability has the sharp boundary
cutoff. Native Haar splitting and weighted-dual representation remain open. -/
theorem boundary_weightedMellinJet_memLp_iff
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : AEMeasurable ell mu)
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha)
    (hf : AEStronglyMeasurable (weightedMellinJet ell phase m s alpha beta) mu) :
    MemLp (weightedMellinJet ell phase m s alpha beta) 2 mu ↔
      (2 : ℝ) * m + 1 < s := by
  rw [memLp_two_iff_integrable_sq_norm hf]
  simp only [weightedMellinJet_sq_norm]
  exact boundary_density_integrable_pullback_iff mu ell hell c hc0 hct hmap
    m s alpha beta hs ha hb

#print axioms boundary_density_integrable_pullback_iff
#print axioms weightedMellinJet_sq_norm
#print axioms boundary_weightedMellinJet_memLp_iff
end SpectralRound5B

namespace SpectralRound5B
open MeasureTheory SpectralRound1B
attribute [local instance] Classical.propDecidable
/-- Measurability follows from the log norm and unitary phase; discharges
this hypothesis of boundary weighted-jet membership without assuming it. -/
theorem weightedMellinJet_measurable
    {X : Type*} [MeasurableSpace X] (ell : X → ℝ) (phase : X → Circle)
    (hell : Measurable ell) (hphase : Measurable (fun x => (phase x : ℂ)))
    (m : ℕ) (s alpha beta : ℝ) :
    Measurable (weightedMellinJet ell phase m s alpha beta) := by
  unfold weightedMellinJet
  fun_prop

/-- Conditional exact multiplicity truncation for the explicit weighted jets.
The only geometric input is the actual log-norm Haar pushforward; N must
still be identified with the genuine Hecke analytic zero order. -/
theorem boundary_weightedMellinJet_orders
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : Measurable ell) (hphase : Measurable (fun x => (phase x : ℂ)))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (weightedMellinJet ell phase m s alpha beta) 2 mu) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  rw [← boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, boundaryJetOrders,
    boundary_weightedMellinJet_memLp_iff mu ell phase hell.aemeasurable
      c hc0 hct hmap m s alpha beta hs ha hb
      (weightedMellinJet_measurable ell phase hell hphase m s alpha beta).aestronglyMeasurable]

#print axioms weightedMellinJet_measurable
#print axioms boundary_weightedMellinJet_orders
end SpectralRound5B

namespace SpectralRound6B
open MeasureTheory Set SpectralRound3B SpectralRound4B SpectralRound5B

/-- The interior membership premise of (10.2.2.6): the actual squared
radial jet density is dominated by an exponentially damped polynomial.
This is a pointwise analytic bound, not a zero or spectrum definition. -/
theorem interior_density_le_exp_polynomial
    (m : ℕ) (s alpha beta x : ℝ) (hs : 0 ≤ s) :
    Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x ≤
      Real.exp (-(2 * (alpha - |beta|)) * |x|) * x ^ (2 * m) := by
  have hp : 0 ≤ x ^ (2 * m) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg x) m
  have hw : (1 + x ^ 2) ^ (-s / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg x]) (by linarith)
  have hb : beta * x ≤ |beta| * |x| := by
    simpa only [abs_mul] using (le_abs_self (beta * x))
  have he : Real.exp (2 * beta * x - 2 * alpha * |x|) ≤
      Real.exp (-(2 * (alpha - |beta|)) * |x|) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ Real.exp (2 * beta * x - 2 * alpha * |x|) * x ^ (2 * m) := by
      unfold radialJetDensity
      exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left hw hp)
        (Real.exp_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right he hp

#print axioms interior_density_le_exp_polynomial
end SpectralRound6B

namespace SpectralRound6B
open MeasureTheory Set SpectralRound3B SpectralRound4B SpectralRound5B
/-- The integrable majorant required by the interior jet bound. -/
theorem exp_abs_even_polynomial_integrable (m : ℕ) (d : ℝ) (hd : 0 < d) :
    Integrable (fun x : ℝ => Real.exp (-d * |x|) * x ^ (2 * m)) := by
  let g : ℝ → ℝ := fun x => Real.exp (-d * |x|) * x ^ (2 * m)
  have hc : Continuous g := by dsimp [g]; fun_prop
  have ht : IntegrableOn (fun x : ℝ => x ^ (2 * m) * Real.exp (-d * x)) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 * m : ℕ)) (p := 1)
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num) hd)
  have hg : IntegrableOn g (Ioi 0) := ht.congr_fun (by
    intro x hx
    dsimp [g]
    rw [abs_of_pos hx, mul_comm]) measurableSet_Ioi
  have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hp : IntegrableOn g (Ici 0) := by
    rw [← hu]
    exact (hc.integrableOn_Icc).union (hg.mono_set (by intro x hx; change (0 : ℝ) < x; change (1 : ℝ) < x at hx; linarith))
  have hn : IntegrableOn g (Iic 0) := by
    simpa [g, pow_mul] using hp.comp_neg
  have hall : Ici (0 : ℝ) ∪ Iic 0 = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 x
  simpa only [hall, integrableOn_univ] using hp.union hn

/-- All finite radial jet orders are integrable strictly inside the strip;
this discharges the analytic all-orders premise of (10.2.2.6). -/
theorem interiorRadialJet_integrable (m : ℕ) (s alpha beta : ℝ)
    (hs : 0 ≤ s) (hb : |beta| < alpha) :
    Integrable (fun x : ℝ => Real.exp (2 * beta * x - 2 * alpha * |x|) *
      radialJetDensity m s x) := by
  have hc : Continuous (fun x : ℝ =>
      Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x) := by
    have hr : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hr
  apply (exp_abs_even_polynomial_integrable m (2 * (alpha - |beta|))
    (by linarith)).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hn : 0 ≤ radialJetDensity m s x := by
    unfold radialJetDensity
    exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) m)
      (Real.rpow_nonneg (by positivity) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) hn)]
  exact interior_density_le_exp_polynomial m s alpha beta x hs

/-- Conditional native measure transport of the full interior membership
criterion. The actual Haar pushforward and native dual realization remain
application obligations; no zero set or spectral operator is prescribed. -/
theorem interior_weightedMellinJet_memLp
    {X : Type*} [MeasurableSpace X] (mu : Measure X) (ell : X → ℝ)
    (phase : X → Circle) (hell : Measurable ell)
    (hphase : Measurable (fun x => (phase x : ℂ)))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map ell mu = c • volume)
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (hb : |beta| < alpha) :
    MemLp (weightedMellinJet ell phase m s alpha beta) 2 mu := by
  rw [memLp_two_iff_integrable_sq_norm
    (weightedMellinJet_measurable ell phase hell hphase m s alpha beta).aestronglyMeasurable]
  simp only [weightedMellinJet_sq_norm]
  let d : ℝ → ℝ := fun x => Real.exp (2 * beta * x - 2 * alpha * |x|) * radialJetDensity m s x
  have hd : Continuous d := by
    dsimp [d]
    have hr : Continuous (radialJetDensity m s) := by
      unfold radialJetDensity
      exact (continuous_id.pow _).mul
        ((continuous_const.add (continuous_id.pow 2)).rpow_const
          (fun x => Or.inl (by positivity)))
    exact (Real.continuous_exp.comp ((continuous_const.mul continuous_id).sub
      (continuous_const.mul continuous_abs))).mul hr
  have ht := integrable_map_measure (μ := mu) (f := ell) (g := d)
    hd.aestronglyMeasurable hell.aemeasurable
  rw [hmap, integrable_smul_measure hc0 hct] at ht
  exact ht.mp (interiorRadialJet_integrable m s alpha beta hs hb)

#print axioms exp_abs_even_polynomial_integrable
#print axioms interiorRadialJet_integrable
#print axioms interior_weightedMellinJet_memLp
end SpectralRound6B

/- Exact reused arithmetic quotient/log definitions and continuity from nuclear B177.
No new credit is claimed for this retained component. -/
noncomputable section
open scoped NumberField Valued WithZero ENNReal NNReal
open NumberField MeasureTheory
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
noncomputable instance classCommGroup : CommGroup (HeckeIdeleClasses K) := inferInstance
noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem genuineIdeleModulus_principal (a : Kˣ) :
    genuineIdeleModulus K (principalIdele K a) = 1 := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(principalIdele K a).val.1 w‖ = w (a : K) := by
    exact NumberField.InfinitePlace.Completion.norm_coe w
      ((WithAbs.equiv _).symm (a : K))
  have hf (v : NumberField.FinitePlace K) :
      ‖(principalIdele K a).val.2 v.maximalIdeal‖ = v (a : K) := by
    exact NumberField.FinitePlace.norm_embedding_eq v (a : K)
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  exact NumberField.prod_abs_eq_one (K := K) a.ne_zero
/-- Outside finitely many finite places, an actual idele has local norm one. -/
theorem genuineIdele_finite_norm_support (a : HeckeIdeles K) :
    (Function.mulSupport (fun v : NumberField.FinitePlace K =>
      ‖a.val.2 v.maximalIdeal‖)).Finite := by
  have he : ∀ᶠ v in Filter.cofinite, ‖a.val.2 v‖ = 1 := by
    filter_upwards [RestrictedProduct.eventually _ _ a.val.2,
      RestrictedProduct.eventually _ _ (a⁻¹).val.2] with v hv hi
    change Valued.v (a.val.2 v) ≤ 1 at hv
    change Valued.v ((a⁻¹).val.2 v) ≤ 1 at hi
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 := by
      have h := congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
      exact h
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm hv
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right hi _
        _ = Valued.v (a.val.2 v) := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  exact (Filter.eventually_cofinite.mp he).preimage
    NumberField.FinitePlace.maximalIdeal_injective.injOn
theorem genuineIdeleModulus_mul (a b : HeckeIdeles K) :
    genuineIdeleModulus K (a * b) = genuineIdeleModulus K a * genuineIdeleModulus K b := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(a * b).val.1 w‖ ^ w.mult =
        ‖a.val.1 w‖ ^ w.mult * ‖b.val.1 w‖ ^ w.mult := by
    change ‖a.val.1 w * b.val.1 w‖ ^ w.mult = _
    rw [norm_mul, mul_pow]
  have hf (v : NumberField.FinitePlace K) :
      ‖(a * b).val.2 v.maximalIdeal‖ =
        ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ := by
    change ‖a.val.2 v.maximalIdeal * b.val.2 v.maximalIdeal‖ = _
    exact norm_mul _ _
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib
    (genuineIdele_finite_norm_support K a) (genuineIdele_finite_norm_support K b)]
  ring

theorem genuineIdeleModulus_ne_zero (a : HeckeIdeles K) :
    genuineIdeleModulus K a ≠ 0 := by
  have h1 : genuineIdeleModulus K 1 = 1 := by
    simpa only [map_one] using genuineIdeleModulus_principal K 1
  have hp := genuineIdeleModulus_mul K a a⁻¹
  rw [mul_inv_cancel, h1] at hp
  intro hz
  rw [hz, zero_mul] at hp
  exact one_ne_zero hp

end MasulloGRH

namespace Round166F
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable def classLog : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (fun y => Real.log (genuineIdeleModulus K y)) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    change Real.log (genuineIdeleModulus K x) = Real.log (genuineIdeleModulus K y)
    rw [hy, genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul])

end Round166F
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)
instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩
end MasulloGRH

namespace MasulloGRH
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
abbrev FinitePrime := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
abbrev LocalField (v : FinitePrime K) := v.adicCompletion K
noncomputable def integralFiniteAdele (x : ∀ v : FinitePrime K, v.adicCompletionIntegers K) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun v : FinitePrime K => LocalField K v)
    (fun v => (v.adicCompletionIntegers K : Set (LocalField K v))) Filter.cofinite x

theorem integralFiniteSet_open : IsOpen
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} := by
  have hr : {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} =
      Set.range (integralFiniteAdele K) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact fun v => (x v).property
  rw [hr]
  exact (RestrictedProduct.isOpenEmbedding_structureMap (fun v =>
    (Valued.isClopen_closedBall (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen)).isOpen_range

noncomputable def finiteNorm (a : HeckeIdeles K) : ℝ :=
  ∏ᶠ v : NumberField.FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem finiteNorm_mul (a b : HeckeIdeles K) :
    finiteNorm K (a*b) = finiteNorm K a * finiteNorm K b := by
  unfold finiteNorm
  have h (v : NumberField.FinitePlace K) :
      ‖(a*b).val.2 v.maximalIdeal‖ = ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ :=
    norm_mul _ _
  simp_rw [h]
  exact finprod_mul_distrib (genuineIdele_finite_norm_support K a)
    (genuineIdele_finite_norm_support K b)

theorem finiteNorm_one_of_integral (a : HeckeIdeles K)
    (ha : ∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1)
    (hi : ∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1) :
    finiteNorm K a = 1 := by
  have hn (v : FinitePrime K) : ‖a.val.2 v‖ = 1 := by
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm (ha v)
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right (hi v) _
        _ = _ := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  simp [finiteNorm, hn]

theorem finiteNorm_continuous : Continuous (finiteNorm K) := by
  let U : Set (HeckeIdeles K) := {a | (∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1) ∧
    (∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1)}
  have ho : IsOpen U := (integralFiniteSet_open K).preimage
    (continuous_snd.comp Units.continuous_val) |>.inter
      ((integralFiniteSet_open K).preimage (continuous_snd.comp Units.continuous_coe_inv))
  have h1 : (1 : HeckeIdeles K) ∈ U := by
    constructor <;> intro v <;> change Valued.v (1 : LocalField K v) ≤ 1 <;> simp
  rw [continuous_iff_continuousAt]
  intro a
  have hV : ∀ᶠ b in 𝓝 a, a⁻¹*b ∈ U :=
    ((ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1))
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [hV] with b hb
  have h := finiteNorm_one_of_integral K (a⁻¹*b) hb.1 hb.2
  have he := finiteNorm_mul K a (a⁻¹*b)
  simpa [h, mul_assoc] using he

theorem genuineIdeleModulus_continuous : Continuous (genuineIdeleModulus K) := by
  have h : Continuous (fun a : HeckeIdeles K =>
      ∏ w : NumberField.InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) := by fun_prop
  exact h.mul (finiteNorm_continuous K)

end MasulloGRH

namespace Round175B
open MasulloGRH Round166F MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Arithmetic logarithm on the actual idele-class quotient. -/
theorem classLog_mul (g x : HeckeIdeleClasses K) :
    classLog K (g * x) = classLog K g + classLog K x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  change Real.log (genuineIdeleModulus K (a*b)) = _
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b)]
  rfl

theorem classLog_continuous : Continuous (classLog K) :=
  ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K)).quotient_lift _


end Round175B
end

namespace SpectralRound7B
open MeasureTheory SpectralRound5B SpectralRound6B
attribute [local instance] Classical.propDecidable

/-- Discharges the radial Haar pushforward premise once the genuine class
splitting and its product Haar normalization have been established. -/
theorem log_pushforward_of_split
    {X C : Type*} [MeasurableSpace X] [MeasurableSpace C]
    (mu : Measure X) (nu : Measure C) (e : X ≃ᵐ C × ℝ)
    (ell : X → ℝ) (hcoord : ∀ x, (e x).2 = ell x)
    (hsplit : Measure.map e mu = nu.prod volume) :
    Measure.map ell mu = nu Set.univ • volume := by
  calc
    Measure.map ell mu = Measure.map (Prod.snd ∘ e) mu := by
      congr 1
      funext x
      exact (hcoord x).symm
    _ = Measure.map Prod.snd (Measure.map e mu) :=
      (Measure.map_map measurable_snd e.measurable).symm
    _ = nu Set.univ • volume := by rw [hsplit, Measure.map_snd_prod]

/-- CONDITIONAL genuine-class interior membership. The arithmetic log is
exactly the descended product of all local absolute values. This removes
an assumed radial pushforward in favor of an explicit finite-mass splitting.
It does not construct the splitting or the native dual identification. -/
theorem genuine_interior_jet_memLp_of_split
    (K : Type*) [Field K] [NumberField K]
    {C : Type*} [MeasurableSpace C] (nu : Measure C)
    (hnu0 : nu Set.univ ≠ 0) (hnuf : nu Set.univ ≠ ⊤)
    (mu : Measure (MasulloGRH.HeckeIdeleClasses K))
    (e : MasulloGRH.HeckeIdeleClasses K ≃ᵐ C × ℝ)
    (hcoord : ∀ x, (e x).2 = Round166F.classLog K x)
    (hsplit : Measure.map e mu = nu.prod volume)
    (phase : MasulloGRH.HeckeIdeleClasses K → Circle)
    (hphase : Measurable (fun x => (phase x : ℂ)))
    (m : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (hb : |beta| < alpha) :
    MemLp (weightedMellinJet (Round166F.classLog K) phase m s alpha beta) 2 mu := by
  exact interior_weightedMellinJet_memLp mu (Round166F.classLog K) phase
    (Round175B.classLog_continuous K).measurable hphase
    (nu Set.univ) hnu0 hnuf
    (log_pushforward_of_split mu nu e (Round166F.classLog K) hcoord hsplit)
    m s alpha beta hs hb

/-- CONDITIONAL genuine-class sharp boundary multiplicity. N remains an
independently supplied natural number, to be attached to genuine zero order.
Discharges only the finite continuous-order count in (10.2.2.5). -/
theorem genuine_boundary_orders_of_split
    (K : Type*) [Field K] [NumberField K]
    {C : Type*} [MeasurableSpace C] (nu : Measure C)
    (hnu0 : nu Set.univ ≠ 0) (hnuf : nu Set.univ ≠ ⊤)
    (mu : Measure (MasulloGRH.HeckeIdeleClasses K))
    (e : MasulloGRH.HeckeIdeleClasses K ≃ᵐ C × ℝ)
    (hcoord : ∀ x, (e x).2 = Round166F.classLog K x)
    (hsplit : Measure.map e mu = nu.prod volume)
    (phase : MasulloGRH.HeckeIdeleClasses K → Circle)
    (hphase : Measurable (fun x => (phase x : ℂ)))
    (N : ℕ) (s alpha beta : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |beta| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (weightedMellinJet (Round166F.classLog K) phase m s alpha beta) 2 mu) =
      Finset.range (min N (Nat.ceil ((s - 1) / 2))) := by
  classical
  exact boundary_weightedMellinJet_orders mu (Round166F.classLog K) phase
    (Round175B.classLog_continuous K).measurable hphase
    (nu Set.univ) hnu0 hnuf
    (log_pushforward_of_split mu nu e (Round166F.classLog K) hcoord hsplit)
    N s alpha beta hs ha hb

#print axioms log_pushforward_of_split
#print axioms genuine_interior_jet_memLp_of_split
#print axioms genuine_boundary_orders_of_split
end SpectralRound7B

namespace Round175B
/-- Exact native squared weight retained from checked nuclear B177. -/
noncomputable def nativeWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (2 * alpha * |t|) * (1 + t^2) ^ (s/2)
end Round175B

namespace SpectralRound7B
open SpectralRound3B SpectralRound5B
/-- Discharges the pointwise native dual-density normalization premise on
actual idele classes. The isometric weighted-dual realization and quotient
annihilator identification do not follow from this identity alone. -/
theorem genuine_jet_sq_eq_nativeDualDensity
    (K : Type*) [Field K] [NumberField K]
    (phase : MasulloGRH.HeckeIdeleClasses K → Circle)
    (m : ℕ) (s alpha beta : ℝ) (x : MasulloGRH.HeckeIdeleClasses K) :
    ‖weightedMellinJet (Round166F.classLog K) phase m s alpha beta x‖ ^ 2 =
      (Real.exp (2 * beta * Round166F.classLog K x) *
        (Round166F.classLog K x) ^ (2 * m)) /
      Round175B.nativeWeight alpha s (Round166F.classLog K x) := by
  let t := Round166F.classLog K x
  have hw : 0 < Round175B.nativeWeight alpha s t := by
    unfold Round175B.nativeWeight
    positivity
  apply (eq_div_iff (ne_of_gt hw)).mpr
  rw [weightedMellinJet_sq_norm]
  change (Real.exp (2 * beta * t - 2 * alpha * |t|) * radialJetDensity m s t) *
    Round175B.nativeWeight alpha s t = _
  have hp : (1 + t^2)^(-s/2) * (1 + t^2)^(s/2) = 1 := by
    rw [← Real.rpow_add (by positivity : 0 < 1 + t^2)]
    convert Real.rpow_zero (1 + t^2) using 1
    congr 1
    ring
  have he : Real.exp (2 * beta * t - 2 * alpha * |t|) *
      Real.exp (2 * alpha * |t|) = Real.exp (2 * beta * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold radialJetDensity Round175B.nativeWeight
  calc
    _ = (Real.exp (2 * beta * t - 2 * alpha * |t|) * Real.exp (2 * alpha * |t|)) *
      (t^(2*m) * ((1+t^2)^(-s/2) * (1+t^2)^(s/2))) := by ring
    _ = _ := by rw [hp, he, mul_one]

#print axioms genuine_jet_sq_eq_nativeDualDensity
end SpectralRound7B

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- Exact character structure from the checked finite-idelic foundation. -/
structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

/-- Descend the actual character; no spectrum or zero set is prescribed. -/
noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K → Circle :=
  Quotient.lift χ.character (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, map_mul, χ.trivial_on_principal, one_mul])

theorem classCharacter_continuous (χ : UnitaryHeckeCharacter K) :
    Continuous (classCharacter K χ) := χ.character.continuous.quotient_lift _

/-- Definition bridge to the same idelic character as the Euler germ. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (x : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk x) = χ.character x := rfl
end MasulloGRH

namespace SpectralRound9B
open MasulloGRH Round166F SpectralRound5B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine complex Mellin jet divided by the native square-root weight.
This is an explicit function on actual classes, not a spectral definition. -/
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)

/-- Discharges the actual character/complex-parameter attachment premise of
native jet integrability. The imaginary parameter is retained in the function. -/
theorem genuineNormalizedMellinJet_norm (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    ‖genuineNormalizedMellinJet K χ z a s alpha m x‖ =
      ‖weightedMellinJet (classLog K) (classCharacter K χ) m s alpha (z.re-a) x‖ := by
  simp only [genuineNormalizedMellinJet, weightedMellinJet, norm_mul,
    Circle.norm_coe, one_mul, Complex.norm_exp, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- CONDITIONAL sharp native boundary criterion for the genuine character and
complex Mellin parameter. Only the actual Haar pushforward is supplied; the
zero order and weighted-dual/common-kernel realization remain separate gaps. -/
theorem genuine_boundary_mellin_memLp_iff (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) :
    MemLp (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu ↔
      (2 : ℝ) * m + 1 < s := by
  have hchi : Measurable (fun x => (classCharacter K χ x : ℂ)) :=
    (continuous_subtype_val.comp (classCharacter_continuous K χ)).measurable
  have hell := (Round175B.classLog_continuous K).measurable
  have hg : Measurable (genuineNormalizedMellinJet K χ z a s alpha m) := by
    unfold genuineNormalizedMellinJet
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simp only [genuineNormalizedMellinJet_norm, weightedMellinJet_sq_norm]
  exact boundary_density_integrable_pullback_iff mu (classLog K) hell.aemeasurable
    c hc0 hct hmap m s alpha (z.re-a) hs ha hb

#print axioms MasulloGRH.classCharacter_mk
#print axioms MasulloGRH.classCharacter_continuous
#print axioms genuineNormalizedMellinJet_norm
#print axioms genuine_boundary_mellin_memLp_iff
end SpectralRound9B

namespace SpectralRound9B
open MasulloGRH Round166F SpectralRound5B SpectralRound6B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Interior counterpart for the genuine complex Mellin jet; discharges the
all-finite-orders membership premise of (10.2.2.6), conditionally on Haar transport. -/
theorem genuine_interior_mellin_memLp (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (hb : |z.re-a| < alpha) :
    MemLp (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu := by
  have hchi : Measurable (fun x => (classCharacter K χ x : ℂ)) :=
    (continuous_subtype_val.comp (classCharacter_continuous K χ)).measurable
  have hell := (Round175B.classLog_continuous K).measurable
  have hg : Measurable (genuineNormalizedMellinJet K χ z a s alpha m) := by
    unfold genuineNormalizedMellinJet
    fun_prop
  have hi := interior_weightedMellinJet_memLp mu (classLog K) (classCharacter K χ)
    hell hchi c hc0 hct hmap m s alpha (z.re-a) hs hb
  rw [memLp_two_iff_integrable_sq_norm
    (weightedMellinJet_measurable (classLog K) (classCharacter K χ) hell hchi
      m s alpha (z.re-a)).aestronglyMeasurable] at hi
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simpa only [genuineNormalizedMellinJet_norm] using hi

/-- Exact boundary truncation after actual-character attachment. N is still
an external finite order; identifying it with analytic Hecke multiplicity is OPEN. -/
theorem genuine_boundary_mellin_orders (χ : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (N : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) :
    (Finset.range N).filter (fun m => MemLp
      (genuineNormalizedMellinJet K χ z a s alpha m) 2 mu) =
      Finset.range (min N (Nat.ceil ((s-1)/2))) := by
  classical
  rw [← SpectralRound1B.boundaryJetOrders_all_real]
  ext m
  simp only [Finset.mem_filter, SpectralRound1B.boundaryJetOrders,
    genuine_boundary_mellin_memLp_iff K χ mu c hc0 hct hmap z a s alpha m hs ha hb]

#print axioms genuine_interior_mellin_memLp
#print axioms genuine_boundary_mellin_orders
end SpectralRound9B

namespace SpectralRound10B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped ComplexConjugate

/-- Discharges the Riesz-conjugation premise of the manuscript's BILINEAR
Mellin pairing after square-root-weight normalization. This is an L2 dual
construction, not a spectral operator or a replacement for the native quotient. -/
noncomputable def normalizedBilinearFunctional
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (g : X → ℂ) (hg : MemLp g 2 mu) : Lp ℂ 2 mu →L[ℂ] ℂ :=
  innerSL ℂ (hg.star.toLp (star g))

/-- Exact integral formula, with the conjugation cancelled. This closes the
bilinear-versus-Hermitian convention gap in the normalized ambient L2 space. -/
theorem normalizedBilinearFunctional_apply
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (g : X → ℂ) (hg : MemLp g 2 mu) (f : Lp ℂ 2 mu) :
    normalizedBilinearFunctional mu g hg f = ∫ x, g x * f x ∂mu := by
  change inner ℂ (hg.star.toLp (star g)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.star.coeFn_toLp] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- CONDITIONAL genuine boundary Mellin functional. The precise premise
discharged is existence of a continuous bilinear jet functional on normalized
ambient L2 for each admitted boundary order. Native weighted isometry and
annihilation of the actual closed theta image remain application obligations. -/
theorem genuine_boundary_continuous_pairing
    (K : Type*) [Field K] [NumberField K]
    (χ : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hb : |z.re-a| = alpha) (hm : (2 : ℝ) * m + 1 < s) :
    ∃ L : Lp ℂ 2 mu →L[ℂ] ℂ, ∀ f : Lp ℂ 2 mu,
      L f = ∫ x, genuineNormalizedMellinJet K χ z a s alpha m x * f x ∂mu := by
  have hg := (genuine_boundary_mellin_memLp_iff K χ mu c hc0 hct hmap
    z a s alpha m hs ha hb).mpr hm
  exact ⟨normalizedBilinearFunctional mu _ hg,
    normalizedBilinearFunctional_apply mu _ hg⟩

#print axioms normalizedBilinearFunctional_apply
#print axioms genuine_boundary_continuous_pairing
end SpectralRound10B

namespace SpectralRound11B
open MeasureTheory MasulloGRH Round166F SpectralRound9B

/-- The positive square-root multiplier for the manuscript's native weight.
Its square discharges the pointwise norm premise of the weighted L2 bridge. -/
noncomputable def nativeHalfWeight (alpha s t : ℝ) : ℝ :=
  Real.exp (alpha * |t|) * (1 + t^2) ^ (s/4)

theorem nativeHalfWeight_pos (alpha s t : ℝ) :
    0 < nativeHalfWeight alpha s t := by
  unfold nativeHalfWeight
  positivity

theorem nativeHalfWeight_sq (alpha s t : ℝ) :
    nativeHalfWeight alpha s t ^ 2 = Round175B.nativeWeight alpha s t := by
  have he : Real.exp (alpha * |t|) ^ 2 = Real.exp (2 * alpha * |t|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hp : ((1+t^2)^(s/4))^2 = (1+t^2)^(s/2) := by
    rw [pow_two, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
    congr 1
    ring
  unfold nativeHalfWeight Round175B.nativeWeight
  rw [mul_pow, he, hp]

/-- Actual unnormalized Mellin jet from (10.2.2.4), with z-a=b+it.
It is not asserted here that z is a zero of a Hecke L-function. -/
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

/-- Exact native numerator/denominator bridge, preserving the imaginary
Mellin parameter and actual character. Discharges the pairing's multiplier
cancellation premise; it does not establish density of the weighted completion. -/
theorem genuineMellinJet_normalization
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    genuineNormalizedMellinJet K chi z a s alpha m x *
      (nativeHalfWeight alpha s (classLog K x) : ℂ) =
      genuineMellinJet K chi z a m x := by
  let t := classLog K x
  have hp : (((1+t^2)^(-s/4) : ℝ) : ℂ) *
      (((1+t^2)^(s/4) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity : 0 < 1+t^2)]
    simp [show -s/4+s/4 = 0 by ring]
  have he : Complex.exp ((z - (a : ℂ)) * (t : ℂ) -
      ((alpha * |t| : ℝ) : ℂ)) * (Real.exp (alpha * |t|) : ℂ) =
      Complex.exp ((z - (a : ℂ)) * (t : ℂ)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, sub_add_cancel]
  simp only [Complex.ofReal_mul] at he
  simp only [genuineNormalizedMellinJet, nativeHalfWeight, genuineMellinJet,
    Complex.ofReal_mul]
  change ((classCharacter K chi x : ℂ) *
      Complex.exp ((z-(a:ℂ))*(t:ℂ)-((alpha:ℂ)*((|t|:ℝ):ℂ))) *
      (((t^m:ℝ):ℂ) * (((1+t^2)^(-s/4):ℝ):ℂ))) *
      ((Real.exp (alpha*|t|):ℂ) * (((1+t^2)^(s/4):ℝ):ℂ)) = _
  calc
    _ = ((classCharacter K chi x : ℂ) *
      (Complex.exp ((z-(a:ℂ))*(t:ℂ)-((alpha:ℂ)*((|t|:ℝ):ℂ))) *
        (Real.exp (alpha*|t|):ℂ)) * ((t^m:ℝ):ℂ)) *
      ((((1+t^2)^(-s/4):ℝ):ℂ) * (((1+t^2)^(s/4):ℝ):ℂ)) := by ring
    _ = _ := by rw [he, hp, mul_one]

#print axioms nativeHalfWeight_sq
#print axioms genuineMellinJet_normalization
end SpectralRound11B

namespace SpectralRound11B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound10B

/-- Discharges the function-level native weighted norm/membership premise.
This is the exact manuscript weight on actual classes, not a surrogate norm. -/
theorem native_normalization_memLp_iff
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ)
    (f : HeckeIdeleClasses K → ℂ) (hf : AEStronglyMeasurable f mu) :
    MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu ↔
      Integrable (fun x => Round175B.nativeWeight alpha s (classLog K x) *
        ‖f x‖^2) mu := by
  have hell := (Round175B.classLog_continuous K).measurable
  have hw : Measurable (fun x : HeckeIdeleClasses K =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ)) := by
    unfold nativeHalfWeight
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) mu :=
    hw.aestronglyMeasurable.mul hf
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have he (x : HeckeIdeleClasses K) :
      ‖(nativeHalfWeight alpha s (classLog K x) : ℂ) * f x‖^2 =
      Round175B.nativeWeight alpha s (classLog K x) * ‖f x‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (nativeHalfWeight_pos alpha s (classLog K x)), nativeHalfWeight_sq]
  simp only [he]

/-- The normalized continuous functional evaluates to the ACTUAL unnormalized
Mellin pairing on every function of finite native weighted norm. This closes
its integral formula; the quotient's theta annihilation is still unresolved. -/
theorem native_pairing_formula
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    normalizedBilinearFunctional mu _ hg (hF.toLp _) =
      ∫ x, genuineMellinJet K chi z a m x * f x ∂mu := by
  rw [normalizedBilinearFunctional_apply]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx, ← mul_assoc, genuineMellinJet_normalization]

#print axioms native_normalization_memLp_iff
#print axioms native_pairing_formula
end SpectralRound11B

namespace SpectralRound12B
open MeasureTheory MasulloGRH Round166F SpectralRound9B SpectralRound10B SpectralRound11B

/-- Discharges surjectivity at the function-representative level of the native
weighted-space normalization required for the actual spectral dual. Density
of the manuscript test completion and theta-quotient descent remain OPEN. -/
theorem native_normalization_surjective
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K)) (alpha s : ℝ) (F : Lp ℂ 2 mu) :
    ∃ f : HeckeIdeleClasses K → ℂ, AEStronglyMeasurable f mu ∧
      Integrable (fun x => Round175B.nativeWeight alpha s (classLog K x) * ‖f x‖^2) mu ∧
      ∀ x, (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x = F x := by
  let w : HeckeIdeleClasses K → ℂ :=
    fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ)
  have hell := (Round175B.classLog_continuous K).measurable
  have hw : Measurable w := by
    dsimp [w, nativeHalfWeight]
    fun_prop
  have hn (x) : w x ≠ 0 := by
    dsimp [w]
    exact_mod_cast (ne_of_gt (nativeHalfWeight_pos alpha s (classLog K x)))
  let f : HeckeIdeleClasses K → ℂ := fun x => (w x)⁻¹ * F x
  have hf : AEStronglyMeasurable f mu :=
    hw.inv.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
  have he : (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) =
      (F : HeckeIdeleClasses K → ℂ) := by
    funext x
    change w x * ((w x)⁻¹ * F x) = F x
    rw [← mul_assoc, mul_inv_cancel₀ (hn x), one_mul]
  have hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu := by
    rw [he]
    exact Lp.memLp F
  exact ⟨f, hf, (native_normalization_memLp_iff K mu alpha s f hf).mp hF,
    fun x => congrFun he x⟩

/-- Discharges absolute integrability of each actual Mellin pairing, before
any infinite trace or zero-series interchange can be considered. The supplied
jet membership is established for admitted orders by the prior sharp criteria. -/
theorem native_pairing_integrable
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu) :
    Integrable (fun x => genuineMellinJet K chi z a m x * f x) mu := by
  have hi := hg.integrable_mul hF
  change Integrable (fun x => genuineNormalizedMellinJet K chi z a s alpha m x *
    ((nativeHalfWeight alpha s (classLog K x) : ℂ) * f x)) mu at hi
  have he : (fun x => genuineNormalizedMellinJet K chi z a s alpha m x *
      ((nativeHalfWeight alpha s (classLog K x) : ℂ) * f x)) =
      (fun x => genuineMellinJet K chi z a m x * f x) := by
    funext x
    rw [← mul_assoc, genuineMellinJet_normalization]
  rwa [he] at hi

#print axioms native_normalization_surjective
#print axioms native_pairing_integrable
end SpectralRound12B

namespace FollowupA633
open MeasureTheory Filter Topology MasulloGRH Round166F SpectralRound9B SpectralRound11B SpectralRound12B
theorem genuineMellinJet_hasDerivAt
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) (z : ℂ) :
    HasDerivAt (fun w : ℂ => genuineMellinJet K chi w a m x)
      (genuineMellinJet K chi z a (m+1) x) z := by
  have he := (((hasDerivAt_id z).sub_const (a : ℂ)).mul_const
    (classLog K x : ℂ)).cexp
  have hh := (he.const_mul (classCharacter K chi x : ℂ)).mul_const
    ((classLog K x ^ m : ℝ) : ℂ)
  convert hh using 1
  simp only [genuineMellinJet, one_mul, Complex.ofReal_pow, pow_succ, Complex.ofReal_mul, id_eq]
  ring


/-- Uniform domination by the two actual endpoint jets, with no compact support. -/
theorem native_jet_strip_bound
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z w : ℂ) (a d : ℝ) (m : ℕ) (x : HeckeIdeleClasses K)
    (hw : ‖w-z‖ ≤ d) :
    ‖genuineMellinJet K chi w a m x‖ ≤
      ‖genuineMellinJet K chi (z+(d:ℂ)) a m x‖ +
      ‖genuineMellinJet K chi (z-(d:ℂ)) a m x‖ := by
  have hn (v : ℂ) : ‖genuineMellinJet K chi v a m x‖ =
      Real.exp ((v.re-a)*classLog K x) * |classLog K x|^m := by
    simp [genuineMellinJet, Complex.norm_exp, Complex.mul_re,
      Complex.sub_re, norm_pow, Real.norm_eq_abs]
  have hr : |w.re-z.re| ≤ d := by
    exact le_trans (by simpa using Complex.abs_re_le_norm (w-z)) hw
  simp only [hn]
  by_cases ht : 0 ≤ classLog K x
  · apply le_trans ?_ (le_add_of_nonneg_right (by positivity))
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (pow_nonneg (abs_nonneg _) _)
    simp only [Complex.add_re, Complex.ofReal_re]
    exact mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp hr).2]) ht
  · apply le_trans ?_ (le_add_of_nonneg_left (by positivity))
    apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (pow_nonneg (abs_nonneg _) _)
    simp only [Complex.sub_re, Complex.ofReal_re]
    exact mul_le_mul_of_nonpos_right (by linarith [(abs_le.mp hr).1]) (le_of_not_ge ht)

/-- Actual same-Haar differentiation on the original weighted space in the
strict interior. The pointwise derivative is reused from followup_E; domination
and integrability are derived from native admission, not hypothesized. -/
theorem native_weighted_hasDerivAt
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (a s alpha : ℝ) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (m : ℕ) (z : ℂ) (hz : |z.re-a| < alpha) :
    HasDerivAt (fun w : ℂ => ∫ x, genuineMellinJet K chi w a m x * f x ∂mu)
      (∫ x, genuineMellinJet K chi z a (m+1) x * f x ∂mu) z := by
  let d : ℝ := (alpha - |z.re-a|)/2
  have hd : 0 < d := by dsimp [d]; linarith
  have hadm (w : ℂ) (hw : ‖w-z‖ ≤ d) : |w.re-a| < alpha := by
    calc
      |w.re-a| = |(w-z).re+(z.re-a)| := by congr 1; simp
      _ ≤ |(w-z).re|+|z.re-a| := abs_add_le _ _
      _ ≤ ‖w-z‖+|z.re-a| := add_le_add (Complex.abs_re_le_norm _) le_rfl
      _ < alpha := by dsimp [d] at hw; linarith
  have hint (w : ℂ) (hw : |w.re-a| < alpha) (n : ℕ) :
      Integrable (fun x => genuineMellinJet K chi w a n x * f x) mu :=
    native_pairing_integrable K chi mu w a s alpha n
      (genuine_interior_mellin_memLp K chi mu c hc0 hct hmap w a s alpha n hs hw) f hF
  have hp := hint (z+(d:ℂ)) (hadm _ (by simp [abs_of_pos hd])) (m+1)
  have hm := hint (z-(d:ℂ)) (hadm _ (by simp [sub_eq_add_neg, add_assoc, abs_of_pos hd])) (m+1)
  have hmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun x => genuineMellinJet K chi w a m x * f x) mu := by
    filter_upwards [Metric.ball_mem_nhds z hd] with w hw
    exact (hint w (hadm w (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw))) m).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z d)
    (F' := fun w x => genuineMellinJet K chi w a (m+1) x * f x)
    (bound := fun x => ‖genuineMellinJet K chi (z+(d:ℂ)) a (m+1) x * f x‖ +
      ‖genuineMellinJet K chi (z-(d:ℂ)) a (m+1) x * f x‖)
    (Metric.ball_mem_nhds z hd) hmeas (hint z hz m) (hint z hz (m+1)).aestronglyMeasurable
    (ae_of_all _ (fun x w hw => ?_)) (hp.norm.add hm.norm)
    (ae_of_all _ (fun x w _ => (genuineMellinJet_hasDerivAt K chi a m x w).mul_const (f x)))).2
  simp only [norm_mul, ← add_mul]
  exact mul_le_mul_of_nonneg_right
    (native_jet_strip_bound K chi z w a d (m+1) x
      (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hw))) (norm_nonneg _)

#print axioms native_jet_strip_bound
#print axioms native_weighted_hasDerivAt

/-- Removes the actual iterated-differentiation premise on the strict interior
of the original weighted space, without a compact-support hypothesis. -/
theorem native_weighted_iteratedDeriv
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (a s alpha : ℝ) (hs : 0 ≤ s)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (m : ℕ) (z : ℂ) (hz : |z.re-a| < alpha) :
    iteratedDeriv m (fun w : ℂ => ∫ x, genuineMellinJet K chi w a 0 x * f x ∂mu) z =
      ∫ x, genuineMellinJet K chi z a m x * f x ∂mu := by
  induction m generalizing z with
  | zero => rfl
  | succ m ih =>
    have hopen : IsOpen {w : ℂ | |w.re-a| < alpha} :=
      isOpen_lt (Complex.continuous_re.sub continuous_const).abs continuous_const
    have he : (fun w => iteratedDeriv m
        (fun v : ℂ => ∫ x, genuineMellinJet K chi v a 0 x * f x ∂mu) w) =ᶠ[𝓝 z]
        (fun w => ∫ x, genuineMellinJet K chi w a m x * f x ∂mu) := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      exact ih w hw
    rw [iteratedDeriv_succ]
    exact he.deriv_eq.trans (native_weighted_hasDerivAt K chi mu c hc0 hct hmap
      a s alpha hs f hF m z hz).deriv

#print axioms native_weighted_iteratedDeriv

end FollowupA633



open Filter Topology

namespace DenseS0

variable {E : Type*} [AddCommGroup E] [Module ℂ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

/-- Retains both defining constraints of the original Schwartz test space. -/
noncomputable def correction (a b : E →L[ℂ] ℂ) (u v : E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - a.smulRight u - b.smulRight v

theorem correction_apply (a b : E →L[ℂ] ℂ) (u v x : E) :
    correction a b u v x = x - a x • u - b x • v := rfl

theorem correction_constraints (a b : E →L[ℂ] ℂ) (u v x : E)
    (hau : a u = 1) (hav : a v = 0) (hbu : b u = 0) (hbv : b v = 1) :
    a (correction a b u v x) = 0 ∧ b (correction a b u v x) = 0 := by
  simp [correction_apply, map_sub, map_smul, hau, hav, hbu, hbv]

theorem correction_fixed (a b : E →L[ℂ] ℂ) (u v x : E)
    (ha : a x = 0) (hb : b x = 0) : correction a b u v x = x := by
  simp [correction_apply, ha, hb]

theorem correction_preserves_algebraic_tests (a b : E →L[ℂ] ℂ)
    (D : Submodule ℂ E) (u v : E) (hu : u ∈ D) (hv : v ∈ D)
    {x : E} (hx : x ∈ D) : correction a b u v x ∈ D := by
  exact D.sub_mem (D.sub_mem hx (D.smul_mem _ hu)) (D.smul_mem _ hv)

/-- Given an actual convergent factorized approximation, correction preserves
its limit and both constraints. No density or Tate division is postulated here. -/
theorem corrected_approximation (a b : E →L[ℂ] ℂ) (u v f : E)
    (ha : a f = 0) (hb : b f = 0)
    (q : ℕ → E) (hq : Tendsto q atTop (𝓝 f)) :
    Tendsto (fun n => correction a b u v (q n)) atTop (𝓝 f) := by
  have h := ((correction a b u v).continuous.tendsto f).comp hq
  simpa only [correction_fixed a b u v f ha hb] using h

/-- Native continuous pairings pass to the corrected limit. Instantiation
requires the original theta pairing, rather than redefining its kernel. -/
theorem annihilates_limit {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : F →L[ℂ] ℂ) (q : ℕ → F) (f : F)
    (hq : Tendsto q atTop (𝓝 f)) (hz : ∀ n, J (q n) = 0) : J f = 0 := by
  have h := (J.continuous.tendsto f).comp hq
  have hzero : Tendsto (fun n => J (q n)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique h hzero

#print axioms correction_constraints
#print axioms correction_preserves_algebraic_tests
#print axioms corrected_approximation
#print axioms annihilates_limit

/-- Density survives intersection with both original evaluation kernels. -/
theorem dense_original_kernel (a b : E →L[ℂ] ℂ) (u v : E)
    (D : Submodule ℂ E) (hD : Dense (D : Set E))
    (hu : u ∈ D) (hv : v ∈ D)
    (hau : a u = 1) (hav : a v = 0) (hbu : b u = 0) (hbv : b v = 1)
    (f : E) (ha : a f = 0) (hb : b f = 0) :
    f ∈ closure {x : E | x ∈ D ∧ a x = 0 ∧ b x = 0} := by
  have h := map_mem_closure (correction a b u v).continuous (hD f)
    (show Set.MapsTo (correction a b u v) (D : Set E)
      {x : E | x ∈ D ∧ a x = 0 ∧ b x = 0} from fun x hx =>
      ⟨correction_preserves_algebraic_tests a b D u v hu hv hx,
        correction_constraints a b u v x hau hav hbu hbv⟩)
  simpa only [correction_fixed a b u v f ha hb] using h

/-- Theta is defined only on the genuine simultaneous kernel. The theorem
requires its actual continuity and dense-test Tate vanishing explicitly. -/
theorem native_pairing_vanishes_on_original_tests
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (a b : E →L[ℂ] ℂ) (u v : E)
    (D : Submodule ℂ E) (hD : Dense (D : Set E))
    (hu : u ∈ D) (hv : v ∈ D)
    (hau : a u = 1) (hav : a v = 0) (hbu : b u = 0) (hbv : b v = 1)
    (theta : (a.ker ⊓ b.ker : Submodule ℂ E) → F) (htheta : Continuous theta)
    (J : F →L[ℂ] ℂ)
    (hzero : ∀ x : (a.ker ⊓ b.ker : Submodule ℂ E), (x : E) ∈ D → J (theta x) = 0)
    (f : (a.ker ⊓ b.ker : Submodule ℂ E)) : J (theta f) = 0 := by
  let q : E → (a.ker ⊓ b.ker : Submodule ℂ E) := fun x =>
    ⟨correction a b u v x, correction_constraints a b u v x hau hav hbu hbv⟩
  have hq : Continuous q := (correction a b u v).continuous.subtype_mk _
  have hc : IsClosed {x : E | J (theta (q x)) = 0} :=
    isClosed_eq (J.continuous.comp (htheta.comp hq)) continuous_const
  have hs : (D : Set E) ⊆ {x : E | J (theta (q x)) = 0} := by
    intro x hx
    exact hzero (q x) (correction_preserves_algebraic_tests a b D u v hu hv hx)
  have hz := closure_minimal hs hc (hD (f : E))
  have he : q (f : E) = f := Subtype.ext
    (correction_fixed a b u v f f.property.1 f.property.2)
  change J (theta (q (f : E))) = 0 at hz
  rwa [he] at hz

#print axioms dense_original_kernel
#print axioms native_pairing_vanishes_on_original_tests
end DenseS0


namespace ActualJetConverse
open Filter Topology MeasureTheory MasulloGRH Round166F
open SpectralRound9B SpectralRound10B SpectralRound11B

theorem tate_product_derivative_zero (L D : ℂ → ℂ) (rho : ℂ) (N m : ℕ)
    (hL : AnalyticAt ℂ L rho) (hD : AnalyticAt ℂ D rho)
    (horder : ∀ k < N, iteratedDeriv k L rho = 0) (hm : m < N) :
    iteratedDeriv m (L * D) rho = 0 := by
  rw [iteratedDeriv_mul hL.contDiffAt hD.contDiffAt]
  apply Finset.sum_eq_zero
  intro k hk
  have hkN : k < N := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hm
  rw [horder k hkN, mul_zero, zero_mul]

/-- Joins Tate derivative vanishing to the actual, correctly normalized B12
native pairing. The displayed unfolding and local Tate inputs are obligations. -/
theorem actual_native_pairing_zero
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (rho : ℂ) (a s alpha : ℝ) (m N : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu)
    (f : HeckeIdeleClasses K → ℂ)
    (hF : MemLp (fun x => (nativeHalfWeight alpha s (classLog K x) : ℂ) * f x) 2 mu)
    (L D : ℂ → ℂ) (hL : AnalyticAt ℂ L rho) (hD : AnalyticAt ℂ D rho)
    (horder : ∀ k < N, iteratedDeriv k L rho = 0) (hm : m < N)
    (hunfold : (∫ x, genuineMellinJet K chi rho a m x * f x ∂mu) =
      iteratedDeriv m (L * D) rho) :
    normalizedBilinearFunctional mu _ hg (hF.toLp _) = 0 := by
  rw [native_pairing_formula K chi mu rho a s alpha m hg f hF, hunfold]
  exact tate_product_derivative_zero L D rho N m hL hD horder hm

/-- Conditional actual-native converse through the ORIGINAL simultaneous
kernel, retaining dense algebraic tests, the same measure, and B12's pairing.
Theta and its normalized representatives are inputs; they are not redefined. -/
theorem actual_native_jet_annihilates_original_theta_closure
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    (ev0 fourierEv0 : V →L[ℂ] ℂ) (u v : V)
    (Dtests : Submodule ℂ V) (hDense : Dense (Dtests : Set V))
    (hu : u ∈ Dtests) (hv : v ∈ Dtests)
    (heu : ev0 u = 1) (hev : ev0 v = 0)
    (hfu : fourierEv0 u = 0) (hfv : fourierEv0 v = 1)
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (rho : ℂ) (a s alpha : ℝ) (m N : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu)
    (theta : (ev0.ker ⊓ fourierEv0.ker : Submodule ℂ V) → Lp ℂ 2 mu)
    (htheta : Continuous theta)
    (seed : (ev0.ker ⊓ fourierEv0.ker : Submodule ℂ V) → HeckeIdeleClasses K → ℂ)
    (hseed : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * seed f x) 2 mu)
    (htheta_seed : ∀ f, theta f = (hseed f).toLp _)
    (L : ℂ → ℂ) (Q : (ev0.ker ⊓ fourierEv0.ker : Submodule ℂ V) → ℂ → ℂ)
    (hL : AnalyticAt ℂ L rho)
    (hQ : ∀ f : (ev0.ker ⊓ fourierEv0.ker : Submodule ℂ V), (f : V) ∈ Dtests → AnalyticAt ℂ (Q f) rho)
    (horder : ∀ k < N, iteratedDeriv k L rho = 0) (hm : m < N)
    (hunfold : ∀ f : (ev0.ker ⊓ fourierEv0.ker : Submodule ℂ V), (f : V) ∈ Dtests →
      (∫ x, genuineMellinJet K chi rho a m x * seed f x ∂mu) =
        iteratedDeriv m (L * Q f) rho) :
    closure (Set.range theta) ⊆
      {F | normalizedBilinearFunctional mu _ hg F = 0} := by
  let J := normalizedBilinearFunctional mu _ hg
  have hz : ∀ f, J (theta f) = 0 := by
    apply DenseS0.native_pairing_vanishes_on_original_tests ev0 fourierEv0 u v
      Dtests hDense hu hv heu hev hfu hfv theta htheta J
    intro f hf
    rw [htheta_seed f]
    exact actual_native_pairing_zero K chi mu rho a s alpha m N hg (seed f)
      (hseed f) L (Q f) hL (hQ f hf) horder hm (hunfold f hf)
  apply closure_minimal
  · rintro F ⟨f, rfl⟩
    exact hz f
  · exact isClosed_eq J.continuous continuous_const

#print axioms tate_product_derivative_zero
#print axioms actual_native_pairing_zero
#print axioms actual_native_jet_annihilates_original_theta_closure
end ActualJetConverse

namespace NativeTrueOrder
open Filter Topology MeasureTheory MasulloGRH Round166F
open SpectralRound9B SpectralRound10B SpectralRound11B

/-- Local scalar division, retaining true finite analytic order.
Adapted from conditional_A's TateDerivative scalar argument. -/
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

/-- Only continuity of the scalar pairing on S_0 is required. -/
theorem scalar_zero_on_original_S0
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    (d q : V →L[ℂ] ℂ) (u v : V) (D : Submodule ℂ V)
    (hD : Dense (D : Set V)) (hu : u ∈ D) (hv : v ∈ D)
    (hdu : d u = 1) (hdv : d v = 0) (hqu : q u = 0) (hqv : q v = 1)
    (P : (d.ker ⊓ q.ker : Submodule ℂ V) → ℂ) (hP : Continuous P)
    (hz : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D → P f = 0) :
    ∀ f, P f = 0 := by
  let R : V → (d.ker ⊓ q.ker : Submodule ℂ V) := fun x =>
    ⟨DenseS0.correction d q u v x,
      DenseS0.correction_constraints d q u v x hdu hdv hqu hqv⟩
  have hR : Continuous R := (DenseS0.correction d q u v).continuous.subtype_mk _
  have hs : (D : Set V) ⊆ {x | P (R x) = 0} := by
    intro x hx
    exact hz (R x) (DenseS0.correction_preserves_algebraic_tests d q D u v hu hv hx)
  intro f
  have hf := closure_minimal hs (isClosed_eq (hP.comp hR) continuous_const) (hD (f : V))
  have he : R (f : V) = f := Subtype.ext
    (DenseS0.correction_fixed d q u v f f.property.1 f.property.2)
  simpa only [Set.mem_setOf_eq, he] using hf

/-- Actual B12 character, Haar, weight and normalized Mellin integral.
Sharp admission and true order replace free membership/vanishing assumptions.
The ORIGINAL theta map is a parameter on S_0; scalar Tate division, unfolding,
and scalar continuity are explicit analytic obligations. -/
theorem admitted_true_order_native_converse
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (rho : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadmit : |rho.re-a| < alpha ∨ (|rho.re-a| = alpha ∧ (2 : ℝ)*m+1 < s))
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    (d q : V →L[ℂ] ℂ) (u v : V) (D : Submodule ℂ V)
    (hD : Dense (D : Set V)) (hu : u ∈ D) (hv : v ∈ D)
    (hdu : d u = 1) (hdv : d v = 0) (hqu : q u = 0) (hqv : q v = 1)
    (theta : (d.ker ⊓ q.ker : Submodule ℂ V) → Lp ℂ 2 mu)
    (Phi : (d.ker ⊓ q.ker : Submodule ℂ V) → HeckeIdeleClasses K → ℂ)
    (hPhi : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * Phi f x) 2 mu)
    (hnorm : ∀ f, theta f = (hPhi f).toLp _)
    (hpair : Continuous (fun f => ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu))
    (L : ℂ → ℂ)
    (Q Z : (d.ker ⊓ q.ker : Submodule ℂ V) → ℂ → ℂ)
    (hL : AnalyticAt ℂ L rho) (hfinite : analyticOrderAt L rho ≠ ⊤)
    (hm : m < analyticOrderNatAt L rho)
    (hQ : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D → AnalyticAt ℂ (Q f) rho)
    (hdiv : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      Z f =ᶠ[𝓝 rho] (fun z => L z * Q f z))
    (hunfold : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      (∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) = iteratedDeriv m (Z f) rho) :
    ∃ hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu,
      (∀ f, normalizedBilinearFunctional mu _ hg (theta f) =
        ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) ∧
      (∀ F ∈ closure (Submodule.span ℂ (Set.range theta) : Set (Lp ℂ 2 mu)),
        normalizedBilinearFunctional mu _ hg F = 0) := by
  have hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu := by
    rcases hadmit with hi | ⟨hb, hm⟩
    · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap rho a s alpha m hs hi
    · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap
        rho a s alpha m hs ha hb).mpr hm
  let J := normalizedBilinearFunctional mu _ hg
  have hp (f) : J (theta f) = ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu := by
    rw [hnorm]
    exact native_pairing_formula K chi mu rho a s alpha m hg (Phi f) (hPhi f)
  have hz : ∀ f, J (theta f) = 0 := by
    apply scalar_zero_on_original_S0 d q u v D hD hu hv hdu hdv hqu hqv
      (fun f => J (theta f))
    · simpa only [hp] using hpair
    · intro f hf
      rw [hp, hunfold f hf]
      exact local_tate_derivative_zero L (Q f) (Z f) rho m hL (hQ f hf)
        hfinite hm (hdiv f hf)
  refine ⟨hg, hp, ?_⟩
  have hr : Set.range theta ⊆ (J.ker : Set (Lp ℂ 2 mu)) := by
    rintro F ⟨f, rfl⟩
    exact hz f
  have hspan : (Submodule.span ℂ (Set.range theta) : Set (Lp ℂ 2 mu)) ⊆
      (J.ker : Set (Lp ℂ 2 mu)) := Submodule.span_le.mpr hr
  exact fun F hF => closure_minimal hspan (isClosed_eq J.continuous continuous_const) hF

#print axioms local_tate_derivative_zero
#print axioms scalar_zero_on_original_S0
#print axioms admitted_true_order_native_converse
end NativeTrueOrder

namespace NativeTrueOrder
open Filter Topology MeasureTheory MasulloGRH Round166F
open SpectralRound9B SpectralRound10B SpectralRound11B

/-- The scalar transform is fixed to the SAME native Haar integral. -/
noncomputable def nativeMellinTransform
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (a : ℝ)
    (Phi : HeckeIdeleClasses K → ℂ) (z : ℂ) : ℂ :=
  ∫ x, genuineMellinJet K chi z a 0 x * Phi x ∂mu

/-- Actual B12 kernel and Riesz slot. Integrated from conditional_A and
followup_F; direct unfolding avoids the unavailable mem_orthogonal.mpr API. -/
theorem native_riesz_orthogonal
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (rho : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu)
    (G : Submodule ℂ (Lp ℂ 2 mu))
    (hann : ∀ F ∈ G, normalizedBilinearFunctional mu _ hg F = 0) :
    hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m)) ∈
      G.orthogonal := by
  change ∀ F ∈ G, inner ℂ F
    (hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m))) = 0
  intro F hF
  have h := hann F hF
  change inner ℂ (hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m))) F = 0 at h
  exact inner_eq_zero_symm.mp h

/-- Strict native admission, genuine finite analytic order, dense original S0,
the SAME scalar integral, and the correctly conjugated Riesz vector are joined.
Only scalar pairing continuity is used. L must still be attached to the actual
completed Hecke function; local Tate division and BOUNDARY differentiation remain explicit premises.
Interior differentiation is now derived from the original native weight. -/
theorem admitted_same_integral_riesz_converse
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (rho : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadmit : |rho.re-a| < alpha ∨ (|rho.re-a| = alpha ∧ (2 : ℝ)*m+1 < s))
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    (d q : V →L[ℂ] ℂ) (u v : V) (D : Submodule ℂ V)
    (hD : Dense (D : Set V)) (hu : u ∈ D) (hv : v ∈ D)
    (hdu : d u = 1) (hdv : d v = 0) (hqu : q u = 0) (hqv : q v = 1)
    (theta : (d.ker ⊓ q.ker : Submodule ℂ V) → Lp ℂ 2 mu)
    (Phi : (d.ker ⊓ q.ker : Submodule ℂ V) → HeckeIdeleClasses K → ℂ)
    (hPhi : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * Phi f x) 2 mu)
    (hnorm : ∀ f, theta f = (hPhi f).toLp _)
    (hpair : Continuous (fun f => ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu))
    (L : ℂ → ℂ)
    (Q : (d.ker ⊓ q.ker : Submodule ℂ V) → ℂ → ℂ)
    (hL : AnalyticAt ℂ L rho) (hfinite : analyticOrderAt L rho ≠ ⊤)
    (hm : m < analyticOrderNatAt L rho)
    (hQ : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D → AnalyticAt ℂ (Q f) rho)
    (hdiv : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      nativeMellinTransform K chi mu a (Phi f) =ᶠ[𝓝 rho] (fun z => L z * Q f z))
    (hboundaryDeriv : |rho.re-a| = alpha → ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      (∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) = iteratedDeriv m (nativeMellinTransform K chi mu a (Phi f)) rho) :
    ∃ hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu,
      (∀ f, normalizedBilinearFunctional mu _ hg (theta f) =
        ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) ∧
      hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m)) ∈
        (Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal := by
  have hunfold : ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      (∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) =
        iteratedDeriv m (nativeMellinTransform K chi mu a (Phi f)) rho := by
    intro f hf
    rcases hadmit with hi | ⟨hb, _⟩
    · exact (FollowupA633.native_weighted_iteratedDeriv K chi mu c hc0 hct hmap
        a s alpha hs (Phi f) (hPhi f) m rho hi).symm
    · exact hboundaryDeriv hb f hf
  obtain ⟨hg, hp, hann⟩ := admitted_true_order_native_converse K chi mu c hc0 hct hmap
    rho a s alpha m hs ha hadmit d q u v D hD hu hv hdu hdv hqu hqv
    theta Phi hPhi hnorm hpair L Q
    (fun f => nativeMellinTransform K chi mu a (Phi f))
    hL hfinite hm hQ hdiv hunfold
  refine ⟨hg, hp, ?_⟩
  apply native_riesz_orthogonal K chi mu rho a s alpha m hg
  intro F hF
  exact hann F hF

#print axioms native_riesz_orthogonal
#print axioms admitted_same_integral_riesz_converse
end NativeTrueOrder

namespace NativeTrueOrder
open Filter Topology MeasureTheory MasulloGRH Round166F
open SpectralRound9B SpectralRound10B SpectralRound11B

/-- The actual SAME-Haar native Mellin-jet integral is continuous on the
original test space whenever its normalized theta representative is continuous.
This discharges scalar continuity, retaining theta continuity as an obligation. -/
theorem continuous_native_jet_pairing
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (rho : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu)
    {T : Type*} [TopologicalSpace T]
    (theta : T → Lp ℂ 2 mu) (htheta : Continuous theta)
    (Phi : T → HeckeIdeleClasses K → ℂ)
    (hPhi : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * Phi f x) 2 mu)
    (hnorm : ∀ f, theta f = (hPhi f).toLp _) :
    Continuous (fun f => ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) := by
  have he : (fun f => ∫ x, genuineMellinJet K chi rho a m x * Phi f x ∂mu) =
      (fun f => normalizedBilinearFunctional mu _ hg (theta f)) := by
    funext f
    rw [hnorm f]
    exact (native_pairing_formula K chi mu rho a s alpha m hg (Phi f) (hPhi f)).symm
  rw [he]
  exact (normalizedBilinearFunctional mu _ hg).continuous.comp htheta

#print axioms continuous_native_jet_pairing
end NativeTrueOrder

namespace NativeTrueOrder
open Filter Topology MeasureTheory MasulloGRH Round166F
open SpectralRound9B SpectralRound10B SpectralRound11B

/-- Actual admitted native family plus supplied residue exhaustion. Every
scalar continuity/division premise is retained for its own character,
zero and order; derivative interchange is retained only at strip boundaries. The geometric theta space is defined independently of jets. -/
theorem continuous_theta_native_space_eq
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    {ι : Type*} (chi : ι → UnitaryHeckeCharacter K)
    (rho : ι → ℂ) (m : ι → ℕ) (a s alpha : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadmit : ∀ i, |(rho i).re-a| < alpha ∨
      (|(rho i).re-a| = alpha ∧ (2 : ℝ)*m i+1 < s))
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (rho i) a s alpha (m i)) 2 mu)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℂ V]
    (d q : V →L[ℂ] ℂ) (u v : V) (D : Submodule ℂ V)
    (hD : Dense (D : Set V)) (hu : u ∈ D) (hv : v ∈ D)
    (hdu : d u = 1) (hdv : d v = 0) (hqu : q u = 0) (hqv : q v = 1)
    (theta : (d.ker ⊓ q.ker : Submodule ℂ V) → Lp ℂ 2 mu)
    (Phi : (d.ker ⊓ q.ker : Submodule ℂ V) → HeckeIdeleClasses K → ℂ)
    (hPhi : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * Phi f x) 2 mu)
    (hnorm : ∀ f, theta f = (hPhi f).toLp _)
    (htheta : Continuous theta)
    (L : ι → ℂ → ℂ)
    (Q : ι → (d.ker ⊓ q.ker : Submodule ℂ V) → ℂ → ℂ)
    (hL : ∀ i, AnalyticAt ℂ (L i) (rho i))
    (hfinite : ∀ i, analyticOrderAt (L i) (rho i) ≠ ⊤)
    (hm : ∀ i, m i < analyticOrderNatAt (L i) (rho i))
    (hQ : ∀ i, ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      AnalyticAt ℂ (Q i f) (rho i))
    (hdiv : ∀ i, ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      nativeMellinTransform K (chi i) mu a (Phi f) =ᶠ[𝓝 (rho i)]
        (fun z => L i z * Q i f z))
    (hboundaryDeriv : ∀ i, |(rho i).re-a| = alpha → ∀ f : (d.ker ⊓ q.ker : Submodule ℂ V), (f : V) ∈ D →
      (∫ x, genuineMellinJet K (chi i) (rho i) a (m i) x * Phi f x ∂mu) =
        iteratedDeriv (m i) (nativeMellinTransform K (chi i) mu a (Phi f)) (rho i))
    (hexhaust : (Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal ≤
      (Submodule.span ℂ (Set.range (fun i => (hg i).star.toLp
        (star (genuineNormalizedMellinJet K (chi i) (rho i) a s alpha (m i)))))).topologicalClosure) :
    (Submodule.span ℂ (Set.range (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (rho i) a s alpha (m i)))))).topologicalClosure =
      (Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal := by
  have hjet (i : ι) : (hg i).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (rho i) a s alpha (m i))) ∈
      (Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal := by
    obtain ⟨hg', hp, hi⟩ := admitted_same_integral_riesz_converse K (chi i) mu c hc0 hct hmap
      (rho i) a s alpha (m i) hs ha (hadmit i) d q u v D hD hu hv hdu hdv hqu hqv
      theta Phi hPhi hnorm
      (continuous_native_jet_pairing K (chi i) mu (rho i) a s alpha (m i)
        (hg i) theta htheta Phi hPhi hnorm) (L i) (Q i) (hL i) (hfinite i) (hm i)
      (hQ i) (hdiv i) (hboundaryDeriv i)
    exact hi
  have hspan : Submodule.span ℂ (Set.range (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K (chi i) (rho i) a s alpha (m i))))) ≤
      (Submodule.span ℂ (Set.range theta)).topologicalClosure.orthogonal := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hjet i
  apply le_antisymm _ hexhaust
  intro x hx
  change ∀ F ∈ (Submodule.span ℂ (Set.range theta)).topologicalClosure, inner ℂ F x = 0
  intro F hF
  have hc : IsClosed {y : Lp ℂ 2 mu | inner ℂ F y = 0} :=
    isClosed_eq (innerSL ℂ F).continuous continuous_const
  apply closure_minimal (fun y hy => ?_) hc hx
  exact hspan hy F hF

#print axioms continuous_theta_native_space_eq
end NativeTrueOrder
