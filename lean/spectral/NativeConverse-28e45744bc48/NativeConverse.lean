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

#check boundaryJetOrders_odd
#print axioms boundaryJetOrders_odd
#check trace_of_binomial_jet_action
#print axioms trace_of_binomial_jet_action
#check boundary_jet_trace_at_odd_weight
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

#check boundaryJetOrders_all_real
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

#check radialJetDensity_tail_comparison
#print axioms radialJetDensity_tail_comparison
#check radialJetDensity_integrable_tail_iff
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
#check radialJetDensity_integrable_halfLine_iff
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
#check boundaryRadialJet_integrable_halfLine_iff
#print axioms boundaryRadialJet_integrable_halfLine_iff
end SpectralRound3B

namespace SpectralRound4B
open MeasureTheory Set SpectralRound3B
/-- Discharges reflection symmetry of the squared radial jet norm, needed
for the negative-tail part of the native boundary multiplicity criterion. -/
theorem radialJetDensity_even (m : ℕ) (s x : ℝ) :
    radialJetDensity m s (-x) = radialJetDensity m s x := by
  simp [radialJetDensity, pow_mul]
#check radialJetDensity_even
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

#check radialJetDensity_integrable_iff
#print axioms radialJetDensity_integrable_iff
#check rightBoundaryRadialJet_integrable_iff
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

#check leftBoundaryRadialJet_integrable_iff
#print axioms leftBoundaryRadialJet_integrable_iff
#check boundaryRadialJet_integrable_iff
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
#check boundary_integrable_orders
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

#check boundary_density_integrable_pullback_iff
#print axioms boundary_density_integrable_pullback_iff
#check weightedMellinJet_sq_norm
#print axioms weightedMellinJet_sq_norm
#check boundary_weightedMellinJet_memLp_iff
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

#check weightedMellinJet_measurable
#print axioms weightedMellinJet_measurable
#check boundary_weightedMellinJet_orders
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

#check interior_density_le_exp_polynomial
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

#check exp_abs_even_polynomial_integrable
#print axioms exp_abs_even_polynomial_integrable
#check interiorRadialJet_integrable
#print axioms interiorRadialJet_integrable
#check interior_weightedMellinJet_memLp
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

#check log_pushforward_of_split
#print axioms log_pushforward_of_split
#check genuine_interior_jet_memLp_of_split
#print axioms genuine_interior_jet_memLp_of_split
#check genuine_boundary_orders_of_split
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

#check genuine_jet_sq_eq_nativeDualDensity
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

#check MasulloGRH.classCharacter_mk
#print axioms MasulloGRH.classCharacter_mk
#check MasulloGRH.classCharacter_continuous
#print axioms MasulloGRH.classCharacter_continuous
#check genuineNormalizedMellinJet_norm
#print axioms genuineNormalizedMellinJet_norm
#check genuine_boundary_mellin_memLp_iff
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

#check genuine_interior_mellin_memLp
#print axioms genuine_interior_mellin_memLp
#check genuine_boundary_mellin_orders
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

#check normalizedBilinearFunctional_apply
#print axioms normalizedBilinearFunctional_apply
#check genuine_boundary_continuous_pairing
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

#check nativeHalfWeight_sq
#print axioms nativeHalfWeight_sq
#check genuineMellinJet_normalization
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

#check native_normalization_memLp_iff
#print axioms native_normalization_memLp_iff
#check native_pairing_formula
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

#check native_normalization_surjective
#print axioms native_normalization_surjective
#check native_pairing_integrable
#print axioms native_pairing_integrable
end SpectralRound12B

open Set Topology
namespace FollowupD26
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

noncomputable def twoMomentCorrection (a b : E →L[ℂ] ℂ) (u v : E) : E →L[ℂ] E :=
  ContinuousLinearMap.id ℂ E - a.smulRight u - b.smulRight v

theorem correction_moments (a b : E →L[ℂ] ℂ) (u v : E)
    (hau : a u = 1) (hav : a v = 0) (hbu : b u = 0) (hbv : b v = 1) (x : E) :
    a (twoMomentCorrection a b u v x) = 0 ∧
    b (twoMomentCorrection a b u v x) = 0 := by
  simp [twoMomentCorrection, map_sub, map_smul, hau, hav, hbu, hbv]

theorem correction_fixes_kernel (a b : E →L[ℂ] ℂ) (u v x : E)
    (ha : a x = 0) (hb : b x = 0) :
    twoMomentCorrection a b u v x = x := by
  simp [twoMomentCorrection, ha, hb]

theorem correction_preserves_tests (T : Submodule ℂ E)
    (a b : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (x : E) (hx : x ∈ T) : twoMomentCorrection a b u v x ∈ T := by
  exact T.sub_mem (T.sub_mem hx (T.smul_mem (a x) hu)) (T.smul_mem (b x) hv)

/-- Finite factorized tests remain dense after imposing both original moments.
This theorem works in a topological vector space, including a Frechet stage;
it does not assert an adelic instantiation or any Tate identity. -/
theorem dense_two_moment_kernel (T : Submodule ℂ E) (hT : Dense (T : Set E))
    (a b : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (hau : a u = 1) (hav : a v = 0) (hbu : b u = 0) (hbv : b v = 1) :
    closure {x : E | x ∈ T ∧ a x = 0 ∧ b x = 0} =
      {x : E | a x = 0 ∧ b x = 0} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx; exact hx.2
    · exact (isClosed_eq a.continuous continuous_const).inter
        (isClosed_eq b.continuous continuous_const)
  · intro x hx
    rw [← correction_fixes_kernel a b u v x hx.1 hx.2]
    apply map_mem_closure (twoMomentCorrection a b u v).continuous (hT x)
    intro y hy
    exact ⟨correction_preserves_tests T a b u v hu hv y hy,
      correction_moments a b u v hau hav hbu hbv y⟩

#print axioms correction_moments
#print axioms correction_fixes_kernel
#print axioms correction_preserves_tests
#print axioms dense_two_moment_kernel
/-- The scalar pairing is defined only on the original two-kernel subtype.
No extension of theta to unrestricted Schwartz tests is required. -/
theorem vanishing_on_original_kernel (T : Submodule ℂ E) (hT : Dense (T : Set E))
    (a b : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (hau : a u = 1) (hav : a v = 0) (hbu : b u = 0) (hbv : b v = 1)
    (J : (a.ker ⊓ b.ker : Submodule ℂ E) → ℂ) (hJ : Continuous J)
    (hz : ∀ x : (a.ker ⊓ b.ker : Submodule ℂ E), (x : E) ∈ T → J x = 0) :
    ∀ x : (a.ker ⊓ b.ker : Submodule ℂ E), J x = 0 := by
  let R : E → (a.ker ⊓ b.ker : Submodule ℂ E) := fun x =>
    ⟨twoMomentCorrection a b u v x, correction_moments a b u v hau hav hbu hbv x⟩
  have hR : Continuous R := (twoMomentCorrection a b u v).continuous.subtype_mk _
  have hs : (T : Set E) ⊆ {x : E | J (R x) = 0} := by
    intro x hx
    exact hz (R x) (correction_preserves_tests T a b u v hu hv x hx)
  intro x
  have h := closure_minimal hs (isClosed_eq (hJ.comp hR) continuous_const) (hT (x : E))
  have he : R (x : E) = x := by
    apply Subtype.ext
    exact correction_fixes_kernel a b u v x x.property.1 x.property.2
  simpa only [Set.mem_setOf_eq, he] using h

#print axioms vanishing_on_original_kernel
end FollowupD26


namespace FollowupD27
open Set Topology MeasureTheory MasulloGRH Round166F SpectralRound9B
open SpectralRound10B SpectralRound11B SpectralRound12B

/-- Actual class-group Mellin integral attached to corrected tests on the
original simultaneous kernel. The test density, normalized theta continuity,
and finite-test Tate vanishing are explicit application obligations. The
measure, character, native weight and jet are the checked B12 objects. -/
theorem genuine_native_jet_from_corrected_tests
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (T : Submodule ℂ E) (hT : Dense (T : Set E))
    (e0 eF : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (hu0 : e0 u = 1) (hv0 : e0 v = 0) (huF : eF u = 0) (hvF : eF v = 1)
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (z : ℂ) (a s alpha : ℝ) (m : ℕ)
    (hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (theta : (e0.ker ⊓ eF.ker : Submodule ℂ E) → HeckeIdeleClasses K → ℂ)
    (hF : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * theta f x) 2 mu)
    (hcont : Continuous (fun f => (hF f).toLp _))
    (hTate : ∀ f : (e0.ker ⊓ eF.ker : Submodule ℂ E), (f : E) ∈ T →
      ∫ x, genuineMellinJet K chi z a m x * theta f x ∂mu = 0) :
    (∀ f, Integrable (fun x => genuineMellinJet K chi z a m x * theta f x) mu ∧
      ∫ x, genuineMellinJet K chi z a m x * theta f x ∂mu = 0) ∧
    (∀ F ∈ closure ((Submodule.span ℂ (Set.range (fun f => (hF f).toLp _))) : Set (Lp ℂ 2 mu)),
      normalizedBilinearFunctional mu _ hg F = 0) := by
  let J := normalizedBilinearFunctional mu
    (genuineNormalizedMellinJet K chi z a s alpha m) hg
  have hall : ∀ f, J ((hF f).toLp _) = 0 := by
    apply FollowupD26.vanishing_on_original_kernel T hT e0 eF u v hu hv
      hu0 hv0 huF hvF (fun f => J ((hF f).toLp _))
      (J.continuous.comp hcont)
    intro f hf
    rw [show J ((hF f).toLp _) =
      ∫ x, genuineMellinJet K chi z a m x * theta f x ∂mu from
      native_pairing_formula K chi mu z a s alpha m hg (theta f) (hF f)]
    exact hTate f hf
  constructor
  · intro f
    refine ⟨native_pairing_integrable K chi mu z a s alpha m hg (theta f) (hF f), ?_⟩
    rw [← native_pairing_formula K chi mu z a s alpha m hg (theta f) (hF f)]
    exact hall f
  · have hspan : Submodule.span ℂ (Set.range (fun f => (hF f).toLp _)) ≤
        (J : Lp ℂ 2 mu →ₗ[ℂ] ℂ).ker := by
      apply Submodule.span_le.mpr
      rintro F ⟨f, rfl⟩
      exact hall f
    exact closure_minimal hspan (isClosed_eq J.continuous continuous_const)

#print axioms genuine_native_jet_from_corrected_tests


/-- Sharp actual admission and closed-span attachment. This integrates the
explicit admission in conditional_B and the closed span in followup_F.
The analytic Tate/theta premises remain visible; no zero-order premise or
all-test division is silently discharged. -/
theorem admitted_genuine_jet_annihilates_closed_span
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (T : Submodule ℂ E) (hT : Dense (T : Set E))
    (e0 eF : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (hu0 : e0 u = 1) (hv0 : e0 v = 0) (huF : eF u = 0) (hvF : eF v = 1)
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadmit : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s))
    (theta : (e0.ker ⊓ eF.ker : Submodule ℂ E) → HeckeIdeleClasses K → ℂ)
    (hF : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * theta f x) 2 mu)
    (hcont : Continuous (fun f => (hF f).toLp _))
    (hTate : ∀ f : (e0.ker ⊓ eF.ker : Submodule ℂ E), (f : E) ∈ T →
      ∫ x, genuineMellinJet K chi z a m x * theta f x ∂mu = 0) :
    ∃ J : Lp ℂ 2 mu →L[ℂ] ℂ,
      (∀ f, J ((hF f).toLp _) =
        ∫ x, genuineMellinJet K chi z a m x * theta f x ∂mu) ∧
      (∀ F ∈ closure ((Submodule.span ℂ (Set.range (fun f => (hF f).toLp _))) :
        Set (Lp ℂ 2 mu)), J F = 0) := by
  have hg : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu := by
    rcases hadmit with hi | ⟨hb, hm⟩
    · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap z a s alpha m hs hi
    · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap
        z a s alpha m hs ha hb).mpr hm
  refine ⟨normalizedBilinearFunctional mu _ hg, ?_, ?_⟩
  · intro f
    exact native_pairing_formula K chi mu z a s alpha m hg (theta f) (hF f)
  · exact (genuine_native_jet_from_corrected_tests T hT e0 eF u v hu hv
      hu0 hv0 huF hvF K chi mu z a s alpha m hg theta hF hcont hTate).2

#print axioms admitted_genuine_jet_annihilates_closed_span

end FollowupD27

namespace FollowupD28
open Set Topology MeasureTheory MasulloGRH Round166F SpectralRound9B
open SpectralRound10B SpectralRound11B SpectralRound12B

/-- Scalar local division, using the true analytic order. Adapted from
conditional_A's TateDerivative; no global equality or arbitrary order is used. -/
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

/-- The same actual quotient measure, character and original native Mellin
integral are used at every complex parameter. No artificial spectrum enters. -/
noncomputable def nativeMellinTransform
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K)) (a : ℝ)
    (f : HeckeIdeleClasses K → ℂ) (z : ℂ) : ℂ :=
  ∫ x, genuineMellinJet K chi z a 0 x * f x ∂mu

/-- Attaches LOCAL division of the actual integral to the sharp admitted
native jet and the original two-moment test domain. The remaining arithmetic
premises are stated as division and differentiation of that exact integral,
not as the desired vanishing. L must still be the genuine completed Hecke
function at application, and theta the original lift with its actual topology. -/
theorem local_tate_division_annihilates_native_closed_span
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (T : Submodule ℂ E) (hT : Dense (T : Set E))
    (e0 eF : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (hu0 : e0 u = 1) (hv0 : e0 v = 0) (huF : eF u = 0) (hvF : eF v = 1)
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (rho : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadmit : |rho.re-a| < alpha ∨
      (|rho.re-a| = alpha ∧ (2 : ℝ)*m+1 < s))
    (theta : (e0.ker ⊓ eF.ker : Submodule ℂ E) → HeckeIdeleClasses K → ℂ)
    (hF : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * theta f x) 2 mu)
    (hpair : Continuous (fun f =>
      ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu))
    (L : ℂ → ℂ) (hL : AnalyticAt ℂ L rho)
    (hfinite : analyticOrderAt L rho ≠ ⊤)
    (hm : m < analyticOrderNatAt L rho)
    (hdivision : ∀ f : (e0.ker ⊓ eF.ker : Submodule ℂ E), (f : E) ∈ T →
      ∃ D : ℂ → ℂ, AnalyticAt ℂ D rho ∧
        nativeMellinTransform K chi mu a (theta f) =ᶠ[𝓝 rho]
          (fun z => L z * D z))
    (hdifferentiate : ∀ f : (e0.ker ⊓ eF.ker : Submodule ℂ E), (f : E) ∈ T →
      iteratedDeriv m (nativeMellinTransform K chi mu a (theta f)) rho =
        ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu) :
    ∃ J : Lp ℂ 2 mu →L[ℂ] ℂ,
      (∀ f, J ((hF f).toLp _) =
        ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu) ∧
      (∀ F ∈ closure ((Submodule.span ℂ (Set.range (fun f => (hF f).toLp _))) :
        Set (Lp ℂ 2 mu)), J F = 0) := by
  have hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu := by
    rcases hadmit with hi | ⟨hb, hm⟩
    · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap rho a s alpha m hs hi
    · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap
        rho a s alpha m hs ha hb).mpr hm
  let J := normalizedBilinearFunctional mu
    (genuineNormalizedMellinJet K chi rho a s alpha m) hg
  have hp (f) : J ((hF f).toLp _) =
      ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu :=
    native_pairing_formula K chi mu rho a s alpha m hg (theta f) (hF f)
  have hall : ∀ f, J ((hF f).toLp _) = 0 := by
    apply FollowupD26.vanishing_on_original_kernel T hT e0 eF u v hu hv
      hu0 hv0 huF hvF (fun f => J ((hF f).toLp _))
    · simpa only [hp] using hpair
    · intro f hf
      obtain ⟨D, hD, hdiv⟩ := hdivision f hf
      rw [hp, ← hdifferentiate f hf]
      exact local_tate_derivative_zero L D _ rho m hL hD hfinite hm hdiv
  refine ⟨J, hp, ?_⟩
  have hspan : Submodule.span ℂ (Set.range (fun f => (hF f).toLp _)) ≤
      (J : Lp ℂ 2 mu →ₗ[ℂ] ℂ).ker := by
    apply Submodule.span_le.mpr
    rintro F ⟨f, rfl⟩
    exact hall f
  exact closure_minimal hspan (isClosed_eq J.continuous continuous_const)

#print axioms local_tate_derivative_zero
#print axioms local_tate_division_annihilates_native_closed_span
end FollowupD28

namespace FollowupD29
open Set Topology MeasureTheory MasulloGRH Round166F SpectralRound9B
open SpectralRound10B SpectralRound11B SpectralRound12B FollowupD28

/-- The true-order, same-integral converse now returns the correctly conjugated
native Riesz vector in the original geometric orthogonal complement. This joins
strict admission, constrained dense tests, scalar continuity and local Tate
division; the genuine completed-Hecke/theta specialization remains an input.
Riesz orientation follows the independently inspected followup_F repair. -/
theorem local_tate_division_riesz_in_original_annihilator
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (T : Submodule ℂ E) (hT : Dense (T : Set E))
    (e0 eF : E →L[ℂ] ℂ) (u v : E) (hu : u ∈ T) (hv : v ∈ T)
    (hu0 : e0 u = 1) (hv0 : e0 v = 0) (huF : eF u = 0) (hvF : eF v = 1)
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (rho : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadmit : |rho.re-a| < alpha ∨
      (|rho.re-a| = alpha ∧ (2 : ℝ)*m+1 < s))
    (theta : (e0.ker ⊓ eF.ker : Submodule ℂ E) → HeckeIdeleClasses K → ℂ)
    (hF : ∀ f, MemLp (fun x =>
      (nativeHalfWeight alpha s (classLog K x) : ℂ) * theta f x) 2 mu)
    (hpair : Continuous (fun f =>
      ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu))
    (L : ℂ → ℂ) (hL : AnalyticAt ℂ L rho)
    (hfinite : analyticOrderAt L rho ≠ ⊤)
    (hm : m < analyticOrderNatAt L rho)
    (hdivision : ∀ f : (e0.ker ⊓ eF.ker : Submodule ℂ E), (f : E) ∈ T →
      ∃ D : ℂ → ℂ, AnalyticAt ℂ D rho ∧
        nativeMellinTransform K chi mu a (theta f) =ᶠ[𝓝 rho]
          (fun z => L z * D z))
    (hdifferentiate : ∀ f : (e0.ker ⊓ eF.ker : Submodule ℂ E), (f : E) ∈ T →
      iteratedDeriv m (nativeMellinTransform K chi mu a (theta f)) rho =
        ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu) :
    ∃ hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu,
      hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m)) ∈
        (Submodule.span ℂ (Set.range (fun f => (hF f).toLp _))).topologicalClosure.orthogonal := by
  have hg : MemLp (genuineNormalizedMellinJet K chi rho a s alpha m) 2 mu := by
    rcases hadmit with hi | ⟨hb, hm⟩
    · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap rho a s alpha m hs hi
    · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap
        rho a s alpha m hs ha hb).mpr hm
  let J := normalizedBilinearFunctional mu
    (genuineNormalizedMellinJet K chi rho a s alpha m) hg
  have hp (f) : J ((hF f).toLp _) =
      ∫ x, genuineMellinJet K chi rho a m x * theta f x ∂mu :=
    native_pairing_formula K chi mu rho a s alpha m hg (theta f) (hF f)
  have hall : ∀ f, J ((hF f).toLp _) = 0 := by
    apply FollowupD26.vanishing_on_original_kernel T hT e0 eF u v hu hv
      hu0 hv0 huF hvF (fun f => J ((hF f).toLp _))
    · simpa only [hp] using hpair
    · intro f hf
      obtain ⟨D, hD, hdiv⟩ := hdivision f hf
      rw [hp, ← hdifferentiate f hf]
      exact local_tate_derivative_zero L D _ rho m hL hD hfinite hm hdiv
  have hspan : Submodule.span ℂ (Set.range (fun f => (hF f).toLp _)) ≤
      (J : Lp ℂ 2 mu →ₗ[ℂ] ℂ).ker := by
    apply Submodule.span_le.mpr
    rintro F ⟨f, rfl⟩
    exact hall f
  have hann : ∀ F ∈ closure ((Submodule.span ℂ
      (Set.range (fun f => (hF f).toLp _))) : Set (Lp ℂ 2 mu)), J F = 0 :=
    closure_minimal hspan (isClosed_eq J.continuous continuous_const)
  refine ⟨hg, ?_⟩
  change ∀ F ∈ (Submodule.span ℂ (Set.range (fun f => (hF f).toLp _))).topologicalClosure,
    inner ℂ F (hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m))) = 0
  intro F hFmem
  have h := hann F hFmem
  change inner ℂ (hg.star.toLp (star (genuineNormalizedMellinJet K chi rho a s alpha m))) F = 0 at h
  exact inner_eq_zero_symm.mp h

#print axioms local_tate_division_riesz_in_original_annihilator
end FollowupD29
