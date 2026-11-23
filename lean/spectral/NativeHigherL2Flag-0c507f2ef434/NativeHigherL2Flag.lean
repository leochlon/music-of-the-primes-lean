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
end SpectralRound3B

namespace SpectralRound4B
open MeasureTheory Set SpectralRound3B
/-- Discharges reflection symmetry of the squared radial jet norm, needed
for the negative-tail part of the native boundary multiplicity criterion. -/
theorem radialJetDensity_even (m : ℕ) (s x : ℝ) :
    radialJetDensity m s (-x) = radialJetDensity m s x := by
  simp [radialJetDensity, pow_mul]

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

end SpectralRound12B


open Set Topology

namespace MasulloGRH.NativeTateConverse
open MeasureTheory Set Topology Round166F SpectralRound9B SpectralRound10B SpectralRound11B

/-- Strict admission gives membership on the SAME Haar measure, including the
zero-width case only through its single boundary condition. -/
theorem native_admitted_memLp
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadm : |z.re-a| < alpha ∨ (|z.re-a| = alpha ∧ (2 : ℝ)*m+1 < s)) :
    MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu := by
  rcases hadm with hi | ⟨hb, hm⟩
  · exact genuine_interior_mellin_memLp K chi mu c hc0 hct hmap z a s alpha m hs hi
  · exact (genuine_boundary_mellin_memLp_iff K chi mu c hc0 hct hmap z a s alpha m hs ha hb).mpr hm

end MasulloGRH.NativeTateConverse
namespace SpectralCycle6B
open MeasureTheory MasulloGRH SpectralRound9B InnerProductSpace
open scoped InnerProductSpace

/-- Construct the finite predecessor flag of the actual conjugated native
Riesz kernels. No span, orthogonality, or unit-norm premises are assumed.
Cross-chain independence is required only for the nonzero normalization. -/
theorem native_gramSchmidt_flag
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (K : Type*) [Field K] [NumberField K]
    (mu : Measure (HeckeIdeleClasses K))
    (chi : ι → UnitaryHeckeCharacter K) (z : ι → ℂ)
    (a s alpha : ℝ) (m : ι → ℕ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)) 2 mu) :
    let jet : ι → Lp ℂ 2 mu := fun i =>
      (hg i).star.toLp (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
    let b := gramSchmidtNormed ℂ jet
    (∀ i, b i ∈ Submodule.span ℂ (jet '' Set.Iic i)) ∧
    (∀ i k, k < i → ⟪jet k, b i⟫_ℂ = 0) ∧
    (∀ i, Submodule.span ℂ (b '' Set.Iic i) =
      Submodule.span ℂ (jet '' Set.Iic i)) ∧
    (LinearIndependent ℂ jet → Orthonormal ℂ b) := by
  dsimp only
  let jet : ι → Lp ℂ 2 mu := fun i =>
    (hg i).star.toLp (star (genuineNormalizedMellinJet K (chi i) (z i) a s alpha (m i)))
  change (∀ i, gramSchmidtNormed ℂ jet i ∈ _) ∧ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact Submodule.smul_mem _ _ (gramSchmidt_mem_span ℂ jet (le_refl i))
  · intro i k hki
    change ⟪jet k, gramSchmidtNormed ℂ jet i⟫_ℂ = 0
    have hj : jet k ∈ Submodule.span ℂ (gramSchmidt ℂ jet '' Set.Iio i) := by
      rw [span_gramSchmidt_Iio]
      exact Submodule.subset_span ⟨k, hki, rfl⟩
    have ho : ∀ x ∈ Submodule.span ℂ (gramSchmidt ℂ jet '' Set.Iio i),
        ⟪x, gramSchmidt ℂ jet i⟫_ℂ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨j, hj, rfl⟩ := hx
          exact gramSchmidt_orthogonal ℂ jet (ne_of_lt hj)
      | zero => simp
      | add x y hx hy hpx hpy => simp [inner_add_left, hpx, hpy]
      | smul c x hx hpx => simp [inner_smul_left, hpx]
    simp only [gramSchmidtNormed, inner_smul_right, ho _ hj, mul_zero]
  · intro i
    exact (span_gramSchmidtNormed jet (Set.Iic i)).trans (span_gramSchmidt_Iic ℂ jet i)
  · exact gramSchmidtNormed_orthonormal

#print axioms native_gramSchmidt_flag
end SpectralCycle6B

namespace SpectralCycle7B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped BigOperators

noncomputable def radialExpHom (z : ℂ) : Multiplicative ℝ →* ℂ where
  toFun t := Complex.exp (z * ((Multiplicative.toAdd t : ℝ) : ℂ))
  map_one' := by simp
  map_mul' t u := by
    change Complex.exp (z * ((Multiplicative.toAdd t + Multiplicative.toAdd u : ℝ) : ℂ)) = _
    simp only [Complex.ofReal_add, mul_add, Complex.exp_add]

theorem radialExpHom_injective : Function.Injective radialExpHom := by
  intro z w h
  have hall : (fun t : ℝ => Complex.exp (z*(t:ℂ))) =
      (fun t : ℝ => Complex.exp (w*(t:ℂ))) := by
    funext t
    exact congrArg (fun f : Multiplicative ℝ →* ℂ => f (Multiplicative.ofAdd t)) h
  have hz : HasDerivAt (fun t : ℝ => Complex.exp (z*(t:ℂ))) z 0 := by
    convert (((Complex.hasDerivAt_exp (z*(0:ℂ))).comp 0
      ((hasDerivAt_id (0:ℂ)).const_mul z))).comp_ofReal using 1
    simp
  have hw : HasDerivAt (fun t : ℝ => Complex.exp (w*(t:ℂ))) w 0 := by
    convert (((Complex.hasDerivAt_exp (w*(0:ℂ))).comp 0
      ((hasDerivAt_id (0:ℂ)).const_mul w))).comp_ofReal using 1
    simp
  rw [hall] at hz
  exact hz.unique hw

/-- Actual original-weight zeroth kernels at distinct roots in one Hecke
component are finitely independent modulo the SAME quotient Haar null sets.
No independence or separation conclusion is an input. -/
theorem native_zero_finite_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (b : ι → ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0) :
    ∀ i ∈ S, b i = 0 := by
  classical
  let W : HeckeIdeleClasses K → ℂ := fun x =>
    (classCharacter K chi x : ℂ) * Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) *
      (((1 + (classLog K x)^2)^(-s/4) : ℝ):ℂ)
  have hW (x) : W x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
  have hfactor (i) (x) : genuineNormalizedMellinJet K chi (z i) a s alpha 0 x =
      W x * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) := by
    have he : Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ) -
        ((alpha * |classLog K x| : ℝ):ℂ)) =
        Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) *
        Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) := by
      rw [sub_eq_add_neg, Complex.exp_add]
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul, he]
    dsimp [W]
    ring
  have hrad : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) = 0 := by
    filter_upwards [h] with x hx
    have hh : W x * (∑ i ∈ S, b i * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ))) = 0 := by
      rw [Finset.mul_sum]
      convert hx using 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [hfactor]
      ring
    exact (mul_eq_zero.mp hh).resolve_left (hW x)
  have hcont : Continuous (fun t : ℝ => ∑ i ∈ S,
      b i * Complex.exp ((z i-(a:ℂ))*(t:ℂ))) := by fun_prop
  have hm := (ae_map_iff (Round175B.classLog_continuous K).measurable.aemeasurable
    (isClosed_eq hcont continuous_const).measurableSet).mpr hrad
  rw [hmap] at hm
  have hm0 : ∀ᵐ t : ℝ ∂volume, ∑ i ∈ S, b i * Complex.exp ((z i-(a:ℂ))*(t:ℂ)) = 0 := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hm0
  have hinj : Function.Injective (fun i => radialExpHom (z i-(a:ℂ))) := by
    intro i j hij
    apply hz
    have he := radialExpHom_injective hij
    linear_combination he
  have hli := (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
    (fun i => radialExpHom (z i-(a:ℂ))) hinj
  apply (linearIndependent_iff'.mp hli) S b
  funext t
  simpa [radialExpHom, Function.comp_def] using congrFun hall (Multiplicative.toAdd t)

#print axioms native_zero_finite_independent
end SpectralCycle7B

namespace SpectralCycle7B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped BigOperators
/-- Independence of the actual conjugated L2 vectors used by native Gram–Schmidt,
for all distinct zeroth roots in one fixed character component. -/
theorem native_zero_L2_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu) :
    LinearIndependent ℂ (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))) := by
  classical
  let J := fun i => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))
  apply linearIndependent_iff'.mpr
  intro S b hsum
  have he (T : Finset ι) :
      (fun x => (∑ i ∈ T, b i • J i) x) =ᵐ[mu]
        (fun x => ∑ i ∈ T, b i * star (genuineNormalizedMellinJet K chi (z i) a s alpha 0 x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (b i • J i) (∑ j ∈ T, b j • J j),
        Lp.coeFn_smul (b i) (J i), (hg i).star.coeFn_toLp, ih] with x hx hs hj ht
      change J i x = star (genuineNormalizedMellinJet K chi (z i) a s alpha 0 x) at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  have hzsum : ∀ᵐ x ∂mu, ∑ i ∈ S,
      star (b i) * genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0 := by
    have hz0 := Lp.coeFn_zero ℂ 2 mu
    have hh := he S
    change (∑ i ∈ S, b i • J i) = 0 at hsum
    rw [hsum] at hh
    filter_upwards [hh, hz0] with x hx hx0
    have hh' := congrArg star (hx.symm.trans hx0)
    simpa only [star_sum, star_mul, star_star, Pi.zero_apply, star_zero, mul_comm] using hh'
  have hb := native_zero_finite_independent K chi mu c hc hmap z hz a s alpha S
    (fun i => star (b i)) hzsum
  intro i hi
  exact star_eq_zero.mp (hb i hi)

#print axioms native_zero_L2_independent
end SpectralCycle7B

namespace SpectralCycle8B
open MeasureTheory MasulloGRH Round166F SpectralRound9B InnerProductSpace
open scoped InnerProductSpace

/-- The actual admitted zeroth Riesz kernels form an independent native flag.
The old L2 membership and linear-independence premises are both discharged;
the same-Haar logarithmic pushforward and strict admission remain explicit. -/
theorem native_admitted_zero_flag
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ alpha)
    (hadm : ∀ i, |(z i).re-a| < alpha ∨ (|(z i).re-a| = alpha ∧ 1 < s)) :
    let hg : ∀ i, MemLp (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu :=
      fun i => NativeTateConverse.native_admitted_memLp K chi mu c hc0 hct hmap
        (z i) a s alpha 0 hs ha (by simpa using hadm i)
    let jet : ι → Lp ℂ 2 mu := fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))
    let b := gramSchmidtNormed ℂ jet
    LinearIndependent ℂ jet ∧ Orthonormal ℂ b ∧
      (∀ i, Submodule.span ℂ (b '' Set.Iic i) = Submodule.span ℂ (jet '' Set.Iic i)) ∧
      (∀ i k, k < i → ⟪jet k, b i⟫_ℂ = 0) := by
  let hg : ∀ i, MemLp (genuineNormalizedMellinJet K chi (z i) a s alpha 0) 2 mu :=
    fun i => NativeTateConverse.native_admitted_memLp K chi mu c hc0 hct hmap
      (z i) a s alpha 0 hs ha (by simpa using hadm i)
  let jet : ι → Lp ℂ 2 mu := fun i => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K chi (z i) a s alpha 0))
  change LinearIndependent ℂ jet ∧ Orthonormal ℂ (gramSchmidtNormed ℂ jet) ∧ _
  have hi : LinearIndependent ℂ jet := SpectralCycle7B.native_zero_L2_independent
    K chi mu c hc0 hmap z hz a s alpha hg
  have hf := SpectralCycle6B.native_gramSchmidt_flag K mu (fun _ : ι => chi)
    z a s alpha (fun _ : ι => 0) hg
  exact ⟨hi, gramSchmidtNormed_orthonormal hi, hf.2.2.1, hf.2.1⟩

#print axioms native_admitted_zero_flag
end SpectralCycle8B

/- Reused spectral_H polynomial isolation and native block proof. -/
namespace SpectralH

/-- A shifted nilpotent derivative has no kernel at a distinct exponent.
This is the algebraic isolation step for actual exponential-polynomial jets. -/
theorem nilpotent_shift_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (N : ℕ) (x : V) (hn : (D ^ N) x = 0)
    (hx : D x + c • x = 0) : x = 0 := by
  induction N generalizing x with
  | zero => simpa using hn
  | succ N ih =>
    have hDx : D x = -(c • x) := eq_neg_of_add_eq_zero_left hx
    have hn' : (D ^ N) (D x) = 0 := by
      rw [pow_succ] at hn
      exact hn
    have hzero : (D ^ N) x = 0 := by
      rw [hDx, map_neg, map_smul] at hn'
      have hz : c • (D ^ N) x = 0 := neg_eq_zero.mp hn'
      exact (smul_eq_zero.mp hz).resolve_left hc
    exact ih x hzero hx

/-- Distinct exponent shifts preserve nonzero vectors in a nilpotent jet block. -/
theorem nilpotent_shift_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (N : ℕ) (x : V) (hn : (D ^ N) x = 0) (hx : x ≠ 0) :
    D x + c • x ≠ 0 := by
  intro h
  exact hx (nilpotent_shift_kernel D c hc N x hn h)

#print axioms nilpotent_shift_kernel
#print axioms nilpotent_shift_ne_zero
/-- Ordinary derivative on the polynomial block of an actual Mellin jet. -/
noncomputable def polynomialDerivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun := Polynomial.derivative
  map_add' _ _ := Polynomial.derivative_add
  map_smul' c p := Polynomial.derivative_smul c p

/-- The distinct-root isolator is injective on every polynomial, with no
nilpotence assumption left for the native exponential-polynomial application. -/
theorem polynomial_shift_kernel (c : ℂ) (hc : c ≠ 0) (p : Polynomial ℂ)
    (hp : Polynomial.derivative p + c • p = 0) : p = 0 := by
  have hn : (polynomialDerivative ^ (p.natDegree + 1)) p = 0 := by
    rw [Module.End.pow_apply]
    exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)
  exact nilpotent_shift_kernel polynomialDerivative c hc (p.natDegree + 1) p hn hp

theorem polynomial_shift_injective (c : ℂ) (hc : c ≠ 0) :
    Function.Injective (fun p : Polynomial ℂ => Polynomial.derivative p + c • p) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply polynomial_shift_kernel c hc
  calc
    Polynomial.derivative (p-q) + c • (p-q) =
        (Polynomial.derivative p + c • p) - (Polynomial.derivative q + c • q) := by
      simp only [map_sub, smul_sub]
      abel
    _ = 0 := sub_eq_zero.mpr hpq

#print axioms polynomial_shift_kernel
#print axioms polynomial_shift_injective
end SpectralH


namespace SpectralH904
open MasulloGRH Round166F SpectralRound9B MeasureTheory
open scoped BigOperators

theorem polynomial_real_zero (p : Polynomial ℂ)
    (h : ∀ t : ℝ, p.eval (t:ℂ) = 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro x ⟨t, rfl⟩
  exact h t

theorem shifted_relation {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (p : ι → Polynomial ℂ) (w : ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) :
    ∀ t : ℝ, ∑ i ∈ S,
      (Polynomial.derivative (p i) + (z i-w) • p i).eval (t:ℂ) *
        Complex.exp (z i*(t:ℂ)) = 0 := by
  intro t
  have hd : HasDerivAt (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)))
      (∑ i ∈ S, ((Polynomial.derivative (p i)).eval (t:ℂ) +
        z i * (p i).eval (t:ℂ)) * Complex.exp (z i*(t:ℂ))) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hec := (Complex.hasDerivAt_exp (z i*(t:ℂ))).comp (t:ℂ)
      ((hasDerivAt_id (t:ℂ)).const_mul (z i))
    have he : HasDerivAt (fun u : ℝ => Complex.exp (z i*(u:ℂ)))
        (Complex.exp (z i*(t:ℂ)) * z i) t := by
      simpa using hec.comp_ofReal
    have hp := ((p i).hasDerivAt (t:ℂ)).comp_ofReal
    convert hp.mul he using 1
    ring
  have heq : (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ))) = fun _ => 0 := funext h
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (0:ℂ))
  calc
    _ = (∑ i ∈ S, ((Polynomial.derivative (p i)).eval (t:ℂ) +
        z i * (p i).eval (t:ℂ)) * Complex.exp (z i*(t:ℂ))) -
        w * (∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
      ring
    _ = 0 := by rw [hz, h t]; ring

theorem finite_polynomial_exp_independent {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (hz : Function.Injective z) (p : ι → Polynomial ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) :
    ∀ i ∈ S, p i = 0 := by
  classical
  induction S using Finset.induction_on generalizing p with
  | empty => simp
  | @insert k S hk ih =>
    have main : ∀ n (p : ι → Polynomial ℂ),
        (Polynomial.derivative^[n]) (p k) = 0 →
        (∀ t : ℝ, ∑ i ∈ insert k S,
          (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) →
        ∀ i ∈ insert k S, p i = 0 := by
      intro n
      induction n with
      | zero =>
        intro p hn hp
        have hpk : p k = 0 := hn
        have hs : ∀ t : ℝ, ∑ i ∈ S,
            (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0 := by
          intro t
          simpa [Finset.sum_insert hk, hpk] using hp t
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpk
        · exact ih p hs i hi
      | succ n ihn =>
        intro p hn hp
        let q : ι → Polynomial ℂ := fun i =>
          Polynomial.derivative (p i) + (z i-z k) • p i
        have hqk : q k = Polynomial.derivative (p k) := by simp [q]
        have hqn : (Polynomial.derivative^[n]) (q k) = 0 := by
          rw [hqk]
          simpa only [Function.iterate_succ_apply] using hn
        have hq := ihn q hqn (shifted_relation (insert k S) z p (z k) hp)
        have hs : ∀ i ∈ S, p i = 0 := by
          intro i hi
          apply SpectralH.polynomial_shift_kernel (z i-z k)
            (sub_ne_zero.mpr (fun he => hk (hz he ▸ hi)))
          exact hq i (Finset.mem_insert_of_mem hi)
        have hpk : p k = 0 := by
          apply polynomial_real_zero
          intro t
          have hh := hp t
          rw [Finset.sum_insert hk] at hh
          have hsum : ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp [hs i hi]
          rw [hsum, add_zero] at hh
          exact (mul_eq_zero.mp hh).resolve_right (Complex.exp_ne_zero _)
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpk
        · exact hs i hi
    exact main ((p k).natDegree+1) p
      (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)) h

/-- Finite mixed higher-jet blocks in one genuine Hecke component, expressed
by their coefficient polynomials, are independent in the ORIGINAL weighted
realization modulo the SAME quotient measure. No independence is assumed. -/
theorem native_polynomial_blocks_independent {ι : Type*}
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (p : ι → Polynomial ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) *
        genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0) :
    ∀ i ∈ S, p i = 0 := by
  classical
  let W : HeckeIdeleClasses K → ℂ := fun x =>
    (classCharacter K chi x : ℂ) * Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) *
      (((1 + (classLog K x)^2)^(-s/4) : ℝ):ℂ)
  have hW (x) : W x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
  have hf (i) (x) : genuineNormalizedMellinJet K chi (z i) a s alpha 0 x =
      W x * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) := by
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul, sub_eq_add_neg,
      Complex.exp_add]
    dsimp [W]
    ring
  have hr : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) = 0 := by
    filter_upwards [h] with x hx
    apply (mul_eq_zero.mp (show W x * (∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ))) = 0 from ?_)).resolve_left (hW x)
    rw [Finset.mul_sum]
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hf]
    ring
  have hcont : Continuous (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp ((z i-(a:ℂ))*(t:ℂ))) := by fun_prop
  have hm := (ae_map_iff (Round175B.classLog_continuous K).measurable.aemeasurable
    (isClosed_eq hcont continuous_const).measurableSet).mpr hr
  rw [hmap] at hm
  have hm0 : ∀ᵐ t : ℝ ∂volume, ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp ((z i-(a:ℂ))*(t:ℂ)) = 0 := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hm0
  have hz' : Function.Injective (fun i => z i-(a:ℂ)) := by
    intro i j he
    apply hz
    linear_combination he
  exact finite_polynomial_exp_independent S (fun i => z i-(a:ℂ)) hz' p (congrFun hall)

#print axioms native_polynomial_blocks_independent
end SpectralH904

namespace SpectralCycle9B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped BigOperators

/-- Specialize the peer polynomial-block theorem to the actual mixed-order
native kernels. Orders are finite and variable at each distinct root. -/
theorem native_mixed_finite_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (N : ι → ℕ) (b : ι → ℕ → ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S, ∑ m ∈ Finset.range (N i),
      b i m * genuineNormalizedMellinJet K chi (z i) a s alpha m x = 0) :
    ∀ i ∈ S, ∀ m < N i, b i m = 0 := by
  classical
  let p : ι → Polynomial ℂ := fun i =>
    ∑ m ∈ Finset.range (N i), Polynomial.monomial m (b i m)
  have hf (i) (m) (x) :
      b i m * genuineNormalizedMellinJet K chi (z i) a s alpha m x =
      (b i m * (classLog K x:ℂ)^m) *
        genuineNormalizedMellinJet K chi (z i) a s alpha 0 x := by
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have hp : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) *
        genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0 := by
    filter_upwards [h] with x hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_monomial, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    exact (hf i m x).symm
  have hp0 := SpectralH904.native_polynomial_blocks_independent
    K chi mu c hc hmap z hz a s alpha S p hp
  intro i hi m hm
  have he := congrArg (fun q : Polynomial ℂ => q.coeff m) (hp0 i hi)
  simpa [p, Polynomial.coeff_monomial, hm] using he

#print axioms native_mixed_finite_independent
end SpectralCycle9B
