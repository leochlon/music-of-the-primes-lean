import Mathlib
set_option linter.unusedSectionVars false
noncomputable section
namespace Round173A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The genuine normed quotient map, not an arbitrary surrogate. -/
def Q : H →L[ℂ] H ⧸ G :=
  G.mkQ.mkContinuous 1 (by intro x; simpa using Submodule.Quotient.norm_mk_le G x)

/-- Orthogonal representative, included in the ambient space. -/
def Slinear : (H ⧸ G) →ₗ[ℂ] H :=
  G.liftQ Gᗮ.starProjection.toLinearMap (by
    intro x hx
    change Gᗮ.starProjection x = 0
    simpa only [Submodule.starProjection_apply_eq_zero_iff,
      Submodule.orthogonal_orthogonal] using hx)

@[simp] theorem Slinear_mk (x : H) :
    Slinear G (G.mkQ x) = Gᗮ.starProjection x := rfl

/-- The quotient infimum, not the open mapping theorem, gives this bound. -/
theorem Slinear_contract (x : H ⧸ G) : ‖Slinear G x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt x hε
  have hp := Submodule.norm_starProjection_apply_le Gᗮ y
  change ‖Slinear G (Submodule.Quotient.mk y)‖ ≤ ‖y‖ at hp
  rw [hy] at hp
  exact hp.trans (le_of_lt hnorm)

def S : (H ⧸ G) →L[ℂ] H :=
  (Slinear G).mkContinuous 1 (by intro x; simpa using Slinear_contract G x)

@[simp] theorem S_Q (x : H) : S G (Q G x) = Gᗮ.starProjection x := rfl

/-- Construct the induced quotient action from invariance, without assuming
an operator identity or any nuclear estimate. -/
def AbarLinear (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) :
    (H ⧸ G) →ₗ[ℂ] H ⧸ G :=
  G.mapQ G A.toLinearMap hA

@[simp] theorem AbarLinear_Q (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    AbarLinear G A hA (Q G x) = Q G (A x) := rfl

/-- Exact algebraic factorisation with the quotient and genuine projector. -/
theorem quotient_projected_factorisation (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Gᗮ.starProjection (A x) = S G (AbarLinear G A hA (Q G x)) := rfl

theorem Q_S (x : H ⧸ G) : Q G (S G x) = x := by
  refine Submodule.Quotient.induction_on G x ?_
  intro y
  have hm : y - Gᗮ.starProjection y ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal y
  have hz : G.mkQ (y - Gᗮ.starProjection y) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).2 hm
  rw [map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

theorem S_isometry (x : H ⧸ G) : ‖S G x‖ = ‖x‖ := by
  apply le_antisymm (Slinear_contract G x)
  have hn := Submodule.Quotient.norm_mk_le G (S G x)
  change ‖Q G (S G x)‖ ≤ ‖S G x‖ at hn
  simpa only [Q_S] using hn

def Abar (A : H →L[ℂ] H) : (H ⧸ G) →L[ℂ] H ⧸ G :=
  (Q G).comp (A.comp (S G))

theorem Abar_Q (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G) (x : H) :
    Abar G A (Q G x) = Q G (A x) := by
  have hm : x - Gᗮ.starProjection x ∈ G := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Gᗮ.sub_starProjection_mem_orthogonal x
  have hz : G.mkQ (A (x - Gᗮ.starProjection x)) = 0 :=
    (Submodule.Quotient.mk_eq_zero G).2 (hA _ hm)
  rw [map_sub, map_sub] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The bounded-composition factorisation in (10.4.2.5), with its actual
quotient maps and map costs established. Native H/G/A attachment remains. -/
theorem bounded_quotient_factorisation (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    Gᗮ.starProjection.comp A = (S G).comp ((Abar G A).comp (Q G)) ∧
    ‖Q G‖ ≤ 1 ∧ ‖S G‖ ≤ 1 ∧ (∀ x : H ⧸ G, ‖S G x‖ = ‖x‖) := by
  refine ⟨?_, ?_, ?_, S_isometry G⟩
  · ext x
    change Gᗮ.starProjection (A x) = S G (Abar G A (Q G x))
    rw [Abar_Q G A hA, S_Q]
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · exact LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem S_mem (x : H ⧸ G) : S G x ∈ Gᗮ := by
  refine Submodule.Quotient.induction_on G x ?_
  intro y
  exact Gᗮ.starProjection_apply_mem y

theorem range_S : LinearMap.range (S G).toLinearMap = Gᗮ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact S_mem G x
  · intro hy
    refine ⟨Q G y, ?_⟩
    change S G (Q G y) = y
    rw [S_Q, Submodule.starProjection_eq_self_iff]
    exact hy

/-- The bounded representative formula is the induced quotient operator,
not just some operator on a space isomorphic to the quotient. -/
theorem Abar_eq_induced (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    (Abar G A).toLinearMap = AbarLinear G A hA := by
  ext x
  change Abar G A (Q G x) = AbarLinear G A hA (Q G x)
  rw [Abar_Q G A hA, AbarLinear_Q]

theorem manuscript_quotient_structure (A : H →L[ℂ] H)
    (hA : ∀ x ∈ G, A x ∈ G) :
    Gᗮ.starProjection.comp A = (S G).comp ((Abar G A).comp (Q G)) ∧
    (Abar G A).toLinearMap = AbarLinear G A hA ∧
    LinearMap.range (S G).toLinearMap = Gᗮ ∧
    (∀ x : H ⧸ G, Q G (S G x) = x) ∧
    ‖Q G‖ ≤ 1 ∧ ‖S G‖ ≤ 1 ∧ (∀ x : H ⧸ G, ‖S G x‖ = ‖x‖) := by
  obtain ⟨hf, hq, hs, hi⟩ := bounded_quotient_factorisation G A hA
  exact ⟨hf, Abar_eq_induced G A hA, range_S G, Q_S G, hq, hs, hi⟩

end Round173A

/-!
Round 174 A review implication: the rank-one ideal-property step in
manuscript (10.4.2.5), attached to the actual normed quotient and its
constructed orthogonal representative. The source above is retained from
A173. No native arithmetic identification or finite spectral cost is assumed
or concluded. Infinite costs below remain in ENNReal and may equal infinity.
-/
open scoped ENNReal
namespace Round174A
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The exact quotient representative transfers each actual rank-one term. -/
theorem quotient_rankOne_identity
    (f : (H ⧸ G) →L[ℂ] ℂ) (v : H ⧸ G) :
    (Round173A.S G).comp ((f.smulRight v).comp (Round173A.Q G)) =
      (f.comp (Round173A.Q G)).smulRight (Round173A.S G v) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    map_smul]

/-- No separately assumed bounds on Q or S: their native quotient norms
were derived in the retained source. -/
theorem quotient_rankOne_cost_le
    (f : (H ⧸ G) →L[ℂ] ℂ) (v : H ⧸ G) :
    ‖f.comp (Round173A.Q G)‖ * ‖Round173A.S G v‖ ≤ ‖f‖ * ‖v‖ := by
  have hQ : ‖Round173A.Q G‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hf : ‖f.comp (Round173A.Q G)‖ ≤ ‖f‖ := by
    calc
      _ ≤ ‖f‖ * ‖Round173A.Q G‖ := f.opNorm_comp_le _
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left hQ (ContinuousLinearMap.opNorm_nonneg f)
      _ = _ := mul_one _
  rw [Round173A.S_isometry]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg v)

/-- The absolute expansion cost cannot increase under S(-)Q. This theorem
does not assert that either extended-real sum is finite. -/
theorem quotient_expansion_cost_le {ι : Type*}
    (f : ι → (H ⧸ G) →L[ℂ] ℂ) (v : ι → H ⧸ G) :
    (∑' i, ENNReal.ofReal
      (‖(f i).comp (Round173A.Q G)‖ * ‖Round173A.S G (v i)‖)) ≤
      ∑' i, ENNReal.ofReal (‖f i‖ * ‖v i‖) := by
  apply ENNReal.tsum_le_tsum
  intro i
  exact ENNReal.ofReal_le_ofReal (quotient_rankOne_cost_le G (f i) (v i))

/-- Conditional reconstruction only: if a quotient expansion has been
derived, it represents convolution FIRST and genuine projection SECOND.
No nuclear summability or finiteness hypothesis occurs. -/
theorem projected_quotient_series_transfer {ι : Type*}
    (A : H →L[ℂ] H) (hA : ∀ x ∈ G, A x ∈ G)
    (f : ι → (H ⧸ G) →L[ℂ] ℂ) (v : ι → H ⧸ G)
    (hrep : ∀ q, HasSum (fun i => f i q • v i) (Round173A.Abar G A q)) :
    (∀ x, HasSum
      (fun i => ((f i).comp (Round173A.Q G)) x • Round173A.S G (v i))
      (Gᗮ.starProjection (A x))) ∧
    (∑' i, ENNReal.ofReal
      (‖(f i).comp (Round173A.Q G)‖ * ‖Round173A.S G (v i)‖)) ≤
      ∑' i, ENNReal.ofReal (‖f i‖ * ‖v i‖) := by
  refine ⟨?_, quotient_expansion_cost_le G f v⟩
  intro x
  have ht := (Round173A.S G).hasSum (hrep (Round173A.Q G x))
  simpa only [map_smul, ContinuousLinearMap.comp_apply,
    Round173A.Abar_Q G A hA, Round173A.S_Q] using ht

end Round174A


/-!
Round 175 A: FINITE_BINOMIAL_QUOTIENT_BLOCK_COST.
This is the finite rank-one estimate needed at manuscript 10.3.1.18--22,
retaining the actual functional/vector norm factors. It does not prove that
the spectral cost summed over all zeros and characters is finite. The arrays
must still be identified with genuine continuous quotient Mellin jets,
Mellin coefficients, and biorthogonal vectors. No such identification is
silently built into these arbitrary arrays.
-/
namespace Round175A
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]

def jetAction (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ) (m : ℕ) : E →L[ℂ] ℂ :=
  ∑ i ∈ Finset.range (m + 1), ((m.choose i : ℂ) * c i) • eta (m - i)

def block (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ)
    (psi : ℕ → E) : E →L[ℂ] E :=
  ∑ m ∈ Finset.range n, (jetAction eta c m).smulRight (psi m)

def blockCost (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ)
    (psi : ℕ → E) : ℝ :=
  ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range (m + 1),
    ((m.choose i : ℝ) * ‖c i‖ * ‖eta (m - i)‖) * ‖psi m‖

/-- The binomial jet action retains all derivative orders and norm factors. -/
theorem jetAction_norm_le (eta : ℕ → E →L[ℂ] ℂ) (c : ℕ → ℂ) (m : ℕ) :
    ‖jetAction eta c m‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖c i‖ * ‖eta (m - i)‖ := by
  unfold jetAction
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1),
        ‖((m.choose i : ℂ) * c i) • eta (m - i)‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_smul, norm_mul, Complex.norm_natCast]

/-- A finite nuclear representation cost, derived without a uniform
biorthogonal bound or any infinite summability hypothesis. -/
theorem block_representation_cost_le (n : ℕ) (eta : ℕ → E →L[ℂ] ℂ)
    (c : ℕ → ℂ) (psi : ℕ → E) :
    (∑ m ∈ Finset.range n, ‖jetAction eta c m‖ * ‖psi m‖) ≤
      blockCost n eta c psi := by
  unfold blockCost
  apply Finset.sum_le_sum
  intro m hm
  calc
    _ ≤ (∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖c i‖ * ‖eta (m - i)‖) * ‖psi m‖ :=
      mul_le_mul_of_nonneg_right (jetAction_norm_le eta c m) (norm_nonneg _)
    _ = _ := Finset.sum_mul _ _ _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- An explicit finite rank-one certificate on the ambient Hilbert space,
using the genuine quotient Q and orthogonal representative S. -/
theorem projected_block_certificate (n : ℕ)
    (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (c : ℕ → ℂ) (psi : ℕ → H ⧸ G) :
    (Round173A.S G).comp ((block n eta c psi).comp (Round173A.Q G)) =
      ∑ m ∈ Finset.range n,
        ((jetAction eta c m).comp (Round173A.Q G)).smulRight
          (Round173A.S G (psi m)) := by
  ext x
  simp [block, ContinuousLinearMap.sum_apply, map_sum]

/-- This is a finite block bound only, not the full leading nuclear bound.
It supplies the conditioned finite cost required by the manuscript's
spectral proof before infinite summation and native identification. -/
theorem projected_block_nuclear_cost (n : ℕ)
    (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (c : ℕ → ℂ) (psi : ℕ → H ⧸ G) :
    (Round173A.S G).comp ((block n eta c psi).comp (Round173A.Q G)) =
      ∑ m ∈ Finset.range n,
        ((jetAction eta c m).comp (Round173A.Q G)).smulRight
          (Round173A.S G (psi m)) ∧
    (∑ m ∈ Finset.range n,
      ‖(jetAction eta c m).comp (Round173A.Q G)‖ * ‖Round173A.S G (psi m)‖)
      ≤ blockCost n eta c psi ∧
    ENNReal.ofReal (blockCost n eta c psi) < ⊤ := by
  refine ⟨projected_block_certificate G n eta c psi, ?_, ENNReal.ofReal_lt_top⟩
  calc
    _ ≤ ∑ m ∈ Finset.range n, ‖jetAction eta c m‖ * ‖psi m‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact Round174A.quotient_rankOne_cost_le G _ _
    _ ≤ _ := block_representation_cost_le n eta c psi

end Round175A
namespace Round177G
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]
def conditionedCost (n : ℕ) (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ)
    (psi : ℕ → H ⧸ G) (b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, ∑ i ∈ Finset.range (m+1),
    ((m.choose i : ℝ) * b i * ‖eta (m-i)‖) * ‖psi m‖


end Round177G
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Round176D
/-- Compact logarithmic-coordinate integration by parts for (10.3.2.8).
This is a premise of the interval argument, not a nuclearity statement. -/
theorem log_mellin_ibp (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hdf : Continuous (deriv f)) (hs : HasCompactSupport f) (z : ℂ) :
    (∫ x : ℝ, deriv f x * Complex.exp (z * (x : ℂ))) =
      -z * ∫ x : ℝ, f x * Complex.exp (z * (x : ℂ)) := by
  let E : ℝ → ℂ := fun x => Complex.exp (z * (x : ℂ))
  have hc : Continuous E := by fun_prop
  have hd (x : ℝ) : HasDerivAt E (z * E x) x := by
    have h : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    convert (h.const_mul z).cexp using 1
    simp [E, mul_comm]
  obtain ⟨R, hR⟩ := hs.bddAbove_image continuous_abs.continuousOn
  have hz0 (x : ℝ) (hx : R < |x|) : f x = 0 := by
    by_contra hn
    exact (not_lt_of_ge (hR ⟨x, subset_closure hn, rfl⟩)) hx
  have ht : Tendsto (f * E) atTop (𝓝 0) := by
    have he : (f * E) =ᶠ[atTop] fun _ => 0 := by
      filter_upwards [eventually_gt_atTop R] with x hx
      simp [Pi.mul_apply, hz0 x (hx.trans_le (le_abs_self x))]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have hb : Tendsto (f * E) atBot (𝓝 0) := by
    have he : (f * E) =ᶠ[atBot] fun _ => 0 := by
      filter_upwards [eventually_lt_atBot (-R)] with x hx
      have h : R < |x| := lt_of_lt_of_le (by linarith) (neg_le_abs x)
      simp [Pi.mul_apply, hz0 x h]
    exact (tendsto_congr' he).mpr tendsto_const_nhds
  have h1 : Integrable (f * fun x => z * E x) :=
    (hf.continuous.mul (continuous_const.mul hc)).integrable_of_hasCompactSupport hs.mul_right
  have h2 : Integrable (deriv f * E) :=
    (hdf.mul hc).integrable_of_hasCompactSupport hs.deriv.mul_right
  have hi := integral_mul_deriv_eq_deriv_mul (fun x => (hf x).hasDerivAt) hd h1 h2 hb ht
  have hi' : z * (∫ x : ℝ, f x * E x) = -(∫ x : ℝ, deriv f x * E x) := by
    simpa only [sub_self, zero_sub, ← integral_const_mul, mul_left_comm] using hi
  change (∫ x : ℝ, deriv f x * E x) = -z * (∫ x : ℝ, f x * E x)
  linear_combination hi'

/-- Every finite number of integrations by parts, with all boundary terms
proved zero by compact support; no spectral finiteness is an input. -/
theorem log_mellin_iterated_ibp (f : ℝ → ℂ)
    (hf : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n f))
    (hs : HasCompactSupport f) (z : ℂ) (n : ℕ) :
    (∫ x : ℝ, iteratedDeriv n f x * Complex.exp (z * (x : ℂ))) =
      (-z)^n * ∫ x : ℝ, f x * Complex.exp (z * (x : ℂ)) := by
  have hc (j : ℕ) : HasCompactSupport (iteratedDeriv j f) := by
    induction j with
    | zero => simpa using hs
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,
      log_mellin_ibp (iteratedDeriv n f) (hf n)
        (by simpa only [iteratedDeriv_succ] using (hf (n+1)).continuous) (hc n), ih]
    ring

#check log_mellin_ibp
#print axioms log_mellin_ibp
#check log_mellin_iterated_ibp
#print axioms log_mellin_iterated_ibp

/-- The finite analytic cost in the logarithmic-coordinate step of
(10.3.2.8), at every integration-by-parts order. The derivative cost is
retained, not replaced by an unjustified order-independent constant. -/
theorem log_mellin_decay_bound (f : ℝ → ℂ)
    (hf : ∀ n : ℕ, Differentiable ℝ (iteratedDeriv n f))
    (hs : HasCompactSupport f) (n : ℕ) :
    Integrable (iteratedDeriv n f) ∧ ∃ R : ℝ, 1 ≤ R ∧
      ∀ (alpha : ℝ), 0 ≤ alpha → ∀ (z : ℂ), |z.re| ≤ alpha →
      ‖z‖^n * ‖∫ x : ℝ, f x * Complex.exp (z * (x : ℂ))‖ ≤
        Real.exp (alpha * R) * ∫ x : ℝ, ‖iteratedDeriv n f x‖ := by
  have hc (j : ℕ) : HasCompactSupport (iteratedDeriv j f) := by
    induction j with
    | zero => simpa using hs
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hi : Integrable (iteratedDeriv n f) volume :=
    (hf n).continuous.integrable_of_hasCompactSupport (hc n)
  obtain ⟨B, hB⟩ := (hc n).bddAbove_image continuous_abs.continuousOn
  let R := max 1 B
  refine ⟨hi, R, le_max_left _ _, ?_⟩
  intro alpha ha z hz
  have hn := congrArg norm (log_mellin_iterated_ibp f hf hs z n)
  simp only [norm_mul, norm_pow, norm_neg] at hn
  rw [← hn]
  have hp (x : ℝ) :
      ‖iteratedDeriv n f x * Complex.exp (z * (x : ℂ))‖ ≤
        Real.exp (alpha * R) * ‖iteratedDeriv n f x‖ := by
    by_cases he : iteratedDeriv n f x = 0
    · simp [he]
    have hr : |x| ≤ R :=
      (hB ⟨x, subset_closure he, rfl⟩).trans (le_max_right _ _)
    have hzR : (z * (x : ℂ)).re ≤ alpha * R := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc
        z.re * x ≤ |z.re * x| := le_abs_self _
        _ = |z.re| * |x| := abs_mul _ _
        _ ≤ alpha * R := mul_le_mul hz hr (abs_nonneg _) ha
    rw [norm_mul, Complex.norm_exp]
    calc
      _ ≤ ‖iteratedDeriv n f x‖ * Real.exp (alpha * R) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzR) (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∫ x : ℝ, Real.exp (alpha * R) * ‖iteratedDeriv n f x‖ :=
      norm_integral_le_of_norm_le (hi.norm.const_mul _) (Eventually.of_forall hp)
    _ = _ := integral_const_mul _ _

#check log_mellin_decay_bound
#print axioms log_mellin_decay_bound
end Round176D

namespace Round177D
/-- The actual logarithmic polynomial derivative, over the real integration
variable with complex values. Used only in the variable-order interval cost. -/
theorem log_power_derivative (m k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (t : ℂ)^m) x =
      (m.descFactorial k : ℂ) * (x : ℂ)^(m-k) := by
  have h (j : ℕ) : iteratedDeriv j (fun t : ℝ => (t : ℂ)^m) =
      fun t => ((iteratedDeriv j (fun u : ℝ => u^m) t : ℝ) : ℂ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have hd : Differentiable ℝ (iteratedDeriv j (fun u : ℝ => u^m)) :=
        (contDiff_iff_iteratedDeriv.mp (contDiff_id.pow m : ContDiff ℝ (↑(⊤ : ENat)) _)).2 j (by simp)
      simpa only [iteratedDeriv_succ] using (hd t).hasDerivAt.ofReal_comp.deriv
  rw [h]
  simp only [iteratedDeriv_pow, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow]

/-- Exact finite Leibniz L1 cost for arbitrary logarithmic moment order.
The support power and descending factorial omitted in (10.3.2.10) are retained.
This discharges the derivative-cost subpremise of the interval p=1 estimate;
it does not assume any spectral summability or quotient nuclearity. -/
theorem log_moment_leibniz_cost (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ENat)) f)
    (hs : HasCompactSupport f) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ m n : ℕ,
      Integrable (iteratedDeriv n (fun x : ℝ => (x : ℂ)^m * f x)) ∧
      (∫ x : ℝ, ‖iteratedDeriv n (fun x : ℝ => (x : ℂ)^m * f x) x‖) ≤
        ∑ i ∈ Finset.range (n+1),
          (n.choose i : ℝ) * (m.descFactorial i : ℝ) * R^(m-i) *
            ∫ x : ℝ, ‖iteratedDeriv (n-i) f x‖ := by
  have hd (j : ℕ) : Differentiable ℝ (iteratedDeriv j f) :=
    (contDiff_iff_iteratedDeriv.mp hf).2 j (by simp)
  have hsub (j : ℕ) : tsupport (iteratedDeriv j f) ⊆ tsupport f := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact (closure_minimal support_deriv_subset isClosed_closure).trans ih
  have hcompact (j : ℕ) : HasCompactSupport (iteratedDeriv j f) := by
    induction j with
    | zero => simpa using hs
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hi (j : ℕ) : Integrable (iteratedDeriv j f) volume :=
    (hd j).continuous.integrable_of_hasCompactSupport (hcompact j)
  obtain ⟨B, hB⟩ := hs.bddAbove_image continuous_abs.continuousOn
  let R := max 1 B
  refine ⟨R, le_max_left _ _, ?_⟩
  intro m n
  let g : ℝ → ℂ := fun x => (x : ℂ)^m * f x
  have hp : ContDiff ℝ (↑(⊤ : ENat)) (fun x : ℝ => (x : ℂ)^m) := Complex.ofRealCLM.contDiff.pow m
  have hg : ContDiff ℝ (↑(⊤ : ENat)) g := hp.mul hf
  have hgs : HasCompactSupport g := hs.mul_left
  have hgc (j : ℕ) : HasCompactSupport (iteratedDeriv j g) := by
    induction j with
    | zero => simpa using hgs
    | succ j ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hgi : Integrable (iteratedDeriv n g) volume :=
    ((contDiff_iff_iteratedDeriv.mp hg).1 n (by simp)).integrable_of_hasCompactSupport (hgc n)
  refine ⟨hgi, ?_⟩
  let c : ℕ → ℝ := fun i => (n.choose i : ℝ) * (m.descFactorial i : ℝ) * R^(m-i)
  have hpoint (x : ℝ) : ‖iteratedDeriv n g x‖ ≤
      ∑ i ∈ Finset.range (n+1), c i * ‖iteratedDeriv (n-i) f x‖ := by
    have he := iteratedDeriv_mul ((contDiff_infty.mp hp) n).contDiffAt
      ((contDiff_infty.mp hf) n).contDiffAt (n := n) (x := x)
    change ‖iteratedDeriv n ((fun t : ℝ => (t : ℂ)^m) * f) x‖ ≤ _
    rw [he]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i hi
    rw [log_power_derivative]
    by_cases hz : iteratedDeriv (n-i) f x = 0
    · simp [hz]
    have hx : |x| ≤ R :=
      (hB ⟨x, hsub (n-i) (subset_closure hz), rfl⟩).trans (le_max_right _ _)
    have hh : ‖(x : ℂ)‖^(m-i) ≤ R^(m-i) := by
      simpa using pow_le_pow_left₀ (abs_nonneg x) hx (m-i)
    simp only [norm_mul, norm_pow, norm_natCast]
    dsimp [c]
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ (n.choose i : ℝ) * (m.descFactorial i : ℝ) by positivity)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hmul
      (norm_nonneg (iteratedDeriv (n-i) f x))
  have hci (i : ℕ) : Integrable (fun x : ℝ => c i * ‖iteratedDeriv (n-i) f x‖) volume :=
    (hi (n-i)).norm.const_mul _
  calc
    _ ≤ ∫ x : ℝ, ∑ i ∈ Finset.range (n+1), c i * ‖iteratedDeriv (n-i) f x‖ :=
      integral_mono hgi.norm (integrable_finset_sum _ (fun i _ => hci i)) hpoint
    _ = _ := by rw [integral_finset_sum _ (fun i _ => hci i)]; simp only [integral_const_mul, c]

#check log_power_derivative
#print axioms log_power_derivative
#check log_moment_leibniz_cost
#print axioms log_moment_leibniz_cost
end Round177D

namespace Round179D
/-- The repaired variable-jet-order strip estimate needed in manuscript
(10.3.2.8)--(10.3.2.11). A single radius works for ALL moment and decay
orders. This is the analytic coefficient premise, not spectral nuclearity. -/
theorem variable_order_strip_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ENat)) f) (hs : HasCompactSupport f) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (m n : ℕ) (alpha : ℝ), 0 ≤ alpha →
      ∀ z : ℂ, |z.re| ≤ alpha →
      ‖z‖^n * ‖∫ x : ℝ, (x : ℂ)^m * f x * Complex.exp (z * (x : ℂ))‖ ≤
        Real.exp (alpha * R) *
          ∑ i ∈ Finset.range (n+1),
            (n.choose i : ℝ) * (m.descFactorial i : ℝ) * R^(m-i) *
              ∫ x : ℝ, ‖iteratedDeriv (n-i) f x‖ := by
  obtain ⟨R₀, hR₀, hcost⟩ := Round177D.log_moment_leibniz_cost f hf hs
  obtain ⟨B, hB⟩ := hs.bddAbove_image continuous_abs.continuousOn
  let R := max R₀ B
  have hR : 1 ≤ R := hR₀.trans (le_max_left _ _)
  refine ⟨R, hR, ?_⟩
  intro m n alpha ha z hz
  let g : ℝ → ℂ := fun x => (x : ℂ)^m * f x
  have hg : ContDiff ℝ (↑(⊤ : ENat)) g :=
    (Complex.ofRealCLM.contDiff.pow m).mul hf
  have hgd (j : ℕ) : Differentiable ℝ (iteratedDeriv j g) :=
    (contDiff_iff_iteratedDeriv.mp hg).2 j (by simp)
  have hgs : HasCompactSupport g := hs.mul_left
  have hsub (j : ℕ) : tsupport (iteratedDeriv j g) ⊆ tsupport f := by
    induction j with
    | zero =>
      simpa only [iteratedDeriv_zero] using
        (closure_minimal (show Function.support g ⊆ tsupport f from
          fun x hx => subset_closure (fun h => hx (by simp [g, h]))) isClosed_closure)
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact (closure_minimal support_deriv_subset isClosed_closure).trans ih
  have hi : Integrable (iteratedDeriv n g) := (hcost m n).1
  have he := congrArg norm (Round176D.log_mellin_iterated_ibp g hgd hgs z n)
  simp only [norm_mul, norm_pow, norm_neg] at he
  change ‖z‖^n * ‖∫ x : ℝ, g x * Complex.exp (z * (x : ℂ))‖ ≤ _
  rw [← he]
  have hp (x : ℝ) : ‖iteratedDeriv n g x * Complex.exp (z * (x : ℂ))‖ ≤
      Real.exp (alpha * R) * ‖iteratedDeriv n g x‖ := by
    by_cases hx : iteratedDeriv n g x = 0
    · simp [hx]
    have hxR : |x| ≤ R :=
      (hB ⟨x, hsub n (subset_closure hx), rfl⟩).trans (le_max_right _ _)
    have hzR : (z * (x : ℂ)).re ≤ alpha * R := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact (le_abs_self (z.re * x)).trans
        ((abs_mul _ _).le.trans (mul_le_mul hz hxR (abs_nonneg _) ha))
    rw [norm_mul, Complex.norm_exp]
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzR)
      (norm_nonneg _)).trans_eq (mul_comm _ _)
  calc
    _ ≤ ∫ x : ℝ, Real.exp (alpha * R) * ‖iteratedDeriv n g x‖ :=
      norm_integral_le_of_norm_le (hi.norm.const_mul _) (Eventually.of_forall hp)
    _ = Real.exp (alpha * R) * ∫ x : ℝ, ‖iteratedDeriv n g x‖ := integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      refine (hcost m n).2.trans (Finset.sum_le_sum ?_)
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (integral_nonneg (fun x => norm_nonneg _))
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by linarith) (le_max_left _ _) _

#check variable_order_strip_decay
#print axioms variable_order_strip_decay
end Round179D

namespace Round179D
/-- Explicit order growth in the coefficient cost: only R^m (m+1)^n
remains, while the test seminorm is independent of the jet order m.
This is the form needed to combine logarithmic multiplicity with height decay. -/
theorem variable_order_polynomial_cost (f : ℝ → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ENat)) f) (hs : HasCompactSupport f) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (m n : ℕ) (alpha : ℝ), 0 ≤ alpha →
      ∀ z : ℂ, |z.re| ≤ alpha →
      ‖z‖^n * ‖∫ x : ℝ, (x : ℂ)^m * f x * Complex.exp (z * (x : ℂ))‖ ≤
        Real.exp (alpha * R) * (R^m * ((m : ℝ)+1)^n *
          ∑ i ∈ Finset.range (n+1),
            (n.choose i : ℝ) * ∫ x : ℝ, ‖iteratedDeriv (n-i) f x‖) := by
  obtain ⟨R, hR, hb⟩ := variable_order_strip_decay f hf hs
  refine ⟨R, hR, ?_⟩
  intro m n alpha ha z hz
  refine (hb m n alpha ha z hz).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hd : (m.descFactorial i : ℝ) ≤ ((m : ℝ)+1)^n := by
    calc
      _ ≤ (m : ℝ)^i := by exact_mod_cast Nat.descFactorial_le_pow m i
      _ ≤ ((m : ℝ)+1)^i := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ (by have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith) hin
  have hp : R^(m-i) ≤ R^m := pow_le_pow_right₀ hR (Nat.sub_le _ _)
  have hpair := mul_le_mul hd hp (pow_nonneg (by linarith : 0 ≤ R) _) (by positivity)
  have hc := mul_le_mul_of_nonneg_left hpair (show 0 ≤ (n.choose i : ℝ) by positivity)
  have ht := mul_le_mul_of_nonneg_right hc
    (integral_nonneg (μ := volume) (fun x : ℝ => norm_nonneg (iteratedDeriv (n-i) f x)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using ht

#check variable_order_polynomial_cost
#print axioms variable_order_polynomial_cost
end Round179D

namespace Round180G
open Round173A Round175A Round177G
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- Explicit finite projected cost for unbounded jet multiplicity. The
conditioning sum is computed from the actual supplied vectors; no bound
on it, or on an infinite sum, is assumed. Native attachment remains. -/
theorem uniform_projected_jet_cost
    (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ENat)) f)
    (hs : HasCompactSupport f) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (N : ℕ) (alpha : ℝ), 0 ≤ alpha →
      ∀ z : ℂ, |z.re| ≤ alpha → ∀ (r n : ℕ)
      (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (psi : ℕ → H ⧸ G),
      let c := fun i => (-1 : ℂ)^r * ∫ x : ℝ,
        (x : ℂ)^(i+r) * f x * Complex.exp (z * (x : ℂ))
      let D := ∑ j ∈ Finset.range (N+1),
        (N.choose j : ℝ) * ∫ x : ℝ, ‖iteratedDeriv (N-j) f x‖
      let C := Real.exp (alpha * R) * (R^(n+r) * ((n+r : ℕ)+1 : ℝ)^N * D)
      (S G).comp ((block n eta c psi).comp (Q G)) =
        ∑ m ∈ Finset.range n,
          ((jetAction eta c m).comp (Q G)).smulRight (S G (psi m)) ∧
      ‖z‖^N * (∑ m ∈ Finset.range n,
        ‖(jetAction eta c m).comp (Q G)‖ * ‖S G (psi m)‖) ≤
        C * conditionedCost G n eta psi (fun _ => 1) := by
  obtain ⟨R, hR, hb⟩ := Round179D.variable_order_polynomial_cost f hf hs
  refine ⟨R, hR, ?_⟩
  intro N alpha ha z hz r n eta psi c D C
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _)
      (integral_nonneg (fun x => norm_nonneg _)))
  have hc (i : ℕ) (hi : i < n) : ‖z‖^N * ‖c i‖ ≤ C := by
    have hir : i+r ≤ n+r := Nat.add_le_add_right (Nat.le_of_lt hi) r
    have hp : R^(i+r) ≤ R^(n+r) := pow_le_pow_right₀ hR hir
    have hiR : ((i+r : ℕ) : ℝ)+1 ≤ ((n+r : ℕ) : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right hir 1
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ((i+r : ℕ) : ℝ)+1) hiR N
    calc
      _ ≤ Real.exp (alpha * R) * (R^(i+r) * (((i+r : ℕ) : ℝ)+1)^N * D) := by
        simpa only [c, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
          using hb (i+r) N alpha ha z hz
      _ ≤ C := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hp hpow (by positivity) (pow_nonneg (by linarith) _)) hD
  refine ⟨projected_block_certificate G n eta c psi, ?_⟩
  refine (mul_le_mul_of_nonneg_left
    (projected_block_nuclear_cost G n eta c psi).2.1 (by positivity : 0 ≤ ‖z‖^N)).trans ?_
  unfold blockCost conditionedCost
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    (Finset.mem_range.mp hm)
  calc
    ‖z‖^N * ((m.choose i : ℝ) * ‖c i‖ * ‖eta (m-i)‖ * ‖psi m‖) =
      (m.choose i : ℝ) * (‖z‖^N * ‖c i‖) * ‖eta (m-i)‖ * ‖psi m‖ := by ring
    _ ≤ (m.choose i : ℝ) * C * ‖eta (m-i)‖ * ‖psi m‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hc i hin) (Nat.cast_nonneg _))
          (ContinuousLinearMap.opNorm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

#check uniform_projected_jet_cost
#print axioms uniform_projected_jet_cost
end Round180G
