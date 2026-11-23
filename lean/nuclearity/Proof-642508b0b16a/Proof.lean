import Mathlib
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
namespace Round179G
open Round173A Round175A Round177G MeasureTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (G : Submodule ℂ H) [G.HasOrthogonalProjection]

/-- The scaled coefficient estimate is applied to the literal projected
quotient block, preserving every conditioning factor. -/
theorem scaled_projected_cost (n : ℕ)
    (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (psi : ℕ → H ⧸ G)
    (c : ℕ → ℂ) (b : ℕ → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hc : ∀ i, d * ‖c i‖ ≤ b i) :
    d * (∑ m ∈ Finset.range n,
      ‖(jetAction eta c m).comp (Q G)‖ * ‖S G (psi m)‖) ≤
        conditionedCost G n eta psi b := by
  apply (mul_le_mul_of_nonneg_left
    (projected_block_nuclear_cost G n eta c psi).2.1 hd).trans
  unfold blockCost conditionedCost
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro i hi
  calc
    d * ((m.choose i : ℝ) * ‖c i‖ * ‖eta (m-i)‖ * ‖psi m‖) =
      ((m.choose i : ℝ) * (d * ‖c i‖) * ‖eta (m-i)‖) * ‖psi m‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hc i) (Nat.cast_nonneg _)) (ContinuousLinearMap.opNorm_nonneg (eta (m-i))))
      (norm_nonneg (psi m))

/-- Interval height decay of the finite projected jet cost, at every
integration-by-parts order N, including log-multiplied tests (r=1).
The scalar f must still be identified with the native character slice.
No spectral summability, nuclearity, or conditioning bound is an input. -/
theorem interval_projected_jet_height_decay
    (f : ℝ → ℂ) (hf : ContDiff ℝ (↑(⊤ : ENat)) f)
    (hs : HasCompactSupport f) (N : ℕ) :
    ∃ R : ℕ → ℝ, (∀ j, 1 ≤ R j) ∧
      (∀ j, Integrable (iteratedDeriv N (fun x : ℝ => (x : ℂ)^j * f x))) ∧
      ∀ (alpha : ℝ), 0 ≤ alpha → ∀ z : ℂ, |z.re| ≤ alpha →
      ∀ (r n : ℕ) (eta : ℕ → (H ⧸ G) →L[ℂ] ℂ) (psi : ℕ → H ⧸ G),
      let c := fun i => (-1 : ℂ)^r * ∫ x : ℝ,
        ((x : ℂ)^(i+r) * f x) * Complex.exp (z * (x : ℂ))
      let b := fun i => Real.exp (alpha * R (i+r)) *
        ∫ x : ℝ, ‖iteratedDeriv N (fun t : ℝ => (t : ℂ)^(i+r) * f t) x‖
      ‖z‖^N * (∑ m ∈ Finset.range n,
        ‖(jetAction eta c m).comp (Q G)‖ * ‖S G (psi m)‖) ≤
          conditionedCost G n eta psi b := by
  have hdec (j : ℕ) := Round176D.log_mellin_decay_bound
    (fun x : ℝ => (x : ℂ)^j * f x)
    (fun k => (contDiff_iff_iteratedDeriv.mp
      ((Complex.ofRealCLM.contDiff.pow j).mul hf)).2 k (by simp))
    hs.mul_left N
  choose R hR using fun j => (hdec j).2
  refine ⟨R, fun j => (hR j).1, fun j => (hdec j).1, ?_⟩
  intro alpha ha z hz r n eta psi
  dsimp only
  apply scaled_projected_cost G n eta psi _ _ _ (by positivity)
  intro i
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using
    (hR (i+r)).2 alpha ha z hz

#check scaled_projected_cost
#print axioms scaled_projected_cost
#check interval_projected_jet_height_decay
#print axioms interval_projected_jet_height_decay
end Round179G
