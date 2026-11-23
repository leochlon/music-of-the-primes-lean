import Mathlib
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

/-! Participant D, round 1. Direct premise: removing bounded cutoffs from
Definition 10.4.3.7's complement-kernel diagonal at phi(C_K^1)=0.
This is a CONDITIONAL analytic interface: kspec must still be attached to the
actual A(phi) after Pspec and its integrable smoothed diagonal established.
It neither defines a substitute spectral operator nor proves nuclearity. -/
namespace GeometricRound1D
open MasulloGRH MeasureTheory Filter
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]

/-- Actual product-formula modulus descended to genuine idele classes. -/
noncomputable def classModulus : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (genuineIdeleModulus K) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul])

theorem classModulus_one : classModulus K 1 = 1 := by
  change genuineIdeleModulus K 1 = 1
  simpa only [map_one] using genuineIdeleModulus_principal K 1

/-- Exactly the test restriction of Theorem 12.5.1.1, not merely phi(1)=0. -/
def NormOneVanishing (phi : HeckeIdeleClasses K → ℂ) : Prop :=
  ∀ x, classModulus K x = 1 → phi x = 0

/-- Formula (10.4.3.50); kspec is an unfilled spectral-kernel interface. -/
def complementKernel (phi : HeckeIdeleClasses K → ℂ)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ :=
  phi (x * y⁻¹) - kspec x y

/-- Discharges the convolution-diagonal cancellation needed in (12.5.1.4).
Representative regularity and attachment to the actual operator remain open. -/
theorem complement_diagonal (phi : HeckeIdeleClasses K → ℂ)
    (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K) :
    complementKernel K phi kspec x x = -kspec x x := by
  have h1 : phi 1 = 0 := hphi 1 (classModulus_one K)
  simp [complementKernel, h1]

/-- Positivity is derived from the actual local absolute values. -/
theorem classModulus_pos (x : HeckeIdeleClasses K) : 0 < classModulus K x := by
  induction x using Quotient.inductionOn with
  | h y =>
    change 0 < genuineIdeleModulus K y
    have hn : 0 ≤ genuineIdeleModulus K y := by
      unfold genuineIdeleModulus
      exact mul_nonneg (Finset.prod_nonneg (fun _ _ => pow_nonneg (norm_nonneg _) _))
        (finprod_nonneg (fun _ => norm_nonneg _))
    exact lt_of_le_of_ne hn (genuineIdeleModulus_ne_zero K y).symm

/-- Discharges pointwise cutoff convergence on the actual quotient whenever
the plateau endpoints tend to 0 and infinity, respectively. For paper cutoffs
these endpoints are 1/Lambda+epsilon and Lambda-epsilon. -/
theorem cutoff_tendsto_one
    (lower upper : ℕ → ℝ)
    (hlower : Tendsto lower atTop (𝓝 0))
    (hupper : Tendsto upper atTop atTop)
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hplateau : ∀ n x, lower n ≤ classModulus K x →
      classModulus K x ≤ upper n → rho n x = 1)
    (x : HeckeIdeleClasses K) :
    Tendsto (fun n => rho n x) atTop (𝓝 1) := by
  have hlo : ∀ᶠ n in atTop, lower n < classModulus K x :=
    (tendsto_order.1 hlower).2 _ (classModulus_pos K x)
  have hhi : ∀ᶠ n in atTop, classModulus K x ≤ upper n :=
    hupper.eventually (eventually_ge_atTop _)
  have he : ∀ᶠ n in atTop, (1 : ℂ) = rho n x := by
    filter_upwards [hlo, hhi] with n hn hn'
    exact (hplateau n x hn.le hn').symm
  exact tendsto_const_nhds.congr' he

/-- CONDITIONAL cutoff-removal interface on the genuine arithmetic quotient.
The sole diagonal integrability premise is explicit; this theorem does not
supply it from nuclearity, or identify kspec with a smoothed operator kernel. -/
theorem complement_diagonal_cutoff_limit
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hdiag : Integrable (fun x => kspec x x) mu)
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hmeas : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi kspec x x ∂mu)
      atTop (𝓝 (- ∫ x, kspec x x ∂mu)) := by
  have hg : Integrable (fun x => complementKernel K phi kspec x x) mu := by
    simpa only [complement_diagonal K phi hphi kspec] using hdiag.neg
  have ht : Tendsto
      (fun n => ∫ x, rho n x * complementKernel K phi kspec x x ∂mu)
      atTop (𝓝 (∫ x, complementKernel K phi kspec x x ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => ‖complementKernel K phi kspec x x‖)
    · intro n
      exact (hmeas n).mul hg.aestronglyMeasurable
    · exact hg.norm
    · intro n
      filter_upwards [hbound n] with x hx
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx
    · filter_upwards [hlim] with x hx
      simpa using hx.mul_const (complementKernel K phi kspec x x)
  simpa only [complement_diagonal K phi hphi kspec, integral_neg] using ht

/-- Combined conditional cutoff-removal statement with geometric plateau data;
pointwise convergence is now proved, not taken as a hypothesis. -/
theorem plateau_complement_diagonal_cutoff_limit
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hdiag : Integrable (fun x => kspec x x) mu)
    (lower upper : ℕ → ℝ)
    (hlower : Tendsto lower atTop (𝓝 0))
    (hupper : Tendsto upper atTop atTop)
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hmeas : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hplateau : ∀ n x, lower n ≤ classModulus K x →
      classModulus K x ≤ upper n → rho n x = 1) :
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi kspec x x ∂mu)
      atTop (𝓝 (- ∫ x, kspec x x ∂mu)) := by
  apply complement_diagonal_cutoff_limit K mu phi hphi kspec hdiag rho hmeas hbound
  exact Filter.Eventually.of_forall
    (cutoff_tendsto_one K lower upper hlower hupper rho hplateau)

#check plateau_complement_diagonal_cutoff_limit
#print axioms plateau_complement_diagonal_cutoff_limit
#check complement_diagonal_cutoff_limit
#print axioms complement_diagonal_cutoff_limit
end GeometricRound1D


/-! Round 2 review: the next missing cutoff premise from Definition 9.3.3.1.
This adds the actual endpoint regime to the retained round-1 conditional result.
No kernel attachment, nuclearity, trace identity, or summability is assumed proved. -/
namespace GeometricRound2D
open Filter MeasureTheory MasulloGRH GeometricRound1D
open scoped Topology

/-- Discharges exactly the endpoint-limit premise of the plateau cutoff lemma
for the manuscript regime Lambda -> infinity and epsilon * Lambda -> 0. -/
theorem manuscript_cutoff_endpoints (L e : ℕ → ℝ)
    (hL : Tendsto L atTop atTop)
    (heL : Tendsto (fun n => e n * L n) atTop (𝓝 0)) :
    Tendsto (fun n => 1 / L n + e n) atTop (𝓝 0) ∧
      Tendsto (fun n => L n - e n) atTop atTop := by
  have hi : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hL
  have hn : ∀ᶠ n in atTop, L n ≠ 0 := by
    filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    exact ne_of_gt hn
  have he : Tendsto e atTop (𝓝 0) := by
    have h := heL.mul hi
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [hn] with n hn
    field_simp [hn]
  constructor
  · simpa only [one_div, zero_add] using hi.add he
  · apply tendsto_atTop.2
    intro b
    have hsmall : ∀ᶠ n in atTop, e n < 1 :=
      (tendsto_order.1 he).2 1 (by norm_num)
    filter_upwards [hL.eventually (eventually_ge_atTop (b + 1)), hsmall] with n hn hs
    linarith

/-- CONDITIONAL arithmetic cutoff reduction for (12.5.1.4), now with the
manuscript's actual endpoint formulas and asymptotic regime. The genuine
class quotient/modulus and exact norm-one vanishing are retained. kspec and
mu must still be attached to the actual smoothed kernel and global Haar measure. -/
theorem manuscript_cutoff_limit
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hdiag : Integrable (fun x => kspec x x) mu)
    (L e : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (heL : Tendsto (fun n => e n * L n) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hmeas : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hbound : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hplateau : ∀ n x, 1 / L n + e n ≤ classModulus K x →
      classModulus K x ≤ L n - e n → rho n x = 1) :
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi kspec x x ∂mu)
      atTop (𝓝 (- ∫ x, kspec x x ∂mu)) := by
  obtain ⟨hlo, hhi⟩ := manuscript_cutoff_endpoints L e hL heL
  exact plateau_complement_diagonal_cutoff_limit K mu phi hphi kspec hdiag
    (fun n => 1 / L n + e n) (fun n => L n - e n) hlo hhi
    rho hmeas hbound hplateau

#check GeometricRound2D.manuscript_cutoff_endpoints
#print axioms GeometricRound2D.manuscript_cutoff_endpoints
#check GeometricRound2D.manuscript_cutoff_limit
#print axioms GeometricRound2D.manuscript_cutoff_limit
end GeometricRound2D

/-! Round 3 D: repair the precise multiplier premise in A.5.4.16 used by
12.1.1.2(2), 12.1.1.3 and 12.2.2.2(4). Absolute normalized averages must be
bounded; convergence of signed averages alone is insufficient. This is a
CONDITIONAL analytic interface, not a new arithmetic operator or trace. -/
namespace GeometricRound3D
open MeasureTheory Filter MasulloGRH
open scoped Topology

/-- The normalization factor is retained on the absolute integral. -/
theorem normalized_multiplier_error_bound
    {X : Type*} [MeasurableSpace X] (nu : Measure X)
    (f m : X → ℂ) (m0 : ℂ) (b e C : ℝ)
    (hb : 0 ≤ b) (he : 0 ≤ e)
    (hf : Integrable f nu) (hmf : Integrable (fun z => m z * f z) nu)
    (hosc : ∀ᵐ z ∂nu, ‖m z - m0‖ ≤ e)
    (habs : b * (∫ z, ‖f z‖ ∂nu) ≤ C) :
    ‖(b : ℂ) * (∫ z, m z * f z ∂nu) -
      m0 * ((b : ℂ) * (∫ z, f z ∂nu))‖ ≤ e * C := by
  have hint : Integrable (fun z => (m z - m0) * f z) nu := by
    simpa only [sub_mul] using hmf.sub (hf.const_mul m0)
  have hid : (b : ℂ) * (∫ z, m z * f z ∂nu) -
      m0 * ((b : ℂ) * (∫ z, f z ∂nu)) =
      (b : ℂ) * (∫ z, (m z - m0) * f z ∂nu) := by
    simp only [sub_mul, integral_sub hmf (hf.const_mul m0), integral_const_mul]
    ring
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  calc
    b * ‖∫ z, (m z - m0) * f z ∂nu‖ ≤
        b * (∫ z, ‖(m z - m0) * f z‖ ∂nu) :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hb
    _ ≤ b * (∫ z, e * ‖f z‖ ∂nu) := by
      apply mul_le_mul_of_nonneg_left _ hb
      apply integral_mono_ae hint.norm (hf.norm.const_mul e)
      filter_upwards [hosc] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    _ = e * (b * (∫ z, ‖f z‖ ∂nu)) := by
      rw [integral_const_mul]
      ring
    _ ≤ e * C := mul_le_mul_of_nonneg_left habs he

/-- CONDITIONAL normalized rectangle smoothing on the genuine idele-class
quotient. Discharges multiplier passage at a fixed diagonal point, once the
actual kernel has bounded normalized absolute averages there. nu_n is exactly
the restriction of the supplied product measure to V_n × V_n; b_n is its
inverse real mass. Haar attachment, positive finite masses, shrinking V_n,
continuity-to-oscillation, and nuclear maximal bounds remain to instantiate. -/
theorem idele_diagonal_multiplier_limit
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [SigmaFinite mu]
    (V : ℕ → Set (HeckeIdeleClasses K))
    (k m : HeckeIdeleClasses K × HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K) (ell : ℂ) (e : ℕ → ℝ) (C : ℝ)
    (he : ∀ n, 0 ≤ e n) (helim : Tendsto e atTop (𝓝 0))
    (hk : ∀ n, IntegrableOn k (V n ×ˢ V n) (mu.prod mu))
    (hmk : ∀ n, IntegrableOn (fun z => m z * k z) (V n ×ˢ V n) (mu.prod mu))
    (hosc : ∀ n, ∀ᵐ z ∂(mu.prod mu).restrict (V n ×ˢ V n),
      ‖m z - m (x,x)‖ ≤ e n)
    (habs : ∀ n, ((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ *
      (∫ z in V n ×ˢ V n, ‖k z‖ ∂mu.prod mu) ≤ C)
    (hlim : Tendsto (fun n =>
      (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
        (∫ z in V n ×ˢ V n, k z ∂mu.prod mu)) atTop (𝓝 ell)) :
    Tendsto (fun n =>
      (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
        (∫ z in V n ×ˢ V n, m z * k z ∂mu.prod mu))
      atTop (𝓝 (m (x,x) * ell)) := by
  let a : ℕ → ℂ := fun n =>
    (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
      (∫ z in V n ×ˢ V n, m z * k z ∂mu.prod mu)
  let d : ℕ → ℂ := fun n =>
    (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
      (∫ z in V n ×ˢ V n, k z ∂mu.prod mu)
  have hbound (n : ℕ) : ‖a n - m (x,x) * d n‖ ≤ e n * C := by
    simpa only [a, d, Complex.ofReal_inv] using normalized_multiplier_error_bound
      ((mu.prod mu).restrict (V n ×ˢ V n)) k m (m (x,x))
      _ _ C (inv_nonneg.mpr ENNReal.toReal_nonneg) (he n)
      (hk n) (hmk n) (hosc n) (habs n)
  have herr : Tendsto (fun n => a n - m (x,x) * d n) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    have ht : Tendsto (fun n => e n * C) atTop (𝓝 0) := by
      simpa using helim.mul_const C
    have hev := (tendsto_order.1 ht).2 eps heps
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact ⟨N, fun n hn => by simpa [dist_zero_right] using (hbound n).trans_lt (hN n hn)⟩
  have hd : Tendsto d atTop (𝓝 ell) := hlim
  have hh := herr.add (hd.const_mul (m (x,x)))
  simpa only [a, d, zero_add, sub_add_cancel] using hh

#check GeometricRound3D.normalized_multiplier_error_bound
#print axioms GeometricRound3D.normalized_multiplier_error_bound
#check GeometricRound3D.idele_diagonal_multiplier_limit
#print axioms GeometricRound3D.idele_diagonal_multiplier_limit
end GeometricRound3D

/-! Round 4 D. Direct premise of A.5.4.16 as used in 12.1.1.2 and
12.2.2.2(4): derive multiplier oscillation and local product integrability
from continuity, shrinking measurable rectangles and the corrected bound on
normalized absolute averages. This remains CONDITIONAL on the actual kernel,
Haar measure and nuclear maximal bound, and does not assert a trace formula. -/
namespace GeometricRound4D
open MeasureTheory Filter MasulloGRH
open scoped Topology

/-- Continuous multipliers pass through diagonal averages on the genuine
idele-class quotient. The product's local integrability on sufficiently small
rectangles is derived, not assumed. No claim of diagonal a.e. regularity or
integrability of the limiting diagonal is made. -/
theorem continuous_idele_diagonal_multiplier_limit
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [SigmaFinite mu]
    (V : ℕ → Set (HeckeIdeleClasses K)) (hV : ∀ n, MeasurableSet (V n))
    (k m : HeckeIdeleClasses K × HeckeIdeleClasses K → ℂ)
    (x : HeckeIdeleClasses K) (ell : ℂ) (C : ℝ)
    (hm : ContinuousAt m (x,x))
    (hshrink : ∀ U ∈ 𝓝 (x,x), ∀ᶠ n in atTop, V n ×ˢ V n ⊆ U)
    (hmeas : ∀ n, AEStronglyMeasurable m ((mu.prod mu).restrict (V n ×ˢ V n)))
    (hk : ∀ n, IntegrableOn k (V n ×ˢ V n) (mu.prod mu))
    (habs : ∀ n, ((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ *
      (∫ z in V n ×ˢ V n, ‖k z‖ ∂mu.prod mu) ≤ C)
    (hlim : Tendsto (fun n =>
      (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
        (∫ z in V n ×ˢ V n, k z ∂mu.prod mu)) atTop (𝓝 ell)) :
    Tendsto (fun n =>
      (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
        (∫ z in V n ×ˢ V n, m z * k z ∂mu.prod mu))
      atTop (𝓝 (m (x,x) * ell)) := by
  let a : ℕ → ℂ := fun n =>
    (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
      (∫ z in V n ×ˢ V n, m z * k z ∂mu.prod mu)
  let d : ℕ → ℂ := fun n =>
    (((mu.prod mu) (V n ×ˢ V n)).toReal⁻¹ : ℂ) *
      (∫ z in V n ×ˢ V n, k z ∂mu.prod mu)
  have herr : Tendsto (fun n => a n - m (x,x) * d n) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    let delta : ℝ := eps / (|C| + 1)
    have hdpos : 0 < delta := div_pos heps (by positivity)
    have hU : {z | ‖m z - m (x,x)‖ < delta} ∈ 𝓝 (x,x) := by
      have hh := hm.eventually (Metric.ball_mem_nhds (m (x,x)) hdpos)
      simpa only [Metric.mem_ball, dist_eq_norm] using hh
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hshrink _ hU)
    refine ⟨N, fun n hn => ?_⟩
    have hosc : ∀ᵐ z ∂(mu.prod mu).restrict (V n ×ˢ V n),
        ‖m z - m (x,x)‖ ≤ delta := by
      filter_upwards [ae_restrict_mem ((hV n).prod (hV n))] with z hz
      exact (hN n hn hz).le
    have hmk : IntegrableOn (fun z => m z * k z) (V n ×ˢ V n) (mu.prod mu) := by
      apply ((hk n).norm.const_mul (‖m (x,x)‖ + delta)).mono'
        ((hmeas n).mul (hk n).aestronglyMeasurable)
      filter_upwards [hosc] with z hz
      change ‖m z * k z‖ ≤ (‖m (x,x)‖ + delta) * ‖k z‖
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have ht := norm_add_le (m z - m (x,x)) (m (x,x))
      simp only [sub_add_cancel] at ht
      linarith
    have hb := GeometricRound3D.normalized_multiplier_error_bound
      ((mu.prod mu).restrict (V n ×ˢ V n)) k m (m (x,x))
      _ delta C (inv_nonneg.mpr ENNReal.toReal_nonneg) hdpos.le
      (hk n) hmk hosc (habs n)
    have hdC : delta * C < eps := by
      have heq : delta * (|C| + 1) = eps := by
        dsimp [delta]
        exact div_mul_cancel₀ _ (by positivity)
      have hC : C < |C| + 1 := lt_of_le_of_lt (le_abs_self C) (by linarith)
      have hh := mul_lt_mul_of_pos_left hC hdpos
      linarith
    simpa only [a, d, dist_zero_right, Complex.ofReal_inv] using hb.trans_lt hdC
  have hd : Tendsto d atTop (𝓝 ell) := hlim
  have hh := herr.add (hd.const_mul (m (x,x)))
  simpa only [a, d, zero_add, sub_add_cancel] using hh

#check GeometricRound4D.continuous_idele_diagonal_multiplier_limit
#print axioms GeometricRound4D.continuous_idele_diagonal_multiplier_limit
end GeometricRound4D

namespace GeometricRound4D
open Filter MasulloGRH
open scoped Topology

/-- Discharges hshrink in continuous_idele_diagonal_multiplier_limit from
exactly the decreasing and neighborhood-cofinal properties of the translated
D-prime neighborhoods in Definition 12.1.1.1. Finite positive measure and the
maximal bound are separate analytic requirements, not consequences here. -/
theorem idele_rectangles_shrink_of_antitone
    (K : Type*) [Field K] [NumberField K]
    (V : ℕ → Set (HeckeIdeleClasses K)) (x : HeckeIdeleClasses K)
    (hanti : Antitone V)
    (hbase : ∀ U ∈ 𝓝 x, ∃ n, V n ⊆ U) :
    ∀ W ∈ 𝓝 (x,x), ∀ᶠ n in atTop, V n ×ˢ V n ⊆ W := by
  intro W hW
  obtain ⟨U, hU, Z, hZ, hUZ⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨N, hN⟩ := hbase (U ∩ Z) (inter_mem hU hZ)
  apply eventually_atTop.2
  refine ⟨N, fun n hn z hz => ?_⟩
  exact hUZ ⟨(hN (hanti hn hz.1)).1, (hN (hanti hn hz.2)).2⟩

#check GeometricRound4D.idele_rectangles_shrink_of_antitone
#print axioms GeometricRound4D.idele_rectangles_shrink_of_antitone
end GeometricRound4D

/-! Round 5 D: simultaneous removal of cutoffs while the supplied spectral
kernel diagonal varies. This discharges the joint-limit premise between
12.1.1.2(3), 12.1.1.20 and 12.5.1.4 PROVIDED strong L1 convergence of the
correctly ordered arithmetic diagonals is established. Weak L1 convergence
alone is not substituted for this hypothesis. No operator or nuclearity is
invented, and no trace identity is assumed or concluded. -/
namespace GeometricRound5D
open MasulloGRH GeometricRound1D MeasureTheory Filter
open scoped Topology

/-- Uniformity in the bounded cutoff needed to pass kernel approximation and
cutoff removal together on the actual idele-class quotient. -/
theorem cutoff_diagonal_error_bound
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (f g rho : HeckeIdeleClasses K → ℂ)
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hr : AEStronglyMeasurable rho mu)
    (hb : ∀ᵐ x ∂mu, ‖rho x‖ ≤ 1) :
    ‖(∫ x, rho x * f x ∂mu) - (∫ x, rho x * g x ∂mu)‖ ≤
      ∫ x, ‖f x - g x‖ ∂mu := by
  have hi (v : HeckeIdeleClasses K → ℂ) (hv : Integrable v mu) :
      Integrable (fun x => rho x * v x) mu := by
    apply hv.norm.mono' (hr.mul hv.aestronglyMeasurable)
    filter_upwards [hb] with x hx
    change ‖rho x * v x‖ ≤ ‖v x‖
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  rw [← integral_sub (hi f hf) (hi g hg)]
  calc
    ‖∫ x, rho x * f x - rho x * g x ∂mu‖ ≤
        ∫ x, ‖rho x * f x - rho x * g x‖ ∂mu :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x - g x‖ ∂mu := by
      apply integral_mono_ae ((hi f hf).sub (hi g hg)).norm (hf.sub hg).norm
      filter_upwards [hb] with x hx
      change ‖rho x * f x - rho x * g x‖ ≤ ‖f x - g x‖
      rw [← mul_sub, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hx

/-- CONDITIONAL joint cutoff/kernel limit. The exact manuscript restriction
phi(C_K^1)=0 is retained. Strong L1 convergence is explicit and must be derived
from the SAME arithmetic operator approximation; product-a.e. or weak L1
convergence does not fill it. No common dominating function is required for
the varying diagonals. -/
theorem moving_diagonal_cutoff_limit
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (kn : ℕ → HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hk : Integrable (fun x => kspec x x) mu)
    (hn : ∀ n, Integrable (fun x => kn n x x) mu)
    (hL1 : Tendsto (fun n => ∫ x, ‖kn n x x - kspec x x‖ ∂mu) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hr : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hl : ∀ᵐ x ∂mu, Tendsto (fun n => rho n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi (kn n) x x ∂mu)
      atTop (𝓝 (-∫ x, kspec x x ∂mu)) := by
  let A : ℕ → ℂ := fun n => ∫ x, rho n x * complementKernel K phi (kn n) x x ∂mu
  let B : ℕ → ℂ := fun n => ∫ x, rho n x * complementKernel K phi kspec x x ∂mu
  have hgn (n : ℕ) : Integrable (fun x => complementKernel K phi (kn n) x x) mu := by
    simpa only [complement_diagonal K phi hphi] using (hn n).neg
  have hgk : Integrable (fun x => complementKernel K phi kspec x x) mu := by
    simpa only [complement_diagonal K phi hphi] using hk.neg
  have herr (n : ℕ) : ‖A n - B n‖ ≤ ∫ x, ‖kn n x x - kspec x x‖ ∂mu := by
    have hh := cutoff_diagonal_error_bound K mu
      (fun x => complementKernel K phi (kn n) x x)
      (fun x => complementKernel K phi kspec x x) (rho n)
      (hgn n) hgk (hr n) (hb n)
    simpa only [A, B, complement_diagonal K phi hphi, neg_sub_neg, norm_sub_rev] using hh
  have he : Tendsto (fun n => A n - B n) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hL1).2 eps heps)
    exact ⟨N, fun n hn => by
      simpa only [dist_zero_right] using (herr n).trans_lt (hN n hn)⟩
  have hB : Tendsto B atTop (𝓝 (-∫ x, kspec x x ∂mu)) :=
    complement_diagonal_cutoff_limit K mu phi hphi kspec hk rho hr hb hl
  have ht := he.add hB
  simpa only [sub_add_cancel, zero_add] using ht

#check GeometricRound5D.cutoff_diagonal_error_bound
#print axioms GeometricRound5D.cutoff_diagonal_error_bound
#check GeometricRound5D.moving_diagonal_cutoff_limit
#print axioms GeometricRound5D.moving_diagonal_cutoff_limit
end GeometricRound5D

namespace GeometricRound5D
open MasulloGRH GeometricRound1D GeometricRound2D MeasureTheory Filter
open scoped Topology

/-- Attaches the joint diagonal limit to Definition 9.3.3.1's actual-modulus
plateau and epsilon*Lambda -> 0 regime. Pointwise cutoff convergence follows
from those endpoint hypotheses; the L1 arithmetic-diagonal bridge is still
explicit. This is a conditional premise for (12.5.1.4), not its trace identity. -/
theorem moving_manuscript_cutoff_limit
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (kn : ℕ → HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hk : Integrable (fun x => kspec x x) mu)
    (hn : ∀ n, Integrable (fun x => kn n x x) mu)
    (hL1 : Tendsto (fun n => ∫ x, ‖kn n x x - kspec x x‖ ∂mu) atTop (𝓝 0))
    (L e : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (heL : Tendsto (fun n => e n * L n) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hr : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hplateau : ∀ n x, 1 / L n + e n ≤ classModulus K x →
      classModulus K x ≤ L n - e n → rho n x = 1) :
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi (kn n) x x ∂mu)
      atTop (𝓝 (-∫ x, kspec x x ∂mu)) := by
  obtain ⟨hlo, hhi⟩ := manuscript_cutoff_endpoints L e hL heL
  apply moving_diagonal_cutoff_limit K mu phi hphi kspec kn hk hn hL1 rho hr hb
  exact Eventually.of_forall fun x =>
    cutoff_tendsto_one K _ _ hlo hhi rho hplateau x

#check GeometricRound5D.moving_manuscript_cutoff_limit
#print axioms GeometricRound5D.moving_manuscript_cutoff_limit
end GeometricRound5D

/-! Round 6 D. Direct target premise: upgrade the bounded-multiplier trace
estimates of 12.1.1.2(2) to the strong L1 diagonal convergence needed by the
joint cutoff limit in 12.5.1.4. The phase multiplier is constructed, not
assumed. Actual arithmetic trace identities and trace-ideal bounds remain
explicit dependencies; this is not an unconditional arithmetic trace formula. -/
namespace GeometricRound6D
open MasulloGRH GeometricRound1D MeasureTheory Filter
open scoped Topology

/-- Direct premise discharged: the L1 norm estimate for the difference of
canonical arithmetic diagonals, once ALL bounded measurable multiplier trace
estimates are available. In particular, continuous test multipliers alone
are not silently substituted for the stated hypothesis. -/
theorem idele_diagonal_L1_le_of_multiplier_bound
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ) (hd : Integrable d mu) (B : ℝ)
    (hbound : ∀ r : HeckeIdeleClasses K → ℂ,
      AEStronglyMeasurable r mu → (∀ᵐ x ∂mu, ‖r x‖ ≤ 1) →
      ‖∫ x, r x * d x ∂mu‖ ≤ B) :
    (∫ x, ‖d x‖ ∂mu) ≤ B := by
  let r : HeckeIdeleClasses K → ℂ := fun x => (‖d x‖ : ℂ) / d x
  have hr : AEStronglyMeasurable r mu := by
    exact ((Complex.continuous_ofReal.measurable.comp_aemeasurable
      hd.aestronglyMeasurable.norm.aemeasurable).div
      hd.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hb : ∀ᵐ x ∂mu, ‖r x‖ ≤ 1 := by
    apply Eventually.of_forall
    intro x
    dsimp [r]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    by_cases hx : d x = 0
    · simp [hx]
    · rw [div_self (norm_ne_zero_iff.mpr hx)]
  have hprod (x : HeckeIdeleClasses K) : r x * d x = (‖d x‖ : ℂ) := by
    by_cases hx : d x = 0
    · simp [r, hx]
    · exact div_mul_cancel₀ _ hx
  have hh := hbound r hr hb
  simp_rw [hprod] at hh
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun x => norm_nonneg (d x))] at hh
  exact hh

#check GeometricRound6D.idele_diagonal_L1_le_of_multiplier_bound
#print axioms GeometricRound6D.idele_diagonal_L1_le_of_multiplier_bound
end GeometricRound6D

namespace GeometricRound6D
open MasulloGRH GeometricRound1D MeasureTheory Filter
open scoped Topology

/-- CONDITIONAL attachment to 12.5.1.4: bounded-multiplier estimates tending
to zero imply the required strong L1 convergence and simultaneous manuscript
cutoff limit. The intended B_n is the trace norm of T_n-T for the SAME actual
ordered operator, via 12.1.1.3 and the trace-ideal inequality. Neither those
operator identities nor nuclearity is asserted here. No summability hypothesis
or replacement arithmetic operator is introduced. -/
theorem moving_manuscript_cutoff_limit_of_multiplier_estimates
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (kn : ℕ → HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hk : Integrable (fun x => kspec x x) mu)
    (hn : ∀ n, Integrable (fun x => kn n x x) mu)
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hestimate : ∀ n (r : HeckeIdeleClasses K → ℂ),
      AEStronglyMeasurable r mu → (∀ᵐ x ∂mu, ‖r x‖ ≤ 1) →
      ‖∫ x, r x * (kn n x x - kspec x x) ∂mu‖ ≤ B n)
    (L e : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (heL : Tendsto (fun n => e n * L n) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hr : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hplateau : ∀ n x, 1 / L n + e n ≤ classModulus K x →
      classModulus K x ≤ L n - e n → rho n x = 1) :
    Tendsto (fun n => ∫ x, ‖kn n x x - kspec x x‖ ∂mu) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi (kn n) x x ∂mu)
      atTop (𝓝 (-∫ x, kspec x x ∂mu)) := by
  have hL1 : Tendsto (fun n => ∫ x, ‖kn n x x - kspec x x‖ ∂mu)
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hB).2 eps heps)
    refine ⟨N, fun n hn' => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact (idele_diagonal_L1_le_of_multiplier_bound K mu _ ((hn n).sub hk)
      (B n) (hestimate n)).trans_lt (hN n hn')
  exact ⟨hL1, GeometricRound5D.moving_manuscript_cutoff_limit K mu phi hphi
    kspec kn hk hn hL1 L e hL heL rho hr hb hplateau⟩

#check GeometricRound6D.moving_manuscript_cutoff_limit_of_multiplier_estimates
#print axioms GeometricRound6D.moving_manuscript_cutoff_limit_of_multiplier_estimates
end GeometricRound6D

/-! Round 7 D. Direct premise discharged: integrability of the limiting
smoothed diagonal in 12.1.1.2(1), needed by 12.1.1.3(3) and 12.5.1.4.
Fatou is applied ON C_K, not on C_K x C_K. A.e. diagonal convergence and
uniform multiplier bounds for the actual approximants remain explicit inputs.
No conclusion of nuclearity, trace identity, or arithmetic kernel attachment. -/
namespace GeometricRound7D
open MasulloGRH GeometricRound1D MeasureTheory Filter
open scoped Topology

/-- Conditional analytic bridge: derive the missing limiting-diagonal L1
premise without assuming an integrable dominating function or limit L1. -/
theorem idele_diagonal_integrable_of_multiplier_approximation
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (d : HeckeIdeleClasses K → ℂ)
    (dn : ℕ → HeckeIdeleClasses K → ℂ)
    (hd : AEStronglyMeasurable d mu)
    (hn : ∀ n, Integrable (dn n) mu)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => dn n x) atTop (𝓝 (d x)))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n (r : HeckeIdeleClasses K → ℂ),
      AEStronglyMeasurable r mu → (∀ᵐ x ∂mu, ‖r x‖ ≤ 1) →
      ‖∫ x, r x * dn n x ∂mu‖ ≤ B) :
    Integrable d mu ∧ (∫ x, ‖d x‖ ∂mu) ≤ B := by
  have hnorm (n : ℕ) : (∫ x, ‖dn n x‖ ∂mu) ≤ B :=
    GeometricRound6D.idele_diagonal_L1_le_of_multiplier_bound
      K mu (dn n) (hn n) B (hbound n)
  have hmass (n : ℕ) : (∫⁻ x, ‖dn n x‖ₑ ∂mu) ≤ ENNReal.ofReal B := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hn n)]
    exact ENNReal.ofReal_le_ofReal (hnorm n)
  have hfat : (∫⁻ x, ‖d x‖ₑ ∂mu) ≤ ENNReal.ofReal B := by
    calc
      (∫⁻ x, ‖d x‖ₑ ∂mu) =
          ∫⁻ x, liminf (fun n => ‖dn n x‖ₑ) atTop ∂mu := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with x hx
        exact hx.enorm.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ x, ‖dn n x‖ₑ ∂mu) atTop :=
        lintegral_liminf_le' (fun n => (hn n).aestronglyMeasurable.enorm)
      _ ≤ ENNReal.ofReal B :=
        liminf_le_of_frequently_le (Eventually.of_forall hmass).frequently
  have hi : Integrable d mu :=
    ⟨hd, hasFiniteIntegral_iff_enorm.mpr (hfat.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hd]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfat
  simpa only [ENNReal.toReal_ofReal hB] using ht

#check GeometricRound7D.idele_diagonal_integrable_of_multiplier_approximation
#print axioms GeometricRound7D.idele_diagonal_integrable_of_multiplier_approximation
end GeometricRound7D

namespace GeometricRound7D
open MasulloGRH GeometricRound1D MeasureTheory Filter
open scoped Topology

/-- Direct premises discharged for 12.1.1.3(3) and 12.5.1.4: limiting diagonal
integrability AND strong L1 convergence from tail estimates involving only
integrable approximants. The actual operator trace bounds and diagonal-a.e.
convergence remain conditional. EXACT norm-one test vanishing is retained. -/
theorem moving_cutoff_limit_of_cauchy_multiplier_bounds
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K))
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (kspec : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (kn : ℕ → HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hk : AEStronglyMeasurable (fun x => kspec x x) mu)
    (hn : ∀ n, Integrable (fun x => kn n x x) mu)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => kn n x x) atTop (𝓝 (kspec x x)))
    (B : ℕ → ℝ) (hBpos : ∀ n, 0 ≤ B n)
    (hB : Tendsto B atTop (𝓝 0))
    (hpair : ∀ n m, n ≤ m → ∀ r : HeckeIdeleClasses K → ℂ,
      AEStronglyMeasurable r mu → (∀ᵐ x ∂mu, ‖r x‖ ≤ 1) →
      ‖∫ x, r x * (kn n x x - kn m x x) ∂mu‖ ≤ B n)
    (L e : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (heL : Tendsto (fun n => e n * L n) atTop (𝓝 0))
    (rho : ℕ → HeckeIdeleClasses K → ℂ)
    (hr : ∀ n, AEStronglyMeasurable (rho n) mu)
    (hb : ∀ n, ∀ᵐ x ∂mu, ‖rho n x‖ ≤ 1)
    (hplateau : ∀ n x, 1 / L n + e n ≤ classModulus K x →
      classModulus K x ≤ L n - e n → rho n x = 1) :
    Integrable (fun x => kspec x x) mu ∧
    Tendsto (fun n => ∫ x, ‖kn n x x - kspec x x‖ ∂mu) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, rho n x * complementKernel K phi (kn n) x x ∂mu)
      atTop (𝓝 (-∫ x, kspec x x ∂mu)) := by
  have herr (n : ℕ) : Integrable (fun x => kn n x x - kspec x x) mu ∧
      (∫ x, ‖kn n x x - kspec x x‖ ∂mu) ≤ B n := by
    refine idele_diagonal_integrable_of_multiplier_approximation K mu
      (fun x => kn n x x - kspec x x)
      (fun m x => kn n x x - kn (max n m) x x)
      ((hn n).aestronglyMeasurable.sub hk)
      (fun m => (hn n).sub (hn (max n m)))
      ?_ (B n) (hBpos n) ?_
    · filter_upwards [hlim] with x hx
      apply (tendsto_const_nhds.sub hx).congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      simp only [max_eq_right hm]
    · intro m r hmr hbr
      exact hpair n (max n m) (le_max_left n m) r hmr hbr
  have hki : Integrable (fun x => kspec x x) mu := by
    have hi := (hn 0).sub (herr 0).1
    change Integrable (fun x => kn 0 x x - (kn 0 x x - kspec x x)) mu at hi
    simpa only [sub_sub_cancel] using hi
  have hL1 : Tendsto (fun n => ∫ x, ‖kn n x x - kspec x x‖ ∂mu)
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hB).2 eps heps)
    refine ⟨N, fun n hNn => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
    exact (herr n).2.trans_lt (hN n hNn)
  exact ⟨hki, hL1, GeometricRound5D.moving_manuscript_cutoff_limit K mu phi hphi
    kspec kn hki hn hL1 L e hL heL rho hr hb hplateau⟩

#check GeometricRound7D.moving_cutoff_limit_of_cauchy_multiplier_bounds
#print axioms GeometricRound7D.moving_cutoff_limit_of_cauchy_multiplier_bounds
end GeometricRound7D

/-! Round 9 D: the sharp logarithmic volume error in (12.4.1.23--24)
with the independent lower cutoff requested at manuscript lines 31174--31177.
This discharges ONLY the dominated-convergence premise after the arithmetic
Fourier density, its logarithmic moment, and the volume formula are attached.
It does not assert those premises, a trace identity, or nuclearity. -/
namespace GeometricRound9D
open MasulloGRH MeasureTheory Filter
open scoped Topology

/-- a=log(lambda*lambda'), b=log(lambda'/lambda''), t=log|w|_S. -/
def logVolumeError (a b t : ℝ) : ℝ :=
  max (a - max t b) 0 - (a - t)

/-- Precise premise: an integrable logarithmic moment dominates BOTH the
upper and independent lower sharp-volume cutoff errors. -/
theorem logVolumeError_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : b ≤ 0) :
    |logVolumeError a b t| ≤ |t| := by
  have h₁ := neg_abs_le t
  have h₂ := le_abs_self t
  rw [abs_le]
  simp only [logVolumeError, max_def]
  split_ifs <;> constructor <;> linarith

theorem logVolumeError_zero (a b t : ℝ) (hb : b ≤ t) (ha : t ≤ a) :
    logVolumeError a b t = 0 := by
  simp [logVolumeError, max_eq_left hb, max_eq_left (sub_nonneg.mpr ha)]

/-- Genuine S-local modulus pulled back to the actual global adele ring;
S is the finite non-Archimedean part and ALL infinite places are included. -/
def sLocalRadius (K : Type*) [Field K] [NumberField K]
    (S : Finset (NumberField.FinitePlace K)) (x : HeckeAdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖x.1 w‖ ^ w.mult) *
    ∏ v ∈ S, ‖x.2 v.maximalIdeal‖

/-- CONDITIONAL §12.4 cutoff interchange on genuine adeles, for a supplied
Fourier density h and supplied measure. Log-radius measurability, negligible
zero-radius locus, and the absolute logarithmic moment remain explicit.
The intended a,b are log(lambda*lambda'),log(lambda'/lambda''); b→-infinity
is essential and does not follow from divergence of the three lambdas alone.
The theorem introduces no replacement arithmetic operator or test class. -/
theorem sLocal_logarithmic_cutoff_error_tendsto_zero
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) (h : HeckeAdeles K → ℂ)
    (hh : AEStronglyMeasurable h mu)
    (ht : AEStronglyMeasurable (fun x => Real.log (sLocalRadius K S x)) mu)
    (hpos : ∀ᵐ x ∂mu, 0 < sLocalRadius K S x)
    (hmoment : Integrable (fun x => ‖h x‖ * |Real.log (sLocalRadius K S x)|) mu)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, b n ≤ 0)
    (halim : Tendsto a atTop atTop) (hblim : Tendsto b atTop atBot) :
    Tendsto (fun n => ∫ x, h x *
      (logVolumeError (a n) (b n) (Real.log (sLocalRadius K S x)) : ℂ) ∂mu)
      atTop (𝓝 0) := by
  let t : HeckeAdeles K → ℝ := fun x => Real.log (sLocalRadius K S x)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x => h x * (logVolumeError (a n) (b n) (t x) : ℂ)) mu := by
    have he : AEStronglyMeasurable
        (fun x => logVolumeError (a n) (b n) (t x)) mu := by
      have hc : Continuous (fun u : ℝ => logVolumeError (a n) (b n) u) := by
        unfold logVolumeError
        fun_prop
      exact hc.comp_aestronglyMeasurable ht
    exact hh.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable he)
  have hdom (n : ℕ) : ∀ᵐ x ∂mu,
      ‖h x * (logVolumeError (a n) (b n) (t x) : ℂ)‖ ≤ ‖h x‖ * |t x| := by
    apply Eventually.of_forall
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (logVolumeError_bound (a n) (b n) (t x) (ha n) (hb n)) (norm_nonneg _)
  have hpoint : ∀ᵐ x ∂mu, Tendsto
      (fun n => h x * (logVolumeError (a n) (b n) (t x) : ℂ)) atTop (𝓝 0) := by
    filter_upwards [hpos] with x hx
    have he : ∀ᶠ n in atTop, h x *
        (logVolumeError (a n) (b n) (t x) : ℂ) = 0 := by
      filter_upwards [halim.eventually (eventually_ge_atTop (t x)),
        hblim.eventually (eventually_le_atBot (t x))] with n hna hnb
      rw [logVolumeError_zero _ _ _ hnb hna]
      simp
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    exact hn.symm
  have hconv := tendsto_integral_of_dominated_convergence
    (fun x => ‖h x‖ * |t x|) hmeas hmoment hdom hpoint
  simpa only [integral_zero] using hconv

#check GeometricRound9D.logVolumeError_bound
#print axioms GeometricRound9D.logVolumeError_bound
#check GeometricRound9D.sLocal_logarithmic_cutoff_error_tendsto_zero
#print axioms GeometricRound9D.sLocal_logarithmic_cutoff_error_tendsto_zero
end GeometricRound9D

/-! Round 10 D. Direct premise of (12.4.1.23--28): turn the checked
logarithmic ERROR limit into the full renormalized sharp-volume integral.
The density and measure still require actual Fourier/Haar attachment. -/
namespace GeometricRound10D
open MasulloGRH GeometricRound9D MeasureTheory Filter
open scoped Topology

/-- CONDITIONAL sharp-volume asymptotic on genuine adeles. This discharges
integrability and integral splitting, which the round-9 error limit alone
could not justify. No nuclearity or arithmetic trace identity is asserted. -/
theorem sLocal_sharp_volume_asymptotic
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) (h : HeckeAdeles K → ℂ)
    (hh : Integrable h mu)
    (ht : AEStronglyMeasurable (fun x => Real.log (sLocalRadius K S x)) mu)
    (hpos : ∀ᵐ x ∂mu, 0 < sLocalRadius K S x)
    (hmoment : Integrable (fun x => ‖h x‖ * |Real.log (sLocalRadius K S x)|) mu)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, b n ≤ 0)
    (halim : Tendsto a atTop atTop) (hblim : Tendsto b atTop atBot) :
    (∀ n, Integrable (fun x => h x *
      ((max (a n - max (Real.log (sLocalRadius K S x)) (b n)) 0 : ℝ) : ℂ)) mu) ∧
    Tendsto (fun n =>
      (∫ x, h x * ((max (a n - max (Real.log (sLocalRadius K S x)) (b n)) 0 : ℝ) : ℂ) ∂mu)
        - (∫ x, h x ∂mu) * (a n : ℂ)) atTop
      (𝓝 (-∫ x, h x * (Real.log (sLocalRadius K S x) : ℂ) ∂mu)) := by
  let t : HeckeAdeles K → ℝ := fun x => Real.log (sLocalRadius K S x)
  let err (n : ℕ) (x : HeckeAdeles K) : ℂ :=
    h x * (logVolumeError (a n) (b n) (t x) : ℂ)
  let vol (n : ℕ) (x : HeckeAdeles K) : ℂ :=
    h x * ((max (a n - max (t x) (b n)) 0 : ℝ) : ℂ)
  have hlog : Integrable (fun x => h x * (t x : ℂ)) mu := by
    refine hmoment.mono' (hh.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable ht)) ?_
    exact Eventually.of_forall (fun x => by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact le_rfl)
  have herr (n : ℕ) : Integrable (err n) mu := by
    have hc : Continuous (fun u : ℝ => logVolumeError (a n) (b n) u) := by
      unfold logVolumeError
      fun_prop
    refine hmoment.mono' (hh.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hc.comp_aestronglyMeasurable ht))) ?_
    apply Eventually.of_forall
    intro x
    change ‖h x * (logVolumeError (a n) (b n) (t x) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (logVolumeError_bound _ _ _ (ha n) (hb n)) (norm_nonneg _)
  have heq (n : ℕ) : vol n = fun x =>
      err n x + (h x * (a n : ℂ) - h x * (t x : ℂ)) := by
    funext x
    dsimp [vol, err, logVolumeError]
    push_cast
    ring
  have hi (n : ℕ) : Integrable (vol n) mu := by
    rw [heq n]
    exact (herr n).add ((hh.mul_const (a n : ℂ)).sub hlog)
  have heqint (n : ℕ) : (∫ x, vol n x ∂mu) - (∫ x, h x ∂mu) * (a n : ℂ) =
      (∫ x, err n x ∂mu) - ∫ x, h x * (t x : ℂ) ∂mu := by
    have hadd : (∫ x, vol n x ∂mu) = (∫ x, err n x ∂mu) +
        ∫ x, h x * (a n : ℂ) - h x * (t x : ℂ) ∂mu := by
      calc
        _ = ∫ x, err n x + (h x * (a n : ℂ) - h x * (t x : ℂ)) ∂mu := by
          rw [heq n]
        _ = _ := integral_add (herr n) ((hh.mul_const (a n : ℂ)).sub hlog)
    have hsub : (∫ x, h x * (a n : ℂ) - h x * (t x : ℂ) ∂mu) =
        (∫ x, h x * (a n : ℂ) ∂mu) - ∫ x, h x * (t x : ℂ) ∂mu :=
      integral_sub (hh.mul_const (a n : ℂ)) hlog
    rw [hadd, hsub, integral_mul_const]
    ring
  have hconv := sLocal_logarithmic_cutoff_error_tendsto_zero K S mu h
    hh.aestronglyMeasurable ht hpos hmoment a b ha hb halim hblim
  refine ⟨hi, ?_⟩
  have hz := hconv.sub_const (∫ x, h x * (t x : ℂ) ∂mu)
  simp only [zero_sub] at hz
  exact hz.congr (fun n => (heqint n).symm)

#check GeometricRound10D.sLocal_sharp_volume_asymptotic
#print axioms GeometricRound10D.sLocal_sharp_volume_asymptotic
end GeometricRound10D

namespace GeometricRound10D
open MasulloGRH GeometricRound1D GeometricRound9D MeasureTheory Filter
open scoped Topology

/-- Direct premise of (12.4.1.25) under EXACT phi(C_K^1)=0: cancellation
of the divergent mass term. The Fourier/periodization mass identity is an
explicit unresolved input, not a definition of h or an assumed trace formula. -/
theorem sLocal_sharp_volume_limit_normOneVanishing
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) (h : HeckeAdeles K → ℂ)
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (hmass : (∫ x, h x ∂mu) = phi 1)
    (hh : Integrable h mu)
    (ht : AEStronglyMeasurable (fun x => Real.log (sLocalRadius K S x)) mu)
    (hpos : ∀ᵐ x ∂mu, 0 < sLocalRadius K S x)
    (hmoment : Integrable (fun x => ‖h x‖ * |Real.log (sLocalRadius K S x)|) mu)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, b n ≤ 0)
    (halim : Tendsto a atTop atTop) (hblim : Tendsto b atTop atBot) :
    Tendsto (fun n => ∫ x, h x *
      ((max (a n - max (Real.log (sLocalRadius K S x)) (b n)) 0 : ℝ) : ℂ) ∂mu)
      atTop (𝓝 (-∫ x, h x * (Real.log (sLocalRadius K S x) : ℂ) ∂mu)) := by
  have hz : (∫ x, h x ∂mu) = 0 := hmass.trans (hphi 1 (classModulus_one K))
  have hc := (sLocal_sharp_volume_asymptotic K S mu h hh ht hpos hmoment
    a b ha hb halim hblim).2
  simpa only [hz, zero_mul, sub_zero] using hc

#check GeometricRound10D.sLocal_sharp_volume_limit_normOneVanishing
#print axioms GeometricRound10D.sLocal_sharp_volume_limit_normOneVanishing
end GeometricRound10D

/-! Round 11 D. Precise premise discharged: the smooth-to-sharp radial volume
error omitted between (12.4.1.21) and (12.4.1.22). The envelope below must still
be established for the actual two smooth cutoff integrals and quotient Haar
normalization. This is not an assumed trace identity or summability premise. -/
namespace GeometricRound11D
open MasulloGRH GeometricRound9D GeometricRound10D MeasureTheory Filter
open scoped Topology

/-- A logarithmic endpoint envelope controls the volume error uniformly in
both endpoints and in the genuine S-local logarithmic radius. -/
theorem volume_envelope_error (a b t d z : ℝ) (hd : 0 ≤ d)
    (hl : max (a - d - max t (b + d)) 0 ≤ z)
    (hu : z ≤ max (a + d - max t (b - d)) 0) :
    |z - max (a - max t b) 0| ≤ 2 * d := by
  have hb₁ : max t (b + d) ≤ max t b + d := by
    apply max_le
    · linarith [le_max_left t b]
    · linarith [le_max_right t b]
  have hb₂ : max t b ≤ max t (b - d) + d := by
    apply max_le
    · linarith [le_max_left t (b - d)]
    · linarith [le_max_right t (b - d)]
  have hlower : max (a - max t b) 0 ≤
      max (a - d - max t (b + d)) 0 + 2 * d := by
    apply max_le
    · linarith [le_max_left (a - d - max t (b + d)) 0]
    · linarith [le_max_right (a - d - max t (b + d)) 0]
  have hupper : max (a + d - max t (b - d)) 0 ≤
      max (a - max t b) 0 + 2 * d := by
    apply max_le
    · linarith [le_max_left (a - max t b) 0]
    · linarith [le_max_right (a - max t b) 0]
  rw [abs_le]
  constructor <;> linarith

/-- CONDITIONAL smooth-volume asymptotic on the actual adele ring. The new
hypothesis is a pointwise geometric envelope, not convergence of traces.
It proves integrability and passage from smooth volume to the r10 sharp
volume limit. Actual Fourier density and Haar identification remain open. -/
theorem sLocal_smooth_volume_asymptotic
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) (h : HeckeAdeles K → ℂ)
    (hh : Integrable h mu)
    (ht : AEStronglyMeasurable (fun x => Real.log (sLocalRadius K S x)) mu)
    (hpos : ∀ᵐ x ∂mu, 0 < sLocalRadius K S x)
    (hmoment : Integrable (fun x => ‖h x‖ * |Real.log (sLocalRadius K S x)|) mu)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, b n ≤ 0)
    (halim : Tendsto a atTop atTop) (hblim : Tendsto b atTop atBot)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (hdlim : Tendsto d atTop (𝓝 0))
    (V : ℕ → HeckeAdeles K → ℝ)
    (hV : ∀ n, AEStronglyMeasurable (V n) mu)
    (henvelope : ∀ n, ∀ᵐ x ∂mu,
      max (a n - d n - max (Real.log (sLocalRadius K S x)) (b n + d n)) 0 ≤ V n x ∧
      V n x ≤ max (a n + d n - max (Real.log (sLocalRadius K S x)) (b n - d n)) 0) :
    (∀ n, Integrable (fun x => h x * (V n x : ℂ)) mu) ∧
    Tendsto (fun n => (∫ x, h x * (V n x : ℂ) ∂mu) -
      (∫ x, h x ∂mu) * (a n : ℂ)) atTop
      (𝓝 (-∫ x, h x * (Real.log (sLocalRadius K S x) : ℂ) ∂mu)) := by
  let t (x : HeckeAdeles K) := Real.log (sLocalRadius K S x)
  let W (n : ℕ) (x : HeckeAdeles K) := max (a n - max (t x) (b n)) 0
  let err (n : ℕ) (x : HeckeAdeles K) : ℂ := h x * ((V n x - W n x : ℝ) : ℂ)
  have hW (n : ℕ) : AEStronglyMeasurable (W n) mu := by
    have hc : Continuous (fun u : ℝ => max (a n - max u (b n)) 0) := by fun_prop
    exact hc.comp_aestronglyMeasurable ht
  have herrmeas (n : ℕ) : AEStronglyMeasurable (err n) mu :=
    hh.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hV n).sub (hW n)))
  have hbound (n : ℕ) : ∀ᵐ x ∂mu, ‖err n x‖ ≤ ‖h x‖ * (2 * d n) := by
    filter_upwards [henvelope n] with x hx
    change ‖h x * ((V n x - W n x : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (volume_envelope_error _ _ _ _ _ (hd n) hx.1 hx.2) (norm_nonneg _)
  have herr (n : ℕ) : Integrable (err n) mu :=
    (hh.norm.mul_const (2 * d n)).mono' (herrmeas n) (hbound n)
  have hintbound (n : ℕ) : ‖∫ x, err n x ∂mu‖ ≤
      (∫ x, ‖h x‖ ∂mu) * (2 * d n) := by
    calc
      _ ≤ ∫ x, ‖err n x‖ ∂mu := norm_integral_le_integral_norm _
      _ ≤ ∫ x, ‖h x‖ * (2 * d n) ∂mu :=
        integral_mono_ae (herr n).norm (hh.norm.mul_const _) (hbound n)
      _ = _ := integral_mul_const _ _
  have hB : Tendsto (fun n => (∫ x, ‖h x‖ ∂mu) * (2 * d n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdlim.const_mul 2 |>.const_mul (∫ x, ‖h x‖ ∂mu)
  have he : Tendsto (fun n => ∫ x, err n x ∂mu) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro eps heps
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hB).2 eps heps)
    exact ⟨N, fun n hn => by
      simpa only [dist_zero_right] using (hintbound n).trans_lt (hN n hn)⟩
  have hs := sLocal_sharp_volume_asymptotic K S mu h hh ht hpos hmoment
    a b ha hb halim hblim
  have hdecomp (n : ℕ) : (fun x => h x * (V n x : ℂ)) =
      fun x => err n x + h x * (W n x : ℂ) := by
    funext x
    dsimp [err]
    push_cast
    ring
  have hi (n : ℕ) : Integrable (fun x => h x * (V n x : ℂ)) mu := by
    rw [hdecomp n]
    exact (herr n).add (hs.1 n)
  have hiint (n : ℕ) : (∫ x, h x * (V n x : ℂ) ∂mu) =
      (∫ x, err n x ∂mu) + ∫ x, h x * (W n x : ℂ) ∂mu := by
    rw [hdecomp n]
    exact integral_add (herr n) (hs.1 n)
  refine ⟨hi, ?_⟩
  have hsum := he.add hs.2
  simp only [zero_add] at hsum
  apply hsum.congr
  intro n
  rw [hiint n]
  ring

#check GeometricRound11D.volume_envelope_error
#print axioms GeometricRound11D.volume_envelope_error
#check GeometricRound11D.sLocal_smooth_volume_asymptotic
#print axioms GeometricRound11D.sLocal_smooth_volume_asymptotic
end GeometricRound11D

namespace GeometricRound11D
open MasulloGRH GeometricRound1D GeometricRound9D MeasureTheory Filter
open scoped Topology

/-- Precise premise: cancel the smooth-volume mass term for the EXACT
Theorem 12.5.1.1 test restriction, after the independent Fourier mass bridge. -/
theorem sLocal_smooth_volume_limit_normOneVanishing
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) (h : HeckeAdeles K → ℂ)
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (hmass : (∫ x, h x ∂mu) = phi 1)
    (hh : Integrable h mu)
    (ht : AEStronglyMeasurable (fun x => Real.log (sLocalRadius K S x)) mu)
    (hpos : ∀ᵐ x ∂mu, 0 < sLocalRadius K S x)
    (hmoment : Integrable (fun x => ‖h x‖ * |Real.log (sLocalRadius K S x)|) mu)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, b n ≤ 0)
    (halim : Tendsto a atTop atTop) (hblim : Tendsto b atTop atBot)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (hdlim : Tendsto d atTop (𝓝 0))
    (V : ℕ → HeckeAdeles K → ℝ)
    (hV : ∀ n, AEStronglyMeasurable (V n) mu)
    (henvelope : ∀ n, ∀ᵐ x ∂mu,
      max (a n - d n - max (Real.log (sLocalRadius K S x)) (b n + d n)) 0 ≤ V n x ∧
      V n x ≤ max (a n + d n - max (Real.log (sLocalRadius K S x)) (b n - d n)) 0) :
    Tendsto (fun n => ∫ x, h x * (V n x : ℂ) ∂mu) atTop
      (𝓝 (-∫ x, h x * (Real.log (sLocalRadius K S x) : ℂ) ∂mu)) := by
  have hz : (∫ x, h x ∂mu) = 0 := hmass.trans (hphi 1 (classModulus_one K))
  have hc := (sLocal_smooth_volume_asymptotic K S mu h hh ht hpos hmoment
    a b ha hb halim hblim d hd hdlim V hV henvelope).2
  simpa only [hz, zero_mul, sub_zero] using hc

/-- Precise premise: the logarithmic error width for the independent lower
cutoff tends to zero. p=epsilon/lambda, q=epsilon'/lambda',
r=epsilon*lambda''. The third limit is an independent required condition. -/
theorem relative_smoothing_log_width_tendsto_zero
    (p q r : ℕ → ℝ)
    (hp : Tendsto p atTop (𝓝 0)) (hq : Tendsto q atTop (𝓝 0))
    (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => |Real.log (1 - p n)| + |Real.log (1 - q n)| +
      |Real.log (1 + r n)|) atTop (𝓝 0) := by
  have hlog := Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)
  have hp1 : Tendsto (fun n => 1 - p n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hp
  have hq1 : Tendsto (fun n => 1 - q n) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hq
  have hr1 : Tendsto (fun n => 1 + r n) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hr
  have hc := ((hlog.tendsto.comp hp1).abs.add
    (hlog.tendsto.comp hq1).abs).add (hlog.tendsto.comp hr1).abs
  simpa only [Real.log_one, abs_zero, add_zero] using hc

#check GeometricRound11D.sLocal_smooth_volume_limit_normOneVanishing
#print axioms GeometricRound11D.sLocal_smooth_volume_limit_normOneVanishing
#check GeometricRound11D.relative_smoothing_log_width_tendsto_zero
#print axioms GeometricRound11D.relative_smoothing_log_width_tendsto_zero
end GeometricRound11D

/-! Round 12 D: discharge the radial-volume envelope premise of r11 from
support and plateau conditions of the TWO cutoffs in (12.4.1.21--24).
The variable u is log|x|_S + log(lambda'); t is log|w|_S. P is the spatial
cutoff in u, Q is the Fourier cutoff in t-u. The quotient-Haar pushforward
and identification with the actual arithmetic kernel are still unresolved. -/
namespace GeometricRound12D
open MeasureTheory Filter
open scoped Topology

/-- The finite logarithmic interval has the required normalized volume.
This is the radial Lebesgue calculation, not the arithmetic Haar bridge. -/
theorem radial_interval_integral (l r : ℝ) :
    Integrable ((Set.Icc l r).indicator (fun _ : ℝ => (1 : ℝ))) ∧
    (∫ u : ℝ, (Set.Icc l r).indicator (fun _ => (1 : ℝ)) u) = max (r-l) 0 := by
  constructor
  · exact (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  · rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
    by_cases h : 0 ≤ r-l
    · rw [ENNReal.toReal_ofReal h, max_eq_left h]
    · have hneg : r-l ≤ 0 := le_of_not_ge h
      rw [ENNReal.ofReal_eq_zero.mpr hneg, ENNReal.toReal_zero, max_eq_right hneg]

/-- Direct target premise: bounded smooth spatial and Fourier cutoffs give
an integrable radial product and an explicit uniform smooth-to-sharp error.
No smoothness is needed for this estimate beyond measurable cutoffs. -/
theorem radial_cutoff_integral_envelope
    (a b t d : ℝ) (hd : 0 ≤ d) (P Q : ℝ → ℝ)
    (hP : Measurable P) (hQ : Measurable Q)
    (hPb : ∀ u, 0 ≤ P u ∧ P u ≤ 1)
    (hQb : ∀ u, 0 ≤ Q u ∧ Q u ≤ 1)
    (hPs : ∀ u, u ∉ Set.Icc b a → P u = 0)
    (hQs : ∀ u, 0 < u → Q u = 0)
    (hPp : ∀ u, b+d ≤ u → u ≤ a-d → P u = 1)
    (hQp : ∀ u, u ≤ -d → Q u = 1) :
    Integrable (fun u => P u * Q (t-u)) ∧
    max (a-2*d-max t b) 0 ≤ (∫ u, P u * Q (t-u)) ∧
    (∫ u, P u * Q (t-u)) ≤ max (a-max t b) 0 ∧
    |(∫ u, P u * Q (t-u)) - max (a-max t b) 0| ≤ 2*d := by
  let lo := (Set.Icc (max (t+d) (b+d)) (a-d)).indicator (fun _ : ℝ => (1 : ℝ))
  let hi := (Set.Icc (max t b) a).indicator (fun _ : ℝ => (1 : ℝ))
  have hn (u : ℝ) : 0 ≤ P u * Q (t-u) := mul_nonneg (hPb u).1 (hQb (t-u)).1
  have hup (u : ℝ) : P u * Q (t-u) ≤ hi u := by
    by_cases hu : u ∈ Set.Icc (max t b) a
    · simp only [hi, Set.indicator_of_mem hu]
      exact mul_le_one₀ (hPb u).2 (hQb (t-u)).1 (hQb (t-u)).2
    · simp only [hi, Set.indicator_of_notMem hu]
      by_cases hp : u ∈ Set.Icc b a
      · have ht : u < t := by
          simp only [Set.mem_Icc] at hp hu
          have hb := hp.1
          have ha := hp.2
          by_contra h
          exact hu ⟨max_le (le_of_not_gt h) hb, ha⟩
        rw [hQs (t-u) (by linarith), mul_zero]
      · rw [hPs u hp, zero_mul]
  have hlo (u : ℝ) : lo u ≤ P u * Q (t-u) := by
    by_cases hu : u ∈ Set.Icc (max (t+d) (b+d)) (a-d)
    · have hp := hPp u ((le_max_right _ _).trans hu.1) hu.2
      have hq := hQp (t-u) (by linarith [le_max_left (t+d) (b+d), hu.1])
      simp only [lo, Set.indicator_of_mem hu, hp, hq, mul_one, le_refl]
    · simpa only [lo, Set.indicator_of_notMem hu] using hn u
  have hf : Integrable (fun u => P u * Q (t-u)) :=
    (radial_interval_integral (max t b) a).1.mono'
      (hP.mul (hQ.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      (Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hn u)] using hup u)
  have hl := integral_mono (radial_interval_integral (max (t+d) (b+d)) (a-d)).1 hf hlo
  have hh := integral_mono hf (radial_interval_integral (max t b) a).1 hup
  change (∫ u, (Set.Icc (max (t+d) (b+d)) (a-d)).indicator (fun _ => (1 : ℝ)) u) ≤ _ at hl
  rw [(radial_interval_integral _ _).2] at hl
  change _ ≤ (∫ u, (Set.Icc (max t b) a).indicator (fun _ => (1 : ℝ)) u) at hh
  rw [(radial_interval_integral _ _).2] at hh
  have heq : (a-d)-max (t+d) (b+d) = a-2*d-max t b := by
    by_cases ht : t ≤ b
    · rw [max_eq_right ht, max_eq_right (by linarith : t+d ≤ b+d)]; ring
    · rw [max_eq_left (le_of_not_ge ht), max_eq_left (by linarith : b+d ≤ t+d)]; ring
  rw [heq] at hl
  refine ⟨hf, hl, hh, ?_⟩
  rw [abs_le]
  constructor
  · have hc : max (a-max t b) 0 ≤ max (a-2*d-max t b) 0 + 2*d := by
      apply max_le
      · linarith [le_max_left (a-2*d-max t b) 0]
      · linarith [le_max_right (a-2*d-max t b) 0]
    linarith
  · linarith

#check GeometricRound12D.radial_cutoff_integral_envelope
#print axioms GeometricRound12D.radial_cutoff_integral_envelope
end GeometricRound12D

namespace GeometricRound12D
/-- Converts the proved two-cutoff bounds to the exact premise of the r11
S-local smooth-volume limit, using width 2d. This is only an endpoint bridge. -/
theorem radial_bounds_to_r11_envelope
    (a b t d z : ℝ) (hd : 0 ≤ d)
    (hl : max (a-2*d-max t b) 0 ≤ z)
    (hu : z ≤ max (a-max t b) 0) :
    max (a-2*d-max t (b+2*d)) 0 ≤ z ∧
    z ≤ max (a+2*d-max t (b-2*d)) 0 := by
  constructor
  · apply le_trans ?_ hl
    apply max_le_max_right
    have hm : max t b ≤ max t (b+2*d) := max_le_max_left t (by linarith)
    linarith
  · apply le_trans hu
    apply max_le_max_right
    have hm : max t (b-2*d) ≤ max t b := max_le_max_left t (by linarith)
    linarith
#check GeometricRound12D.radial_bounds_to_r11_envelope
#print axioms GeometricRound12D.radial_bounds_to_r11_envelope
end GeometricRound12D

/-! Round 13 D. Precise premises of (12.4.1.22--24): parameter measurability,
absolute radial Fubini at finite cutoff, and removal of the radial envelope
hypothesis from r11 using r12. The actual Fourier density, normalized Haar
transport and kernel/operator identification remain independent obligations. -/
namespace GeometricRound13D
open MasulloGRH GeometricRound1D GeometricRound9D GeometricRound11D
  GeometricRound12D MeasureTheory Filter
open scoped Topology

/-- Discharges r12 dependency R12-13: measurability in the logarithmic radius. -/
theorem radial_integral_measurable (P Q : ℝ → ℝ)
    (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (fun t : ℝ => ∫ u : ℝ, P u * Q (t-u)) := by
  have hm : Measurable (fun z : ℝ × ℝ => P z.2 * Q (z.1-z.2)) :=
    (hP.comp measurable_snd).mul (hQ.comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- CONDITIONAL arithmetic radial Fubini for the very same two-cutoff
integrand in (12.4.1.22--23). Its absolute integrability is proved from L1 of
the density and finite spatial support; no integral-interchange premise is
assumed. The density h still must be the genuine Fourier density. -/
theorem sLocal_radial_cutoff_fubini
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) [SFinite mu]
    (h : HeckeAdeles K → ℂ) (hm : Measurable h) (hh : Integrable h mu)
    (ht : Measurable (fun x => Real.log (sLocalRadius K S x)))
    (a b : ℝ) (P Q : ℝ → ℝ) (hP : Measurable P) (hQ : Measurable Q)
    (hPb : ∀ u, 0 ≤ P u ∧ P u ≤ 1)
    (hQb : ∀ u, 0 ≤ Q u ∧ Q u ≤ 1)
    (hPs : ∀ u, u ∉ Set.Icc b a → P u = 0) :
    Integrable (fun z : HeckeAdeles K × ℝ =>
      h z.1 * ((P z.2 * Q (Real.log (sLocalRadius K S z.1)-z.2) : ℝ) : ℂ))
      (mu.prod volume) ∧
    (∫ x, (∫ u : ℝ, h x * ((P u * Q (Real.log (sLocalRadius K S x)-u) : ℝ) : ℂ)) ∂mu) =
      ∫ u : ℝ, ∫ x, h x * ((P u * Q (Real.log (sLocalRadius K S x)-u) : ℝ) : ℂ) ∂mu := by
  let t (x : HeckeAdeles K) := Real.log (sLocalRadius K S x)
  let J := (Set.Icc b a).indicator (fun _ : ℝ => (1 : ℝ))
  have hJ : Integrable J := (radial_interval_integral b a).1
  have hbnd (x : HeckeAdeles K) (u : ℝ) :
      |P u * Q (t x-u)| ≤ J u := by
    rw [abs_of_nonneg (mul_nonneg (hPb u).1 (hQb _).1)]
    by_cases hu : u ∈ Set.Icc b a
    · simp only [J, Set.indicator_of_mem hu]
      exact mul_le_one₀ (hPb u).2 (hQb _).1 (hQb _).2
    · simp only [J, Set.indicator_of_notMem hu, hPs u hu, zero_mul, le_refl]
  have hmprod : Measurable (fun z : HeckeAdeles K × ℝ =>
      h z.1 * ((P z.2 * Q (t z.1-z.2) : ℝ) : ℂ)) := by
    exact (hm.comp measurable_fst).mul (Complex.continuous_ofReal.measurable.comp
      ((hP.comp measurable_snd).mul
        (hQ.comp ((ht.comp measurable_fst).sub measurable_snd))))
  have hi : Integrable (fun z : HeckeAdeles K × ℝ =>
      h z.1 * ((P z.2 * Q (t z.1-z.2) : ℝ) : ℂ)) (mu.prod volume) := by
    refine (hh.norm.mul_prod hJ).mono' hmprod.aestronglyMeasurable ?_
    apply Eventually.of_forall
    intro z
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbnd z.1 z.2) (norm_nonneg _)
  exact ⟨hi, integral_integral_swap hi⟩

/-- CONDITIONAL actual-adele cutoff limit for (12.4.1.24--28), retaining
exact phi(C_K^1)=0. Compared with r11, neither measurable V nor its geometric
envelope is assumed: both are derived for the actual radial integral P*Q.
The L1/log moment, Fourier mass and Haar/kernel attachment remain explicit. -/
theorem sLocal_two_cutoff_limit_normOneVanishing
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K))
    (mu : Measure (HeckeAdeles K)) (h : HeckeAdeles K → ℂ)
    (phi : HeckeIdeleClasses K → ℂ) (hphi : NormOneVanishing K phi)
    (hmass : (∫ x, h x ∂mu) = phi 1) (hh : Integrable h mu)
    (ht : Measurable (fun x => Real.log (sLocalRadius K S x)))
    (hpos : ∀ᵐ x ∂mu, 0 < sLocalRadius K S x)
    (hmoment : Integrable (fun x => ‖h x‖ * |Real.log (sLocalRadius K S x)|) mu)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, b n ≤ 0)
    (halim : Tendsto a atTop atTop) (hblim : Tendsto b atTop atBot)
    (d : ℕ → ℝ) (hd : ∀ n, 0 ≤ d n) (hdlim : Tendsto d atTop (𝓝 0))
    (P Q : ℕ → ℝ → ℝ) (hP : ∀ n, Measurable (P n)) (hQ : ∀ n, Measurable (Q n))
    (hPb : ∀ n u, 0 ≤ P n u ∧ P n u ≤ 1)
    (hQb : ∀ n u, 0 ≤ Q n u ∧ Q n u ≤ 1)
    (hPs : ∀ n u, u ∉ Set.Icc (b n) (a n) → P n u = 0)
    (hQs : ∀ n u, 0 < u → Q n u = 0)
    (hPp : ∀ n u, b n+d n ≤ u → u ≤ a n-d n → P n u = 1)
    (hQp : ∀ n u, u ≤ -d n → Q n u = 1) :
    (∀ n, Integrable (fun x => h x *
      ((∫ u : ℝ, P n u * Q n (Real.log (sLocalRadius K S x)-u) : ℝ) : ℂ)) mu) ∧
    Tendsto (fun n => ∫ x, h x *
      ((∫ u : ℝ, P n u * Q n (Real.log (sLocalRadius K S x)-u) : ℝ) : ℂ) ∂mu)
      atTop (𝓝 (-∫ x, h x * (Real.log (sLocalRadius K S x) : ℂ) ∂mu)) := by
  let V (n : ℕ) (x : HeckeAdeles K) :=
    ∫ u : ℝ, P n u * Q n (Real.log (sLocalRadius K S x)-u)
  have hV (n : ℕ) : AEStronglyMeasurable (V n) mu :=
    ((radial_integral_measurable (P n) (Q n) (hP n) (hQ n)).comp ht).aestronglyMeasurable
  have henv (n : ℕ) : ∀ᵐ x ∂mu,
      max (a n-2*d n-max (Real.log (sLocalRadius K S x)) (b n+2*d n)) 0 ≤ V n x ∧
      V n x ≤ max (a n+2*d n-max (Real.log (sLocalRadius K S x)) (b n-2*d n)) 0 := by
    apply Eventually.of_forall
    intro x
    have H := radial_cutoff_integral_envelope (a n) (b n)
      (Real.log (sLocalRadius K S x)) (d n) (hd n) (P n) (Q n)
      (hP n) (hQ n) (hPb n) (hQb n) (hPs n) (hQs n) (hPp n) (hQp n)
    exact radial_bounds_to_r11_envelope _ _ _ _ _ (hd n) H.2.1 H.2.2.1
  have hdl : Tendsto (fun n => 2*d n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hdlim.const_mul 2
  have H := sLocal_smooth_volume_asymptotic K S mu h hh ht.aestronglyMeasurable
    hpos hmoment a b ha hb halim hblim (fun n => 2*d n)
    (fun n => mul_nonneg (by norm_num) (hd n)) hdl V hV henv
  have hz : (∫ x, h x ∂mu) = 0 := hmass.trans (hphi 1 (classModulus_one K))
  exact ⟨H.1, by simpa only [hz, zero_mul, sub_zero] using H.2⟩

#check GeometricRound13D.radial_integral_measurable
#print axioms GeometricRound13D.radial_integral_measurable
#check GeometricRound13D.sLocal_radial_cutoff_fubini
#print axioms GeometricRound13D.sLocal_radial_cutoff_fubini
#check GeometricRound13D.sLocal_two_cutoff_limit_normOneVanishing
#print axioms GeometricRound13D.sLocal_two_cutoff_limit_normOneVanishing
end GeometricRound13D

/-! Round 14 D review: discharge precisely the log-radius measurability
premise ht in the checked r13 finite-cutoff Fubini and two-cutoff limit.
This uses the genuine adele coordinates and finite-S radius, with the Borel
sigma algebra. It does not construct the Fourier density or its measure,
prove the zero-coordinate null set, or justify S-unit sum/limit exchange. -/
namespace GeometricRound14D
open MasulloGRH GeometricRound9D MeasureTheory

/-- Actual finite-S radius is continuous; this supplies the measurability
input to (12.4.1.22--24), not a surrogate arithmetic radius. -/
theorem sLocalRadius_continuous
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (NumberField.FinitePlace K)) :
    Continuous (sLocalRadius K S) := by
  unfold sLocalRadius
  apply Continuous.mul
  · exact continuous_finset_prod Finset.univ (fun w _ =>
      ((continuous_apply w).comp continuous_fst).norm.pow w.mult)
  · exact continuous_finset_prod S (fun v _ =>
      ((RestrictedProduct.continuous_eval v.maximalIdeal).comp continuous_snd).norm)

/-- Removes the explicit ht premise of r13 for the Borel structure on
actual adeles. Positivity a.e. and logarithmic integrability stay separate. -/
theorem sLocal_logRadius_measurable
    (K : Type*) [Field K] [NumberField K]
    [MeasurableSpace (HeckeAdeles K)] [BorelSpace (HeckeAdeles K)]
    (S : Finset (NumberField.FinitePlace K)) :
    Measurable (fun x : HeckeAdeles K => Real.log (sLocalRadius K S x)) := by
  exact Real.measurable_log.comp (sLocalRadius_continuous K S).measurable

#check GeometricRound14D.sLocalRadius_continuous
#print axioms GeometricRound14D.sLocalRadius_continuous
#check GeometricRound14D.sLocal_logRadius_measurable
#print axioms GeometricRound14D.sLocal_logRadius_measurable
end GeometricRound14D
