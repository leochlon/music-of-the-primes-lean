import Mathlib

/- Independent Fermat escape estimate and actual strict boundary mask.
   No RH, EveryCharacter or right-half-plane nonvanishing premise. -/
open Complex Filter Topology
namespace RetainedHalfPlaneR03

theorem source_escape {ρ : ℕ → ℂ} (hρ0 : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ j in atTop, R ≤ ‖ρ j‖ := by
  have h0 := hsum.tendsto_atTop_zero
  simp_rw [Complex.normSq_eq_norm_sq] at h0
  have hR2 : (0 : ℝ) < (R ^ 2)⁻¹ := by positivity
  filter_upwards [h0.eventually_lt_const hR2] with j hj
  have hnj : 0 < ‖ρ j‖ := norm_pos_iff.mpr (hρ0 j)
  have hsq : R ^ 2 ≤ ‖ρ j‖ ^ 2 := by
    rw [← inv_le_inv₀ (by positivity) (by positivity)]
    exact le_of_lt (by simpa using hj)
  nlinarith [sq_nonneg (R - ‖ρ j‖), sq_nonneg (R + ‖ρ j‖)]

noncomputable def retained (α s : ℝ) (ρ : ℂ) (k : ℕ) : ℂ :=
  if |ρ.re - 1/2| < α ∨ (|ρ.re - 1/2| = α ∧ (2 : ℝ)*k+1 < s)
  then 1 else 0

/-- A single source-weight majorant controls ALL retained copies, including
boundary jets, throughout the narrow witness half-plane on a bounded set. -/
theorem retained_majorant (α s δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (z ρ : ℂ) (k : ℕ) (hρ : ρ ≠ 0) (hz : ‖z‖ ≤ R)
    (hgap : 1/2 + α + δ ≤ z.re) :
    ‖retained α s ρ k * ((z-ρ)^2)⁻¹‖ ≤
      ((δ+R)/δ)^2 * (Complex.normSq ρ)⁻¹ := by
  unfold retained
  split_ifs with h
  · have hrre : ρ.re ≤ 1/2 + α := by
      have habs : |ρ.re - 1/2| ≤ α := by
        rcases h with h | h
        · exact h.le
        · exact h.1.le
      have := le_abs_self (ρ.re - 1/2)
      linarith
    have hd : δ ≤ ‖z-ρ‖ := by
      have := Complex.re_le_norm (z-ρ)
      simp only [sub_re] at this
      linarith
    have hd0 : 0 < ‖z-ρ‖ := lt_of_lt_of_le hδ hd
    have hr0 : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
    have hn : ‖ρ‖ ≤ ‖z-ρ‖ + R := by
      have ht := norm_sub_norm_le ρ z
      rw [norm_sub_rev] at ht
      linarith
    have hratio : ‖ρ‖ / ‖z-ρ‖ ≤ (δ+R)/δ := by
      apply (div_le_div_iff₀ hd0 hδ).mpr
      nlinarith [mul_le_mul_of_nonneg_right hn hδ.le,
        mul_nonneg hR (sub_nonneg.mpr hd)]
    simp only [one_mul, norm_inv, norm_pow, Complex.normSq_eq_norm_sq]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (sq_pos_of_pos hr0)).mpr
    calc
      (‖z-ρ‖^2)⁻¹ * ‖ρ‖^2 = (‖ρ‖ / ‖z-ρ‖)^2 := by
        rw [div_pow, div_eq_mul_inv, mul_comm]
      _ ≤ ((δ+R)/δ)^2 := by gcongr
  · simp only [zero_mul, norm_zero]
    exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (Complex.normSq_nonneg _))

/-- Exact retained-zero normal convergence on each bounded right-half-plane
patch. The arithmetic input is the source's multiplicity-indexed square sum. -/
theorem retained_uniform (α s δ R : ℝ) (hδ : 0 < δ) (hR : 0 ≤ R)
    (ρ : ℕ → ℂ) (jet : ℕ → ℕ) (hρ : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹) :
    TendstoUniformlyOn
      (fun S : Finset ℕ => fun z : ℂ =>
        ∑ j ∈ S, retained α s (ρ j) (jet j) * ((z-ρ j)^2)⁻¹)
      (fun z : ℂ => ∑' j, retained α s (ρ j) (jet j) * ((z-ρ j)^2)⁻¹)
      atTop {z : ℂ | ‖z‖ ≤ R ∧ 1/2 + α + δ ≤ z.re} := by
  apply tendstoUniformlyOn_tsum (hsum.mul_left (((δ+R)/δ)^2))
  intro j z hz
  exact retained_majorant α s δ R hδ hR z (ρ j) (jet j) (hρ j) hz.1 hz.2


/-- The actual retained part is holomorphic at every same-width witness point.
This is derived from the source weight bound, not assumed regularity. -/
theorem retained_differentiableAt (α s : ℝ)
    (ρ : ℕ → ℂ) (jet : ℕ → ℕ) (hρ : ∀ j, ρ j ≠ 0)
    (hsum : Summable fun j => (Complex.normSq (ρ j))⁻¹)
    (q : ℂ) (hq : 1/2 + α < q.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => ∑' j, retained α s (ρ j) (jet j) * ((z-ρ j)^2)⁻¹) q := by
  classical
  let δ : ℝ := (q.re - (1/2 + α))/2
  let R : ℝ := ‖q‖ + 1
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let U : Set ℂ := {z | ‖z‖ < R ∧ 1/2 + α + δ < z.re}
  have ho : IsOpen U := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_re)
  have hqU : q ∈ U := by
    constructor
    · dsimp [R]; linarith
    · dsimp [δ]; linarith
  have hc := (retained_uniform α s δ R hδ hR ρ jet hρ hsum).mono
    (show U ⊆ {z : ℂ | ‖z‖ ≤ R ∧ 1/2 + α + δ ≤ z.re} from
      fun z hz => ⟨hz.1.le, hz.2.le⟩)
  have ht : ∀ j, DifferentiableOn ℂ
      (fun z : ℂ => retained α s (ρ j) (jet j) * ((z-ρ j)^2)⁻¹) U := by
    intro j
    by_cases hh : |(ρ j).re - 1/2| < α ∨
      (|(ρ j).re - 1/2| = α ∧ (2 : ℝ)*(jet j)+1 < s)
    · have hr : (ρ j).re ≤ 1/2 + α := by
        have habs : |(ρ j).re - 1/2| ≤ α := by
          rcases hh with h | h
          · exact h.le
          · exact h.1.le
        have := le_abs_self ((ρ j).re - 1/2)
        linarith
      intro z hz
      have hn : z-ρ j ≠ 0 := by
        intro he
        have heq := sub_eq_zero.mp he
        have hzr := hz.2
        rw [heq] at hzr
        linarith
      exact ((differentiableAt_const (retained α s (ρ j) (jet j))).mul
        (((differentiableAt_id.sub (differentiableAt_const (ρ j))).pow 2).inv
          (pow_ne_zero 2 hn))).differentiableWithinAt
    · simp only [retained, if_neg hh, zero_mul]
      exact differentiableOn_const 0
  have hd := hc.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun S => DifferentiableOn.fun_sum fun j _ => ht j) ho
  exact hd.differentiableAt (ho.mem_nhds hqU)

end RetainedHalfPlaneR03
#print axioms RetainedHalfPlaneR03.source_escape
#print axioms RetainedHalfPlaneR03.retained_majorant
#print axioms RetainedHalfPlaneR03.retained_uniform

#print axioms RetainedHalfPlaneR03.retained_differentiableAt
