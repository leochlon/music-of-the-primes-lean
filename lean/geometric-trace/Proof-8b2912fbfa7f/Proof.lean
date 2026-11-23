import Mathlib
set_option linter.unusedSimpArgs false
namespace CriticalLineAudit
/-- Discharges the complex-place angular Fubini majorant premise: for each
normalized radius q<1, the double geometric expansion of the squared trace
kernel is absolutely summable, with one majorant independent of the angle.
The actual radial substitution is q=exp(-x/2), since the complex norm is squared. -/
theorem complexPlace_angular_geometric_expansion {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun p : ℕ × ℕ => q ^ p.1 * q ^ p.2) ((1-q)⁻¹ * (1-q)⁻¹) ∧
    ∀ u : ℂ, ‖u‖ = 1 →
      (∀ p : ℕ × ℕ,
        ‖((q : ℂ) * u)^p.1 * ((q : ℂ) * (starRingEnd ℂ) u)^p.2‖ =
          q^p.1 * q^p.2) ∧
      HasSum (fun p : ℕ × ℕ =>
        ((q : ℂ) * u)^p.1 * ((q : ℂ) * (starRingEnd ℂ) u)^p.2)
        (((‖1 - (q : ℂ) * u‖ ^ 2 : ℝ) : ℂ)⁻¹) := by
  have hg : HasSum (fun n : ℕ => q^n) (1-q)⁻¹ :=
    hasSum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hq] using hq1)
  have hgn : Summable (fun n : ℕ => ‖q^n‖) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq _)] using hg.summable
  have hmaj : Summable (fun p : ℕ × ℕ => q^p.1 * q^p.2) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hq _) (pow_nonneg hq _)), abs_of_nonneg hq]
      using hgn.mul_norm hgn
  refine ⟨hg.mul hg hmaj, ?_⟩
  intro u hu
  have hnu : ‖(q : ℂ) * u‖ = q := by simp [norm_mul, hu, abs_of_nonneg hq]
  have hnv : ‖(q : ℂ) * (starRingEnd ℂ) u‖ = q := by
    simp [norm_mul, hu, abs_of_nonneg hq]
  have hnorm : ∀ p : ℕ × ℕ,
      ‖((q : ℂ) * u)^p.1 * ((q : ℂ) * (starRingEnd ℂ) u)^p.2‖ =
        q^p.1 * q^p.2 := by
    intro p
    rw [norm_mul, norm_pow, norm_pow, hnu, hnv]
  refine ⟨hnorm, ?_⟩
  have habs : Summable (fun p : ℕ × ℕ =>
      ‖((q : ℂ) * u)^p.1 * ((q : ℂ) * (starRingEnd ℂ) u)^p.2‖) := by
    simpa only [hnorm] using hmaj
  have hsum := (hasSum_geometric_of_norm_lt_one (hnu.trans_lt hq1)).mul
    (hasSum_geometric_of_norm_lt_one (hnv.trans_lt hq1)) habs.of_norm
  have he : (1 - (q : ℂ) * u) * (1 - (q : ℂ) * (starRingEnd ℂ) u) =
      ((‖1 - (q : ℂ) * u‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = (1 - (q : ℂ) * u) * (starRingEnd ℂ) (1 - (q : ℂ) * u) := by simp
      _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [← mul_inv, he] at hsum
  exact hsum
#check complexPlace_angular_geometric_expansion
#print axioms complexPlace_angular_geometric_expansion
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
/-- Discharges the angular infinite-sum/integral interchange premise in
§1.4.3 for every continuous unit-bounded angular character profile and every
finite angular measure. The dominating geometric sum is derived above,
not assumed. Haar normalization and orthogonality are separate next steps. -/
theorem complexPlace_angular_integral_hasSum
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (χ : Circle → ℂ) (hχ : Continuous χ) (hχnorm : ∀ u, ‖χ u‖ ≤ 1)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun p : ℕ × ℕ => ∫ u : Circle,
      χ u * (((q : ℂ) * (u : ℂ))^p.1 *
        ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^p.2) ∂μ)
      (∫ u : Circle, χ u * (((‖1 - (q : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹) ∂μ) := by
  have hg := complexPlace_angular_geometric_expansion hq hq1
  apply hasSum_integral_of_dominated_convergence
    (fun p : ℕ × ℕ => fun _ : Circle => q^p.1 * q^p.2)
  · intro p
    have hc : Continuous (fun u : Circle =>
        χ u * (((q : ℂ) * (u : ℂ))^p.1 *
          ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^p.2)) := by fun_prop
    exact hc.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall (fun u => by
      rw [norm_mul, (hg.2 (u : ℂ) (Circle.norm_coe u)).1 p]
      exact mul_le_of_le_one_left
        (mul_nonneg (pow_nonneg hq _) (pow_nonneg hq _)) (hχnorm u))
  · exact Eventually.of_forall (fun _ => hg.1.summable)
  · simpa only [hg.1.tsum_eq] using
      (integrable_const ((1-q)⁻¹ * (1-q)⁻¹) :
        Integrable (fun _ : Circle => (1-q)⁻¹ * (1-q)⁻¹) μ)
  · exact Eventually.of_forall (fun u =>
      ((hg.2 (u : ℂ) (Circle.norm_coe u)).2).mul_left (χ u))
#check complexPlace_angular_integral_hasSum
#print axioms complexPlace_angular_integral_hasSum
end CriticalLineAudit

set_option linter.unusedSimpArgs false
namespace CriticalLineAudit
/-- Connects the normalized geometric expansion to the actual complex-place
trace denominator |1-r*u|^2. This is needed before the radial substitution
x=log(r^2); it is not a replacement kernel. -/
theorem complexPlace_actual_denominator_norm {r : ℝ} (hr : 1 < r)
    {u : ℂ} (hu : ‖u‖ = 1) :
    ‖1 - (r : ℂ) * u‖ = r * ‖1 - ((r⁻¹ : ℝ) : ℂ) * u‖ := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrpos
  have hi : (r : ℂ) * ((r⁻¹ : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_inv, mul_inv_cancel₀ hr0]
  have hu0 : u * (starRingEnd ℂ) u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  have he : 1 - (r : ℂ) * u =
      (-(r : ℂ) * u) * (1 - ((r⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) u) := by
    calc
      _ = -(r : ℂ) * u + ((r : ℂ) * ((r⁻¹ : ℝ) : ℂ)) *
          (u * (starRingEnd ℂ) u) := by rw [hi, hu0]; ring
      _ = _ := by ring
  have hc : ‖1 - ((r⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) u‖ =
      ‖1 - ((r⁻¹ : ℝ) : ℂ) * u‖ := by
    have hs : 1 - ((r⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) u =
        (starRingEnd ℂ) (1 - ((r⁻¹ : ℝ) : ℂ) * u) := by simp
    rw [hs]
    exact Complex.norm_conj _
  rw [he, norm_mul, hc]
  simp [norm_mul, hu, abs_of_pos hrpos]
#check complexPlace_actual_denominator_norm
#print axioms complexPlace_actual_denominator_norm
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩

/-- Discharges the Haar cancellation premise for every nontrivial angular
character, with the actual measure invariant under multiplication. -/
theorem angularHaar_nontrivial_character (μ : Measure Circle)
    [μ.IsMulLeftInvariant] (χ : Circle →* ℂ)
    (hχ : ∃ g, χ g ≠ 1) : (∫ u : Circle, χ u ∂μ) = 0 := by
  obtain ⟨g, hg⟩ := hχ
  have hi := integral_mul_left_eq_self (μ := μ) (fun u => χ u) g
  simp only [map_mul, integral_const_mul] at hi
  have hz : (χ g - 1) * (∫ u : Circle, χ u ∂μ) = 0 := by
    rw [sub_mul, one_mul, hi, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hg)

/-- Discharges the uniform angular-series convergence premise on every
closed radius interval [0,Q], Q<1; the bound is independent of angle.
It does not assert a bound as Q tends to one. -/
theorem complexPlace_angular_normal_convergence {Q : ℝ}
    (hQ : 0 ≤ Q) (hQ1 : Q < 1) :
    TendstoUniformlyOn
      (fun S : Finset (ℕ × ℕ) => fun x : ℝ × Circle =>
        ∑ p ∈ S, (((x.1 : ℂ) * (x.2 : ℂ))^p.1 *
          ((x.1 : ℂ) * (starRingEnd ℂ) (x.2 : ℂ))^p.2))
      (fun x => ∑' p : ℕ × ℕ, (((x.1 : ℂ) * (x.2 : ℂ))^p.1 *
          ((x.1 : ℂ) * (starRingEnd ℂ) (x.2 : ℂ))^p.2))
      atTop {x | 0 ≤ x.1 ∧ x.1 ≤ Q} := by
  apply tendstoUniformlyOn_tsum (complexPlace_angular_geometric_expansion hQ hQ1).1.summable
  intro p x hx
  rw [((complexPlace_angular_geometric_expansion hx.1
    (lt_of_le_of_lt hx.2 hQ1)).2 (x.2 : ℂ) (Circle.norm_coe x.2)).1 p]
  exact mul_le_mul (pow_le_pow_left₀ hx.1 hx.2 p.1)
    (pow_le_pow_left₀ hx.1 hx.2 p.2) (pow_nonneg hx.1 _) (pow_nonneg hQ _)

/-- Discharges the angular sum/integral interchange for the ACTUAL complex
trace denominator |1-r*u|^2, r>1. The r^-2 normalization is explicit and
no radial integrability, zero sum, or trace formula is assumed. -/
theorem complexPlace_actual_angular_integral_hasSum
    (μ : Measure Circle) [IsFiniteMeasure μ]
    (χ : Circle → ℂ) (hχ : Continuous χ) (hχnorm : ∀ u, ‖χ u‖ ≤ 1)
    {r : ℝ} (hr : 1 < r) :
    HasSum (fun p : ℕ × ℕ => ((r : ℂ)^2)⁻¹ * ∫ u : Circle,
      χ u * ((((r⁻¹ : ℝ) : ℂ) * (u : ℂ))^p.1 *
        (((r⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ) (u : ℂ))^p.2) ∂μ)
      (∫ u : Circle, χ u * (((‖1 - (r : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹) ∂μ) := by
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hq : 0 ≤ r⁻¹ := inv_nonneg.mpr hrpos.le
  have hq1 : r⁻¹ < 1 := (inv_lt_one₀ hrpos).2 hr
  have hs := (complexPlace_angular_integral_hasSum μ χ hχ hχnorm hq hq1).mul_left
    (((r : ℂ)^2)⁻¹)
  rw [← integral_const_mul] at hs
  have he : (fun u : Circle => ((r : ℂ)^2)⁻¹ *
        (χ u * (((‖1 - ((r⁻¹ : ℝ) : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹))) =
      (fun u : Circle => χ u * (((‖1 - (r : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹)) := by
    funext u
    rw [complexPlace_actual_denominator_norm hr (Circle.norm_coe u), mul_pow,
      Complex.ofReal_mul, Complex.ofReal_pow, mul_inv]
    simp only [Complex.ofReal_pow]
    ring
  rw [he] at hs
  exact hs
#check angularHaar_nontrivial_character
#print axioms angularHaar_nontrivial_character
#check complexPlace_angular_normal_convergence
#print axioms complexPlace_angular_normal_convergence
#check complexPlace_actual_angular_integral_hasSum
#print axioms complexPlace_actual_angular_integral_hasSum
end CriticalLineAudit

namespace CriticalLineAudit
/-- Needed for the angular Haar diagonal surviving the complex-place expansion. -/
theorem angular_diagonal (q : ℝ) (u : Circle) (n : ℕ) :
  ((q : ℂ) * (u : ℂ))^n * ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^n =
    (q : ℂ)^(2*n) := by
  rw [← mul_pow]
  have hu : (u : ℂ) * (starRingEnd ℂ) (u : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have he : ((q : ℂ) * (u : ℂ)) * ((q : ℂ) * (starRingEnd ℂ) (u : ℂ)) = (q : ℂ)^2 := by
    calc
      _ = (q : ℂ)^2 * ((u : ℂ) * (starRingEnd ℂ) (u : ℂ)) := by ring
      _ = _ := by rw [hu, mul_one]
  rw [he, pow_mul]
#check angular_diagonal
#print axioms angular_diagonal
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
/-- Discharges the surviving diagonal series evaluation needed after Haar
orthogonality in the complex-place local-uniform-bound argument. Angular
probability normalization is explicit; off-diagonal cancellation is separate. -/
theorem complexPlace_angular_diagonal_integral_hasSum
    (μ : Measure Circle) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => ∫ u : Circle,
      ((q : ℂ) * (u : ℂ))^n * ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^n ∂μ)
      (1 - (q : ℂ)^2)⁻¹ := by
  have hp : ∀ n : ℕ, (∫ u : Circle,
      ((q : ℂ) * (u : ℂ))^n * ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^n ∂μ) =
        (q : ℂ)^(2*n) := by
    intro n
    simp only [angular_diagonal]
    simp
  have hnorm : ‖(q : ℂ)^2‖ < 1 := by
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    nlinarith
  simpa only [hp, pow_mul] using hasSum_geometric_of_norm_lt_one hnorm
#check complexPlace_angular_diagonal_integral_hasSum
#print axioms complexPlace_angular_diagonal_integral_hasSum
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
/-- Discharges the missing nontriviality premise for every off-diagonal
angular monomial of the actual complex-place denominator expansion. -/
theorem angular_offDiagonal_nontrivial {m n : ℕ} (hmn : m ≠ n) :
    ∃ u : Circle, (u : ℂ)^m * (starRingEnd ℂ) (u : ℂ)^n ≠ 1 := by
  let t : ℝ := Real.pi / ((m : ℝ) - n)
  let u : Circle := Circle.exp t
  refine ⟨u, ?_⟩
  intro he
  have hmnC : (m : ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hu : (starRingEnd ℂ) (u : ℂ) * (u : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have hp : (u : ℂ)^m = (u : ℂ)^n := by
    calc
      _ = ((u : ℂ)^m * (starRingEnd ℂ) (u : ℂ)^n) * (u : ℂ)^n := by
        rw [mul_assoc, ← mul_pow, hu, one_pow, mul_one]
      _ = _ := by rw [he, one_mul]
  have heq : Complex.exp ((m : ℂ) * ((t : ℂ) * Complex.I)) =
      Complex.exp ((n : ℂ) * ((t : ℂ) * Complex.I)) := by
    simpa only [Complex.exp_nat_mul, ← Circle.coe_exp] using hp
  have ha : (Real.pi : ℂ) * Complex.I =
      (m : ℂ) * ((t : ℂ) * Complex.I) - (n : ℂ) * ((t : ℂ) * Complex.I) := by
    dsimp [t]
    push_cast
    field_simp
  have hh : Complex.exp ((Real.pi : ℂ) * Complex.I) = 1 := by
    rw [ha, Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  rw [Complex.exp_pi_mul_I] at hh
  norm_num at hh

/-- Discharges precisely the off-diagonal Haar cancellation premise in the
complex-place local uniform estimate of section 1.4.3. -/
theorem angular_offDiagonal_integral (μ : Measure Circle) [μ.IsMulLeftInvariant]
    {m n : ℕ} (hmn : m ≠ n) :
    (∫ u : Circle, (u : ℂ)^m * (starRingEnd ℂ) (u : ℂ)^n ∂μ) = 0 := by
  let χ : Circle →* ℂ := (Circle.coeHom ^ m) *
    (((starRingEnd ℂ).toMonoidHom.comp Circle.coeHom) ^ n)
  exact angularHaar_nontrivial_character μ χ (angular_offDiagonal_nontrivial hmn)
#check angular_offDiagonal_nontrivial
#print axioms angular_offDiagonal_nontrivial
#check angular_offDiagonal_integral
#print axioms angular_offDiagonal_integral
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
/-- Supplies the exact Haar integral of each angular expansion coefficient,
including every off-diagonal term, needed for the sharp complex bound. -/
theorem angular_monomial_integral (μ : Measure Circle)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (q : ℝ) (m n : ℕ) :
    (∫ u : Circle, ((q : ℂ) * (u : ℂ))^m *
      ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^n ∂μ) =
        if m = n then (q : ℂ)^(2*m) else 0 := by
  classical
  by_cases h : m = n
  · subst n
    simp [angular_diagonal]
  · rw [if_neg h]
    have he : (fun u : Circle => ((q : ℂ) * (u : ℂ))^m *
        ((q : ℂ) * (starRingEnd ℂ) (u : ℂ))^n) =
        (fun u : Circle => ((q : ℂ)^m * (q : ℂ)^n) *
          ((u : ℂ)^m * (starRingEnd ℂ) (u : ℂ)^n)) := by
      funext u
      simp only [mul_pow]
      ring
    rw [he, integral_const_mul, angular_offDiagonal_integral μ h, mul_zero]

/-- Discharges the sharp normalized angular average in section 1.4.3;
it improves the crude geometric majorant at the singular radius q=1. -/
theorem complexPlace_normalized_Haar_average (μ : Measure Circle)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∫ u : Circle, (((‖1 - (q : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹) ∂μ) =
      (1 - (q : ℂ)^2)⁻¹ := by
  classical
  have hs := complexPlace_angular_integral_hasSum μ (fun _ => 1)
    continuous_const (by intro u; simp) hq hq1
  simp only [one_mul, angular_monomial_integral μ q] at hs
  have hf : ∀ m : ℕ, HasSum
      (fun n : ℕ => if m = n then (q : ℂ)^(2*m) else 0) ((q : ℂ)^(2*m)) := by
    intro m
    simpa only [eq_comm] using (hasSum_ite_eq m ((q : ℂ)^(2*m)))
  have ht := hs.prod_fiberwise hf
  have hd := complexPlace_angular_diagonal_integral_hasSum μ hq hq1
  simp only [angular_diagonal] at hd
  simp only [integral_const, probReal_univ, one_smul] at hd
  exact ht.unique hd
#check angular_monomial_integral
#print axioms angular_monomial_integral
#check complexPlace_normalized_Haar_average
#print axioms complexPlace_normalized_Haar_average
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
/-- Discharges the exact unweighted Haar average for the manuscript's ACTUAL
complex denominator, at every r>1, with normalized angular Haar measure. -/
theorem complexPlace_actual_Haar_average (μ : Measure Circle)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    {r : ℝ} (hr : 1 < r) :
    (∫ u : Circle, (((‖1 - (r : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹) ∂μ) =
      ((r : ℂ)^2 - 1)⁻¹ := by
  have hrp : 0 < r := lt_trans zero_lt_one hr
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hrp
  have he : (fun u : Circle => (((‖1 - (r : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹)) =
      (fun u : Circle => ((r : ℂ)^2)⁻¹ *
        (((‖1 - ((r⁻¹ : ℝ) : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹)) := by
    funext u
    rw [complexPlace_actual_denominator_norm hr (Circle.norm_coe u), mul_pow,
      Complex.ofReal_mul, Complex.ofReal_pow, mul_inv]
  rw [he, integral_const_mul, complexPlace_normalized_Haar_average μ
    (inv_nonneg.mpr hrp.le) ((inv_lt_one₀ hrp).2 hr), ← mul_inv]
  congr 1
  rw [Complex.ofReal_inv]
  field_simp

#check complexPlace_actual_Haar_average
#print axioms complexPlace_actual_Haar_average
end CriticalLineAudit

namespace CriticalLineAudit
open MeasureTheory Filter
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
/-- Discharges the angular majorant for EVERY unit-bounded profile in the
complex-place approximation family. The bound is independent of the profile;
radial integration with the anchored difference remains a separate premise. -/
theorem complexPlace_actual_Haar_profile_bound (μ : Measure Circle)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
    (χ : Circle → ℂ) (hχ : ∀ u, ‖χ u‖ ≤ 1)
    {r : ℝ} (hr : 1 < r) :
    ‖∫ u : Circle, χ u * (((‖1 - (r : ℂ) * (u : ℂ)‖^2 : ℝ) : ℂ)⁻¹) ∂μ‖ ≤
      (r^2 - 1)⁻¹ := by
  have hrp : 0 < r := lt_trans zero_lt_one hr
  have hn (u : Circle) : 1 - (r : ℂ) * (u : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp he)
    simp [norm_mul, Circle.norm_coe, abs_of_pos hrp] at hh
    linarith
  have hc : Continuous (fun u : Circle => (‖1 - (r : ℂ) * (u : ℂ)‖^2)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro u
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (hn u))
  have hi := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) (μ := μ)
  have havg : (∫ u : Circle, (‖1 - (r : ℂ) * (u : ℂ)‖^2)⁻¹ ∂μ) =
      (r^2 - 1)⁻¹ := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simpa using complexPlace_actual_Haar_average μ hr
  rw [← havg]
  apply norm_integral_le_of_norm_le hi
  exact Eventually.of_forall (fun u => by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (sq_nonneg _)) (hχ u))
#check complexPlace_actual_Haar_profile_bound
#print axioms complexPlace_actual_Haar_profile_bound
end CriticalLineAudit
