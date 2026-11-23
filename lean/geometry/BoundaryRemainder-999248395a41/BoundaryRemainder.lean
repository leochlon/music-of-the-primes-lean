import Mathlib

/-! Rational trivial-character radial bookkeeping. The Mellin integral is
with du, the actual radial Haar in F35/F36. No zero exclusion or infinite
remainder limit is asserted. The boundary admission criterion stays strict. -/
namespace FReview.BoundaryRemainder
open MeasureTheory
noncomputable section

def boundaryOrders (N : ℕ) (s : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun j => (2 : ℝ)*j+1<s)

theorem boundaryOrders_exact (N : ℕ) (s : ℝ) :
    boundaryOrders N s = Finset.range (min N (Nat.ceil ((s-1)/2))) := by
  classical
  ext j
  simp only [boundaryOrders, Finset.mem_filter, Finset.mem_range, Nat.lt_min, Nat.lt_ceil]
  constructor
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩
  · rintro ⟨hN, hs⟩
    exact ⟨hN, by linarith⟩

def GenuineZero := {rho : ℂ // completedRiemannZeta rho = 0 ∧ rho ≠ 0 ∧ rho ≠ 1}

def zeroOrder (rho : GenuineZero) : ℕ := (analyticOrderAt completedRiemannZeta rho.val).toNat

def retained (a l r s : ℝ) (rho : GenuineZero) : ℕ :=
  if a+l < rho.val.re ∧ rho.val.re < a+r then zeroOrder rho
  else if rho.val.re = a+l ∨ rho.val.re = a+r then
    min (zeroOrder rho) (Nat.ceil ((s-1)/2)) else 0

theorem retained_le (a l r s : ℝ) (rho : GenuineZero) :
    retained a l r s rho ≤ zeroOrder rho := by
  unfold retained
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _
  · exact Nat.zero_le _

def radialMellin (a : ℝ) (h : ℝ → ℂ) (rho : GenuineZero) : ℂ :=
  ∫ u : ℝ, h u * Complex.exp ((rho.val-(a : ℂ))*(u : ℂ))

/-- Every genuine zero retains its omitted multiplicity, including edge jets.
The universal h covers h0 and h1(u)=-u*h0(u) separately. -/
theorem actual_retained_omitted_balance (a l r s : ℝ) (h : ℝ → ℂ)
    (rho : GenuineZero) :
    (retained a l r s rho : ℂ)*radialMellin a h rho +
      ((zeroOrder rho-retained a l r s rho : ℕ) : ℂ)*radialMellin a h rho =
        (zeroOrder rho : ℂ)*radialMellin a h rho := by
  have hn := Nat.sub_add_cancel (retained_le a l r s rho)
  have hc : (retained a l r s rho : ℂ) +
      ((zeroOrder rho-retained a l r s rho : ℕ) : ℂ) = (zeroOrder rho : ℂ) := by
    exact_mod_cast (Nat.add_comm _ _).trans hn
  rw [← add_mul, hc]

#print axioms boundaryOrders_exact
#print axioms actual_retained_omitted_balance
end
end FReview.BoundaryRemainder
