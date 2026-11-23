import Mathlib
namespace DivisorialCarving

theorem telescoping (c : ℕ → ℂ) (n : ℕ) :
    c 0 = c n - ∑ k ∈ Finset.range n, (c (k+1)-c k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      c 0 = c n - ∑ k ∈ Finset.range n, (c (k+1)-c k) := ih
      _ = c (n+1) - ((∑ k ∈ Finset.range n, (c (k+1)-c k)) +
            (c (n+1)-c n)) := by ring

theorem mask_product_drop (a b c d : ℝ) :
    a*b-c*d=(a-c)*b+c*(b-d) := by ring

theorem inverse_defect {R : Type*} [Ring R] (g k gi ki : R)
    (hg : gi*g=1) (hk : k*ki=1) :
    gi-ki=gi*(k-g)*ki := by
  calc
    gi-ki=gi*1-1*ki := by simp
    _=gi*(k*ki)-(gi*g)*ki := by rw [hg, hk]
    _=gi*(k-g)*ki := by noncomm_ring

theorem gram_defect {R : Type*} [Ring R] (f fs gi ki : R) :
    f*gi*fs-f*ki*fs=f*(gi-ki)*fs := by noncomm_ring

#print axioms telescoping
#print axioms inverse_defect
#print axioms gram_defect
end DivisorialCarving
