import Mathlib

namespace NativeSourceDefectK34

theorem ordered_local_correction (wide narrow source correction : ℂ)
    (h : wide - correction = narrow + source) :
    correction = wide - narrow - source := by linear_combination -h

theorem error_composition (a b c : ℂ) (u v : ℝ)
    (h₁ : ‖a-b‖ ≤ u) (h₂ : ‖b-c‖ ≤ v) : ‖a-c‖ ≤ u+v := by
  calc
    ‖a-c‖ = ‖(a-b)+(b-c)‖ := by congr 1; ring
    _ ≤ ‖a-b‖ + ‖b-c‖ := norm_add_le _ _
    _ ≤ u+v := add_le_add h₁ h₂

theorem finite_source_shells (b : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range n, (b k-b (k+1)) = b 0-b n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem source_pairing_subtract_constant (m c z : ℂ) (hz : z=0) :
    m-c*z=m := by simp [hz]

end NativeSourceDefectK34

#print axioms NativeSourceDefectK34.ordered_local_correction
#print axioms NativeSourceDefectK34.error_composition
#print axioms NativeSourceDefectK34.finite_source_shells
#print axioms NativeSourceDefectK34.source_pairing_subtract_constant
