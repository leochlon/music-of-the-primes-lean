import Mathlib

namespace NativeShellCarving

/-- The manuscript unit masks decrease: removed shells have this sign. -/
theorem descending_return {C : Type*} [AddCommGroup C]
    (c : ℕ → C) (N : ℕ) :
    c 0 = c N + ∑ k ∈ Finset.range N, (c k - c (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    abel

/-- Carve BOTH actual theta columns; no cross term may be dropped. -/
theorem paired_mask_difference {R : Type*} [Ring R]
    (a b c d : R) : a*b-c*d = (a-c)*b+c*(b-d) := by
  noncomm_ring

/-- The original inverse Gram and the local inverse Gram differ by this term. -/
theorem gram_transport_defect {R : Type*} [Ring R]
    (f g p ft : R) : f*g*ft = f*p*ft + f*(g-p)*ft := by
  noncomm_ring

/-- Each carved orbital term retains the input-cutoff order correction. -/
theorem carved_input_order (h w ai aj mi mo : ℂ) :
    h*w*ai*aj*mo + h*w*ai*aj*(mi-mo) = h*w*ai*aj*mi := by
  ring

theorem logged_carved_input_order (ell h w ai aj mi mo : ℂ) :
    (-ell*h)*w*ai*aj*mo + (-ell*h)*w*ai*aj*(mi-mo) =
      (-ell*h)*w*ai*aj*mi := by
  ring

end NativeShellCarving

#print axioms NativeShellCarving.descending_return
#print axioms NativeShellCarving.gram_transport_defect
#print axioms NativeShellCarving.logged_carved_input_order
