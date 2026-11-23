import Mathlib

namespace NativePWCorrection

theorem condensation_defect {R : Type*} [Ring R] (m s a : R)
    (hinvariant : s*a*s=a*s) :
    m*s*a-m*a*s=m*s*a*(1-s) := by
  calc
    m*s*a-m*a*s = m*s*a-m*(s*a*s) := by rw [hinvariant]; noncomm_ring
    _ = m*s*a*(1-s) := by noncomm_ring

theorem finite_condensation_split {R : Type*} [Ring R] (m s a e : R) :
    m*s*a-m*s*a*e = m*s*a*(s-e)+m*s*a*(1-s) := by
  noncomm_ring

theorem tensor_order_by_coordinates {H K I : Type*}
    (p a t : H → H) (eta : I → H → K)
    (hp : ∀ x, p (p x)=p x) (ht : ∀ x, p (t x)=t x)
    (heta : ∀ i x, eta i (p x)=eta i x)
    (hcoord : ∀ i x, eta i (t x)=eta i (a x))
    (hsep : ∀ x y, p x=x → p y=y →
      (∀ i, eta i x=eta i y) → x=y) :
    ∀ x, t x=p (a x) := by
  intro x
  apply hsep (t x) (p (a x)) (ht x) (hp (a x))
  intro i
  rw [hcoord, heta]

#print axioms condensation_defect
#print axioms tensor_order_by_coordinates
end NativePWCorrection
