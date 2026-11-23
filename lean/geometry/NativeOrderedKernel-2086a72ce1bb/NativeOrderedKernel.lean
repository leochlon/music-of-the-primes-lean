import Mathlib
namespace NativeOrderedKernel

theorem native_order_defect {R : Type*} [Ring R] (s a : R)
    (hsource : (1-s)*a*s=0) : s*a-a*s=s*a*(1-s) := by
  have hx : (1-s)*a*s=a*s-s*a*s := by noncomm_ring
  rw [hx] at hsource
  have ha : a*s=s*a*s := sub_eq_zero.mp hsource
  calc
    s*a-a*s = s*a-s*a*s := by rw [ha]
    _ = s*a*(1-s) := by noncomm_ring

theorem cutoff_kernel_sign (h mx my : ℂ) :
    h*my-mx*h=h*(my-mx) := by ring

theorem logged_commutator (h mx my u : ℂ) :
    (-u*h)*my-mx*(-u*h)=(-u)*(h*(my-mx)) := by ring

#print axioms native_order_defect
end NativeOrderedKernel
