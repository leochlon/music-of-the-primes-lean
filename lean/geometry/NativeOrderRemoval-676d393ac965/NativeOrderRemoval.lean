import Mathlib

namespace NativeOrderRemoval

theorem derivative_kernel (c q qp h hp hpp : ℂ) :
    c^2*h - 2*c*(hp+q*h) + hpp+2*q*hp+(q^2-qp)*h =
    (c^2*h-2*c*hp+hpp)-2*q*(c*h-hp)+(q^2-qp)*h := by
  ring

theorem logged_second_derivative (c u h hp hpp : ℂ) :
    c^2*(-u*h)-2*c*(-h-u*hp)+(-2*hp-u*hpp) =
    -u*(c^2*h-2*c*hp+hpp)+2*(c*h-hp) := by
  ring

theorem mixed_block {R : Type*} [Ring R] (p a : R)
    (_hp : p*p=p) (hinv : p*a*(1-p)=0) :
    a*p-p*a=(1-p)*a*p := by
  have ha : p*a=p*a*p := by
    have hx : p*a*(1-p)=p*a-p*a*p := by noncomm_ring
    rw [hx] at hinv
    exact sub_eq_zero.mp hinv
  calc
    a*p-p*a = a*p-p*a*p := congrArg (fun z : R => a*p-z) ha
    _ = (1-p)*a*p := by noncomm_ring

theorem mixed_diagonal_zero {R : Type*} [Ring R] (p a : R)
    (hp : p*p=p) : p*((1-p)*a*p)=0 := by
  have hz : p*(1-p)=0 := by rw [mul_sub, mul_one, hp, sub_self]
  calc
    p*((1-p)*a*p) = (p*(1-p))*a*p := by noncomm_ring
    _ = 0 := by rw [hz, zero_mul, zero_mul]

#print axioms derivative_kernel
#print axioms mixed_block
end NativeOrderRemoval
