import Mathlib
set_option maxHeartbeats 800000
open scoped BigOperators
namespace TraceRepairE
/-- Accounting for actual full and selected multiplicities. This is not an
assertion that either sum is the trace of the manuscript operator. -/
theorem corrected_trace_with_omitted_multiplicities {ι : Type*}
    (m d w : ι → ℂ) (G P : ℂ)
    (hm : Summable (fun i => m i * w i))
    (hd : Summable (fun i => d i * w i))
    (hfull : G = P - ∑' i, m i * w i) :
    G + (∑' i, (m i - d i) * w i) = P - ∑' i, d i * w i := by
  have he : (fun i => (m i - d i) * w i) =
      (fun i => m i * w i - d i * w i) := by funext i; ring
  rw [he, hm.tsum_sub hd, hfull]
  ring

/-- The printed selected formula requires exactly the missing remainder to
vanish; summability and full explicit formula do not remove this obligation. -/
theorem selected_formula_iff_remainder_zero {ι : Type*}
    (m d w : ι → ℂ) (G P : ℂ)
    (hm : Summable (fun i => m i * w i))
    (hd : Summable (fun i => d i * w i))
    (hfull : G = P - ∑' i, m i * w i) :
    G = P - ∑' i, d i * w i ↔ (∑' i, (m i - d i) * w i) = 0 := by
  have h := corrected_trace_with_omitted_multiplicities m d w G P hm hd hfull
  constructor
  · intro he
    rw [← he] at h
    exact add_left_cancel (h.trans (add_zero G).symm)
  · intro he
    simpa [he] using h
#print axioms corrected_trace_with_omitted_multiplicities
#print axioms selected_formula_iff_remainder_zero
/-- For the genuine analytic zero subtype, retained multiplicities may include
boundary jets. Full and selected sums are independent explicit hypotheses. -/
theorem genuine_zero_selected_correction (f : ℂ → ℂ)
    (d : {z : ℂ // f z = 0} → ℕ) (w : ℂ → ℂ) (G P : ℂ)
    (hm : Summable (fun i : {z : ℂ // f z = 0} =>
      (analyticOrderNatAt f i.val : ℂ) * w i.val))
    (hd : Summable (fun i : {z : ℂ // f z = 0} => (d i : ℂ) * w i.val))
    (hfull : G = P - ∑' i : {z : ℂ // f z = 0},
      (analyticOrderNatAt f i.val : ℂ) * w i.val) :
    G + (∑' i : {z : ℂ // f z = 0},
      ((analyticOrderNatAt f i.val : ℂ) - (d i : ℂ)) * w i.val) =
      P - ∑' i : {z : ℂ // f z = 0}, (d i : ℂ) * w i.val :=
by
  have he : (fun i : {z : ℂ // f z = 0} =>
      ((analyticOrderNatAt f i.val : ℂ) - (d i : ℂ)) * w i.val) =
      (fun i : {z : ℂ // f z = 0} =>
      (analyticOrderNatAt f i.val : ℂ) * w i.val - (d i : ℂ) * w i.val) := by
    funext i
    ring
  rw [he, hm.tsum_sub hd, hfull]
  ring

/-- If T is the actual retained-jet trace, J the strict-interior zero sum,
and B its boundary contribution, the printed formula drops O+B, not just O. -/
theorem strict_interior_formula_iff_total_defect_zero
    (G P T J B O : ℂ) (htrace : T = J + B)
    (hcorrected : G + O = P - T) :
    G = P - J ↔ O + B = 0 := by
  constructor
  · intro h
    linear_combination hcorrected - htrace - h
  · intro h
    linear_combination hcorrected - htrace - h

/-- Subtracting corrected strip identities preserves precisely the difference
of their omitted contributions. This does not produce the baseline's hraw. -/
theorem width_subtraction_retains_remainder
    (G P Ta Tb Oa Ob : ℂ)
    (ha : G + Oa = P - Ta) (hb : G + Ob = P - Tb) :
    Tb - Ta = Oa - Ob := by
  linear_combination hb - ha

/-- The tensor in manuscript 10.4.3.43 convolves the coefficient functional.
At every finite stage its action is P_N(A v), with no commutation premise. -/
theorem coefficient_kernel_is_PA {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (s : Finset ι) (ell : ι → V →ₗ[ℂ] ℂ)
    (u : ι → V) (A : V →ₗ[ℂ] V) (v : V) :
    (∑ i ∈ s, (ell i).comp A v • u i) =
      (fun z => ∑ i ∈ s, ell i z • u i) (A v) := rfl

/-- The AP kernel instead acts on the output vectors. -/
theorem output_kernel_is_AP {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} (s : Finset ι) (ell : ι → V →ₗ[ℂ] ℂ)
    (u : ι → V) (A : V →ₗ[ℂ] V) (v : V) :
    (∑ i ∈ s, ell i v • A (u i)) = A (∑ i ∈ s, ell i v • u i) := by
  simp only [map_sum, map_smul]

#print axioms genuine_zero_selected_correction
#print axioms strict_interior_formula_iff_total_defect_zero
#print axioms width_subtraction_retains_remainder
#print axioms coefficient_kernel_is_PA
#print axioms output_kernel_is_AP
end TraceRepairE
