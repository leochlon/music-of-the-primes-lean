import Mathlib

/-! Round 182 G. The exact two-root Gram cancellation for the native
s = 0 weight exp(2 * alpha * |x|). This is a necessary local step toward
whole-cluster estimates, not a global nuclearity theorem. -/
namespace Round182G

noncomputable def gramNumerator (a b c : ℝ) : ℝ :=
  16 * (a^2-b^2) * (a^2-c^2)
noncomputable def gramDenominator (a b c t : ℝ) : ℝ :=
  (4*a^2-(b+c)^2+t^2)^2 + 4*(b+c)^2*t^2
noncomputable def rootDistanceSq (b c t : ℝ) : ℝ := (b-c)^2+t^2
noncomputable def gapFactor (a b c t : ℝ) : ℝ :=
  8*a^2+2*(b+c)^2+t^2-(b-c)^2

/-- The native Gram determinant contains exactly the squared root distance.
It is retained, then cancelled; it is not bounded away from zero. -/
theorem native_gram_determinant (a b c t : ℝ) :
    gramDenominator a b c t - gramNumerator a b c =
      rootDistanceSq b c t * gapFactor a b c t := by
  unfold gramDenominator gramNumerator rootDistanceSq gapFactor
  ring

/-- Uniform native two-root cancellation throughout the open strip.
The squared inequality avoids dividing by a possibly zero distance, and
therefore also holds at the confluent limit. -/
theorem two_root_native_gram_cancellation (a b c t : ℝ)
    (_ha : 0 ≤ a) (hb : |b| ≤ a) (hc : |c| ≤ a) :
    0 ≤ gramNumerator a b c ∧
    rootDistanceSq b c t * gramNumerator a b c ≤
      (2*a)^2 * (gramDenominator a b c t - gramNumerator a b c) := by
  have hb' := abs_le.mp hb
  have hc' := abs_le.mp hc
  have hb2 : b^2 ≤ a^2 := by nlinarith [sq_nonneg (a-b), sq_nonneg (a+b)]
  have hc2 : c^2 ≤ a^2 := by nlinarith [sq_nonneg (a-c), sq_nonneg (a+c)]
  have hd2 : (b-c)^2 ≤ 4*a^2 := by
    have h1 : 0 ≤ 2*a-(b-c) := by linarith
    have h2 : 0 ≤ 2*a+(b-c) := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hn : 0 ≤ gramNumerator a b c := by
    unfold gramNumerator
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hb2)) (sub_nonneg.mpr hc2)
  have hnupper : gramNumerator a b c ≤ 16*a^4 := by
    have hh := mul_le_mul (show a^2-b^2 ≤ a^2 by nlinarith [sq_nonneg b])
      (show a^2-c^2 ≤ a^2 by nlinarith [sq_nonneg c])
      (sub_nonneg.mpr hc2) (sq_nonneg a)
    unfold gramNumerator
    nlinarith
  have hf : 4*a^2 ≤ gapFactor a b c t := by
    unfold gapFactor
    nlinarith [sq_nonneg (b+c), sq_nonneg t]
  have hfactor : gramNumerator a b c ≤ (2*a)^2 * gapFactor a b c t := by
    have hh := mul_le_mul_of_nonneg_left hf (show 0 ≤ 4*a^2 by positivity)
    nlinarith
  refine ⟨hn, ?_⟩
  rw [native_gram_determinant]
  have hd : 0 ≤ rootDistanceSq b c t := by unfold rootDistanceSq; positivity
  nlinarith [mul_le_mul_of_nonneg_left hfactor hd]

/-- Actual coefficient differences can be inserted before cancelling the
Gram determinant. D is a local Mellin derivative bound, not an inverse-Gram
or nuclearity assumption. -/
theorem measured_two_root_offdiagonal (a b c t D : ℝ) (u v : ℂ)
    (ha : 0 ≤ a) (hb : |b| ≤ a) (hc : |c| ≤ a)
    (hM : ‖v-u‖^2 ≤ D^2 * rootDistanceSq b c t) :
    ‖v-u‖^2 * gramNumerator a b c ≤
      (2*a*D)^2 * (gramDenominator a b c t - gramNumerator a b c) := by
  obtain ⟨hn, hbound⟩ := two_root_native_gram_cancellation a b c t ha hb hc
  have h1 := mul_le_mul_of_nonneg_right hM hn
  have h2 := mul_le_mul_of_nonneg_left hbound (sq_nonneg D)
  nlinarith

#check native_gram_determinant
#print axioms native_gram_determinant
#check two_root_native_gram_cancellation
#print axioms two_root_native_gram_cancellation
#check measured_two_root_offdiagonal
#print axioms measured_two_root_offdiagonal
end Round182G
