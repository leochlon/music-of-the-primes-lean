import Mathlib

/-! Round 54 C. A concrete convolution calculation on the genuine idele-class
 group. This is an input to the spectral trace calculation, not a trace theorem.
 The Sobolev quotient, nuclearity, genuine zero divisor, and limit remain open. -/
open scoped NumberField
open MeasureTheory

namespace MasulloTrace
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev IdeleClasses := HeckeIdeles K ⧸ principalIdeles K

variable [MeasurableSpace (IdeleClasses K)]

/-- The actual left convolution formula from manuscript 10.4.2.26.
No assertion about its Sobolev domain is built into this definition. -/
noncomputable def convolution (μ : Measure (IdeleClasses K))
    (φ f : IdeleClasses K → ℂ) (x : IdeleClasses K) : ℂ :=
  ∫ g, φ g * f (g⁻¹ * x) ∂μ

/-- Mellin transform with the manuscript's positive-character convention. -/
noncomputable def mellin (μ : Measure (IdeleClasses K))
    (φ : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ) : ℂ :=
  ∫ g, φ g * (c g : ℂ) ∂μ

/-- Convolution acts on the inverse of a genuine idele-class character with
 the positive-convention Mellin eigenvalue. This does not identify a zero. -/
theorem convolution_inverse_character
    (μ : Measure (IdeleClasses K)) (φ : IdeleClasses K → ℂ)
    (c : IdeleClasses K →* ℂˣ) (x : IdeleClasses K) :
    convolution K μ φ (fun y => (c (y⁻¹) : ℂ)) x =
      mellin K μ φ c * (c (x⁻¹) : ℂ) := by
  unfold convolution mellin
  have h (g : IdeleClasses K) :
      φ g * (c ((g⁻¹ * x)⁻¹) : ℂ) =
        (φ g * (c g : ℂ)) * (c (x⁻¹) : ℂ) := by
    have he : (g⁻¹ * x)⁻¹ = x⁻¹ * g := by
      exact (mul_inv_rev g⁻¹ x).trans (congrArg (fun z => x⁻¹ * z) (inv_inv g))
    have hc : c ((g⁻¹ * x)⁻¹) = c (x⁻¹) * c g := by
      rw [he]
      exact c.map_mul _ _
    have hv := congrArg (fun u : ℂˣ => (u : ℂ)) hc
    change (c ((g⁻¹ * x)⁻¹) : ℂ) = (c (x⁻¹) : ℂ) * (c g : ℂ) at hv
    rw [hv]
    ring
  simp_rw [h]
  exact integral_mul_const _ _

variable [MeasurableMul (IdeleClasses K)]

/-- The coefficient functional used in 10.4.2.22 transforms by the genuine
 character. Left invariance of the measure is the exact required hypothesis. -/
theorem mellin_left_translate (μ : Measure (IdeleClasses K))
    [μ.IsMulLeftInvariant] (f : IdeleClasses K → ℂ)
    (c : IdeleClasses K →* ℂˣ) (g : IdeleClasses K) :
    (∫ x, f (g⁻¹ * x) * (c x : ℂ) ∂μ) =
      (c g : ℂ) * mellin K μ f c := by
  calc
    _ = ∫ y, f (g⁻¹ * (g * y)) * (c (g * y) : ℂ) ∂μ :=
      (integral_mul_left_eq_self (fun x => f (g⁻¹ * x) * (c x : ℂ)) g).symm
    _ = ∫ y, (c g : ℂ) * (f y * (c y : ℂ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he : g⁻¹ * (g * y) = y := inv_mul_cancel_left g y
      rw [he, c.map_mul]
      change f y * ((c g : ℂ) * (c y : ℂ)) = _
      ring
    _ = _ := integral_const_mul _ _

/-- Fubini justified Mellin coefficient identity for the actual convolution.
The product integrability premise is stated, not inferred from an unproved
Sobolev or spectral estimate. -/
theorem mellin_convolution (μ : Measure (IdeleClasses K))
    [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (h : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ)) (μ.prod μ)) :
    mellin K μ (convolution K μ φ f) c =
      mellin K μ φ c * mellin K μ f c := by
  change (∫ x, (∫ g, φ g * f (g⁻¹ * x) ∂μ) * (c x : ℂ) ∂μ) = _
  calc
    _ = ∫ x, ∫ g, φ g * f (g⁻¹ * x) * (c x : ℂ) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const _ _).symm
    _ = ∫ g, ∫ x, φ g * f (g⁻¹ * x) * (c x : ℂ) ∂μ ∂μ :=
      integral_integral_swap h
    _ = ∫ g, φ g * ((c g : ℂ) * mellin K μ f c) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp_rw [mul_assoc]
      rw [integral_const_mul, mellin_left_translate K μ f c g]
    _ = mellin K μ φ c * mellin K μ f c := by
      simp_rw [← mul_assoc]
      exact integral_mul_const _ _

/-- The same Fubini premise certifies that the output Mellin integral exists;
this conclusion does not rely on the default value of a divergent integral. -/
theorem mellin_convolution_integrable (μ : Measure (IdeleClasses K))
    [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (h : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ)) (μ.prod μ)) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ)) μ ∧
    mellin K μ (convolution K μ φ f) c =
      mellin K μ φ c * mellin K μ f c := by
  constructor
  · have hi := h.integral_prod_left
    change Integrable (fun x => ∫ g, φ g * f (g⁻¹ * x) * (c x : ℂ) ∂μ) μ at hi
    simp_rw [integral_mul_const] at hi
    exact hi
  · exact mellin_convolution K μ φ f c h

omit [MeasurableMul (IdeleClasses K)] in
/-- Haar shear discharges the product-integrability premise for the actual
convolution coefficient from weighted L1 conditions on its two inputs. -/
theorem weighted_convolution_joint_integrable
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (hφ : Integrable (fun g => φ g * (c g : ℂ)) μ)
    (hf : Integrable (fun x => f x * (c x : ℂ)) μ) :
    Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ)) (μ.prod μ) := by
  have hp := hφ.mul_prod hf
  have hs := ((measurePreserving_prod_inv_mul μ μ).integrable_comp
    hp.aestronglyMeasurable).mpr hp
  apply hs.swap.congr
  filter_upwards [] with p
  change (φ p.2 * (c p.2 : ℂ)) *
    (f (p.2⁻¹ * p.1) * (c (p.2⁻¹ * p.1) : ℂ)) = _
  have hc : (c p.2 : ℂ) * (c (p.2⁻¹ * p.1) : ℂ) = (c p.1 : ℂ) := by
    rw [← Units.val_mul, ← c.map_mul, mul_inv_cancel_left]
  calc
    _ = φ p.2 * f (p.2⁻¹ * p.1) *
      ((c p.2 : ℂ) * (c (p.2⁻¹ * p.1) : ℂ)) := by ring
    _ = _ := by rw [hc]

/-- Degree-zero spectral coefficient calculation with justified Fubini. -/
theorem mellin_convolution_of_weighted_integrable
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (hφ : Integrable (fun g => φ g * (c g : ℂ)) μ)
    (hf : Integrable (fun x => f x * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ)) μ ∧
    mellin K μ (convolution K μ φ f) c =
      mellin K μ φ c * mellin K μ f c := by
  exact mellin_convolution_integrable K μ φ f c
    (weighted_convolution_joint_integrable K μ φ f c hφ hf)

/-- For a continuous compactly supported test and continuous genuine
idele-class character, weighted integrability of the test is automatic.
Only weighted integrability of the lifted vector remains a hypothesis. -/
theorem mellin_convolution_compact_test
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hc : Continuous (fun x => (c x : ℂ)))
    (hf : Integrable (fun x => f x * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ)) μ ∧
    mellin K μ (convolution K μ φ f) c =
      mellin K μ φ c * mellin K μ f c := by
  exact mellin_convolution_of_weighted_integrable K μ φ f c
    ((hφ.mul hc).integrable_of_hasCompactSupport hφsupp.mul_right) hf

#check mellin_convolution_compact_test
#print axioms mellin_convolution_compact_test
#check weighted_convolution_joint_integrable
#print axioms weighted_convolution_joint_integrable
#check mellin_convolution_of_weighted_integrable
#print axioms mellin_convolution_of_weighted_integrable
#check mellin_convolution_integrable
#print axioms mellin_convolution_integrable
#check mellin_convolution
#print axioms mellin_convolution
#check mellin_left_translate
#print axioms mellin_left_translate
#check convolution_inverse_character
#print axioms convolution_inverse_character

/-- First logarithmic Mellin coefficient used by manuscript 10.4.2.22.
The log-modulus law is explicit; identification of `ell` with the genuine
idelic log modulus, and Sobolev moment bounds, are still prerequisites. -/
theorem mellin_convolution_first_log_coefficient
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Integrable (fun g => φ g * (c g : ℂ)) μ)
    (hf : Integrable (fun x => f x * (c x : ℂ)) μ)
    (hφ1 : Integrable (fun g => (φ g * ell g) * (c g : ℂ)) μ)
    (hf1 : Integrable (fun x => (f x * ell x) * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x) μ ∧
    (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ∂μ) =
      mellin K μ (fun g => φ g * ell g) c * mellin K μ f c +
      mellin K μ φ c * mellin K μ (fun x => f x * ell x) c := by
  have h1 := weighted_convolution_joint_integrable K μ
    (fun g => φ g * ell g) f c hφ1 hf
  have h2 := weighted_convolution_joint_integrable K μ
    φ (fun x => f x * ell x) c hφ hf1
  have he (x g : IdeleClasses K) : ell x = ell g + ell (g⁻¹ * x) := by
    rw [← hell, mul_inv_cancel_left]
  have hinner : ∀ᵐ x ∂μ,
      convolution K μ φ f x * (c x : ℂ) * ell x =
      convolution K μ (fun g => φ g * ell g) f x * (c x : ℂ) +
      convolution K μ φ (fun y => f y * ell y) x * (c x : ℂ) := by
    filter_upwards [h1.prod_right_ae, h2.prod_right_ae] with x hx1 hx2
    unfold convolution
    calc
      _ = ∫ g, φ g * f (g⁻¹ * x) * (c x : ℂ) * ell x ∂μ := by
        rw [integral_mul_const, integral_mul_const]
      _ = ∫ g, (φ g * ell g) * f (g⁻¹ * x) * (c x : ℂ) +
          φ g * (f (g⁻¹ * x) * ell (g⁻¹ * x)) * (c x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        rw [he x g]
        ring
      _ = _ := by
        rw [integral_add hx1 hx2, integral_mul_const, integral_mul_const]
  have hm1 := mellin_convolution_of_weighted_integrable K μ
    (fun g => φ g * ell g) f c hφ1 hf
  have hm2 := mellin_convolution_of_weighted_integrable K μ
    φ (fun x => f x * ell x) c hφ hf1
  constructor
  · apply (hm1.1.add hm2.1).congr
    filter_upwards [hinner] with x hx
    exact hx.symm
  · calc
      _ = ∫ x, convolution K μ (fun g => φ g * ell g) f x * (c x : ℂ) +
          convolution K μ φ (fun y => f y * ell y) x * (c x : ℂ) ∂μ :=
        integral_congr_ae hinner
      _ = _ := by
        rw [integral_add hm1.1 hm2.1]
        exact congrArg₂ (· + ·) hm1.2 hm2.2

#check mellin_convolution_first_log_coefficient
#print axioms mellin_convolution_first_log_coefficient

/-- First logarithmic coefficient for the manuscript's compact test class:
continuity and compact support discharge both test moment hypotheses. -/
theorem mellin_convolution_first_log_compact_test
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hc : Continuous (fun x => (c x : ℂ))) (hellcont : Continuous ell)
    (hf : Integrable (fun x => f x * (c x : ℂ)) μ)
    (hf1 : Integrable (fun x => (f x * ell x) * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x) μ ∧
    (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ∂μ) =
      mellin K μ (fun g => φ g * ell g) c * mellin K μ f c +
      mellin K μ φ c * mellin K μ (fun x => f x * ell x) c := by
  exact mellin_convolution_first_log_coefficient K μ φ f c ell hell
    ((hφ.mul hc).integrable_of_hasCompactSupport hφsupp.mul_right) hf
    (((hφ.mul hellcont).mul hc).integrable_of_hasCompactSupport
      hφsupp.mul_right.mul_right) hf1

#check mellin_convolution_first_log_compact_test
#print axioms mellin_convolution_first_log_compact_test

omit [MeasurableMul (IdeleClasses K)] in
/-- Finite logarithmic orders in 10.4.2.22: all moment Fubini premises
follow from the corresponding input moments. No zero multiplicity is assumed. -/
theorem convolution_log_moment_integrable
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y) (n : ℕ)
    (hφ : ∀ j ≤ n, Integrable (fun g => (φ g * ell g ^ j) * (c g : ℂ)) μ)
    (hf : ∀ j ≤ n, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x ^ n) μ := by
  have hs : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
        ((φ p.2 * ell p.2 ^ j) *
          (f (p.2⁻¹ * p.1) * ell (p.2⁻¹ * p.1) ^ (n-j)) * (c p.1 : ℂ)))
      (μ.prod μ) := by
    apply integrable_finset_sum
    intro j hj
    exact (weighted_convolution_joint_integrable K μ
      (fun g => φ g * ell g ^ j) (fun x => f x * ell x ^ (n-j)) c
      (hφ j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      (hf (n-j) (Nat.sub_le _ _))).const_mul _
  have hj : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ) * ell p.1 ^ n) (μ.prod μ) := by
    apply hs.congr
    filter_upwards [] with p
    have he : ell p.1 = ell p.2 + ell (p.2⁻¹ * p.1) := by
      rw [← hell, mul_inv_cancel_left]
    rw [he, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi := hj.integral_prod_left
  simp_rw [integral_mul_const] at hi
  exact hi

#check convolution_log_moment_integrable
#print axioms convolution_log_moment_integrable

/-- The full finite-order coefficient identity required by (10.4.2.29–33).
All interchanges follow from the explicitly stated input moment bounds. -/
theorem mellin_convolution_log_coefficients
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y) (n : ℕ)
    (hφ : ∀ j ≤ n, Integrable (fun g => (φ g * ell g ^ j) * (c g : ℂ)) μ)
    (hf : ∀ j ≤ n, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x ^ n) μ ∧
    (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ^ n ∂μ) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
        (mellin K μ (fun g => φ g * ell g ^ j) c *
         mellin K μ (fun x => f x * ell x ^ (n-j)) c) := by
  constructor
  · exact convolution_log_moment_integrable K μ φ f c ell hell n hφ hf
  let H : ℕ → IdeleClasses K × IdeleClasses K → ℂ := fun j p =>
    (φ p.2 * ell p.2 ^ j) *
      (f (p.2⁻¹ * p.1) * ell (p.2⁻¹ * p.1) ^ (n-j)) * (c p.1 : ℂ)
  have hH (j : ℕ) (hj : j ∈ Finset.range (n+1)) : Integrable (H j) (μ.prod μ) := by
    exact weighted_convolution_joint_integrable K μ
      (fun g => φ g * ell g ^ j) (fun x => f x * ell x ^ (n-j)) c
      (hφ j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      (hf (n-j) (Nat.sub_le _ _))
  have heq (p : IdeleClasses K × IdeleClasses K) :
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ) * ell p.1 ^ n =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) * H j p := by
    have he : ell p.1 = ell p.2 + ell (p.2⁻¹ * p.1) := by
      rw [← hell, mul_inv_cancel_left]
    rw [he, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [H]
    ring
  have hsum : Integrable (fun p =>
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) * H j p) (μ.prod μ) := by
    apply integrable_finset_sum
    intro j hj
    exact (hH j hj).const_mul _
  have hjoint : Integrable (fun p : IdeleClasses K × IdeleClasses K =>
      φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ) * ell p.1 ^ n) (μ.prod μ) :=
    hsum.congr (Filter.Eventually.of_forall (fun p => (heq p).symm))
  calc
    _ = ∫ p : IdeleClasses K × IdeleClasses K,
        φ p.2 * f (p.2⁻¹ * p.1) * (c p.1 : ℂ) * ell p.1 ^ n ∂(μ.prod μ) := by
      rw [integral_prod _ hjoint]
      simp_rw [integral_mul_const]
      rfl
    _ = ∫ p, ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) * H j p ∂(μ.prod μ) :=
      integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
        (∫ p, H j p ∂(μ.prod μ)) := by
      rw [integral_finset_sum _ (fun j hj => (hH j hj).const_mul _)]
      simp_rw [integral_const_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      rw [integral_prod _ (hH j hj)]
      dsimp [H]
      simp_rw [integral_mul_const]
      exact mellin_convolution K μ (fun g => φ g * ell g ^ j)
        (fun x => f x * ell x ^ (n-j)) c (hH j hj)

#check mellin_convolution_log_coefficients
#print axioms mellin_convolution_log_coefficients

/-- Compact admissible tests have all finite weighted logarithmic moments.
Only the moment bounds of the actual lift remain to be supplied. -/
theorem mellin_convolution_log_compact_test
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hc : Continuous (fun x => (c x : ℂ))) (hellcont : Continuous ell)
    (n : ℕ)
    (hf : ∀ j ≤ n, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x ^ n) μ ∧
    (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ^ n ∂μ) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℂ) *
        (mellin K μ (fun g => φ g * ell g ^ j) c *
         mellin K μ (fun x => f x * ell x ^ (n-j)) c) := by
  apply mellin_convolution_log_coefficients K μ φ f c ell hell n _ hf
  intro j hj
  exact (((hφ.mul (hellcont.pow j)).mul hc).integrable_of_hasCompactSupport
    hφsupp.mul_right.mul_right)

#check mellin_convolution_log_compact_test
#print axioms mellin_convolution_log_compact_test

/-- Actual convolution preserves the annihilator of the first N logarithmic
Mellin coefficient functionals. This is the well-definedness implication needed
before identifying that annihilator with the manuscript spectral quotient. -/
theorem convolution_preserves_log_annihilator
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hc : Continuous (fun x => (c x : ℂ))) (hellcont : Continuous ell)
    (N : ℕ)
    (hf : ∀ j < N, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ)
    (hzero : ∀ j < N, mellin K μ (fun x => f x * ell x ^ j) c = 0) :
    ∀ n < N,
      Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x ^ n) μ ∧
      (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ^ n ∂μ) = 0 := by
  intro n hn
  obtain ⟨hi, he⟩ := mellin_convolution_log_compact_test K μ φ f c ell hell
    hφ hφsupp hc hellcont n (fun j hj => hf j (lt_of_le_of_lt hj hn))
  refine ⟨hi, he.trans ?_⟩
  apply Finset.sum_eq_zero
  intro j hj
  rw [hzero (n-j) (lt_of_le_of_lt (Nat.sub_le _ _) hn)]
  simp

#check convolution_preserves_log_annihilator
#print axioms convolution_preserves_log_annihilator

/-- On a genuine convolution coefficient with all lower coefficients zero,
the diagonal scalar is exactly the positive-convention Mellin transform.
This is the repeated-zero diagonal calculation, conditional on the actual
spectral identification; no diagonal proxy operator is introduced. -/
theorem convolution_log_filtration_diagonal
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hc : Continuous (fun x => (c x : ℂ))) (hellcont : Continuous ell)
    (n : ℕ)
    (hf : ∀ j ≤ n, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ)
    (hzero : ∀ j < n, mellin K μ (fun x => f x * ell x ^ j) c = 0) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x ^ n) μ ∧
    (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ^ n ∂μ) =
      mellin K μ φ c * mellin K μ (fun x => f x * ell x ^ n) c := by
  obtain ⟨hi, he⟩ := mellin_convolution_log_compact_test K μ φ f c ell hell
    hφ hφsupp hc hellcont n hf
  refine ⟨hi, he.trans ?_⟩
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnpos : 0 < n := lt_of_lt_of_le hjpos hjle
    rw [hzero (n-j) (Nat.sub_lt hnpos hjpos)]
    simp
  · simp

#check convolution_log_filtration_diagonal
#print axioms convolution_log_filtration_diagonal

omit [MeasurableMul (IdeleClasses K)] in
/-- The manuscript pairing (10.2.2.3) makes the coefficient moments absolutely
integrable: w is the square root of its Hardy-Sobolev density, and the logarithmic
coefficient divided by w is the dual L2 vector. No boundedness of a lift is
silently substituted for this Hilbert-space hypothesis. -/
theorem logarithmic_moment_integrable_of_weighted_L2
    (μ : Measure (IdeleClasses K)) (f w : IdeleClasses K → ℂ)
    (c : IdeleClasses K →* ℂˣ) (ell : IdeleClasses K → ℂ) (n : ℕ)
    (hw : ∀ x, w x ≠ 0)
    (hf : MemLp (fun x => w x * f x) 2 μ)
    (hdual : MemLp (fun x => ((c x : ℂ) * ell x ^ n) / w x) 2 μ) :
    Integrable (fun x => (f x * ell x ^ n) * (c x : ℂ)) μ := by
  have h := hdual.integrable_mul hf
  apply h.congr
  filter_upwards [] with x
  change ((c x : ℂ) * ell x ^ n) / w x * (w x * f x) = _
  field_simp [hw x]

#check logarithmic_moment_integrable_of_weighted_L2
#print axioms logarithmic_moment_integrable_of_weighted_L2

/-- Integrated Sobolev-pairing version of the actual convolution diagonal
calculation used for the coefficient functionals in (10.4.2.22).
The genuine spectral dual-membership theorem is still an explicit obligation. -/
theorem convolution_log_diagonal_of_weighted_L2
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f w : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hc : Continuous (fun x => (c x : ℂ))) (hellcont : Continuous ell)
    (n : ℕ) (hw : ∀ x, w x ≠ 0)
    (hf : MemLp (fun x => w x * f x) 2 μ)
    (hdual : ∀ j ≤ n, MemLp (fun x => ((c x : ℂ) * ell x ^ j) / w x) 2 μ)
    (hzero : ∀ j < n, mellin K μ (fun x => f x * ell x ^ j) c = 0) :
    Integrable (fun x => convolution K μ φ f x * (c x : ℂ) * ell x ^ n) μ ∧
    (∫ x, convolution K μ φ f x * (c x : ℂ) * ell x ^ n ∂μ) =
      mellin K μ φ c * mellin K μ (fun x => f x * ell x ^ n) c := by
  apply convolution_log_filtration_diagonal K μ φ f c ell hell
    hφ hφsupp hc hellcont n _ hzero
  intro j hj
  exact logarithmic_moment_integrable_of_weighted_L2 K μ f w c ell j hw hf (hdual j hj)

#check convolution_log_diagonal_of_weighted_L2
#print axioms convolution_log_diagonal_of_weighted_L2

/-! The following identities close the character-shift compatibility required
by (10.4.3.3–4). They concern the actual convolution on the idele-class group.
For q = |.|^a, twisting the theta image by q shifts coefficient c to c/q.
Construction of that canonical modulus and the genuine divisor remains open. -/

omit [MeasurableMul (IdeleClasses K)] in
theorem convolution_character_twist
    (μ : Measure (IdeleClasses K)) (φ f : IdeleClasses K → ℂ)
    (q : IdeleClasses K →* ℂˣ) (x : IdeleClasses K) :
    convolution K μ φ (fun y => (q y : ℂ) * f y) x =
      (q x : ℂ) * convolution K μ (fun g => φ g / (q g : ℂ)) f x := by
  unfold convolution
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [q.map_mul, q.map_inv]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ring

#check convolution_character_twist
#print axioms convolution_character_twist

omit [MeasurableMul (IdeleClasses K)] in
theorem mellin_character_shift
    (μ : Measure (IdeleClasses K)) (f : IdeleClasses K → ℂ)
    (c q : IdeleClasses K →* ℂˣ) :
    mellin K μ (fun x => (q x : ℂ) * f x) (c * q⁻¹) =
      mellin K μ f c := by
  unfold mellin
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_inv_eq_inv_val]
  have hq : (q x : ℂ) ≠ 0 := Units.ne_zero (q x)
  field_simp [hq]

#check mellin_character_shift
#print axioms mellin_character_shift

omit [MeasurableMul (IdeleClasses K)] in
theorem logarithmic_mellin_character_shift
    (μ : Measure (IdeleClasses K)) (f ell : IdeleClasses K → ℂ)
    (c q : IdeleClasses K →* ℂˣ) (n : ℕ) :
    mellin K μ (fun x => ((q x : ℂ) * f x) * ell x ^ n) (c * q⁻¹) =
      mellin K μ (fun x => f x * ell x ^ n) c := by
  simpa only [mul_assoc] using
    mellin_character_shift K μ (fun x => f x * ell x ^ n) c q

#check logarithmic_mellin_character_shift
#print axioms logarithmic_mellin_character_shift

/-- Applied directly to the actual coefficient filtration: the diagonal after
shifting the theta image by q is M(phi)(c/q), with the original test phi.
No zero set, nuclear trace, or spectral identification is assumed or defined. -/
theorem shifted_convolution_log_diagonal
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c q : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hcq : Continuous (fun x => ((c * q⁻¹) x : ℂ)))
    (hellcont : Continuous ell) (n : ℕ)
    (hf : ∀ j ≤ n, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ)
    (hzero : ∀ j < n, mellin K μ (fun x => f x * ell x ^ j) c = 0) :
    Integrable (fun x =>
      convolution K μ φ (fun y => (q y : ℂ) * f y) x *
        ((c * q⁻¹) x : ℂ) * ell x ^ n) μ ∧
    (∫ x, convolution K μ φ (fun y => (q y : ℂ) * f y) x *
        ((c * q⁻¹) x : ℂ) * ell x ^ n ∂μ) =
      mellin K μ φ (c * q⁻¹) * mellin K μ (fun x => f x * ell x ^ n) c := by
  have he (j : ℕ) (x : IdeleClasses K) :
      (((q x : ℂ) * f x) * ell x ^ j) * ((c * q⁻¹) x : ℂ) =
        (f x * ell x ^ j) * (c x : ℂ) := by
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul,
      Units.val_inv_eq_inv_val]
    have hq : (q x : ℂ) ≠ 0 := Units.ne_zero (q x)
    field_simp [hq]
  have hm : ∀ j ≤ n, Integrable
      (fun x => (((q x : ℂ) * f x) * ell x ^ j) * ((c * q⁻¹) x : ℂ)) μ := by
    intro j hj
    simpa only [he] using hf j hj
  have hz : ∀ j < n,
      mellin K μ (fun x => ((q x : ℂ) * f x) * ell x ^ j) (c * q⁻¹) = 0 := by
    intro j hj
    rw [logarithmic_mellin_character_shift]
    exact hzero j hj
  obtain ⟨hi, hd⟩ := convolution_log_filtration_diagonal K μ φ
    (fun y => (q y : ℂ) * f y) (c * q⁻¹) ell hell hφ hφsupp hcq hellcont n hm hz
  refine ⟨hi, ?_⟩
  simpa only [logarithmic_mellin_character_shift] using hd

#check shifted_convolution_log_diagonal
#print axioms shifted_convolution_log_diagonal
/-- Cutoff removal for the actual shifted convolution coefficient in
(10.4.2.20). The earlier convolution theorem supplies integrability.
The infinite nuclear trace and genuine divisor are still unproved. -/
theorem shifted_convolution_log_diagonal_cutoff_limit
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ f : IdeleClasses K → ℂ) (c q : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hcq : Continuous (fun x => ((c * q⁻¹) x : ℂ)))
    (hellcont : Continuous ell) (n : ℕ)
    (hf : ∀ j ≤ n, Integrable (fun x => (f x * ell x ^ j) * (c x : ℂ)) μ)
    (hzero : ∀ j < n, mellin K μ (fun x => f x * ell x ^ j) c = 0)
    (ρ : ℕ → IdeleClasses K → ℂ)
    (hρmeas : ∀ k, AEStronglyMeasurable (ρ k) μ)
    (hρbound : ∀ k x, ‖ρ k x‖ ≤ 1)
    (hρlim : ∀ x, Filter.Tendsto (fun k => ρ k x) Filter.atTop (nhds 1)) :
    (∀ k, Integrable (fun x => ρ k x *
      (convolution K μ φ (fun y => (q y : ℂ) * f y) x *
        ((c * q⁻¹) x : ℂ) * ell x ^ n)) μ) ∧
    Filter.Tendsto (fun k => ∫ x, ρ k x *
      (convolution K μ φ (fun y => (q y : ℂ) * f y) x *
        ((c * q⁻¹) x : ℂ) * ell x ^ n) ∂μ) Filter.atTop
      (nhds (mellin K μ φ (c * q⁻¹) *
        mellin K μ (fun x => f x * ell x ^ n) c)) := by
  let U : IdeleClasses K → ℂ := fun x =>
    convolution K μ φ (fun y => (q y : ℂ) * f y) x *
      ((c * q⁻¹) x : ℂ) * ell x ^ n
  obtain ⟨hi, hd⟩ := shifted_convolution_log_diagonal K μ φ f c q ell hell
    hφ hφsupp hcq hellcont n hf hzero
  have hUi : Integrable U μ := hi
  have hbound (k : ℕ) (x : IdeleClasses K) : ‖ρ k x * U x‖ ≤ ‖U x‖ := by
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hρbound k x) (norm_nonneg (U x))
  constructor
  · intro k
    exact hUi.norm.mono' ((hρmeas k).mul hUi.aestronglyMeasurable)
      (Filter.Eventually.of_forall (hbound k))
  · have ht : Filter.Tendsto (fun k => ∫ x, ρ k x * U x ∂μ)
        Filter.atTop (nhds (∫ x, U x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => ‖U x‖)
      · intro k
        exact (hρmeas k).mul hUi.aestronglyMeasurable
      · exact hUi.norm
      · intro k
        exact Filter.Eventually.of_forall (hbound k)
      · apply Filter.Eventually.of_forall
        intro x
        simpa only [one_mul] using (hρlim x).mul_const (U x)
    change Filter.Tendsto (fun k => ∫ x, ρ k x * U x ∂μ) Filter.atTop _
    change (∫ x, U x ∂μ) = _ at hd
    rw [hd] at ht
    exact ht

#check shifted_convolution_log_diagonal_cutoff_limit
#print axioms shifted_convolution_log_diagonal_cutoff_limit
end MasulloTrace

namespace MasulloTrace
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (IdeleClasses K)] [MeasurableMul (IdeleClasses K)]

/-- The infinite cutoff exchange required in (10.4.2.20), for the actual
shifted convolution coefficients. The L1 majorant is an explicit premise;
it is not asserted for the genuine Hecke spectral lifts. No trace is defined
by this sum, and no zero set or multiplicity is postulated. -/
theorem shifted_convolution_cutoff_tsum_limit
    {ι : Type*}
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ : IdeleClasses K → ℂ) (f : ι → IdeleClasses K → ℂ)
    (c : ι → IdeleClasses K →* ℂˣ) (q : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hcq : ∀ i, Continuous (fun x => ((c i * q⁻¹) x : ℂ)))
    (hellcont : Continuous ell) (n : ι → ℕ)
    (hf : ∀ i j, j ≤ n i →
      Integrable (fun x => (f i x * ell x ^ j) * (c i x : ℂ)) μ)
    (hzero : ∀ i j, j < n i →
      mellin K μ (fun x => f i x * ell x ^ j) (c i) = 0)
    (ρ : ℕ → IdeleClasses K → ℂ)
    (hρmeas : ∀ k, AEStronglyMeasurable (ρ k) μ)
    (hρbound : ∀ k x, ‖ρ k x‖ ≤ 1)
    (hρlim : ∀ x, Filter.Tendsto (fun k => ρ k x) Filter.atTop (nhds 1))
    (hmajor : Summable (fun i => ∫ x,
      ‖convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i‖ ∂μ)) :
    (∀ k, Summable (fun i => ∫ x, ρ k x *
      (convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i) ∂μ)) ∧
    Summable (fun i => mellin K μ φ (c i * q⁻¹) *
      mellin K μ (fun x => f i x * ell x ^ n i) (c i)) ∧
    Filter.Tendsto (fun k => ∑' i, ∫ x, ρ k x *
      (convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i) ∂μ) Filter.atTop
      (nhds (∑' i, mellin K μ φ (c i * q⁻¹) *
        mellin K μ (fun x => f i x * ell x ^ n i) (c i))) := by
  let U : ι → IdeleClasses K → ℂ := fun i x =>
    convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
      ((c i * q⁻¹) x : ℂ) * ell x ^ n i
  let b : ι → ℝ := fun i => ∫ x, ‖U i x‖ ∂μ
  have hui (i : ι) : Integrable (U i) μ :=
    (shifted_convolution_log_diagonal K μ φ (f i) (c i) q ell hell
      hφ hφsupp (hcq i) hellcont (n i) (hf i) (hzero i)).1
  have hdiag (i : ι) : (∫ x, U i x ∂μ) =
      mellin K μ φ (c i * q⁻¹) *
        mellin K μ (fun x => f i x * ell x ^ n i) (c i) :=
    (shifted_convolution_log_diagonal K μ φ (f i) (c i) q ell hell
      hφ hφsupp (hcq i) hellcont (n i) (hf i) (hzero i)).2
  have hcut (i : ι) := shifted_convolution_log_diagonal_cutoff_limit K μ φ
    (f i) (c i) q ell hell hφ hφsupp (hcq i) hellcont (n i) (hf i)
    (hzero i) ρ hρmeas hρbound hρlim
  have hb : Summable b := hmajor
  have hbound (k : ℕ) (i : ι) : ‖∫ x, ρ k x * U i x ∂μ‖ ≤ b i := by
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono_ae ((hcut i).1 k).norm (hui i).norm
    apply Filter.Eventually.of_forall
    intro x
    change ‖ρ k x * U i x‖ ≤ ‖U i x‖
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hρbound k x) (norm_nonneg (U i x))
  have hsum (k : ℕ) : Summable (fun i => ∫ x, ρ k x * U i x ∂μ) :=
    hb.of_norm_bounded (hbound k)
  have hsumdiag : Summable (fun i => mellin K μ φ (c i * q⁻¹) *
      mellin K μ (fun x => f i x * ell x ^ n i) (c i)) := by
    apply hb.of_norm_bounded
    intro i
    rw [← hdiag i]
    exact norm_integral_le_integral_norm _
  refine ⟨hsum, hsumdiag, ?_⟩
  apply tendsto_tsum_of_dominated_convergence hb
  · intro i
    exact (hcut i).2
  · exact Filter.Eventually.of_forall hbound

#check shifted_convolution_cutoff_tsum_limit
#print axioms shifted_convolution_cutoff_tsum_limit
end MasulloTrace

namespace MasulloTrace
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (IdeleClasses K)] [MeasurableMul (IdeleClasses K)]

/-- Weighted rank-one L2 summability implies the actual convolution cutoff
exchange in (10.4.2.20), discharging the L1-majorant premise of the inherited
round-61 theorem. The genuine spectral-lift L2 summability remains explicit;
this is not a nuclearity theorem or an identification with Hecke zeros. -/
theorem shifted_convolution_cutoff_tsum_of_weighted_L2
    {ι : Type*}
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ : IdeleClasses K → ℂ) (f : ι → IdeleClasses K → ℂ)
    (c : ι → IdeleClasses K →* ℂˣ) (q : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hcq : ∀ i, Continuous (fun x => ((c i * q⁻¹) x : ℂ)))
    (hellcont : Continuous ell) (n : ι → ℕ)
    (hf : ∀ i j, j ≤ n i →
      Integrable (fun x => (f i x * ell x ^ j) * (c i x : ℂ)) μ)
    (hzero : ∀ i j, j < n i →
      mellin K μ (fun x => f i x * ell x ^ j) (c i) = 0)
    (ρ : ℕ → IdeleClasses K → ℂ)
    (hρmeas : ∀ k, AEStronglyMeasurable (ρ k) μ)
    (hρbound : ∀ k x, ‖ρ k x‖ ≤ 1)
    (hρlim : ∀ x, Filter.Tendsto (fun k => ρ k x) Filter.atTop (nhds 1))
    (w : IdeleClasses K → ℂ) (hw : ∀ x, w x ≠ 0)
    (hleft : ∀ i, MemLp (fun x => w x *
      convolution K μ φ (fun y => (q y : ℂ) * f i y) x) 2 μ)
    (hright : ∀ i, MemLp (fun x =>
      (((c i * q⁻¹) x : ℂ) * ell x ^ n i) / w x) 2 μ)
    (hnuclear : Summable (fun i =>
      (∫ x, ‖w x * convolution K μ φ (fun y => (q y : ℂ) * f i y) x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
      (∫ x, ‖(((c i * q⁻¹) x : ℂ) * ell x ^ n i) / w x‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)))) :
    (∀ k, Summable (fun i => ∫ x, ρ k x *
      (convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i) ∂μ)) ∧
    Summable (fun i => mellin K μ φ (c i * q⁻¹) *
      mellin K μ (fun x => f i x * ell x ^ n i) (c i)) ∧
    Filter.Tendsto (fun k => ∑' i, ∫ x, ρ k x *
      (convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i) ∂μ) Filter.atTop
      (nhds (∑' i, mellin K μ φ (c i * q⁻¹) *
        mellin K μ (fun x => f i x * ell x ^ n i) (c i))) := by
  apply shifted_convolution_cutoff_tsum_limit K μ φ f c q ell hell hφ hφsupp
    hcq hellcont n hf hzero ρ hρmeas hρbound hρlim
  apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg _)) _ hnuclear
  intro i
  let A : IdeleClasses K → ℂ := fun x => w x *
    convolution K μ φ (fun y => (q y : ℂ) * f i y) x
  let B : IdeleClasses K → ℂ := fun x =>
    (((c i * q⁻¹) x : ℂ) * ell x ^ n i) / w x
  have hA : MemLp A (ENNReal.ofReal (2 : ℝ)) μ := by simpa [A] using hleft i
  have hB : MemLp B (ENNReal.ofReal (2 : ℝ)) μ := by simpa [B] using hright i
  have hpq : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hbound := integral_mul_norm_le_Lp_mul_Lq hpq hA hB
  have heq : (fun x =>
      ‖convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i‖) =
      (fun x => ‖A x‖ * ‖B x‖) := by
    funext x
    rw [← norm_mul]
    congr 1
    dsimp [A, B]
    field_simp [hw x]
  rw [heq]
  exact hbound

#check shifted_convolution_cutoff_tsum_of_weighted_L2
#print axioms shifted_convolution_cutoff_tsum_of_weighted_L2

end MasulloTrace

namespace MasulloTrace
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (IdeleClasses K)] [MeasurableMul (IdeleClasses K)]

omit [MeasurableMul (IdeleClasses K)] in
/-- Scalar normalization of the actual logarithmic Mellin functional. -/
theorem logarithmic_mellin_const_mul
    (μ : Measure (IdeleClasses K)) (f ell : IdeleClasses K → ℂ)
    (c : IdeleClasses K →* ℂˣ) (a : ℂ) (j : ℕ) :
    mellin K μ (fun x => (a * f x) * ell x ^ j) c =
      a * mellin K μ (fun x => f x * ell x ^ j) c := by
  unfold mellin
  simp only [mul_assoc]
  exact integral_const_mul _ _

/-- The scaling operation on a lift is explicit, not a spectral existence claim. -/
noncomputable def normalizedMellinLift (μ : Measure (IdeleClasses K))
    (f : IdeleClasses K → ℂ) (c : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ) (n : ℕ) (x : IdeleClasses K) : ℂ :=
  (mellin K μ (fun y => f y * ell y ^ n) c)⁻¹ * f x

/-- Closes the non-unit top-moment factor in the cutoff coefficient formula.
The precise cost of normalizing every lift is retained in `hmajor`.
Genuine Hecke lifts, their nonzero moments, and this summable bound are not
asserted to exist. This theorem is used at (10.4.2.20) -> (12.5.1.4), but
neither its scalar series nor its index type is defined to be a trace/divisor. -/
theorem normalized_shifted_convolution_cutoff_tsum
    {ι : Type*}
    [MeasurableMul₂ (IdeleClasses K)] [MeasurableInv (IdeleClasses K)]
    [OpensMeasurableSpace (IdeleClasses K)]
    (μ : Measure (IdeleClasses K)) [μ.IsMulLeftInvariant] [SFinite μ]
    [IsFiniteMeasureOnCompacts μ]
    (φ : IdeleClasses K → ℂ) (f : ι → IdeleClasses K → ℂ)
    (c : ι → IdeleClasses K →* ℂˣ) (q : IdeleClasses K →* ℂˣ)
    (ell : IdeleClasses K → ℂ)
    (hell : ∀ x y, ell (x * y) = ell x + ell y)
    (hφ : Continuous φ) (hφsupp : HasCompactSupport φ)
    (hcq : ∀ i, Continuous (fun x => ((c i * q⁻¹) x : ℂ)))
    (hellcont : Continuous ell) (n : ι → ℕ)
    (hf : ∀ i j, j ≤ n i →
      Integrable (fun x => (f i x * ell x ^ j) * (c i x : ℂ)) μ)
    (hzero : ∀ i j, j < n i →
      mellin K μ (fun x => f i x * ell x ^ j) (c i) = 0)
    (hne : ∀ i, mellin K μ (fun x => f i x * ell x ^ n i) (c i) ≠ 0)
    (ρ : ℕ → IdeleClasses K → ℂ)
    (hρmeas : ∀ k, AEStronglyMeasurable (ρ k) μ)
    (hρbound : ∀ k x, ‖ρ k x‖ ≤ 1)
    (hρlim : ∀ x, Filter.Tendsto (fun k => ρ k x) Filter.atTop (nhds 1))
    (hmajor : Summable (fun i =>
      ‖(mellin K μ (fun x => f i x * ell x ^ n i) (c i))⁻¹‖ *
        ∫ x, ‖convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
          ((c i * q⁻¹) x : ℂ) * ell x ^ n i‖ ∂μ)) :
    (∀ i, mellin K μ
      (fun x => normalizedMellinLift K μ (f i) (c i) ell (n i) x * ell x ^ n i)
      (c i) = 1) ∧
    (∀ k, Summable (fun i => ∫ x, ρ k x *
      (convolution K μ φ
        (fun y => (q y : ℂ) * normalizedMellinLift K μ (f i) (c i) ell (n i) y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i) ∂μ)) ∧
    Summable (fun i => mellin K μ φ (c i * q⁻¹)) ∧
    Filter.Tendsto (fun k => ∑' i, ∫ x, ρ k x *
      (convolution K μ φ
        (fun y => (q y : ℂ) * normalizedMellinLift K μ (f i) (c i) ell (n i) y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i) ∂μ) Filter.atTop
      (nhds (∑' i, mellin K μ φ (c i * q⁻¹))) := by
  let a : ι → ℂ := fun i =>
    (mellin K μ (fun x => f i x * ell x ^ n i) (c i))⁻¹
  let F : ι → IdeleClasses K → ℂ := fun i =>
    normalizedMellinLift K μ (f i) (c i) ell (n i)
  have hF (i : ι) (x : IdeleClasses K) : F i x = a i * f i x := rfl
  have hmoment (i : ι) (j : ℕ) :
      mellin K μ (fun x => F i x * ell x ^ j) (c i) =
        a i * mellin K μ (fun x => f i x * ell x ^ j) (c i) := by
    simp_rw [hF]
    exact logarithmic_mellin_const_mul K μ (f i) ell (c i) (a i) j
  have htop (i : ι) :
      mellin K μ (fun x => F i x * ell x ^ n i) (c i) = 1 := by
    rw [hmoment]
    exact inv_mul_cancel₀ (hne i)
  have hFi (i : ι) (j : ℕ) (hj : j ≤ n i) :
      Integrable (fun x => (F i x * ell x ^ j) * (c i x : ℂ)) μ := by
    simp_rw [hF]
    simpa only [mul_assoc] using (hf i j hj).const_mul (a i)
  have hFzero (i : ι) (j : ℕ) (hj : j < n i) :
      mellin K μ (fun x => F i x * ell x ^ j) (c i) = 0 := by
    rw [hmoment, hzero i j hj, mul_zero]
  have hconv (i : ι) (x : IdeleClasses K) :
      convolution K μ φ (fun y => (q y : ℂ) * F i y) x =
        a i * convolution K μ φ (fun y => (q y : ℂ) * f i y) x := by
    unfold convolution
    simp_rw [hF]
    calc
      _ = ∫ g, a i * (φ g * ((q (g⁻¹ * x) : ℂ) * f i (g⁻¹ * x))) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with g
        ring
      _ = _ := integral_const_mul _ _
  have hmajorF : Summable (fun i => ∫ x,
      ‖convolution K μ φ (fun y => (q y : ℂ) * F i y) x *
        ((c i * q⁻¹) x : ℂ) * ell x ^ n i‖ ∂μ) := by
    have he (i : ι) : (∫ x,
        ‖convolution K μ φ (fun y => (q y : ℂ) * F i y) x *
          ((c i * q⁻¹) x : ℂ) * ell x ^ n i‖ ∂μ) =
        ‖a i‖ * ∫ x,
          ‖convolution K μ φ (fun y => (q y : ℂ) * f i y) x *
            ((c i * q⁻¹) x : ℂ) * ell x ^ n i‖ ∂μ := by
      simp_rw [hconv, mul_assoc, norm_mul]
      rw [integral_const_mul]
    simp_rw [he]
    exact hmajor
  have h := shifted_convolution_cutoff_tsum_limit K μ φ F c q ell hell hφ hφsupp
    hcq hellcont n hFi hFzero ρ hρmeas hρbound hρlim hmajorF
  refine ⟨htop, h.1, ?_, ?_⟩
  · simpa only [htop, mul_one] using h.2.1
  · simpa only [htop, mul_one] using h.2.2

#check normalized_shifted_convolution_cutoff_tsum
#print axioms normalized_shifted_convolution_cutoff_tsum
end MasulloTrace
