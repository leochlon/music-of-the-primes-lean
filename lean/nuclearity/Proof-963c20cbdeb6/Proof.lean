import Mathlib

/-!
Participant H, round 54. An integrated partial step for the spectral action in
(10.4.2.29)--(10.4.2.33): the actual convolution on the genuine idele-class group
acts on multiplicative coefficient functions by the correctly oriented Mellin
integral. This does NOT identify a spectral quotient with genuine Hecke zeros.
-/
open scoped NumberField
open MeasureTheory

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K

variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- The convolution formula in the manuscript, on the actual idele-class group.
Its analytic domain is imposed explicitly in the theorems below. -/
noncomputable def actualConvolution
    (μ : Measure (HeckeIdeleClasses K))
    (φ ψ : HeckeIdeleClasses K → ℂ) (x : HeckeIdeleClasses K) : ℂ :=
  ∫ g, φ g * ψ (g⁻¹ * x) ∂μ

/-- The inverse character is forced by the left-convolution convention.
This is valid for any multiplicative coefficient on the genuine class group;
it neither introduces nor chooses any zeros. -/
theorem actualConvolution_character
    (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ)
    (c : HeckeIdeleClasses K →* ℂˣ) (x : HeckeIdeleClasses K) :
    actualConvolution K μ φ (fun g => (c g : ℂ)) x =
      (∫ g, φ g * ((c g : ℂ)⁻¹) ∂μ) * (c x : ℂ) := by
  unfold actualConvolution
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  simp_rw [← mul_assoc]
  exact integral_mul_const _ _

/-- Absolute integrability of the actual convolution character integrand is
inherited from the weighted Mellin integrand; no Fubini interchange is used. -/
theorem actualConvolution_character_integrable
    (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (h : Integrable (fun g => φ g * ((c g : ℂ)⁻¹)) μ)
    (x : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * (c (g⁻¹ * x) : ℂ)) μ := by
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, ← mul_assoc]
  exact h.mul_const _

/-- The coefficient action occurring in (10.4.2.29)--(10.4.2.33).
It is defined by the actual group translation, not by its desired eigenvalue. -/
noncomputable def translatedCoefficient
    (μ : Measure (HeckeIdeleClasses K))
    (φ η : HeckeIdeleClasses K → ℂ) (y : HeckeIdeleClasses K) : ℂ :=
  ∫ g, φ g * η (g * y) ∂μ

theorem translatedCoefficient_character
    (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ)
    (c : HeckeIdeleClasses K →* ℂˣ) (y : HeckeIdeleClasses K) :
    translatedCoefficient K μ φ (fun g => (c g : ℂ)) y =
      (∫ g, φ g * (c g : ℂ) ∂μ) * (c y : ℂ) := by
  unfold translatedCoefficient
  simp only [map_mul, Units.val_mul, ← mul_assoc]
  exact integral_mul_const _ _

theorem translatedCoefficient_character_integrable
    (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (h : Integrable (fun g => φ g * (c g : ℂ)) μ)
    (y : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * (c (g * y) : ℂ)) μ := by
  simp only [map_mul, Units.val_mul, ← mul_assoc]
  exact h.mul_const _

/-- The exact complement formula (10.4.3.50). Identifying `k` as a
representative of the genuine spectral operator remains a separate obligation. -/
noncomputable def geometricComplement (φ : HeckeIdeleClasses K → ℂ)
    (k : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (x y : HeckeIdeleClasses K) : ℂ := φ (x * y⁻¹) - k x y

/-- Conditional removal of cutoffs from the complement diagonal, used in
(12.5.1.4). Integrability of that precise spectral diagonal and convergence
of the precise cutoffs are explicit assumptions, not inferred from L² kernels. -/
theorem geometricComplement_cutoff_limit
    (μ : Measure (HeckeIdeleClasses K))
    (φ : HeckeIdeleClasses K → ℂ) (hφ : φ 1 = 0)
    (k : HeckeIdeleClasses K → HeckeIdeleClasses K → ℂ)
    (hk : Integrable (fun x => k x x) μ)
    (ρ : ℕ → HeckeIdeleClasses K → ℂ)
    (hm : ∀ n, AEStronglyMeasurable (ρ n) μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖ρ n x‖ ≤ 1)
    (ht : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => ρ n x) Filter.atTop (nhds 1)) :
    Filter.Tendsto
      (fun n => ∫ x, ρ n x * geometricComplement K φ k x x ∂μ)
      Filter.atTop (nhds (-(∫ x, k x x ∂μ))) := by
  have hd : ∀ x, geometricComplement K φ k x x = -k x x := by
    intro x
    simp [geometricComplement, hφ]
  simp_rw [hd]
  rw [← integral_neg]
  apply tendsto_integral_of_dominated_convergence (fun x => ‖k x x‖)
  · intro n
    exact (hm n).mul hk.aestronglyMeasurable.neg
  · exact hk.norm
  · intro n
    filter_upwards [hb n] with x hx
    rw [norm_mul, norm_neg]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  · filter_upwards [ht] with x hx
    simpa only [one_mul] using hx.mul_const (-k x x)

end MasulloGRH

#check MasulloGRH.actualConvolution_character
#print axioms MasulloGRH.actualConvolution_character
#check MasulloGRH.actualConvolution_character_integrable
#print axioms MasulloGRH.actualConvolution_character_integrable

#check MasulloGRH.translatedCoefficient_character
#print axioms MasulloGRH.translatedCoefficient_character
#check MasulloGRH.translatedCoefficient_character_integrable
#print axioms MasulloGRH.translatedCoefficient_character_integrable

#check MasulloGRH.geometricComplement_cutoff_limit
#print axioms MasulloGRH.geometricComplement_cutoff_limit

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- Logarithmic coefficients in (10.4.2.29). The positive norm homomorphism
is an explicit parameter; its identification with the normalized idelic norm
is NOT asserted by this partial theorem. -/
noncomputable def logJet
    (ν : HeckeIdeleClasses K →* ℝ)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (m : ℕ) (g : HeckeIdeleClasses K) : ℂ :=
  (c g : ℂ) * (Real.log (ν g) : ℂ) ^ m

/- Exact binomial translation, before taking any trace or identifying zeros. -/
omit [MeasurableSpace (HeckeIdeleClasses K)] in
theorem logJet_mul
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (m : ℕ) (g y : HeckeIdeleClasses K) :
    logJet K ν c m (g * y) =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * logJet K ν c i g * logJet K ν c (m-i) y := by
  simp only [logJet, map_mul, Units.val_mul]
  rw [Real.log_mul (ne_of_gt (hν g)) (ne_of_gt (hν y)), Complex.ofReal_add,
    add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Weighted logarithmic moments are the explicit analytic assumptions
needed to integrate (10.4.2.33); each order up to m is required. -/
theorem translatedCoefficient_logJet
    (μ : Measure (HeckeIdeleClasses K))
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ : HeckeIdeleClasses K → ℂ) (m : ℕ)
    (hφ : ∀ i ≤ m, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (y : HeckeIdeleClasses K) :
    translatedCoefficient K μ φ (logJet K ν c m) y =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * (∫ g, φ g * logJet K ν c i g ∂μ) *
          logJet K ν c (m-i) y := by
  have hid : ∀ g, φ g * logJet K ν c m (g * y) =
      ∑ i ∈ Finset.range (m + 1),
        ((m.choose i : ℂ) * (φ g * logJet K ν c i g)) *
          logJet K ν c (m-i) y := by
    intro g
    rw [logJet_mul K ν hν c m g y, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold translatedCoefficient
  simp_rw [hid]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_mul_const, integral_const_mul]
  · intro i hi
    exact ((hφ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).const_mul _).mul_const _

/-- The same moment assumptions give absolute integrability of the actual
translated jet, so the preceding identity does not exploit totalization. -/
theorem translatedCoefficient_logJet_integrable
    (μ : Measure (HeckeIdeleClasses K))
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ : HeckeIdeleClasses K → ℂ) (m : ℕ)
    (hφ : ∀ i ≤ m, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (y : HeckeIdeleClasses K) :
    Integrable (fun g => φ g * logJet K ν c m (g * y)) μ := by
  simp_rw [logJet_mul K ν hν c m, Finset.mul_sum]
  apply integrable_finset_sum
  intro i hi
  have h := ((hφ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).const_mul
    (m.choose i : ℂ)).mul_const (logJet K ν c (m-i) y)
  convert h using 1
  ext g
  ring

end MasulloGRH

#check MasulloGRH.logJet_mul
#print axioms MasulloGRH.logJet_mul
#check MasulloGRH.translatedCoefficient_logJet
#print axioms MasulloGRH.translatedCoefficient_logJet
#check MasulloGRH.translatedCoefficient_logJet_integrable
#print axioms MasulloGRH.translatedCoefficient_logJet_integrable

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- Separate the leading coefficient from all strictly lower logarithmic orders. -/
theorem translatedCoefficient_logJet_leading
    (μ : Measure (HeckeIdeleClasses K))
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ : HeckeIdeleClasses K → ℂ) (m : ℕ)
    (hφ : ∀ i ≤ m, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (y : HeckeIdeleClasses K) :
    translatedCoefficient K μ φ (logJet K ν c m) y =
      (∫ g, φ g * (c g : ℂ) ∂μ) * logJet K ν c m y +
      ∑ i ∈ Finset.range m,
        (m.choose (i+1) : ℂ) * (∫ g, φ g * logJet K ν c (i+1) g ∂μ) *
          logJet K ν c (m-(i+1)) y := by
  rw [translatedCoefficient_logJet K μ ν hν c φ m hφ y,
    Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
    logJet, pow_zero, mul_one]
  exact add_comm _ _

end MasulloGRH
#check MasulloGRH.translatedCoefficient_logJet_leading
#print axioms MasulloGRH.translatedCoefficient_logJet_leading

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K)]

/-- Compactly supported continuous tests discharge every finite jet moment.
The measure must be finite on compact sets; no spectral assertion is assumed. -/
theorem logJet_moment_integrable
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (m : ℕ) :
    Integrable (fun g => φ g * logJet K ν c m g) μ := by
  have hlog : Continuous (fun g => (Real.log (ν g) : ℂ)) :=
    Complex.continuous_ofReal.comp (hνc.log (fun g => ne_of_gt (hν g)))
  exact (hφc.mul (hc.mul (hlog.pow m))).integrable_of_hasCompactSupport
    hφs.mul_right

/-- Translation formula for the compact test class, with moment integrability
proved rather than assumed. Smooth admissible tests satisfy the stated regularity. -/
theorem translatedCoefficient_logJet_compact
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (m : ℕ) (y : HeckeIdeleClasses K) :
    translatedCoefficient K μ φ (logJet K ν c m) y =
      ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℂ) * (∫ g, φ g * logJet K ν c i g ∂μ) *
          logJet K ν c (m-i) y := by
  exact translatedCoefficient_logJet K μ ν hν c φ m
    (fun i _ => logJet_moment_integrable K μ ν hν hνc c hc φ hφc hφs i) y

end MasulloGRH
#check MasulloGRH.logJet_moment_integrable
#print axioms MasulloGRH.logJet_moment_integrable
#check MasulloGRH.translatedCoefficient_logJet_compact
#print axioms MasulloGRH.translatedCoefficient_logJet_compact
