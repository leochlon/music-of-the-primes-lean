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

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- Finite multiplicity contribution from the actual translated coefficient
integral. The basis and operator-realization hypotheses are explicit: this
is not an identification of these coefficients with genuine Hecke zeros. -/
theorem actualCoefficientSpace_trace
    (μ : Measure (HeckeIdeleClasses K))
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ)
    (hφ : ∀ i < N, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (W : Submodule ℂ (HeckeIdeleClasses K → ℂ))
    (b : Module.Basis (Fin N) ℂ W)
    (hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val)
    (T : W →ₗ[ℂ] W)
    (hT : ∀ i y, (T (b i) : HeckeIdeleClasses K → ℂ) y =
      translatedCoefficient K μ φ (logJet K ν c i.val) y) :
    LinearMap.trace ℂ W T = (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  classical
  let v : ℕ → W := fun m => if h : m < N then b ⟨m, h⟩ else 0
  let M : ℂ := ∫ g, φ g * (c g : ℂ) ∂μ
  have hv (m : ℕ) (hm : m < N) :
      (v m : HeckeIdeleClasses K → ℂ) = logJet K ν c m := by
    simp only [v, dif_pos hm]
    exact hb ⟨m, hm⟩
  have hdiag (j : Fin N) : b.repr (T (b j)) j = M := by
    have hvec : T (b j) = M • b j +
        ∑ i ∈ Finset.range j.val,
          ((j.val.choose (i+1) : ℂ) * (∫ g, φ g * logJet K ν c (i+1) g ∂μ)) •
            v (j.val-(i+1)) := by
      apply Subtype.ext
      funext y
      rw [hT, translatedCoefficient_logJet_leading K μ ν hν c φ j.val
        (fun i hi => hφ i (lt_of_le_of_lt hi j.isLt))]
      simp only [Submodule.coe_add, Submodule.coe_smul, Finset.sum_apply,
        Submodule.coe_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hb j]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hm : j.val - (i+1) < N := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      rw [hv _ hm]
    rw [hvec]
    simp only [map_add, map_smul, map_sum, Finsupp.add_apply,
      Finsupp.smul_apply, smul_eq_mul]
    have hz : ∀ i ∈ Finset.range j.val, b.repr (v (j.val-(i+1))) j = 0 := by
      intro i hi
      have hj : j.val-(i+1) < j.val := by
        have := Finset.mem_range.mp hi
        omega
      have hm : j.val-(i+1) < N := lt_trans hj j.isLt
      have hn : (⟨j.val-(i+1), hm⟩ : Fin N) ≠ j := by
        intro he
        have hval : j.val-(i+1) = j.val := congrArg Fin.val he
        exact (Nat.ne_of_lt hj) hval
      simp [v, hm, hn]
    simp [M]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i hi, mul_zero]
  rw [LinearMap.trace_eq_matrix_trace ℂ b T]
  simp [Matrix.trace, LinearMap.toMatrix_apply, hdiag, M]

end MasulloGRH
#check MasulloGRH.actualCoefficientSpace_trace
#print axioms MasulloGRH.actualCoefficientSpace_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- Construct the translated integral action on the coefficient space.
The coefficient basis remains explicit; no spectral identification is assumed. -/
theorem actualCoefficientSpace_exists_trace
    (μ : Measure (HeckeIdeleClasses K))
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ)
    (hφ : ∀ i < N, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (W : Submodule ℂ (HeckeIdeleClasses K → ℂ))
    (b : Module.Basis (Fin N) ℂ W)
    (hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val) :
    ∃ T : W →ₗ[ℂ] W,
      (∀ i y, (T (b i) : HeckeIdeleClasses K → ℂ) y =
        translatedCoefficient K μ φ (logJet K ν c i.val) y) ∧
      LinearMap.trace ℂ W T = (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  classical
  let v : ℕ → W := fun m => if h : m < N then b ⟨m, h⟩ else 0
  have hv (m : ℕ) (hm : m < N) :
      (v m : HeckeIdeleClasses K → ℂ) = logJet K ν c m := by
    simp only [v, dif_pos hm]
    exact hb ⟨m, hm⟩
  let w : Fin N → W := fun j =>
    ∑ i ∈ Finset.range (j.val+1),
      ((j.val.choose i : ℂ) * (∫ g, φ g * logJet K ν c i g ∂μ)) • v (j.val-i)
  have hw (j : Fin N) (y : HeckeIdeleClasses K) :
      (w j : HeckeIdeleClasses K → ℂ) y =
        translatedCoefficient K μ φ (logJet K ν c j.val) y := by
    rw [translatedCoefficient_logJet K μ ν hν c φ j.val
      (fun i hi => hφ i (lt_of_le_of_lt hi j.isLt))]
    simp only [w, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hv _ (lt_of_le_of_lt (Nat.sub_le _ _) j.isLt)]
  let T : W →ₗ[ℂ] W := b.constr ℂ w
  have hT : ∀ i y, (T (b i) : HeckeIdeleClasses K → ℂ) y =
      translatedCoefficient K μ φ (logJet K ν c i.val) y := by
    intro i y
    simpa only [T, Module.Basis.constr_basis] using hw i y
  exact ⟨T, hT, actualCoefficientSpace_trace K μ ν hν c φ N hφ W b hb T hT⟩

end MasulloGRH
#check MasulloGRH.actualCoefficientSpace_exists_trace
#print axioms MasulloGRH.actualCoefficientSpace_exists_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- The constructed finite coefficient operator is the actual translated
integral on every vector, with absolute integrability proved. This is the finite
coefficient action needed before the nuclear expansion in (10.4.2.34); it does
not identify the coefficient space with the genuine spectral quotient. -/
theorem actualCoefficientSpace_realized_trace
    (μ : Measure (HeckeIdeleClasses K))
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ : HeckeIdeleClasses K → ℂ) (N : ℕ)
    (hφ : ∀ i < N, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (W : Submodule ℂ (HeckeIdeleClasses K → ℂ))
    (b : Module.Basis (Fin N) ℂ W)
    (hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val) :
    ∃ T : W →ₗ[ℂ] W,
      (∀ (f : W) y,
        Integrable (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ ∧
        (T f : HeckeIdeleClasses K → ℂ) y =
          translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y) ∧
      LinearMap.trace ℂ W T = (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  classical
  obtain ⟨T, hT, htrace⟩ :=
    actualCoefficientSpace_exists_trace K μ ν hν c φ N hφ W b hb
  refine ⟨T, ?_, htrace⟩
  intro f y
  have hf (z : HeckeIdeleClasses K) :
      (f : HeckeIdeleClasses K → ℂ) z =
        ∑ j : Fin N, b.repr f j * logJet K ν c j.val z := by
    have he := congrArg (fun q : W => (q : HeckeIdeleClasses K → ℂ) z)
      (b.sum_repr f)
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul, hb] using he.symm
  have hi (j : Fin N) :
      Integrable (fun g => φ g * logJet K ν c j.val (g * y)) μ :=
    translatedCoefficient_logJet_integrable K μ ν hν c φ j.val
      (fun i hi => hφ i (lt_of_le_of_lt hi j.isLt)) y
  have hform (g : HeckeIdeleClasses K) :
      φ g * (f : HeckeIdeleClasses K → ℂ) (g * y) =
        ∑ j : Fin N, b.repr f j * (φ g * logJet K ν c j.val (g * y)) := by
    rw [hf, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hint : Integrable
      (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ := by
    simp_rw [hform]
    exact integrable_finset_sum _ (fun j _ => (hi j).const_mul _)
  refine ⟨hint, ?_⟩
  have heq : translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y =
      ∑ j : Fin N, b.repr f j * translatedCoefficient K μ φ
        (logJet K ν c j.val) y := by
    unfold translatedCoefficient
    simp_rw [hform]
    rw [integral_finset_sum _ (fun j _ => (hi j).const_mul _)]
    simp_rw [integral_const_mul]
  rw [heq]
  have he := congrArg (fun q : W => (q : HeckeIdeleClasses K → ℂ) y)
    (congrArg T (b.sum_repr f))
  simpa only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hT] using he.symm

end MasulloGRH
#check MasulloGRH.actualCoefficientSpace_realized_trace
#print axioms MasulloGRH.actualCoefficientSpace_realized_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K)]

/-- For continuous compactly supported tests the finite coefficient action is
uniquely specified by the actual integral on every vector. All finite moments
are discharged here. Identification of W and N with a genuine Hecke spectral
block, and passage to the full nuclear trace, remain outside this theorem. -/
theorem actualCoefficientSpace_compact_trace
    (μ : Measure (HeckeIdeleClasses K)) [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (N : ℕ)
    (W : Submodule ℂ (HeckeIdeleClasses K → ℂ))
    (b : Module.Basis (Fin N) ℂ W)
    (hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val) :
    ∃! T : W →ₗ[ℂ] W,
      (∀ (f : W) y,
        Integrable (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ ∧
        (T f : HeckeIdeleClasses K → ℂ) y =
          translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y) ∧
      LinearMap.trace ℂ W T = (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  obtain ⟨T, hT, htrace⟩ := actualCoefficientSpace_realized_trace K μ ν hν c φ N
    (fun i _ => logJet_moment_integrable K μ ν hν hνc c hc φ hφc hφs i) W b hb
  refine ⟨T, ⟨hT, htrace⟩, ?_⟩
  intro U hU
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext y
  exact (hU.1 f y).2.trans ((hT f y).2.symm)

end MasulloGRH
#check MasulloGRH.actualCoefficientSpace_compact_trace
#print axioms MasulloGRH.actualCoefficientSpace_compact_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [MeasurableMul (HeckeIdeleClasses K)]

/-- Haar/Fubini transpose identity for the actual convolution and coefficient
operators. Both absolute joint-integrability obligations are explicit. This
is the pairing step needed before the spectral trace, not that trace itself. -/
theorem actualConvolution_transpose
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    (φ ψ η : HeckeIdeleClasses K → ℂ)
    (hleft : Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.2 * ψ (p.2⁻¹ * p.1) * η p.1) (μ.prod μ))
    (hright : Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ p.2 * η (p.1 * p.2)) (μ.prod μ)) :
    (∫ x, actualConvolution K μ φ ψ x * η x ∂μ) =
      ∫ y, ψ y * translatedCoefficient K μ φ η y ∂μ := by
  unfold actualConvolution translatedCoefficient
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap hleft]
  have hs (g : HeckeIdeleClasses K) :
      (∫ x, φ g * ψ (g⁻¹ * x) * η x ∂μ) =
        ∫ y, φ g * ψ y * η (g * y) ∂μ := by
    simpa only [inv_mul_cancel_left] using
      (integral_mul_left_eq_self (μ := μ)
        (fun x => φ g * ψ (g⁻¹ * x) * η x) g).symm
  simp_rw [hs]
  rw [integral_integral_swap hright]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  ring

end MasulloGRH
#check MasulloGRH.actualConvolution_transpose
#print axioms MasulloGRH.actualConvolution_transpose

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [MeasurableMul (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K)]

/-- Integration of the Haar/Fubini transpose identity with the finite
coefficient trace. The operator is constructed from translated integrals;
the pairing with the original convolution is proved on its stated domain.
Identification with a genuine Hecke zero block is still an explicit gap. -/
theorem actualCoefficientSpace_transpose_trace
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (N : ℕ)
    (W : Submodule ℂ (HeckeIdeleClasses K → ℂ))
    (b : Module.Basis (Fin N) ℂ W)
    (hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val) :
    ∃ T : W →ₗ[ℂ] W,
      (∀ (f : W) y,
        Integrable (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ ∧
        (T f : HeckeIdeleClasses K → ℂ) y =
          translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y) ∧
      (∀ (f : W) (ψ : HeckeIdeleClasses K → ℂ),
        Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
          φ p.2 * ψ (p.2⁻¹ * p.1) * (f : HeckeIdeleClasses K → ℂ) p.1) (μ.prod μ) →
        Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
          φ p.1 * ψ p.2 * (f : HeckeIdeleClasses K → ℂ) (p.1 * p.2)) (μ.prod μ) →
        (∫ x, actualConvolution K μ φ ψ x * (f : HeckeIdeleClasses K → ℂ) x ∂μ) =
          ∫ y, ψ y * (T f : HeckeIdeleClasses K → ℂ) y ∂μ) ∧
      LinearMap.trace ℂ W T = (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  obtain ⟨T, ⟨hT, htrace⟩, _⟩ :=
    actualCoefficientSpace_compact_trace K μ ν hν hνc c hc φ hφc hφs N W b hb
  refine ⟨T, hT, ?_, htrace⟩
  intro f ψ hleft hright
  rw [actualConvolution_transpose K μ φ ψ (f : HeckeIdeleClasses K → ℂ) hleft hright]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [(hT f y).2]

end MasulloGRH
#check MasulloGRH.actualCoefficientSpace_transpose_trace
#print axioms MasulloGRH.actualCoefficientSpace_transpose_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]

/-- The finite weighted moments give absolute integrability of the actual
translated two-variable coefficient kernel. This is the Fubini obligation
in the spectral convolution calculation, with no compact-support restriction
on the vector psi. -/
theorem logJet_joint_integrable
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (c : HeckeIdeleClasses K →* ℂˣ)
    (φ ψ : HeckeIdeleClasses K → ℂ) (m : ℕ)
    (hφ : ∀ i ≤ m, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (hψ : ∀ i ≤ m, Integrable (fun g => ψ g * logJet K ν c i g) μ) :
    Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ p.2 * logJet K ν c m (p.1 * p.2)) (μ.prod μ) := by
  have heq : (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ p.2 * logJet K ν c m (p.1 * p.2)) =
      fun p => ∑ i ∈ Finset.range (m + 1), (m.choose i : ℂ) *
        ((φ p.1 * logJet K ν c i p.1) *
          (ψ p.2 * logJet K ν c (m-i) p.2)) := by
    funext p
    rw [logJet_mul K ν hν c m p.1 p.2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  apply integrable_finset_sum
  intro i hi
  exact ((hφ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).mul_prod
    (hψ (m-i) (Nat.sub_le m i))).const_mul _

variable [MeasurableMul₂ (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]

/-- The actual convolution has the logarithmic transpose pairing for
continuous, possibly noncompact vectors with finite weighted moments.
Both joint Fubini hypotheses are proved by tensor integrability and Haar shear. -/
theorem actualConvolution_logJet_transpose
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ ψ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ) (hψc : Continuous ψ)
    (m : ℕ)
    (hφ : ∀ i ≤ m, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (hψ : ∀ i ≤ m, Integrable (fun g => ψ g * logJet K ν c i g) μ) :
    (∫ x, actualConvolution K μ φ ψ x * logJet K ν c m x ∂μ) =
      ∫ y, ψ y * translatedCoefficient K μ φ (logJet K ν c m) y ∂μ := by
  have hr := logJet_joint_integrable K μ ν hν c φ ψ m hφ hψ
  have hlog : Continuous (fun g => (Real.log (ν g) : ℂ)) :=
    Complex.continuous_ofReal.comp (hνc.log (fun g => ne_of_gt (hν g)))
  have hη : Continuous (logJet K ν c m) := hc.mul (hlog.pow m)
  have hiC : Continuous (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ (p.1⁻¹ * p.2) * logJet K ν c m p.2) :=
    ((hφc.comp continuous_fst).mul
      (hψc.comp (continuous_fst.inv.mul continuous_snd))).mul
      (hη.comp continuous_snd)
  have hi : Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ (p.1⁻¹ * p.2) * logJet K ν c m p.2) (μ.prod μ) := by
    apply ((measurePreserving_prod_mul μ μ).integrable_comp hiC.aestronglyMeasurable).mp
    simpa only [Function.comp_def, inv_mul_cancel_left] using hr
  exact actualConvolution_transpose K μ φ ψ (logJet K ν c m) hi.swap hr

end MasulloGRH
#check MasulloGRH.logJet_joint_integrable
#print axioms MasulloGRH.logJet_joint_integrable
#check MasulloGRH.actualConvolution_logJet_transpose
#print axioms MasulloGRH.actualConvolution_logJet_transpose

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]

/-- Integration into the same finite coefficient trace: every basis
coefficient pairs with the actual convolution on noncompact continuous
vectors having the required weighted moments. N is still a basis dimension,
not a proved arithmetic zero multiplicity. -/
theorem actualCoefficientSpace_weighted_transpose_trace
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (N : ℕ)
    (W : Submodule ℂ (HeckeIdeleClasses K → ℂ))
    (b : Module.Basis (Fin N) ℂ W)
    (hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val) :
    ∃ T : W →ₗ[ℂ] W,
      (∀ (f : W) y,
        Integrable (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ ∧
        (T f : HeckeIdeleClasses K → ℂ) y =
          translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y) ∧
      (∀ (i : Fin N) (ψ : HeckeIdeleClasses K → ℂ), Continuous ψ →
        (∀ j < N, Integrable (fun g => ψ g * logJet K ν c j g) μ) →
        (∫ x, actualConvolution K μ φ ψ x * (b i : HeckeIdeleClasses K → ℂ) x ∂μ) =
          ∫ y, ψ y * (T (b i) : HeckeIdeleClasses K → ℂ) y ∂μ) ∧
      LinearMap.trace ℂ W T = (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  obtain ⟨T, ⟨hT, htrace⟩, _⟩ :=
    actualCoefficientSpace_compact_trace K μ ν hν hνc c hc φ hφc hφs N W b hb
  refine ⟨T, hT, ?_, htrace⟩
  intro i ψ hψc hψ
  have ht := actualConvolution_logJet_transpose K μ ν hν hνc c hc φ ψ hφc hψc
    i.val (fun j _ => logJet_moment_integrable K μ ν hν hνc c hc φ hφc hφs j)
    (fun j hj => hψ j (lt_of_le_of_lt hj i.isLt))
  calc
    _ = ∫ y, ψ y * translatedCoefficient K μ φ (logJet K ν c i.val) y ∂μ := by
      simpa only [hb i] using ht
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [(hT (b i) y).2, hb i]

end MasulloGRH
#check MasulloGRH.actualCoefficientSpace_weighted_transpose_trace
#print axioms MasulloGRH.actualCoefficientSpace_weighted_transpose_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]

/-- Absolute outer integrability of both coefficient pairings used in the
weighted finite trace theorem, ruling out reliance on totalized integrals. -/
theorem actualConvolution_logJet_transpose_integrable
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g)
    (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (φ ψ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ) (hψc : Continuous ψ)
    (m : ℕ)
    (hφ : ∀ i ≤ m, Integrable (fun g => φ g * logJet K ν c i g) μ)
    (hψ : ∀ i ≤ m, Integrable (fun g => ψ g * logJet K ν c i g) μ) :
    Integrable (fun x => actualConvolution K μ φ ψ x * logJet K ν c m x) μ ∧
    Integrable (fun y => ψ y * translatedCoefficient K μ φ (logJet K ν c m) y) μ ∧
    (∫ x, actualConvolution K μ φ ψ x * logJet K ν c m x ∂μ) =
      ∫ y, ψ y * translatedCoefficient K μ φ (logJet K ν c m) y ∂μ := by
  have hr := logJet_joint_integrable K μ ν hν c φ ψ m hφ hψ
  have hlog : Continuous (fun g => (Real.log (ν g) : ℂ)) :=
    Complex.continuous_ofReal.comp (hνc.log (fun g => ne_of_gt (hν g)))
  have hη : Continuous (logJet K ν c m) := hc.mul (hlog.pow m)
  have hiC : Continuous (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ (p.1⁻¹ * p.2) * logJet K ν c m p.2) :=
    ((hφc.comp continuous_fst).mul
      (hψc.comp (continuous_fst.inv.mul continuous_snd))).mul
      (hη.comp continuous_snd)
  have hi : Integrable (fun p : HeckeIdeleClasses K × HeckeIdeleClasses K =>
      φ p.1 * ψ (p.1⁻¹ * p.2) * logJet K ν c m p.2) (μ.prod μ) := by
    apply ((measurePreserving_prod_mul μ μ).integrable_comp hiC.aestronglyMeasurable).mp
    simpa only [Function.comp_def, inv_mul_cancel_left] using hr
  refine ⟨?_, ?_, actualConvolution_transpose K μ φ ψ (logJet K ν c m) hi.swap hr⟩
  · simpa only [actualConvolution, integral_mul_const] using hi.integral_prod_right
  · have heq : (fun y => ∫ g, φ g * ψ y * logJet K ν c m (g * y) ∂μ) =
        fun y => ψ y * translatedCoefficient K μ φ (logJet K ν c m) y := by
      funext y
      unfold translatedCoefficient
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with g
      ring
    rw [← heq]
    exact hr.integral_prod_right

end MasulloGRH
#check MasulloGRH.actualConvolution_logJet_transpose_integrable
#print axioms MasulloGRH.actualConvolution_logJet_transpose_integrable

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The logarithmic coefficients are independent when the logarithmic norm
has a section. No basis or zero multiplicity is assumed in this assertion. -/
theorem logJet_linearIndependent
    (ν : HeckeIdeleClasses K →* ℝ) (c : HeckeIdeleClasses K →* ℂˣ)
    (τ : ℝ → HeckeIdeleClasses K) (hτ : ∀ t, Real.log (ν (τ t)) = t)
    (N : ℕ) : LinearIndependent ℂ (fun i : Fin N => logJet K ν c i.val) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  let p : Polynomial ℂ := ∑ j : Fin N, Polynomial.monomial j.val (a j)
  have hz (t : ℝ) : p.eval (t : ℂ) = 0 := by
    have hx := congrFun ha (τ t)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      logJet, hτ] at hx
    have hm : (c (τ t) : ℂ) * (∑ j : Fin N, a j * (t : ℂ) ^ j.val) = 0 := by
      rw [Finset.mul_sum]
      convert hx using 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hs := (mul_eq_zero.mp hm).resolve_left (Units.ne_zero _)
    simpa [p, Polynomial.eval_finset_sum, Polynomial.eval_monomial] using hs
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
    rintro z ⟨t, rfl⟩
    exact hz t
  have hh := congrArg (fun q : Polynomial ℂ => q.coeff i.val) hp
  simpa [p, Polynomial.coeff_monomial, Fin.val_inj] using hh

end MasulloGRH
#check MasulloGRH.logJet_linearIndependent
#print axioms MasulloGRH.logJet_linearIndependent

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The concrete span of the first N logarithmic coefficient functions. -/
noncomputable def logJetSpace
    (ν : HeckeIdeleClasses K →* ℝ) (c : HeckeIdeleClasses K →* ℂˣ) (N : ℕ) :
    Submodule ℂ (HeckeIdeleClasses K → ℂ) :=
  Submodule.span ℂ (Set.range (fun i : Fin N => logJet K ν c i.val))

variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]

/-- Finite trace and actual convolution pairing on a constructed coefficient
space, without an assumed basis. The section and arithmetic identification
of the norm/character remain separate explicit obligations. -/
theorem actualLogJetSpan_weighted_transpose_trace
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g) (hνc : Continuous ν)
    (c : HeckeIdeleClasses K →* ℂˣ) (hc : Continuous (fun g => (c g : ℂ)))
    (τ : ℝ → HeckeIdeleClasses K) (hτ : ∀ t, Real.log (ν (τ t)) = t)
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (N : ℕ) :
    ∃ (b : Module.Basis (Fin N) ℂ (logJetSpace K ν c N))
      (T : logJetSpace K ν c N →ₗ[ℂ] logJetSpace K ν c N),
      (∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val) ∧
      (∀ (f : logJetSpace K ν c N) y,
        Integrable (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ ∧
        (T f : HeckeIdeleClasses K → ℂ) y =
          translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y) ∧
      (∀ (i : Fin N) (ψ : HeckeIdeleClasses K → ℂ), Continuous ψ →
        (∀ j < N, Integrable (fun g => ψ g * logJet K ν c j g) μ) →
        (∫ x, actualConvolution K μ φ ψ x * (b i : HeckeIdeleClasses K → ℂ) x ∂μ) =
          ∫ y, ψ y * (T (b i) : HeckeIdeleClasses K → ℂ) y ∂μ) ∧
      LinearMap.trace ℂ (logJetSpace K ν c N) T =
        (N : ℂ) * (∫ g, φ g * (c g : ℂ) ∂μ) := by
  let b : Module.Basis (Fin N) ℂ (logJetSpace K ν c N) :=
    Module.Basis.span (logJet_linearIndependent K ν c τ hτ N)
  have hb : ∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν c i.val := by
    intro i
    exact Module.Basis.span_apply (logJet_linearIndependent K ν c τ hτ N) i
  obtain ⟨T, hT, hpair, htrace⟩ := actualCoefficientSpace_weighted_transpose_trace
    K μ ν hν hνc c hc φ hφc hφs N (logJetSpace K ν c N) b hb
  exact ⟨b, T, hb, hT, hpair, htrace⟩

end MasulloGRH
#check MasulloGRH.actualLogJetSpan_weighted_transpose_trace
#print axioms MasulloGRH.actualLogJetSpan_weighted_transpose_trace

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- Descent of an actual idelic Hecke quasicharacter, with triviality on
principal ideles proved rather than assumed for a class-group placeholder. -/
noncomputable def descendedHeckeCharacter
    (χ : HeckeIdeles K →* ℂˣ)
    (hp : ∀ a : Kˣ, χ (principalIdele K a) = 1) :
    HeckeIdeleClasses K →* ℂˣ :=
  QuotientGroup.lift (principalIdeles K) χ (by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact hp a)

theorem descendedHeckeCharacter_mk
    (χ : HeckeIdeles K →* ℂˣ)
    (hp : ∀ a : Kˣ, χ (principalIdele K a) = 1) (x : HeckeIdeles K) :
    descendedHeckeCharacter K χ hp (QuotientGroup.mk x) = χ x := rfl

theorem descendedHeckeCharacter_continuous
    (χ : HeckeIdeles K →* ℂˣ)
    (hp : ∀ a : Kˣ, χ (principalIdele K a) = 1)
    (hχ : Continuous (fun x => (χ x : ℂ))) :
    Continuous (fun g => (descendedHeckeCharacter K χ hp g : ℂ)) := by
  exact (QuotientGroup.isQuotientMap_mk (principalIdeles K)).continuous_iff.mpr hχ

end MasulloGRH
#check MasulloGRH.descendedHeckeCharacter_mk
#print axioms MasulloGRH.descendedHeckeCharacter_mk
#check MasulloGRH.descendedHeckeCharacter_continuous
#print axioms MasulloGRH.descendedHeckeCharacter_continuous

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
variable [MeasurableSpace (HeckeIdeleClasses K)]
variable [MeasurableMul₂ (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K)]
variable [OpensMeasurableSpace (HeckeIdeleClasses K × HeckeIdeleClasses K)]

/-- The finite coefficient trace instantiated by a genuine idelic Hecke
quasicharacter. The norm and its section remain explicit hypotheses; N has
not been identified with an arithmetic zero multiplicity. -/
theorem genuineHeckeCharacter_logJet_trace
    (μ : Measure (HeckeIdeleClasses K)) [SFinite μ] [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (ν : HeckeIdeleClasses K →* ℝ) (hν : ∀ g, 0 < ν g) (hνc : Continuous ν)
    (χ : HeckeIdeles K →* ℂˣ)
    (hp : ∀ a : Kˣ, χ (principalIdele K a) = 1)
    (hχ : Continuous (fun x => (χ x : ℂ)))
    (τ : ℝ → HeckeIdeleClasses K) (hτ : ∀ t, Real.log (ν (τ t)) = t)
    (φ : HeckeIdeleClasses K → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (N : ℕ) :
    ∃ (b : Module.Basis (Fin N) ℂ (logJetSpace K ν (descendedHeckeCharacter K χ hp) N))
      (T : logJetSpace K ν (descendedHeckeCharacter K χ hp) N →ₗ[ℂ] logJetSpace K ν (descendedHeckeCharacter K χ hp) N),
      (∀ i, (b i : HeckeIdeleClasses K → ℂ) = logJet K ν (descendedHeckeCharacter K χ hp) i.val) ∧
      (∀ (f : logJetSpace K ν (descendedHeckeCharacter K χ hp) N) y,
        Integrable (fun g => φ g * (f : HeckeIdeleClasses K → ℂ) (g * y)) μ ∧
        (T f : HeckeIdeleClasses K → ℂ) y =
          translatedCoefficient K μ φ (f : HeckeIdeleClasses K → ℂ) y) ∧
      (∀ (i : Fin N) (ψ : HeckeIdeleClasses K → ℂ), Continuous ψ →
        (∀ j < N, Integrable (fun g => ψ g * logJet K ν (descendedHeckeCharacter K χ hp) j g) μ) →
        (∫ x, actualConvolution K μ φ ψ x * (b i : HeckeIdeleClasses K → ℂ) x ∂μ) =
          ∫ y, ψ y * (T (b i) : HeckeIdeleClasses K → ℂ) y ∂μ) ∧
      LinearMap.trace ℂ (logJetSpace K ν (descendedHeckeCharacter K χ hp) N) T =
        (N : ℂ) * (∫ g, φ g * ((descendedHeckeCharacter K χ hp) g : ℂ) ∂μ) := by
  exact actualLogJetSpan_weighted_transpose_trace K μ ν hν hνc
    (descendedHeckeCharacter K χ hp)
    (descendedHeckeCharacter_continuous K χ hp hχ) τ hτ φ hφc hφs N

end MasulloGRH
#check MasulloGRH.genuineHeckeCharacter_logJet_trace
#print axioms MasulloGRH.genuineHeckeCharacter_logJet_trace
