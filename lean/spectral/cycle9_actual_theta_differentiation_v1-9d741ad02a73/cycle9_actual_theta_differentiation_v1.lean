import Mathlib
attribute [local instance] Classical.propDecidable
set_option linter.unnecessarySeqFocus false

/- Exact reused arithmetic quotient/log definitions and continuity from nuclear B177.
No new credit is claimed for this retained component. -/
noncomputable section
open scoped NumberField Valued WithZero ENNReal NNReal
open NumberField MeasureTheory
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
noncomputable instance classCommGroup : CommGroup (HeckeIdeleClasses K) := inferInstance
noncomputable def genuineIdeleModulus (a : HeckeIdeles K) : ℝ :=
  (∏ w : InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) *
    ∏ᶠ v : FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem genuineIdeleModulus_principal (a : Kˣ) :
    genuineIdeleModulus K (principalIdele K a) = 1 := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(principalIdele K a).val.1 w‖ = w (a : K) := by
    exact NumberField.InfinitePlace.Completion.norm_coe w
      ((WithAbs.equiv _).symm (a : K))
  have hf (v : NumberField.FinitePlace K) :
      ‖(principalIdele K a).val.2 v.maximalIdeal‖ = v (a : K) := by
    exact NumberField.FinitePlace.norm_embedding_eq v (a : K)
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  exact NumberField.prod_abs_eq_one (K := K) a.ne_zero
/-- Outside finitely many finite places, an actual idele has local norm one. -/
theorem genuineIdele_finite_norm_support (a : HeckeIdeles K) :
    (Function.mulSupport (fun v : NumberField.FinitePlace K =>
      ‖a.val.2 v.maximalIdeal‖)).Finite := by
  have he : ∀ᶠ v in Filter.cofinite, ‖a.val.2 v‖ = 1 := by
    filter_upwards [RestrictedProduct.eventually _ _ a.val.2,
      RestrictedProduct.eventually _ _ (a⁻¹).val.2] with v hv hi
    change Valued.v (a.val.2 v) ≤ 1 at hv
    change Valued.v ((a⁻¹).val.2 v) ≤ 1 at hi
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 := by
      have h := congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
      exact h
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm hv
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right hi _
        _ = Valued.v (a.val.2 v) := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  exact (Filter.eventually_cofinite.mp he).preimage
    NumberField.FinitePlace.maximalIdeal_injective.injOn
theorem genuineIdeleModulus_mul (a b : HeckeIdeles K) :
    genuineIdeleModulus K (a * b) = genuineIdeleModulus K a * genuineIdeleModulus K b := by
  have hi (w : NumberField.InfinitePlace K) :
      ‖(a * b).val.1 w‖ ^ w.mult =
        ‖a.val.1 w‖ ^ w.mult * ‖b.val.1 w‖ ^ w.mult := by
    change ‖a.val.1 w * b.val.1 w‖ ^ w.mult = _
    rw [norm_mul, mul_pow]
  have hf (v : NumberField.FinitePlace K) :
      ‖(a * b).val.2 v.maximalIdeal‖ =
        ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ := by
    change ‖a.val.2 v.maximalIdeal * b.val.2 v.maximalIdeal‖ = _
    exact norm_mul _ _
  unfold genuineIdeleModulus
  simp_rw [hi, hf]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib
    (genuineIdele_finite_norm_support K a) (genuineIdele_finite_norm_support K b)]
  ring

theorem genuineIdeleModulus_ne_zero (a : HeckeIdeles K) :
    genuineIdeleModulus K a ≠ 0 := by
  have h1 : genuineIdeleModulus K 1 = 1 := by
    simpa only [map_one] using genuineIdeleModulus_principal K 1
  have hp := genuineIdeleModulus_mul K a a⁻¹
  rw [mul_inv_cancel, h1] at hp
  intro hz
  rw [hz, zero_mul] at hp
  exact one_ne_zero hp

end MasulloGRH

namespace Round166F
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable def classLog : HeckeIdeleClasses K → ℝ :=
  Quotient.lift (fun y => Real.log (genuineIdeleModulus K y)) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    change Real.log (genuineIdeleModulus K x) = Real.log (genuineIdeleModulus K y)
    rw [hy, genuineIdeleModulus_mul, genuineIdeleModulus_principal, one_mul])

end Round166F
namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
noncomputable instance classMeasurableSpace : MeasurableSpace (HeckeIdeleClasses K) :=
  borel (HeckeIdeleClasses K)
instance classBorelSpace : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩
end MasulloGRH

namespace MasulloGRH
open scoped Topology
variable (K : Type*) [Field K] [NumberField K]
abbrev FinitePrime := IsDedekindDomain.HeightOneSpectrum (𝓞 K)
abbrev LocalField (v : FinitePrime K) := v.adicCompletion K
noncomputable def integralFiniteAdele (x : ∀ v : FinitePrime K, v.adicCompletionIntegers K) :
    IsDedekindDomain.FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun v : FinitePrime K => LocalField K v)
    (fun v => (v.adicCompletionIntegers K : Set (LocalField K v))) Filter.cofinite x

theorem integralFiniteSet_open : IsOpen
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} := by
  have hr : {a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K | ∀ v : FinitePrime K,
      a v ∈ (v.adicCompletionIntegers K : Set (LocalField K v))} =
      Set.range (integralFiniteAdele K) := by
    ext a
    constructor
    · intro ha
      exact ⟨fun v => ⟨a v, ha v⟩, by ext v; rfl⟩
    · rintro ⟨x, rfl⟩
      exact fun v => (x v).property
  rw [hr]
  exact (RestrictedProduct.isOpenEmbedding_structureMap (fun v =>
    (Valued.isClopen_closedBall (LocalField K v)
      (show (1 : WithZero (Multiplicative ℤ)) ≠ 0 by simp)).isOpen)).isOpen_range

noncomputable def finiteNorm (a : HeckeIdeles K) : ℝ :=
  ∏ᶠ v : NumberField.FinitePlace K, ‖a.val.2 v.maximalIdeal‖

theorem finiteNorm_mul (a b : HeckeIdeles K) :
    finiteNorm K (a*b) = finiteNorm K a * finiteNorm K b := by
  unfold finiteNorm
  have h (v : NumberField.FinitePlace K) :
      ‖(a*b).val.2 v.maximalIdeal‖ = ‖a.val.2 v.maximalIdeal‖ * ‖b.val.2 v.maximalIdeal‖ :=
    norm_mul _ _
  simp_rw [h]
  exact finprod_mul_distrib (genuineIdele_finite_norm_support K a)
    (genuineIdele_finite_norm_support K b)

theorem finiteNorm_one_of_integral (a : HeckeIdeles K)
    (ha : ∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1)
    (hi : ∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1) :
    finiteNorm K a = 1 := by
  have hn (v : FinitePrime K) : ‖a.val.2 v‖ = 1 := by
    have hp : a.val.2 v * (a⁻¹).val.2 v = 1 :=
      congrArg (fun z : HeckeAdeles K => z.2 v) a.val_inv
    have hpv : Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) = 1 := by
      rw [← map_mul, hp, map_one]
    have hv1 : Valued.v (a.val.2 v) = 1 := by
      apply le_antisymm (ha v)
      calc
        1 = Valued.v (a.val.2 v) * Valued.v ((a⁻¹).val.2 v) := hpv.symm
        _ ≤ Valued.v (a.val.2 v) * 1 := mul_le_mul_right (hi v) _
        _ = _ := mul_one _
    change Valued.norm (a.val.2 v) = 1
    rw [Valued.norm_def, hv1, map_one]
    rfl
  simp [finiteNorm, hn]

theorem finiteNorm_continuous : Continuous (finiteNorm K) := by
  let U : Set (HeckeIdeles K) := {a | (∀ v : FinitePrime K, Valued.v (a.val.2 v) ≤ 1) ∧
    (∀ v : FinitePrime K, Valued.v ((a⁻¹).val.2 v) ≤ 1)}
  have ho : IsOpen U := (integralFiniteSet_open K).preimage
    (continuous_snd.comp Units.continuous_val) |>.inter
      ((integralFiniteSet_open K).preimage (continuous_snd.comp Units.continuous_coe_inv))
  have h1 : (1 : HeckeIdeles K) ∈ U := by
    constructor <;> intro v <;> change Valued.v (1 : LocalField K v) ≤ 1 <;> simp
  rw [continuous_iff_continuousAt]
  intro a
  have hV : ∀ᶠ b in 𝓝 a, a⁻¹*b ∈ U :=
    ((ho.preimage (continuous_const.mul continuous_id)).mem_nhds (by simpa using h1))
  apply continuousAt_const.congr_of_eventuallyEq
  filter_upwards [hV] with b hb
  have h := finiteNorm_one_of_integral K (a⁻¹*b) hb.1 hb.2
  have he := finiteNorm_mul K a (a⁻¹*b)
  simpa [h, mul_assoc] using he

theorem genuineIdeleModulus_continuous : Continuous (genuineIdeleModulus K) := by
  have h : Continuous (fun a : HeckeIdeles K =>
      ∏ w : NumberField.InfinitePlace K, ‖a.val.1 w‖ ^ w.mult) := by fun_prop
  exact h.mul (finiteNorm_continuous K)

end MasulloGRH

namespace Round175B
open MasulloGRH Round166F MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Arithmetic logarithm on the actual idele-class quotient. -/
theorem classLog_mul (g x : HeckeIdeleClasses K) :
    classLog K (g * x) = classLog K g + classLog K x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  change Real.log (genuineIdeleModulus K (a*b)) = _
  rw [genuineIdeleModulus_mul, Real.log_mul
    (genuineIdeleModulus_ne_zero K a) (genuineIdeleModulus_ne_zero K b)]
  rfl

theorem classLog_continuous : Continuous (classLog K) :=
  ((genuineIdeleModulus_continuous K).log
    (genuineIdeleModulus_ne_zero K)).quotient_lift _


end Round175B
end

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
/-- Exact character structure from the checked finite-idelic foundation. -/
structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1

/-- Descend the actual character; no spectrum or zero set is prescribed. -/
noncomputable def classCharacter (χ : UnitaryHeckeCharacter K) :
    HeckeIdeleClasses K → Circle :=
  Quotient.lift χ.character (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    rw [hy, map_mul, χ.trivial_on_principal, one_mul])

theorem classCharacter_continuous (χ : UnitaryHeckeCharacter K) :
    Continuous (classCharacter K χ) := χ.character.continuous.quotient_lift _

/-- Definition bridge to the same idelic character as the Euler germ. -/
theorem classCharacter_mk (χ : UnitaryHeckeCharacter K) (x : HeckeIdeles K) :
    classCharacter K χ (QuotientGroup.mk x) = χ.character x := rfl
end MasulloGRH


namespace SpectralRound11B
open MasulloGRH Round166F
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)

end SpectralRound11B



namespace ConditionalB27
open MeasureTheory MasulloGRH Round166F SpectralRound11B

/-- Exact pointwise derivative premise for the native same-Haar Mellin
integral. Domination to exchange derivative and integral is separate. -/
theorem genuineMellinJet_hasDerivAt
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) (z : ℂ) :
    HasDerivAt (fun w => genuineMellinJet K chi w a m x)
      (genuineMellinJet K chi z a (m+1) x) z := by
  have hd := (((hasDerivAt_id z).sub_const (a : ℂ)).mul_const
    (classLog K x : ℂ)).cexp.const_mul (classCharacter K chi x : ℂ)
  have h := hd.mul_const ((classLog K x ^ m : ℝ) : ℂ)
  convert h using 1 <;> simp [genuineMellinJet, pow_succ] <;> ring

/-- All pointwise derivatives are the actual logarithmic native jets, with
no factorial or sign change. This does not assert integral interchange. -/
theorem genuineMellinJet_iteratedDeriv
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) :
    iteratedDeriv m (fun z => genuineMellinJet K chi z a 0 x) =
      (fun z => genuineMellinJet K chi z a m x) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (genuineMellinJet_hasDerivAt K chi a m x z).deriv

#print axioms genuineMellinJet_hasDerivAt
#print axioms genuineMellinJet_iteratedDeriv
end ConditionalB27

namespace ConditionalA878
open MeasureTheory MasulloGRH Round166F Round175B SpectralRound11B Filter Topology
variable (K : Type*) [Field K] [NumberField K]
local instance : MeasurableSpace (HeckeIdeleClasses K) := borel _
local instance : BorelSpace (HeckeIdeleClasses K) := ⟨rfl⟩
variable {mu : Measure (HeckeIdeleClasses K)}

/-- Concrete exponential moment majorant for the genuine quotient-Haar integral. -/
theorem native_jet_norm_bound (chi : UnitaryHeckeCharacter K) (a : ℝ) (m : ℕ)
    (Phi : HeckeIdeleClasses K → ℂ) (z : ℂ) (R : ℝ) (hz : ‖z-(a:ℂ)‖ ≤ R)
    (x : HeckeIdeleClasses K) :
    ‖genuineMellinJet K chi z a m x * Phi x‖ ≤
      Real.exp (R * |classLog K x|) * |classLog K x|^m * ‖Phi x‖ := by
  have he : ((z-(a:ℂ)) * (classLog K x : ℂ)).re ≤ R * |classLog K x| := by
    calc
      _ ≤ ‖(z-(a:ℂ)) * (classLog K x : ℂ)‖ := Complex.re_le_norm _
      _ = ‖z-(a:ℂ)‖ * |classLog K x| := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  simpa only [genuineMellinJet, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_pow] using
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (by positivity : 0 ≤ |classLog K x|^m))
      (norm_nonneg (Phi x))

/-- Actual same-Haar derivative interchange from explicit exponential moments.
The original theta moment estimate, not an assumed derivative identity, is the remaining input. -/
theorem native_mellin_hasDerivAt (chi : UnitaryHeckeCharacter K) (a : ℝ)
    (Phi : HeckeIdeleClasses K → ℂ) (hPhi : AEStronglyMeasurable Phi mu)
    (hmom : ∀ (R : ℝ) (n : ℕ), Integrable (fun x =>
      Real.exp (R * |classLog K x|) * |classLog K x|^n * ‖Phi x‖) mu)
    (m : ℕ) (z : ℂ) :
    HasDerivAt (fun w => ∫ x, genuineMellinJet K chi w a m x * Phi x ∂mu)
      (∫ x, genuineMellinJet K chi z a (m+1) x * Phi x ∂mu) z := by
  have hmeas (w : ℂ) (n : ℕ) : AEStronglyMeasurable
      (fun x => genuineMellinJet K chi w a n x * Phi x) mu := by
    have hc : Continuous (fun x => genuineMellinJet K chi w a n x) := by
      have hl := classLog_continuous K
      have hh := classCharacter_continuous K chi
      unfold genuineMellinJet
      fun_prop
    exact hc.aestronglyMeasurable.mul hPhi
  have hi : Integrable (fun x => genuineMellinJet K chi z a m x * Phi x) mu :=
    (hmom ‖z-(a:ℂ)‖ m).mono' (hmeas z m)
      (Eventually.of_forall (native_jet_norm_bound K chi a m Phi z _ le_rfl))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z (by norm_num : (0:ℝ)<1))
    (Eventually.of_forall fun w => hmeas w m) hi (hmeas z (m+1))
    (bound := fun x => Real.exp ((‖z-(a:ℂ)‖+1) * |classLog K x|) *
      |classLog K x|^(m+1) * ‖Phi x‖) ?_
    (hmom (‖z-(a:ℂ)‖+1) (m+1)) ?_).2
  · exact Eventually.of_forall fun x w hw => native_jet_norm_bound K chi a (m+1) Phi w _
      (by
        have hw' : ‖w-z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        calc
          ‖w-(a:ℂ)‖ = ‖(w-z)+(z-(a:ℂ))‖ := by congr 1; ring
          _ ≤ ‖w-z‖ + ‖z-(a:ℂ)‖ := norm_add_le _ _
          _ ≤ ‖z-(a:ℂ)‖+1 := by linarith) x
  · exact Eventually.of_forall fun x w _ =>
      (ConditionalB27.genuineMellinJet_hasDerivAt K chi a m x w).mul_const (Phi x)

/-- Discharges the full finite-order derivative identity for these actual integrals. -/
theorem native_mellin_iteratedDeriv (chi : UnitaryHeckeCharacter K) (a : ℝ)
    (Phi : HeckeIdeleClasses K → ℂ) (hPhi : AEStronglyMeasurable Phi mu)
    (hmom : ∀ (R : ℝ) (n : ℕ), Integrable (fun x =>
      Real.exp (R * |classLog K x|) * |classLog K x|^n * ‖Phi x‖) mu)
    (m : ℕ) :
    iteratedDeriv m (fun z => ∫ x, genuineMellinJet K chi z a 0 x * Phi x ∂mu) =
      (fun z => ∫ x, genuineMellinJet K chi z a m x * Phi x ∂mu) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (native_mellin_hasDerivAt K chi a Phi hPhi hmom m z).deriv

#print axioms native_jet_norm_bound
#print axioms native_mellin_hasDerivAt
#print axioms native_mellin_iteratedDeriv
end ConditionalA878

namespace ConditionalA879
open MeasureTheory Set MasulloGRH Round166F Round175B
theorem exp_abs_even_polynomial_integrable (m : ℕ) (d : ℝ) (hd : 0 < d) :
    Integrable (fun x : ℝ => Real.exp (-d * |x|) * x ^ (2 * m)) := by
  let g : ℝ → ℝ := fun x => Real.exp (-d * |x|) * x ^ (2 * m)
  have hc : Continuous g := by dsimp [g]; fun_prop
  have ht : IntegrableOn (fun x : ℝ => x ^ (2 * m) * Real.exp (-d * x)) (Ioi 0) := by
    simpa only [Real.rpow_one, Real.rpow_natCast] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 * m : ℕ)) (p := 1)
        (by exact lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _)) (by norm_num) hd)
  have hg : IntegrableOn g (Ioi 0) := ht.congr_fun (by
    intro x hx
    dsimp [g]
    rw [abs_of_pos hx, mul_comm]) measurableSet_Ioi
  have hu : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (h | h)
      · exact h.1
      · linarith
    · intro hx
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  have hp : IntegrableOn g (Ici 0) := by
    rw [← hu]
    exact (hc.integrableOn_Icc).union (hg.mono_set (by intro x hx; change (0 : ℝ) < x; change (1 : ℝ) < x at hx; linarith))
  have hn : IntegrableOn g (Iic 0) := by
    simpa [g, pow_mul] using hp.comp_neg
  have hall : Ici (0 : ℝ) ∪ Iic 0 = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total 0 x
  simpa only [hall, integrableOn_univ] using hp.union hn


variable (K : Type*) [Field K] [NumberField K]

/-- The actual log-Haar exponential-polynomial majorant, reusing B12. -/
theorem native_exp_polynomial_integrable
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume) (n : ℕ) :
    Integrable (fun x => Real.exp (-|classLog K x|) *
      (1 + (classLog K x)^(2*n))) mu := by
  have hr : Integrable (fun t : ℝ => Real.exp (-|t|) * (1+t^(2*n))) := by
    have h0 := exp_abs_even_polynomial_integrable 0 1 (by norm_num)
    have hn := exp_abs_even_polynomial_integrable n 1 (by norm_num)
    have h0' : Integrable (fun t : ℝ => Real.exp (-|t|)) := by simpa using h0
    have hn' : Integrable (fun t : ℝ => Real.exp (-|t|) * t^(2*n)) := by simpa using hn
    convert h0'.add hn' using 1
    funext t
    simp only [Pi.add_apply]
    ring
  have hcmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-|t|) * (1+t^(2*n))) (Measure.map (classLog K) mu) := by
    exact (by fun_prop : Continuous (fun t : ℝ => Real.exp (-|t|) * (1+t^(2*n)))).aestronglyMeasurable
  have hs : Integrable (fun t : ℝ => Real.exp (-|t|) * (1+t^(2*n)))
      (Measure.map (classLog K) mu) := by
    rw [hmap]
    exact hr.smul_measure hc
  exact (integrable_map_measure hcmeas (classLog_continuous K).measurable.aemeasurable).mp hs

/-- Specialization of (3.2.2.7–9): two-sided theta decay supplies every
exponential log moment on the SAME quotient measure; no derivative is assumed. -/
theorem native_moments_of_two_sided_decay
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (Phi : HeckeIdeleClasses K → ℂ) (hPhi : Continuous Phi)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, ∀ x,
      ‖Phi x‖ ≤ C * Real.exp (-(N:ℝ) * |classLog K x|))
    (R : ℝ) (n : ℕ) :
    Integrable (fun x => Real.exp (R * |classLog K x|) *
      |classLog K x|^n * ‖Phi x‖) mu := by
  obtain ⟨N, hN⟩ := exists_nat_gt (R+1)
  obtain ⟨C, hC⟩ := hdecay N
  have hC0 : 0 ≤ C := by
    have hh := hC 1
    exact nonneg_of_mul_nonneg_left (le_trans (norm_nonneg _) hh) (Real.exp_pos _)
  apply ((native_exp_polynomial_integrable K mu c hc hmap n).const_mul C).mono'
    (by have hl := classLog_continuous K; exact (by fun_prop : Continuous
      (fun x => Real.exp (R * |classLog K x|) * |classLog K x|^n * ‖Phi x‖)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    have ht : 0 ≤ |classLog K x| := abs_nonneg _
    have hp : |classLog K x|^n ≤ 1 + (classLog K x)^(2*n) := by
      have hh := sq_nonneg (|classLog K x|^n - 1)
      have he : (|classLog K x|^n)^2 = (classLog K x)^(2*n) := by
        rw [← pow_mul, Nat.mul_comm n 2, pow_mul, sq_abs]
        simp only [← pow_mul]
      nlinarith
    have he : Real.exp (R * |classLog K x|) *
        Real.exp (-(N:ℝ) * |classLog K x|) ≤ Real.exp (-|classLog K x|) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ Real.exp (R * |classLog K x|) * |classLog K x|^n *
          (C * Real.exp (-(N:ℝ) * |classLog K x|)) :=
        mul_le_mul_of_nonneg_left (hC x) (by positivity)
      _ = C * (Real.exp (R * |classLog K x|) *
          Real.exp (-(N:ℝ) * |classLog K x|)) * |classLog K x|^n := by ring
      _ ≤ C * Real.exp (-|classLog K x|) * |classLog K x|^n := by gcongr
      _ ≤ C * (Real.exp (-|classLog K x|) * (1+(classLog K x)^(2*n))) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ C * Real.exp (-|classLog K x|))]

/-- Finite-order differentiated native integral under the original analytic
form of the two-sided theta estimate. Binding Phi to the adelic theta series
and proving that estimate for original S_0 remain explicit translation work. -/
theorem native_rapid_mellin_iteratedDeriv
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (chi : UnitaryHeckeCharacter K) (a : ℝ)
    (Phi : HeckeIdeleClasses K → ℂ) (hPhi : Continuous Phi)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, ∀ x,
      ‖Phi x‖ ≤ C * Real.exp (-(N:ℝ) * |classLog K x|)) (m : ℕ) :
    iteratedDeriv m (fun z => ∫ x,
      SpectralRound11B.genuineMellinJet K chi z a 0 x * Phi x ∂mu) =
      (fun z => ∫ x, SpectralRound11B.genuineMellinJet K chi z a m x * Phi x ∂mu) := by
  exact ConditionalA878.native_mellin_iteratedDeriv K chi a Phi hPhi.aestronglyMeasurable
    (native_moments_of_two_sided_decay K mu c hc hmap Phi hPhi hdecay) m

#print axioms native_moments_of_two_sided_decay
#print axioms native_rapid_mellin_iteratedDeriv
end ConditionalA879

namespace ConditionalB880
open MasulloGRH
variable (K : Type*) [Field K] [NumberField K]

/-- The actual principal-idele series from the proof of Theorem 2.2.3.4.
For original Schwartz--Bruhat tests its convergence is Lemma 2.2.2.1;
that analytic theorem is not asserted here by use of the totalized tsum. -/
noncomputable def ideleTheta (f : HeckeAdeles K → ℂ) (x : HeckeIdeles K) : ℂ :=
  ∑' u : Kˣ, f ((principalIdele K u * x).val)

/-- Representative independence is proved by actual principal-idele reindexing,
not assumed as an arbitrary invariance field on the theta map. -/
theorem ideleTheta_principal (f : HeckeAdeles K → ℂ)
    (v : Kˣ) (x : HeckeIdeles K) :
    ideleTheta K f (principalIdele K v * x) = ideleTheta K f x := by
  have h := (Equiv.mulRight v).tsum_eq
    (fun u : Kˣ => f ((principalIdele K u * x).val))
  change (∑' u : Kˣ, f ((principalIdele K (u*v) * x).val)) = _ at h
  simpa only [ideleTheta, map_mul, mul_assoc] using h

/-- The original principal series descended to the existing arithmetic quotient.
No arbitrary quotient function, representative selector, or descent axiom is used. -/
noncomputable def classTheta (f : HeckeAdeles K → ℂ) : HeckeIdeleClasses K → ℂ :=
  Quotient.lift (ideleTheta K f) (by
    intro x y h
    have hh : x⁻¹ * y ∈ principalIdeles K :=
      QuotientGroup.eq.mp (Quotient.sound h)
    obtain ⟨u, hu⟩ := hh
    have hy : y = principalIdele K u * x := by
      rw [hu, mul_right_comm, inv_mul_cancel, one_mul]
    change ideleTheta K f x = ideleTheta K f y
    rw [hy, ideleTheta_principal])

/-- Exact original series formula, with the actual number-field embedding. -/
theorem classTheta_mk (f : HeckeAdeles K → ℂ) (x : HeckeIdeles K) :
    classTheta K f (QuotientGroup.mk x) =
      ∑' u : Kˣ, f (algebraMap K (HeckeAdeles K) (u : K) * x.val) := rfl

/-- The convergence obligation itself also does not depend on a representative.
This does not prove the Schwartz--Bruhat lattice estimate. -/
theorem theta_summable_principal_iff (f : HeckeAdeles K → ℂ)
    (v : Kˣ) (x : HeckeIdeles K) :
    Summable (fun u : Kˣ => f ((principalIdele K u * (principalIdele K v * x)).val)) ↔
      Summable (fun u : Kˣ => f ((principalIdele K u * x).val)) := by
  have h := (Equiv.mulRight v).summable_iff
    (f := fun u : Kˣ => f ((principalIdele K u * x).val))
  change Summable (fun u : Kˣ => f ((principalIdele K (u*v) * x).val)) ↔ _ at h
  simpa only [map_mul, mul_assoc] using h

#print axioms ideleTheta_principal
#print axioms classTheta_mk
#print axioms theta_summable_principal_iff
end ConditionalB880

namespace FollowupA635
open MasulloGRH Round166F Round175B ConditionalB880
variable (K : Type*) [Field K] [NumberField K]

/-- Actual logarithmic inversion, used by Poisson's change of variables. -/
theorem actual_classLog_inv (x : HeckeIdeleClasses K) :
    classLog K x⁻¹ = -classLog K x := by
  have h1 : classLog K (1 : HeckeIdeleClasses K) = 0 := by
    have h := classLog_mul K (1 : HeckeIdeleClasses K) 1
    simp only [one_mul] at h
    linarith
  have h := classLog_mul K x x⁻¹
  rw [mul_inv_cancel, h1] at h
  linarith

/-- The exact two-constraint step in the proof of Theorem 2.2.3.4(3).
The functions are the actual arithmetic theta series. The one-sided lattice
bounds and the original Poisson formula remain explicit; neither two-sided
decay nor any differentiated Mellin identity is an input. -/
theorem actual_theta_two_sided_decay
    (f fhat : HeckeAdeles K → ℂ) (hzero : f 0 = 0) (hhat_zero : fhat 0 = 0)
    (hpoisson : ∀ x : HeckeIdeleClasses K,
      classTheta K f x - (Real.exp (-classLog K x) : ℂ) * fhat 0 + f 0 =
        (Real.exp (-classLog K x) : ℂ) * classTheta K fhat x⁻¹)
    (hforward : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : HeckeIdeleClasses K,
      0 ≤ classLog K x → ‖classTheta K f x‖ ≤ C * Real.exp (-(N:ℝ) * classLog K x))
    (hdual_forward : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : HeckeIdeleClasses K,
      0 ≤ classLog K x → ‖classTheta K fhat x‖ ≤ C * Real.exp (-(N:ℝ) * classLog K x)) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ x : HeckeIdeleClasses K,
      ‖classTheta K f x‖ ≤ C * Real.exp (-(N:ℝ) * |classLog K x|) := by
  intro N
  obtain ⟨C, hC, hf⟩ := hforward N
  obtain ⟨D, hD, hh⟩ := hdual_forward (N+1)
  refine ⟨max C D, ?_⟩
  intro x
  by_cases hx : 0 ≤ classLog K x
  · rw [abs_of_nonneg hx]
    exact (hf x hx).trans (mul_le_mul_of_nonneg_right (le_max_left C D) (Real.exp_pos _).le)
  · have hx' : classLog K x ≤ 0 := le_of_not_ge hx
    have hi : 0 ≤ classLog K x⁻¹ := by rw [actual_classLog_inv]; linarith
    have hp : classTheta K f x =
        (Real.exp (-classLog K x) : ℂ) * classTheta K fhat x⁻¹ := by
      simpa only [hzero, hhat_zero, mul_zero, sub_zero, add_zero] using hpoisson x
    rw [hp, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), abs_of_nonpos hx']
    calc
      _ ≤ Real.exp (-classLog K x) *
          (D * Real.exp (-((N+1:ℕ):ℝ) * classLog K x⁻¹)) :=
        mul_le_mul_of_nonneg_left (hh x⁻¹ hi) (Real.exp_pos _).le
      _ = D * Real.exp (-(N:ℝ) * (-classLog K x)) := by
        rw [actual_classLog_inv, mul_left_comm, ← Real.exp_add]
        congr 2
        push_cast
        ring
      _ ≤ max C D * Real.exp (-(N:ℝ) * (-classLog K x)) :=
        mul_le_mul_of_nonneg_right (le_max_right C D) (Real.exp_pos _).le

#print axioms actual_classLog_inv
#print axioms actual_theta_two_sided_decay
end FollowupA635

namespace FollowupA635
open MeasureTheory MasulloGRH Round166F ConditionalB880
open SpectralRound11B
variable (K : Type*) [Field K] [NumberField K]

/-- Actual arithmetic theta specialization of the reused Mellin derivative.
It removes the independent two-sided-decay/differentiated-integral inputs;
original Poisson, one-sided Schwartz lattice estimates and theta continuity
remain explicitly upstream, and fhat must still be bound to Fourier(f). -/
theorem actual_theta_mellin_iteratedDeriv
    (mu : Measure (HeckeIdeleClasses K)) (c : ENNReal) (hc : c ≠ ⊤)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (chi : UnitaryHeckeCharacter K) (a : ℝ)
    (f fhat : HeckeAdeles K → ℂ) (hzero : f 0 = 0) (hhat_zero : fhat 0 = 0)
    (hcontinuous : Continuous (classTheta K f))
    (hpoisson : ∀ x : HeckeIdeleClasses K,
      classTheta K f x - (Real.exp (-classLog K x) : ℂ) * fhat 0 + f 0 =
        (Real.exp (-classLog K x) : ℂ) * classTheta K fhat x⁻¹)
    (hforward : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : HeckeIdeleClasses K,
      0 ≤ classLog K x → ‖classTheta K f x‖ ≤ C * Real.exp (-(N:ℝ) * classLog K x))
    (hdual_forward : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : HeckeIdeleClasses K,
      0 ≤ classLog K x → ‖classTheta K fhat x‖ ≤ C * Real.exp (-(N:ℝ) * classLog K x))
    (m : ℕ) :
    iteratedDeriv m (fun z => ∫ x,
      genuineMellinJet K chi z a 0 x * classTheta K f x ∂mu) =
      (fun z => ∫ x, genuineMellinJet K chi z a m x * classTheta K f x ∂mu) := by
  exact ConditionalA879.native_rapid_mellin_iteratedDeriv K mu c hc hmap chi a
    (classTheta K f) hcontinuous
    (actual_theta_two_sided_decay K f fhat hzero hhat_zero hpoisson hforward hdual_forward) m

#print axioms actual_theta_mellin_iteratedDeriv
end FollowupA635
