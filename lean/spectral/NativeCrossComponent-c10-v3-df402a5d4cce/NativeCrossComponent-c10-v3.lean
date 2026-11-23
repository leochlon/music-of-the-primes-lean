import Mathlib
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

namespace SpectralRound9B
open MasulloGRH Round166F MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The genuine complex Mellin jet divided by the native square-root weight.
This is an explicit function on actual classes, not a spectral definition. -/
noncomputable def genuineNormalizedMellinJet (χ : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K χ x : ℂ) *
    Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ) -
      ((alpha * |classLog K x| : ℝ) : ℂ)) *
    (((classLog K x)^m * (1 + (classLog K x)^2)^(-s / 4) : ℝ) : ℂ)

end SpectralRound9B


namespace SpectralRound11B
open MasulloGRH Round166F
noncomputable def genuineMellinJet
    (K : Type*) [Field K] [NumberField K] (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a : ℝ) (m : ℕ) (x : HeckeIdeleClasses K) : ℂ :=
  (classCharacter K chi x : ℂ) * Complex.exp ((z - (a : ℂ)) * (classLog K x : ℂ)) *
    ((classLog K x ^ m : ℝ) : ℂ)
end SpectralRound11B


namespace SpectralH

/-- A shifted nilpotent derivative has no kernel at a distinct exponent.
This is the algebraic isolation step for actual exponential-polynomial jets. -/
theorem nilpotent_shift_kernel
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (N : ℕ) (x : V) (hn : (D ^ N) x = 0)
    (hx : D x + c • x = 0) : x = 0 := by
  induction N generalizing x with
  | zero => simpa using hn
  | succ N ih =>
    have hDx : D x = -(c • x) := eq_neg_of_add_eq_zero_left hx
    have hn' : (D ^ N) (D x) = 0 := by
      rw [pow_succ] at hn
      exact hn
    have hzero : (D ^ N) x = 0 := by
      rw [hDx, map_neg, map_smul] at hn'
      have hz : c • (D ^ N) x = 0 := neg_eq_zero.mp hn'
      exact (smul_eq_zero.mp hz).resolve_left hc
    exact ih x hzero hx

/-- Distinct exponent shifts preserve nonzero vectors in a nilpotent jet block. -/
theorem nilpotent_shift_ne_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (D : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0)
    (N : ℕ) (x : V) (hn : (D ^ N) x = 0) (hx : x ≠ 0) :
    D x + c • x ≠ 0 := by
  intro h
  exact hx (nilpotent_shift_kernel D c hc N x hn h)

#print axioms nilpotent_shift_kernel
#print axioms nilpotent_shift_ne_zero
/-- Ordinary derivative on the polynomial block of an actual Mellin jet. -/
noncomputable def polynomialDerivative : Polynomial ℂ →ₗ[ℂ] Polynomial ℂ where
  toFun := Polynomial.derivative
  map_add' _ _ := Polynomial.derivative_add
  map_smul' c p := Polynomial.derivative_smul c p

/-- The distinct-root isolator is injective on every polynomial, with no
nilpotence assumption left for the native exponential-polynomial application. -/
theorem polynomial_shift_kernel (c : ℂ) (hc : c ≠ 0) (p : Polynomial ℂ)
    (hp : Polynomial.derivative p + c • p = 0) : p = 0 := by
  have hn : (polynomialDerivative ^ (p.natDegree + 1)) p = 0 := by
    rw [Module.End.pow_apply]
    exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self p.natDegree)
  exact nilpotent_shift_kernel polynomialDerivative c hc (p.natDegree + 1) p hn hp

theorem polynomial_shift_injective (c : ℂ) (hc : c ≠ 0) :
    Function.Injective (fun p : Polynomial ℂ => Polynomial.derivative p + c • p) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply polynomial_shift_kernel c hc
  calc
    Polynomial.derivative (p-q) + c • (p-q) =
        (Polynomial.derivative p + c • p) - (Polynomial.derivative q + c • q) := by
      simp only [map_sub, smul_sub]
      abel
    _ = 0 := sub_eq_zero.mpr hpq

#print axioms polynomial_shift_kernel
#print axioms polynomial_shift_injective
end SpectralH


namespace SpectralH904
open MasulloGRH Round166F SpectralRound9B MeasureTheory
open scoped BigOperators

theorem polynomial_real_zero (p : Polynomial ℂ)
    (h : ∀ t : ℝ, p.eval (t:ℂ) = 0) : p = 0 := by
  apply p.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective Complex.ofReal_injective).mono
  rintro x ⟨t, rfl⟩
  exact h t

theorem shifted_relation {ι : Type*} (S : Finset ι) (z : ι → ℂ)
    (p : ι → Polynomial ℂ) (w : ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) :
    ∀ t : ℝ, ∑ i ∈ S,
      (Polynomial.derivative (p i) + (z i-w) • p i).eval (t:ℂ) *
        Complex.exp (z i*(t:ℂ)) = 0 := by
  intro t
  have hd : HasDerivAt (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)))
      (∑ i ∈ S, ((Polynomial.derivative (p i)).eval (t:ℂ) +
        z i * (p i).eval (t:ℂ)) * Complex.exp (z i*(t:ℂ))) t := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hec := (Complex.hasDerivAt_exp (z i*(t:ℂ))).comp (t:ℂ)
      ((hasDerivAt_id (t:ℂ)).const_mul (z i))
    have he : HasDerivAt (fun u : ℝ => Complex.exp (z i*(u:ℂ)))
        (Complex.exp (z i*(t:ℂ)) * z i) t := by
      simpa using hec.comp_ofReal
    have hp := ((p i).hasDerivAt (t:ℂ)).comp_ofReal
    convert hp.mul he using 1
    ring
  have heq : (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ))) = fun _ => 0 := funext h
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const t (0:ℂ))
  calc
    _ = (∑ i ∈ S, ((Polynomial.derivative (p i)).eval (t:ℂ) +
        z i * (p i).eval (t:ℂ)) * Complex.exp (z i*(t:ℂ))) -
        w * (∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
      ring
    _ = 0 := by rw [hz, h t]; ring

theorem finite_polynomial_exp_independent {ι : Type*} (S : Finset ι)
    (z : ι → ℂ) (hz : Function.Injective z) (p : ι → Polynomial ℂ)
    (h : ∀ t : ℝ, ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) :
    ∀ i ∈ S, p i = 0 := by
  classical
  induction S using Finset.induction_on generalizing p with
  | empty => simp
  | @insert k S hk ih =>
    have main : ∀ n (p : ι → Polynomial ℂ),
        (Polynomial.derivative^[n]) (p k) = 0 →
        (∀ t : ℝ, ∑ i ∈ insert k S,
          (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0) →
        ∀ i ∈ insert k S, p i = 0 := by
      intro n
      induction n with
      | zero =>
        intro p hn hp
        have hpk : p k = 0 := hn
        have hs : ∀ t : ℝ, ∑ i ∈ S,
            (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0 := by
          intro t
          simpa [Finset.sum_insert hk, hpk] using hp t
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpk
        · exact ih p hs i hi
      | succ n ihn =>
        intro p hn hp
        let q : ι → Polynomial ℂ := fun i =>
          Polynomial.derivative (p i) + (z i-z k) • p i
        have hqk : q k = Polynomial.derivative (p k) := by simp [q]
        have hqn : (Polynomial.derivative^[n]) (q k) = 0 := by
          rw [hqk]
          simpa only [Function.iterate_succ_apply] using hn
        have hq := ihn q hqn (shifted_relation (insert k S) z p (z k) hp)
        have hs : ∀ i ∈ S, p i = 0 := by
          intro i hi
          apply SpectralH.polynomial_shift_kernel (z i-z k)
            (sub_ne_zero.mpr (fun he => hk (hz he ▸ hi)))
          exact hq i (Finset.mem_insert_of_mem hi)
        have hpk : p k = 0 := by
          apply polynomial_real_zero
          intro t
          have hh := hp t
          rw [Finset.sum_insert hk] at hh
          have hsum : ∑ i ∈ S, (p i).eval (t:ℂ) * Complex.exp (z i*(t:ℂ)) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            simp [hs i hi]
          rw [hsum, add_zero] at hh
          exact (mul_eq_zero.mp hh).resolve_right (Complex.exp_ne_zero _)
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hpk
        · exact hs i hi
    exact main ((p k).natDegree+1) p
      (Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)) h

/-- Finite mixed higher-jet blocks in one genuine Hecke component, expressed
by their coefficient polynomials, are independent in the ORIGINAL weighted
realization modulo the SAME quotient measure. No independence is assumed. -/
theorem native_polynomial_blocks_independent {ι : Type*}
    (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (hz : Function.Injective z) (a s alpha : ℝ)
    (S : Finset ι) (p : ι → Polynomial ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) *
        genuineNormalizedMellinJet K chi (z i) a s alpha 0 x = 0) :
    ∀ i ∈ S, p i = 0 := by
  classical
  let W : HeckeIdeleClasses K → ℂ := fun x =>
    (classCharacter K chi x : ℂ) * Complex.exp (-((alpha * |classLog K x| : ℝ):ℂ)) *
      (((1 + (classLog K x)^2)^(-s/4) : ℝ):ℂ)
  have hW (x) : W x ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (Circle.coe_ne_zero _) (Complex.exp_ne_zero _))
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)))
  have hf (i) (x) : genuineNormalizedMellinJet K chi (z i) a s alpha 0 x =
      W x * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) := by
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul, sub_eq_add_neg,
      Complex.exp_add]
    dsimp [W]
    ring
  have hr : ∀ᵐ x ∂mu, ∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ)) = 0 := by
    filter_upwards [h] with x hx
    apply (mul_eq_zero.mp (show W x * (∑ i ∈ S,
      (p i).eval (classLog K x:ℂ) * Complex.exp ((z i-(a:ℂ))*(classLog K x:ℂ))) = 0 from ?_)).resolve_left (hW x)
    rw [Finset.mul_sum]
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hf]
    ring
  have hcont : Continuous (fun t : ℝ => ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp ((z i-(a:ℂ))*(t:ℂ))) := by fun_prop
  have hm := (ae_map_iff (Round175B.classLog_continuous K).measurable.aemeasurable
    (isClosed_eq hcont continuous_const).measurableSet).mpr hr
  rw [hmap] at hm
  have hm0 : ∀ᵐ t : ℝ ∂volume, ∑ i ∈ S,
      (p i).eval (t:ℂ) * Complex.exp ((z i-(a:ℂ))*(t:ℂ)) = 0 := by
    simpa only [ae_iff, Measure.smul_apply, smul_eq_mul, mul_eq_zero, hc, false_or] using hm
  have hall := (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hm0
  have hz' : Function.Injective (fun i => z i-(a:ℂ)) := by
    intro i j he
    apply hz
    linear_combination he
  exact finite_polynomial_exp_independent S (fun i => z i-(a:ℂ)) hz' p (congrFun hall)

#print axioms native_polynomial_blocks_independent
end SpectralH904

/- Reused spectral_B selected coefficient extraction and L2 transfer. -/
namespace SpectralCycle9B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped BigOperators

/-- Independence of arbitrary finite selections of distinct exponent/order pairs. -/
theorem native_selected_finite_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (m : ι → ℕ) (hz : Function.Injective (fun i => (z i, m i)))
    (a s alpha : ℝ) (S : Finset ι) (b : ι → ℂ)
    (h : ∀ᵐ x ∂mu, ∑ i ∈ S,
      b i * genuineNormalizedMellinJet K chi (z i) a s alpha (m i) x = 0) :
    ∀ i ∈ S, b i = 0 := by
  classical
  let p : ℂ → Polynomial ℂ := fun w => ∑ j ∈ S,
    if z j = w then Polynomial.monomial (m j) (b j) else 0
  have hf (i) (x) :
      b i * genuineNormalizedMellinJet K chi (z i) a s alpha (m i) x =
      (b i * (classLog K x:ℂ)^(m i)) *
        genuineNormalizedMellinJet K chi (z i) a s alpha 0 x := by
    simp only [genuineNormalizedMellinJet, pow_zero, one_mul,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  have hp : ∀ᵐ x ∂mu, ∑ w ∈ S.image z,
      (p w).eval (classLog K x:ℂ) *
        genuineNormalizedMellinJet K chi w a s alpha 0 x = 0 := by
    filter_upwards [h] with x hx
    convert hx using 1
    simp only [p, Polynomial.eval_finset_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_eq_single (z j)]
    · simpa using (hf j x).symm
    · intro w hw hne
      simp [Ne.symm hne]
    · intro hn
      exact False.elim (hn (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
  have hp0 := SpectralH904.native_polynomial_blocks_independent
    K chi mu c hc hmap id Function.injective_id a s alpha (S.image z) p hp
  intro i hi
  have he := congrArg (fun q : Polynomial ℂ => q.coeff (m i))
    (hp0 (z i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hcoef : (p (z i)).coeff (m i) = b i := by
    simp only [p, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      by_cases hzj : z j = z i
      · have hmj : m j ≠ m i := fun hh => hji (hz (Prod.ext hzj hh))
        simp [hzj, Polynomial.coeff_monomial, hmj]
      · simp [hzj]
    · exact fun hn => False.elim (hn hi)
  simpa only [hcoef, Polynomial.coeff_zero] using he

#print axioms native_selected_finite_independent
end SpectralCycle9B

namespace SpectralCycle9B
open MeasureTheory MasulloGRH Round166F SpectralRound9B
open scoped BigOperators
/-- Independence of the actual conjugated L2 vectors used by native Gram–Schmidt,
for all distinct admitted exponent/order labels in one fixed character component. -/
theorem native_selected_L2_independent
    {ι : Type*} (K : Type*) [Field K] [NumberField K]
    (chi : UnitaryHeckeCharacter K) (mu : Measure (HeckeIdeleClasses K))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (z : ι → ℂ) (m : ι → ℕ) (hz : Function.Injective (fun i => (z i, m i))) (a s alpha : ℝ)
    (hg : ∀ i, MemLp (genuineNormalizedMellinJet K chi (z i) a s alpha (m i)) 2 mu) :
    LinearIndependent ℂ (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K chi (z i) a s alpha (m i)))) := by
  classical
  let J := fun i => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K chi (z i) a s alpha (m i)))
  apply linearIndependent_iff'.mpr
  intro S b hsum
  have he (T : Finset ι) :
      (fun x => (∑ i ∈ T, b i • J i) x) =ᵐ[mu]
        (fun x => ∑ i ∈ T, b i * star (genuineNormalizedMellinJet K chi (z i) a s alpha (m i) x)) := by
    induction T using Finset.induction_on with
    | empty => simpa using (Lp.coeFn_zero ℂ 2 mu)
    | @insert i T hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (b i • J i) (∑ j ∈ T, b j • J j),
        Lp.coeFn_smul (b i) (J i), (hg i).star.coeFn_toLp, ih] with x hx hs hj ht
      change J i x = star (genuineNormalizedMellinJet K chi (z i) a s alpha (m i) x) at hj
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hs, hj, ht] using hx
  have hzsum : ∀ᵐ x ∂mu, ∑ i ∈ S,
      star (b i) * genuineNormalizedMellinJet K chi (z i) a s alpha (m i) x = 0 := by
    have hz0 := Lp.coeFn_zero ℂ 2 mu
    have hh := he S
    change (∑ i ∈ S, b i • J i) = 0 at hsum
    rw [hsum] at hh
    filter_upwards [hh, hz0] with x hx hx0
    have hh' := congrArg star (hx.symm.trans hx0)
    simpa only [star_sum, star_mul, star_star, Pi.zero_apply, star_zero, mul_comm] using hh'
  have hb := native_selected_finite_independent K chi mu c hc hmap z m hz a s alpha S
    (fun i => star (b i)) hzsum
  intro i hi
  exact star_eq_zero.mp (hb i hi)

#print axioms native_selected_L2_independent
end SpectralCycle9B
/- Reused followup_B cycle 9 orthogonality; not new credit. -/
namespace Spectral34B
open MasulloGRH Round166F Round175B SpectralRound9B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- Reused FollowupD31.classCharacter_mul, on the original arithmetic quotient. -/
theorem classCharacter_mul (chi : UnitaryHeckeCharacter K)
    (g x : HeckeIdeleClasses K) :
    classCharacter K chi (g*x) = classCharacter K chi g * classCharacter K chi x := by
  refine Quotient.inductionOn₂ g x ?_
  intro a b
  exact map_mul chi.character a b

/-- The actual original weight is invariant under the norm-one subgroup. -/
theorem normalizedJet_norm_one_translate (chi : UnitaryHeckeCharacter K)
    (z : ℂ) (a s alpha : ℝ) (m : ℕ) (g x : HeckeIdeleClasses K)
    (hg : classLog K g = 0) :
    genuineNormalizedMellinJet K chi z a s alpha m (g*x) =
      (classCharacter K chi g : ℂ) * genuineNormalizedMellinJet K chi z a s alpha m x := by
  simp only [genuineNormalizedMellinJet, classCharacter_mul, Circle.coe_mul,
    classLog_mul, hg, zero_add]
  ring

/-- Actual cross-component orthogonality, manuscript paragraph immediately
before (10.3.1.16), for all orders and original normalized weights.
The distinct compact restrictions are witnessed by a norm-one class g. -/
theorem native_cross_component_integral_zero
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi psi : UnitaryHeckeCharacter K) (z w : ℂ) (a s alpha : ℝ) (m n : ℕ)
    (g : HeckeIdeleClasses K) (hg : classLog K g = 0)
    (hd : (star (classCharacter K chi g : ℂ)) * (classCharacter K psi g : ℂ) ≠ 1) :
    (∫ x, star (genuineNormalizedMellinJet K chi z a s alpha m x) *
      genuineNormalizedMellinJet K psi w a s alpha n x ∂mu) = 0 := by
  let F := fun x => star (genuineNormalizedMellinJet K chi z a s alpha m x) *
    genuineNormalizedMellinJet K psi w a s alpha n x
  have he := integral_mul_left_eq_self (μ := mu) F g
  have hx (x : HeckeIdeleClasses K) : F (g*x) =
      (star (classCharacter K chi g : ℂ) * (classCharacter K psi g : ℂ)) * F x := by
    dsimp [F]
    rw [normalizedJet_norm_one_translate K chi z a s alpha m g x hg,
      normalizedJet_norm_one_translate K psi w a s alpha n g x hg, map_mul]
    ring
  simp_rw [hx] at he
  rw [integral_const_mul] at he
  have hz : ((star (classCharacter K chi g : ℂ) * (classCharacter K psi g : ℂ))-1) *
      (∫ x, F x ∂mu) = 0 := by rw [sub_mul, he, one_mul, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hd)

#print axioms normalizedJet_norm_one_translate
#print axioms native_cross_component_integral_zero
end Spectral34B

namespace Spectral35B
open MasulloGRH Round166F SpectralRound9B MeasureTheory
variable (K : Type*) [Field K] [NumberField K]

/-- The manuscript's compact-character label, on the actual norm-one classes. -/
noncomputable def compactRestriction (chi : UnitaryHeckeCharacter K) :
    {g : HeckeIdeleClasses K // classLog K g = 0} → Circle :=
  fun g => classCharacter K chi g

/-- Distinct actual compact restrictions supply the separating class needed
by Haar orthogonality; neither a witness nor orthogonality is an assumption. -/
theorem native_distinct_component_integral_zero
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi psi : UnitaryHeckeCharacter K)
    (hd : compactRestriction K chi ≠ compactRestriction K psi)
    (z w : ℂ) (a s alpha : ℝ) (m n : ℕ) :
    (∫ x, star (genuineNormalizedMellinJet K chi z a s alpha m x) *
      genuineNormalizedMellinJet K psi w a s alpha n x ∂mu) = 0 := by
  classical
  obtain ⟨g, hg⟩ := Function.ne_iff.mp hd
  apply Spectral34B.native_cross_component_integral_zero K mu chi psi z w a s alpha m n
    g.val g.property
  intro he
  apply hg
  apply Subtype.ext
  have hu : star (classCharacter K chi g.val : ℂ) *
      (classCharacter K chi g.val : ℂ) = 1 := by
    change (starRingEnd ℂ) _ * _ = _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    norm_num
  have hn : star (classCharacter K chi g.val : ℂ) ≠ 0 := by
    exact star_ne_zero.mpr (Circle.coe_ne_zero _)
  exact (mul_left_cancel₀ hn (he.trans hu.symm)).symm

/-- Cross-component orthogonality of the ACTUAL conjugated Riesz vectors in
the original half-weight L2 realization, for every admitted pair of orders. -/
theorem native_distinct_component_riesz_orthogonal
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi psi : UnitaryHeckeCharacter K)
    (hd : compactRestriction K chi ≠ compactRestriction K psi)
    (z w : ℂ) (a s alpha : ℝ) (m n : ℕ)
    (hf : MemLp (genuineNormalizedMellinJet K chi z a s alpha m) 2 mu)
    (hg : MemLp (genuineNormalizedMellinJet K psi w a s alpha n) 2 mu) :
    inner ℂ (hf.star.toLp (star (genuineNormalizedMellinJet K chi z a s alpha m)))
      (hg.star.toLp (star (genuineNormalizedMellinJet K psi w a s alpha n))) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, star (genuineNormalizedMellinJet K psi w a s alpha n x) *
        genuineNormalizedMellinJet K chi z a s alpha m x ∂mu := by
      apply integral_congr_ae
      filter_upwards [hf.star.coeFn_toLp, hg.star.coeFn_toLp] with x hx hy
      rw [hx, hy]
      simp [RCLike.inner_apply]
    _ = 0 := native_distinct_component_integral_zero K mu psi chi
      (Ne.symm hd) w z a s alpha n m

#print axioms native_distinct_component_integral_zero
#print axioms native_distinct_component_riesz_orthogonal
end Spectral35B

namespace Spectral36B
open MeasureTheory MasulloGRH Round166F SpectralRound9B Spectral35B
open scoped BigOperators

/-- The full original-weight native Riesz family is independent across all
compact-character components and all injective exponent/order labels.
This joins the two checked component results at (10.3.1.16). -/
theorem native_cross_component_L2_independent
    {ι κ : Type*} (K : Type*) [Field K] [NumberField K]
    [MeasurableMul (HeckeIdeleClasses K)]
    (mu : Measure (HeckeIdeleClasses K)) [mu.IsMulLeftInvariant]
    (chi : κ → UnitaryHeckeCharacter K)
    (hchi : Function.Injective (fun k => compactRestriction K (chi k)))
    (component : ι → κ) (z : ι → ℂ) (m : ι → ℕ)
    (hlabel : Function.Injective (fun i => (component i, z i, m i)))
    (c : ENNReal) (hc : c ≠ 0)
    (hmap : Measure.map (classLog K) mu = c • volume)
    (a s alpha : ℝ)
    (hg : ∀ i, MemLp
      (genuineNormalizedMellinJet K (chi (component i)) (z i) a s alpha (m i)) 2 mu) :
    LinearIndependent ℂ (fun i => (hg i).star.toLp
      (star (genuineNormalizedMellinJet K (chi (component i)) (z i) a s alpha (m i)))) := by
  classical
  let J : ι → Lp ℂ 2 mu := fun i => (hg i).star.toLp
    (star (genuineNormalizedMellinJet K (chi (component i)) (z i) a s alpha (m i)))
  have ho (i j : ι) (hij : component i ≠ component j) : inner ℂ (J i) (J j) = 0 :=
    native_distinct_component_riesz_orthogonal K mu (chi (component i))
      (chi (component j)) (fun he => hij (hchi he))
      (z i) (z j) a s alpha (m i) (m j) (hg i) (hg j)
  change LinearIndependent ℂ J
  apply linearIndependent_iff'.mpr
  intro S b hsum i hi
  let T := S.filter (fun j => component j = component i)
  have hTS : T ⊆ S := Finset.filter_subset _ _
  have hiT : i ∈ T := Finset.mem_filter.mpr ⟨hi, rfl⟩
  let v : Lp ℂ 2 mu := ∑ j ∈ T, b j • J j
  have hv : v = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    have he : inner ℂ v (∑ j ∈ S, b j • J j) = inner ℂ v v := by
      rw [inner_sum]
      change _ = inner ℂ v (∑ j ∈ T, b j • J j)
      rw [inner_sum]
      symm
      apply Finset.sum_subset hTS
      intro j hj hjT
      rw [inner_smul_right]
      have hjc : component j ≠ component i := by
        intro hh
        exact hjT (Finset.mem_filter.mpr ⟨hj, hh⟩)
      have hzero : inner ℂ v (J j) = 0 := by
        dsimp [v]
        rw [sum_inner]
        apply Finset.sum_eq_zero
        intro k hk
        rw [inner_smul_left, ho k j]
        · simp
        · exact fun hh => hjc (hh.symm.trans (Finset.mem_filter.mp hk).2)
      rw [hzero, mul_zero]
    rw [hsum, inner_zero_right] at he
    exact he.symm
  have hcomp (j : T) : component j = component i := (Finset.mem_filter.mp j.property).2
  let hgT : ∀ j : T, MemLp
      (genuineNormalizedMellinJet K (chi (component i)) (z j) a s alpha (m j)) 2 mu := by
    intro j
    simpa only [hcomp j] using hg j
  have hinj : Function.Injective (fun j : T => (z j, m j)) := by
    intro j k hjk
    apply Subtype.ext
    apply hlabel
    exact Prod.ext ((hcomp j).trans (hcomp k).symm) hjk
  have hlocal : LinearIndependent ℂ (fun j : T => J j) := by
    have hh := SpectralCycle9B.native_selected_L2_independent K (chi (component i))
      mu c hc hmap (fun j : T => z j) (fun j : T => m j) hinj a s alpha hgT
    have heq : (fun j : T => J j) = (fun j : T => (hgT j).star.toLp
        (star (genuineNormalizedMellinJet K (chi (component i)) (z j) a s alpha (m j)))) := by
      funext j
      dsimp [J]
      simp only [hcomp j]
    rw [heq]
    exact hh
  have hzsum : ∑ j : T, b j • J j = 0 := by
    exact (Finset.sum_coe_sort T (fun j => b j • J j)).trans hv
  exact (linearIndependent_iff'.mp hlocal Finset.univ (fun j : T => b j)
    hzsum ⟨i, hiT⟩ (Finset.mem_univ _))

#print axioms native_cross_component_L2_independent
end Spectral36B
