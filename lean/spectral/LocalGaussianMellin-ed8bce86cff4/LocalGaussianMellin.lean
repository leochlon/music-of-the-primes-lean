import Mathlib
/- Mellin/Gamma calculation adapted from the pinned source
S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.lean,
lines 25–81. Reused proof, newly checked in this compiler; no new novelty claimed.
The actual global completed-Hecke all-test division remains unproved. -/
open MeasureTheory Set
open scoped Real
namespace ConditionalA881
theorem integral_comp_abs_cx {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

theorem mellin_gaussian {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z
      = (2 : ℂ)⁻¹ * (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2) := by
  have h1 : (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ))
      = fun t : ℝ => (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) (t ^ (2 : ℝ)) := by
    funext t
    have hp : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t 2]
      norm_num
    rw [hp]
  have h2 := mellin_comp_rpow (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) z (2 : ℝ)
  have h3 := mellin_comp_mul_left (fun u : ℝ => (Real.exp (-u) : ℂ)) (z / 2) Real.pi_pos
  have h4 : (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ))
      = fun u : ℝ => (fun v : ℝ => (Real.exp (-v) : ℂ)) (Real.pi * u) := by
    funext u; rfl
  have h5 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    have h6 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2)
        = Complex.GammaIntegral (z / 2) := by
      rw [Complex.GammaIntegral_eq_mellin]
    rw [h6, ← Complex.Gamma_eq_integral (by simpa using hz)]
  have hcast : z / ((2 : ℝ) : ℂ) = z / 2 := by norm_num
  rw [h1, h2, hcast, h4, h3, h5]
  rw [Complex.real_smul, smul_eq_mul]
  have habs : |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [habs]
  push_cast
  ring


/-- The manuscript real Gaussian (3.4.3.3), integrated against
|x|^(z-1) dx: the local multiplicative measure is explicitly dx/|x|.
The normalization is Gamma_R(z), including the factor from both real signs. -/
theorem manuscript_real_gaussian_zeta (z : ℂ) (hz : 0 < z.re) :
    (∫ x : ℝ, (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      ((|x| : ℝ) : ℂ) ^ (z - 1)) = Complex.Gammaℝ z := by
  have he : (fun x : ℝ => (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      ((|x| : ℝ) : ℂ) ^ (z - 1)) =
      (fun x : ℝ => (fun t : ℝ => (t : ℂ) ^ (z - 1) *
        (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) |x|) := by
    funext x
    simp only [sq_abs]
    ring
  rw [he]
  change (∫ x : ℝ, (fun t : ℝ => (t : ℂ) ^ (z - 1) *
    (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) |x|) = _
  rw [integral_comp_abs_cx (f := fun t : ℝ => (t : ℂ) ^ (z - 1) *
    (Real.exp (-(Real.pi * t ^ 2)) : ℂ))]
  have hm : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (z - 1) *
      (Real.exp (-(Real.pi * x ^ 2)) : ℂ)) =
      mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z := by
    simp only [mellin, smul_eq_mul]
  rw [hm, mellin_gaussian hz, Complex.Gammaℝ_def, neg_div]
  ring

/-- The manuscript odd real Gaussian (3.4.3.4). On R^*, x/|x| is
exactly the sign character; the density |x|^(z-1) explicitly fixes dx/|x|. -/
theorem manuscript_real_odd_gaussian_zeta (z : ℂ) (hz : 0 < z.re) :
    (∫ x : ℝ, ((x : ℂ) * (Real.exp (-(Real.pi * x ^ 2)) : ℂ)) *
      ((x / |x| : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (z - 1)) =
        Complex.Gammaℝ (z + 1) := by
  have he : (∫ x : ℝ, ((x : ℂ) * (Real.exp (-(Real.pi * x ^ 2)) : ℂ)) *
      ((x / |x| : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (z - 1)) =
      (∫ x : ℝ, (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
        ((|x| : ℝ) : ℂ) ^ ((z + 1) - 1)) := by
    apply integral_congr_ae
    have hn : ∀ᵐ x : ℝ, x ≠ 0 := by
      apply ae_iff.mpr
      simp
    filter_upwards [hn] with x hx
    have hr : x * (x / |x|) = |x| := by
      rw [← mul_div_assoc]
      apply (div_eq_iff (abs_ne_zero.mpr hx)).mpr
      nlinarith [sq_abs x]
    have hc : (x : ℂ) * ((x / |x| : ℝ) : ℂ) = ((|x| : ℝ) : ℂ) := by
      exact_mod_cast hr
    have ha : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (abs_ne_zero.mpr hx)
    have hp := Complex.cpow_add (z - 1) 1 ha
    rw [Complex.cpow_one, sub_add_cancel] at hp
    rw [add_sub_cancel_right, hp]
    calc
      _ = (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
          ((x : ℂ) * ((x / |x| : ℝ) : ℂ)) * ((|x| : ℝ) : ℂ) ^ (z - 1) := by ring
      _ = _ := by rw [hc]; ring
  rw [he]
  apply manuscript_real_gaussian_zeta
  simpa using (show 0 < z.re + 1 by linarith)

#print axioms manuscript_real_odd_gaussian_zeta
#print axioms manuscript_real_gaussian_zeta
end ConditionalA881
