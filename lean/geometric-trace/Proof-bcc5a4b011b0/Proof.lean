import Mathlib

open scoped NumberField
namespace GeometricC

abbrev Ideles (K : Type*) [Field K] [NumberField K] :=
  (NumberField.AdeleRing (𝓞 K) K)ˣ
noncomputable def principal (K : Type*) [Field K] [NumberField K] : Kˣ →* Ideles K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom
abbrev Classes (K : Type*) [Field K] [NumberField K] :=
  Ideles K ⧸ (principal K).range


noncomputable def skewIdele (K : Type*) [Field K] [NumberField K]
    (p : Ideles K × Kˣ) : Ideles K := (principal K p.2)⁻¹ * p.1

theorem principal_skew_class (K : Type*) [Field K] [NumberField K]
    (x : Ideles K) (h : Kˣ) :
    (QuotientGroup.mk (skewIdele K (x,h)) : Classes K) = QuotientGroup.mk x := by
  apply QuotientGroup.eq.mpr
  refine ⟨h, ?_⟩
  simp [skewIdele, mul_inv_rev, mul_comm]

end GeometricC

namespace GeometricC
open Filter Topology
noncomputable section

/-- The specific quotient-factorized test lift proposed to repair the per-unit
mass step in (12.4.1.20--24). This uses actual ideles and the principal quotient;
restriction/descent to the S-local quotient is still a separate bridge. -/
def quotientTestLift (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (φ : Classes K → ℂ) (x : Ideles K) : ℂ :=
  (u0 x : ℂ) * φ (QuotientGroup.mk x)

/-- Discharges the periodization premise of (12.4.1.4) for this chosen lift.
Only normalized indentation is supplied; summability of the test lift follows. -/
theorem quotientTestLift_periodizes (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (φ : Classes K → ℂ)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (x : Ideles K) :
    HasSum (fun h : Kˣ => quotientTestLift K u0 φ (skewIdele K (x,h)))
      (φ (QuotientGroup.mk x)) := by
  have H := (hpart x).smul_const (φ (QuotientGroup.mk x))
  simpa [quotientTestLift, principal_skew_class, Complex.real_smul] using H

/-- Discharges the algebraic termwise zero-mass premise for the chosen lift:
all principal values vanish, hence in particular all S-unit values vanish.
The target restriction φ(C_K^1)=0 implies the ONLY consequence used here,
φ(1)=0. This does not extend the trace formula to tests satisfying only φ(1)=0.
Fourier inversion and S-local descent remain explicit missing attachments. -/
theorem quotientTestLift_principal_zero (K : Type*) [Field K] [NumberField K]
    (u0 : Ideles K → ℝ) (φ : Classes K → ℂ)
    (hφ : φ (QuotientGroup.mk (1 : Ideles K)) = 0) (ξ : Kˣ) :
    quotientTestLift K u0 φ (principal K ξ) = 0 := by
  have hc := principal_skew_class K (1 : Ideles K) ξ⁻¹
  simp only [skewIdele, map_inv, inv_inv, mul_one] at hc
  rw [quotientTestLift, hc, hφ, mul_zero]

/-- Discharges the compact-support premise for the chosen lift in (12.4.1.4),
from a precise proper-support condition on the indentation over compact sets
of the actual idele quotient. Construction of such a smooth indentation is
NOT assumed proved. No operator, Fourier transform or trace is replaced. -/
theorem quotientTestLift_hasCompactSupport
    (K : Type*) [Field K] [NumberField K] [T2Space (Ideles K)]
    (u0 : Ideles K → ℝ) (φ : Classes K → ℂ)
    (hφ : HasCompactSupport φ)
    (hproper : ∀ Q : Set (Classes K), IsCompact Q →
      IsCompact (tsupport u0 ∩ (QuotientGroup.mk : Ideles K → Classes K) ⁻¹' Q)) :
    HasCompactSupport (quotientTestLift K u0 φ) := by
  have hc := hproper (tsupport φ) hφ
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro x hx
  have hprod : (u0 x : ℂ) * φ (QuotientGroup.mk x) ≠ 0 := hx
  have hu : u0 x ≠ 0 := by
    intro h
    apply hprod
    simp [h]
  have hp : φ (QuotientGroup.mk x) ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  exact ⟨subset_closure hu, subset_closure hp⟩

#check GeometricC.quotientTestLift_periodizes
#print axioms GeometricC.quotientTestLift_periodizes
#check GeometricC.quotientTestLift_principal_zero
#print axioms GeometricC.quotientTestLift_principal_zero
#check GeometricC.quotientTestLift_hasCompactSupport
#print axioms GeometricC.quotientTestLift_hasCompactSupport
end
end GeometricC

namespace GeometricC
open Filter Topology
noncomputable section
/-- The actual S-ideles, needed to restrict the lift in (12.4.1.4).
S lists finite places; all infinite coordinates are unrestricted. -/
def sIdeleGroup (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Subgroup (Ideles K) where
  carrier := {x | ∀ v, v ∉ S → Valued.v (x.val.2 v) = 1}
  one_mem' := by
    intro v hv
    change Valued.v (1 : v.adicCompletion K) = 1
    exact map_one _
  mul_mem' := by
    intro a b ha hb v hv
    change Valued.v (a.val.2 v * b.val.2 v) = 1
    rw [map_mul, ha v hv, hb v hv, one_mul]
  inv_mem' := by
    intro a ha v hv
    have hh : a.val.2 v * (a⁻¹).val.2 v = 1 := by
      have h := congrArg (fun x : Ideles K => x.val.2 v) (mul_inv_cancel a)
      exact h
    have h := congrArg Valued.v hh
    simpa only [map_mul, ha v hv, map_one, one_mul] using h

/-- Genuine principal S-units, as the inverse image of the S-idele subgroup.
No class-number or S-local quotient identification is silently assumed. -/
def sUnitGroup (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  (sIdeleGroup K S).comap (principal K)

/-- Discharges the support restriction needed before replacing the global
principal sum by the S-unit sum in (12.4.1.4). -/
theorem lift_zero_outside_sUnits (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (u0 : Ideles K → ℝ) (φ : Classes K → ℂ)
    (hu : ∀ x, x ∉ sIdeleGroup K S → u0 x = 0)
    (x : Ideles K) (hx : x ∈ sIdeleGroup K S)
    (h : Kˣ) (hh : h ∉ sUnitGroup K S) :
    quotientTestLift K u0 φ (skewIdele K (x,h)) = 0 := by
  have hz : skewIdele K (x,h) ∉ sIdeleGroup K S := by
    intro hz
    apply hh
    change principal K h ∈ sIdeleGroup K S
    have hm := (sIdeleGroup K S).mul_mem hx ((sIdeleGroup K S).inv_mem hz)
    simpa [skewIdele, mul_inv_rev, mul_assoc] using hm
  simp [quotientTestLift, hu _ hz]

#check GeometricC.lift_zero_outside_sUnits
#print axioms GeometricC.lift_zero_outside_sUnits
end
end GeometricC

namespace GeometricC
open Filter Topology
noncomputable section
/-- Discharges the actual S-unit periodization premise of (12.4.1.4):
normalized global indentation supported on S-ideles yields a summable
periodization over genuine S-units. No infinite sum/limit is exchanged. -/
theorem quotientTestLift_sUnit_periodizes
    (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (u0 : Ideles K → ℝ) (φ : Classes K → ℂ)
    (hu : ∀ x, x ∉ sIdeleGroup K S → u0 x = 0)
    (hpart : ∀ x, HasSum (fun h : Kˣ => u0 (skewIdele K (x,h))) 1)
    (x : Ideles K) (hx : x ∈ sIdeleGroup K S) :
    HasSum (fun h : sUnitGroup K S =>
      quotientTestLift K u0 φ (skewIdele K (x,h.val))) (φ (QuotientGroup.mk x)) := by
  have hs : Function.support (fun h : Kˣ =>
      quotientTestLift K u0 φ (skewIdele K (x,h))) ⊆ (sUnitGroup K S : Set Kˣ) := by
    intro h hh
    by_contra hn
    exact hh (lift_zero_outside_sUnits K S u0 φ hu x hx h hn)
  exact (hasSum_subtype_iff_of_support_subset hs).2
    (quotientTestLift_periodizes K u0 φ hpart x)

#check GeometricC.quotientTestLift_sUnit_periodizes
#print axioms GeometricC.quotientTestLift_sUnit_periodizes
end
end GeometricC

namespace GeometricC
noncomputable section
/-- Principal inclusion of the genuine S-units into genuine S-ideles. -/
def sPrincipal (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    sUnitGroup K S →* sIdeleGroup K S where
  toFun h := ⟨principal K h.val, h.property⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_mul' a b := by apply Subtype.ext; exact map_mul _ _ _

/-- Discharges injectivity of the S-idele/S-unit quotient into the actual
idele class group, an algebraic part of the quotient identification before
(12.4.1.4). Surjectivity, topology, Haar transport, and the further quotient
by outside-S local units are not claimed. -/
theorem sClass_eq_iff_class_eq (K : Type*) [Field K] [NumberField K]
    (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (x y : sIdeleGroup K S) :
    (QuotientGroup.mk x : sIdeleGroup K S ⧸ (sPrincipal K S).range) =
      QuotientGroup.mk y ↔
    (QuotientGroup.mk x.val : Classes K) = QuotientGroup.mk y.val := by
  rw [QuotientGroup.eq, QuotientGroup.eq]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.val, congrArg Subtype.val hh⟩
  · rintro ⟨h, hh⟩
    have hs : h ∈ sUnitGroup K S := by
      change principal K h ∈ sIdeleGroup K S
      rw [hh]
      exact (sIdeleGroup K S).mul_mem ((sIdeleGroup K S).inv_mem x.property) y.property
    refine ⟨⟨h, hs⟩, ?_⟩
    apply Subtype.ext
    exact hh

#check GeometricC.sClass_eq_iff_class_eq
#print axioms GeometricC.sClass_eq_iff_class_eq
end
end GeometricC
