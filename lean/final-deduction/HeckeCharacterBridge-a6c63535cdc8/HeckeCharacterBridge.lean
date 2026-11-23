import Mathlib

/- The genuine arithmetic definitions below are excerpts of the frozen
F53 seed and alpo's IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean and
TateThesis/HeckeChar.lean. This minimal file certifies their character bridge;
it does not recompile or claim their analytic continuation theorems.
The source adelic notation is expanded to its Mathlib type for compatibility. -/
open scoped NumberField NumberField.AdeleRing

namespace MasulloGRH
variable (K : Type*) [Field K] [NumberField K]
abbrev HeckeAdeles := NumberField.AdeleRing (𝓞 K) K
abbrev HeckeIdeles := (HeckeAdeles K)ˣ
noncomputable def principalIdele : Kˣ →* HeckeIdeles K :=
  Units.map (algebraMap K (HeckeAdeles K)).toMonoidHom
noncomputable def principalIdeles : Subgroup (HeckeIdeles K) :=
  (principalIdele K).range
abbrev HeckeIdeleClasses := HeckeIdeles K ⧸ principalIdeles K
structure UnitaryHeckeCharacter where
  character : ContinuousMonoidHom (HeckeIdeles K) Circle
  trivial_on_principal : ∀ a : Kˣ, character (principalIdele K a) = 1
end MasulloGRH

namespace GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
abbrev IdeleGroup : Type _ := (NumberField.AdeleRing (𝓞 K) K)ˣ
namespace IdeleGroup
def diagonal : Kˣ →* IdeleGroup K :=
  Units.map (algebraMap K (NumberField.AdeleRing (𝓞 K) K)).toMonoidHom
end IdeleGroup
abbrev IdeleClassGroup : Type _ := IdeleGroup K ⧸ (IdeleGroup.diagonal K).range
namespace IdeleClassGroup
def mk : IdeleGroup K →* IdeleClassGroup K := QuotientGroup.mk' _
end IdeleClassGroup
abbrev HeckeCharacter : Type _ := IdeleClassGroup K →ₜ* Circle
namespace HeckeCharacter
variable {K} (χ : HeckeCharacter K)
def toIdele : IdeleGroup K →* Circle :=
  (χ : IdeleClassGroup K →* Circle).comp (IdeleClassGroup.mk K)
end HeckeCharacter
end
end GroundTheory.Global

namespace MasulloGRH
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem principalIdele_eq_ground_diagonal :
    principalIdele K = GroundTheory.Global.IdeleGroup.diagonal K := rfl

/-- Descend the ACTUAL continuous idelic character through principal ideles. -/
def UnitaryHeckeCharacter.toGround (χ : UnitaryHeckeCharacter K) :
    GroundTheory.Global.HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift _ χ.character.toMonoidHom (by
    rintro x ⟨a, rfl⟩
    exact χ.trivial_on_principal a)
  continuous_toFun := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
    exact χ.character.continuous

/-- Pull back the quotient character along the genuine quotient projection. -/
def UnitaryHeckeCharacter.ofGround (χ : GroundTheory.Global.HeckeCharacter K) :
    UnitaryHeckeCharacter K where
  character :=
    { toMonoidHom := χ.toIdele
      continuous_toFun := χ.continuous.comp QuotientGroup.continuous_mk }
  trivial_on_principal := by
    intro a
    change χ (GroundTheory.Global.IdeleClassGroup.mk K (principalIdele K a)) = 1
    have h : GroundTheory.Global.IdeleClassGroup.mk K (principalIdele K a) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨a, rfl⟩
    rw [h, map_one]

@[simp] theorem UnitaryHeckeCharacter.toGround_toIdele
    (χ : UnitaryHeckeCharacter K) (x : HeckeIdeles K) :
    (χ.toGround K).toIdele x = χ.character x := rfl

@[simp] theorem UnitaryHeckeCharacter.ofGround_toGround
    (χ : UnitaryHeckeCharacter K) :
    UnitaryHeckeCharacter.ofGround K (χ.toGround K) = χ := by
  cases χ
  rfl

@[simp] theorem UnitaryHeckeCharacter.toGround_ofGround
    (χ : GroundTheory.Global.HeckeCharacter K) :
    (UnitaryHeckeCharacter.ofGround K χ).toGround K = χ := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    (GroundTheory.Global.IdeleGroup.diagonal K).range x
  rfl

/-- Every genuine unitary character is covered, with no norm-twist restriction. -/
def unitaryHeckeCharacterEquiv :
    UnitaryHeckeCharacter K ≃ GroundTheory.Global.HeckeCharacter K where
  toFun := UnitaryHeckeCharacter.toGround K
  invFun := UnitaryHeckeCharacter.ofGround K
  left_inv := UnitaryHeckeCharacter.ofGround_toGround K
  right_inv := UnitaryHeckeCharacter.toGround_ofGround K

/-- The bridge preserves all actual local restrictions, hence uniformizer values. -/
theorem unitaryHeckeCharacterEquiv_local_values
    (χ : UnitaryHeckeCharacter K) {A : Type*} (localEmbedding : A → HeckeIdeles K) :
    (fun a => ((unitaryHeckeCharacterEquiv K χ).toIdele (localEmbedding a) : ℂ)) =
      fun a => (χ.character (localEmbedding a) : ℂ) := rfl

#print axioms unitaryHeckeCharacterEquiv
#print axioms unitaryHeckeCharacterEquiv_local_values
#print axioms UnitaryHeckeCharacter.toGround
#print axioms UnitaryHeckeCharacter.ofGround
end
end MasulloGRH
