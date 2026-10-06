module

public import GS.NonmanifoldFinal.SphereCoordinates
public import GS.NonmanifoldObstruction.PuncturedNeighbourhood

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Transport the existing sphere retract to all finite column sets

The d+2 convention of the old section is eliminated by an explicit equivalence.
The resulting retract has a genuine Fin-indexed Euclidean sphere as its source.
-/
noncomputable section
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {A A' B B' X Y : Type*}
  [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace B]
  [TopologicalSpace B'] [TopologicalSpace X] [TopologicalSpace Y]

/-- Transport BOTH maps, including the left-inverse identity. -/
def transportSectionPair (p : ContinuousSectionPair A B)
    (hA : A' ≃ₜ A) (hB : B ≃ₜ B') : ContinuousSectionPair A' B' where
  sectionMap a := hB (p.sectionMap (hA a))
  retractionMap b := hA.symm (p.retractionMap (hB.symm b))
  section_continuous := hB.continuous.comp (p.section_continuous.comp hA.continuous)
  retraction_continuous := hA.symm.continuous.comp
    (p.retraction_continuous.comp hB.symm.continuous)
  retraction_section a := by simp only [Homeomorph.symm_apply_apply,
    p.retraction_section]

/-- Remove a SINGLE marked point from an open subset. -/
abbrev PuncturedIn (U : Set X) (x : X) := {p : X // p ∈ U ∧ p ≠ x}

def puncturedImage (h : X ≃ₜ Y) (U : Set X) (x : X) :
    PuncturedIn U x ≃ₜ PuncturedIn (h '' U) (h x) where
  toFun p := ⟨h p.val,⟨p.val,p.property.1,rfl⟩,
    fun he => p.property.2 (h.injective he)⟩
  invFun p := ⟨h.symm p.val,by
    obtain ⟨a,ha,he⟩ := p.property.1
    simpa only [← he,Homeomorph.symm_apply_apply] using ha,
    by
      intro he
      apply p.property.2
      calc
        p.val = h (h.symm p.val) := (h.apply_symm_apply p.val).symm
        _ = h x := congrArg h he⟩
  left_inv p := by apply Subtype.ext; exact h.symm_apply_apply p.val
  right_inv p := by apply Subtype.ext; exact h.apply_symm_apply p.val
  continuous_toFun := (h.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (h.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- No restriction to an artificially selected cone branch occurs here. -/
theorem every_punctured_cone_open_has_standard_sphere_retract
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (hκ : 2 ≤ Fintype.card κ) (U : Set (ConeSpace ι κ))
    (hU : IsOpen U) (hzero : productZero ∈ U) :
    Nonempty (ContinuousSectionPair
      (UnitSphere (Fin (Fintype.card ι + 2))) (PuncturedIn U productZero)) := by
  let d := Fintype.card κ - 2
  let e : ConeSpace ι κ ≃ₜ ConeSpace ι (Fin (d+2)) := coneCoordinatesExtra hκ
  let V : Set (ConeSpace ι (Fin (d+2))) := e '' U
  have hV : IsOpen V := e.isOpenMap U hU
  have he0 : e productZero = productZero := coneCoordinatesExtra_zero hκ
  have hv0 : productZero ∈ V := ⟨productZero,hzero,he0⟩
  obtain ⟨p⟩ := punctured_open_has_sphere_retract (ι := ι) d V hV hv0
  have hPunctured : PuncturedIn U productZero ≃ₜ PuncturedOpen d V := by
    change PuncturedIn U productZero ≃ₜ PuncturedIn V productZero
    have hh := puncturedImage e U productZero
    rw [he0] at hh
    exact hh
  exact ⟨transportSectionPair p planeSphereFinHomeomorph.symm hPunctured.symm⟩

end GS.NonmanifoldFinal
