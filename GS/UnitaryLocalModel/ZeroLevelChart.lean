module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Restrict a product-valued partial homeomorphism to its zero level. -/
noncomputable section
open Set
namespace GS.UnitaryLocalModel
variable {X F E : Type*} [TopologicalSpace X] [TopologicalSpace F]
  [TopologicalSpace E] [Zero F]

def zeroLevelSource (e : OpenPartialHomeomorph X (F × E)) (p : X → Prop) : Set {x // p x} :=
  {x | x.val ∈ e.source}

def zeroLevelTarget (e : OpenPartialHomeomorph X (F × E)) : Set E :=
  {y | (0,y) ∈ e.target}

/-- The equality of the level conditions is required only on the chart source. -/
def zeroLevelHomeomorph (e : OpenPartialHomeomorph X (F × E)) (p : X → Prop)
    (hp : ∀ x ∈ e.source, p x ↔ (e x).1 = 0) :
    zeroLevelSource e p ≃ₜ zeroLevelTarget e where
  toFun x := ⟨(e x.val.val).2, by
    have hh : e x.val.val = (0,(e x.val.val).2) :=
      Prod.ext ((hp _ x.property).mp x.val.property) rfl
    change (0,(e x.val.val).2) ∈ e.target
    rw [← hh]
    exact e.map_source x.property⟩
  invFun y := ⟨⟨e.symm (0,y.val), (hp _ (e.map_target y.property)).mpr
    (congrArg Prod.fst (e.right_inv y.property))⟩, e.map_target y.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hh : e x.val.val = (0,(e x.val.val).2) :=
      Prod.ext ((hp _ x.property).mp x.val.property) rfl
    change e.symm (0,(e x.val.val).2) = x.val.val
    rw [← hh, e.left_inv x.property]
  right_inv y := by
    apply Subtype.ext
    exact congrArg Prod.snd (e.right_inv y.property)
  continuous_toFun := by
    have hc : Continuous (fun x : zeroLevelSource e p => e x.val.val) :=
      e.continuousOn.restrict.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
          (fun x => x.property))
    exact hc.snd.subtype_mk _
  continuous_invFun := by
    have hc : Continuous (fun y : zeroLevelTarget e => e.symm (0,y.val)) :=
      e.continuousOn_symm.restrict.comp
        ((continuous_const.prodMk continuous_subtype_val).subtype_mk
          (fun y => y.property))
    exact (hc.subtype_mk _).subtype_mk _

end GS.UnitaryLocalModel
