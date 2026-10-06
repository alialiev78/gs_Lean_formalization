module

public import GS.NonmanifoldObstruction.OpenGerms

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

set_option autoImplicit false

/-!
# Exact transport of the original local Euclidean property

The auxiliary intrinsic definition is proved equivalent to EuclideanAtSubset,
not silently substituted for it. All transfer lemmas are elementary topology;
none assert invariance of dimension or a homological computation.
-/
noncomputable section
open GS GS.NonmanifoldObstruction
namespace GS.NonmanifoldFinal

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local Euclidean charts stated directly on a topological space. -/
def EuclideanAt (x : X) : Prop :=
  ∃ (U : Set X), IsOpen U ∧ x ∈ U ∧
    ∃ (n : ℕ) (V : Set (EuclideanSpace ℝ (Fin n))), IsOpen V ∧
      Nonempty (U ≃ₜ V)

/-- Flatten an ambient-open restriction of a subtype. -/
def subtypeOpenIntersection (S U : Set X) :
    ↥(Subtype.val ⁻¹' U : Set S) ≃ₜ ↥(S ∩ U) where
  toFun a := ⟨a.val.val,a.val.property,a.property⟩
  invFun a := ⟨⟨a.val,a.property.1⟩,a.property.2⟩
  left_inv a := rfl
  right_inv a := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The old ambient-subset definition and intrinsic subtype charts agree. -/
theorem euclideanAtSubset_iff (S : Set X) (x : X) (hx : x ∈ S) :
    EuclideanAtSubset S x ↔ EuclideanAt (⟨x,hx⟩ : S) := by
  constructor
  · rintro ⟨_,U,hU,hxU,n,V,hV,⟨h⟩⟩
    exact ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU,
      n,V,hV,⟨(subtypeOpenIntersection S U).trans h⟩⟩
  · rintro ⟨A,hA,hxA,n,V,hV,⟨h⟩⟩
    obtain ⟨U,hU,hUA⟩ := isOpen_induced_iff.mp hA
    have hxU : x ∈ U := by
      change (⟨x,hx⟩ : S) ∈ Subtype.val ⁻¹' U
      rw [hUA]
      exact hxA
    have he : (Subtype.val ⁻¹' U : Set S) ≃ₜ A :=
      Homeomorph.setCongr hUA
    exact ⟨hx,U,hU,hxU,n,V,hV,
      ⟨(subtypeOpenIntersection S U).symm.trans (he.trans h)⟩⟩

/-- Transfer a chart along a global homeomorphism. -/
theorem euclideanAt_of_homeomorph (h : X ≃ₜ Y) (x : X)
    (hx : EuclideanAt x) : EuclideanAt (h x) := by
  rcases hx with ⟨U,hU,ha,n,V,hV,⟨c⟩⟩
  exact ⟨h '' U,h.isOpenMap U hU,⟨x,ha,rfl⟩,n,V,hV,
    ⟨(restrictImage h U).symm.trans c⟩⟩

/-- Apply the preceding universe-polymorphic lemma in both directions. -/
theorem euclideanAt_homeomorph (h : X ≃ₜ Y) (x : X) :
    EuclideanAt x ↔ EuclideanAt (h x) := by
  constructor
  · exact euclideanAt_of_homeomorph h x
  · intro hx
    simpa only [h.symm_apply_apply] using
      euclideanAt_of_homeomorph h.symm (h x) hx

/-- Passing to an open subspace neither creates nor destroys a chart at a point. -/
theorem euclideanAt_open_iff (S : Set X) (hS : IsOpen S) (x : S) :
    EuclideanAt x ↔ EuclideanAt x.val := by
  constructor
  · rintro ⟨A,hA,hx,n,V,hV,⟨c⟩⟩
    exact ⟨Subtype.val '' A,hS.isOpenMap_subtype_val A hA,
      ⟨x,hx,rfl⟩,n,V,hV,⟨(flattenImage S A).symm.trans c⟩⟩
  · rintro ⟨U,hU,hxU,n,V,hV,⟨c⟩⟩
    let A : Set U := Subtype.val ⁻¹' S
    have hA : IsOpen A := hS.preimage continuous_subtype_val
    let B : Set V := c '' A
    have hB : IsOpen B := c.isOpenMap A hA
    let C : Set (EuclideanSpace ℝ (Fin n)) := Subtype.val '' B
    have hC : IsOpen C := hV.isOpenMap_subtype_val B hB
    let D : Set S := Subtype.val ⁻¹' U
    have hD : IsOpen D := hU.preimage continuous_subtype_val
    let swap : ↥(S ∩ U) ≃ₜ ↥(U ∩ S) := Homeomorph.setCongr (Set.inter_comm S U)
    let cD : D ≃ₜ A := ((subtypeOpenIntersection S U).trans swap).trans
      (subtypeOpenIntersection U S).symm
    exact ⟨D,hD,hxU,n,C,hC,
      ⟨(cD.trans (restrictImage c A)).trans (flattenImage V B)⟩⟩

/-- The pointed OPEN local model transports the exact chart property. -/
theorem euclideanAt_pointedOpenModel {x : X} {y : Y}
    (g : PointedOpenModel X Y x y) : EuclideanAt x ↔ EuclideanAt y := by
  let a : g.source := ⟨x,g.source_point⟩
  calc
    EuclideanAt x ↔ EuclideanAt a :=
      (euclideanAt_open_iff g.source g.source_open a).symm
    _ ↔ EuclideanAt (g.chart a) := euclideanAt_homeomorph g.chart a
    _ ↔ EuclideanAt (g.chart a).val :=
      euclideanAt_open_iff g.target g.target_open (g.chart a)
    _ ↔ EuclideanAt y := by rw [g.map_point g.source_point]

/-- The negative form used at the end of a genuine nonmanifold proof. -/
theorem not_euclideanAt_of_pointedOpenModel {x : X} {y : Y}
    (g : PointedOpenModel X Y x y) (hy : ¬ EuclideanAt y) : ¬ EuclideanAt x := by
  intro hx
  exact hy ((euclideanAt_pointedOpenModel g).mp hx)

end GS.NonmanifoldFinal
